import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51640_aux

variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure XW where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat

structure Inst where
  NN : Nat
  AA : Nat
  HX : Nat
  HY : Nat
  segsX : List (ℕ × ℕ)
  segsY : List (ℕ × ℕ)
  rawP : List ℕ
  TG : ℕ

def segOk (AA : ℕ) (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)

structure InstOk (I : Inst) : Prop where
  segX_ok : I.segsX.all (segOk I.AA) = true
  segY_ok : I.segsY.all (segOk I.AA) = true
  HX_eq : I.HX = bitsOf I.segsX
  HY_eq : I.HY = bitsOf I.segsY
  AA_TG : I.AA &&& I.TG = I.AA
  TG_lt : I.TG < 2 ^ I.NN
  AA_lt : I.AA < 2 ^ I.NN
  raw_good : I.rawP.all (fun w => I.segsX.all (segGood w 0) && I.segsY.all (segGood w I.NN)) = true
  rawP_len : I.rawP.length = 8

noncomputable section coreC
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def spC (NN : Nat) (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def covC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (spC NN d l w.s) ih) v
def twiceC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (spC NN d l w.s) (covC NN d l t)) ih) v
def hitC (HX HY : Nat) (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hitsC (HX HY : Nat) (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hitC HX HY f e))) (m))
def flagC (NN AA : Nat) (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (spC NN d l w.s) o) AA
def rectC (NN AA HX HY : Nat) (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flagC NN AA d l o w :: m)) (true) (hitsC HX HY (flagC NN AA d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def joinC (HX HY : Nat) (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hitsC HX HY f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hitsC HX HY f c.b)) (hitsC HX HY f c.a)) cs
def bipC (NN AA HX HY : Nat) (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => joinC HX HY ih f cs [f] [] []) (flagC NN AA false l o w)) v
def anyEC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hitsC HX HY f t)) m
def rmFC (HX HY : Nat) (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hitC HX HY f e)) m
def starC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyEC HX HY (rmFC HX HY f t))) false (hitsC HX HY f (rmFC HX HY f t))) (anyEC HX HY t)) (hitsC HX HY f t)) m
def flkC (NN AA : Nat) (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flagC NN AA false l o w)) v
def mkXC (NN : Nat) (d : Bool) (l o : Nat) (v : List W) : List XW :=
  List.rec (motive := fun _ => List XW) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (spC NN d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) fun remaining =>
    Bool.rec (motive := fun _ => Bool) false
      (kids (child f g) e n remaining a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v))
      (Nat.beq (Nat.land remaining g) g)
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Bool.rec (motive := fun _ => Bool) (Nat.beq dc 0) true (Nat.beq da 0)))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : XW → Bool) (xs : List XW) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : XW → XW → Bool) (xs : List XW) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : XW → XW → Bool) (xs : List XW) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : XW → XW → Bool) (xs : List XW) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wstC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twiceC NN d l v)
def nodeC (NN : Nat) (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cvC (NN : Nat) (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)
def tstC (NN AA HX HY : Nat) (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flkC NN AA l (wstC NN d l v) v (starC HX HY))) false (bipC NN AA HX HY l (wstC NN d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rectC NN AA HX HY d l (wstC NN d l v) v [])) (Nat.beq n e)) v.length
def mvC (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def lookC (NN AA HX HY : Nat) (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => cvC NN (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1))) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => cvC NN (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1))) fuel
end coreC

def bigNat_0 : Nat := 0xffffeffffefbffff7fffbffff7bfffddffffbfffdeffffeeffffdeffff7bffff7bdbffff7bfffbbfffbbbffeb56b6ab7fffeaaffffd55fffab7fffdbfffedad5b56affffdb55affffb7fffed5ad6dab7fffdbfffed6adaffffbffff6dbfff0000000000000000
def bigNat_1 : Nat := 0x14a94954800015500002aa000548000240001252a4a95000024aa500004800012a5292548000240001295250000400009240000000000000000000
def bigNat_2 : Nat := 0x10000100001040000800040000840002200004000210000110000210000840000842400008400044000444000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0x1ffffc00000000000000000000000000000001ffffc000000000000000000007fffe07fff07fff07000000004064043804808700908e46404632023000002000808700084808c24047800080146408632043000414810c2043c49223c000000000000000004046d54460001230048800a30800c440091802442827a600042c2008508010708484597004b7804eb83804600006030000002000000400023000018000000103000000000542000037fffe040c01a3000018000010a1a00003ffff6dbffffb1b26c7ec74e930
def bigNat_4 : Nat := 0x7fffe07fff800000000000000000000000000007fffe0787fffef000007fff700000020200006068000c0d22022a50060c10307800810204180d308b0181860c0d0000208500c0c10607884484181e06068c308a80000000000000000082180061808120c048321d8c023a9800826020984040382040d04081a1094ba03c054ba78000006bd3802180103000000000000001100002800001bfffe00c18102000018458000030000010210c2800001bfffec62c2ffff80000618000289adfbe3e7ad990
def bigNat_5 : Nat := 0x1ffff81fffe07fffef007fffef7fff700000000000000000001f110006e28006c52003f0001e000000810006e12094007e0003e081024052003f0001e1a05b000d800370d801b00000000000000000104a0018a010245009140215010432081148045208088c044ab600556c00a6d2780066d2786dd380000004a00008000000008800001400002b7fffc000000204040800001b05affff800000c181602b7fffc00000d02d80000000006c00003a33cd08dd25e728
def bigNat_6 : Nat := 0x7fffe00007fffef000003ffff00003c000001ffffbc000007fffef7b000000000000000000001024011015141402a482a077000152800a94185a00ac0524836a005250029281a802da002a28015141ad000549015240921dc000000000000000002080206002224f01000024d817800001247080001e10102052265e000000c4937bd880030080180801808802816008800000a00000155fff800000000000c2d0056000001b5000000000000d4016d800000000000d68000000000006dbfff7c284fed028b254b
def bigNat_7 : Nat := 0x3ffff7fff80000001ffffbdfffef000000000000000000000000000000000140019815003700001400001b0000d80900008500370000000360001b01ab50000003300019812912006e001b8000050000000000000000004110c1810c408886122188606208c0d14673299cc02120c063279e664f79081c0081081c091060110e09110c04000a000000aaffffc00000000000000000d800056affffc00000000000000d5ac00000000000000d6adaffffbffff00000051ff4ca4c6a68795
def bigNat_8 : Nat := 0x7fffeffff000000000003ffff7fffbdffffdc0000000000000000000000000000000000000001200015219e000033800005800019c000ce01b52a60006380000006380031c012a58930433c0219e0000000670019c0000160000000000000000008203060030830f1863c6108180110301847c311f1ec23f0e80380080700200e0110200e0120180a030102030b0000ab7fffe000000000000000000000000dad5b0000000000000000000000d5ad6dab7fffdbfffe0000000000000000000084bd5419e9fb170e
def bigNat_9 : Nat := 0x1ffffc0000007fffeffff7fffef7fffb8000000000000000000000000000000000000000000000000000000016ad68009e000013c00002600009e0004f00125ab42857c0024a217c004be00000000000bc0005e0000000178005e0000058000000000000000000fc1c0801c0020fe043f820fe07a1fc1c078001e00003c00003c0080780200f0020000f00201e0101c00201c0b56b60000000000000000000000000000000dad5b56affffdb55affffb7fffe00000000000000000000000000000000000000a4cfbb63b53967a1
def bigNat_10 : Nat := 0x1ffffdffffdf000000000000000000000000000000000000000000000000000000000000000000000000000004894c04e000005c00000b80004e0002700000000000180000000180000c000000000000c000060000000018000600000060000000000000000000ffe00ffe00fbf0007c003f00043e0001f8003e0010fc0008fc0010f80043f0004213f00043e0023e00203e00b56b6ab7fffeaaffffd55fffab7fffdbfffe0000000000000000000000000000000000000000000000000000000000000000026863f8391937ac7
def bigNat_11 : Nat := 0xffffeffffefbffff7fffbffff7bfffddffffbfffdeffffeeffffdeffff7bffff7bdbffff7bfffbbfffbbbffeb56b6ab7fffeaaffffd55fffab7fffdbfffedad5b56affffdb55affffb7fffed5ad6dab7fffdbfffed6adaffffbffff6dbfffffffffffffffffff
def NN0 : Nat := 821
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 78), (78, 81), (81, 84), (84, 87), (87, 106), (106, 124), (124, 126), (126, 129), (129, 132), (132, 134), (134, 136), (136, 139), (139, 141), (141, 144), (144, 162), (162, 165), (165, 183), (183, 186), (186, 188), (188, 190), (190, 193), (193, 196), (196, 199), (199, 201), (201, 204), (204, 206), (206, 209), (209, 211), (211, 213), (213, 216), (216, 235), (235, 238), (238, 256), (256, 258), (258, 261), (261, 263), (263, 265), (265, 267), (267, 270), (270, 273), (273, 292), (292, 294), (294, 296), (296, 299), (299, 301), (301, 303), (303, 306), (306, 309), (309, 311), (311, 313), (313, 316), (316, 318), (318, 321), (321, 324), (324, 342), (342, 345), (345, 363), (363, 366), (366, 368), (368, 370), (370, 385), (385, 387), (387, 389), (389, 391), (391, 393), (393, 412), (412, 414), (414, 416), (416, 418), (418, 420), (420, 439), (439, 442), (442, 444), (444, 446), (446, 448), (448, 451), (451, 454), (454, 456), (456, 459), (459, 461), (461, 463), (463, 466), (466, 468)]
def segsY0 : List (ℕ × ℕ) := [(468, 482), (482, 486), (486, 490), (490, 506), (506, 510), (510, 526), (526, 531), (531, 550), (550, 553), (553, 558), (558, 563), (563, 582), (582, 587), (587, 604), (604, 609), (609, 628), (628, 632), (632, 652), (652, 657), (657, 674), (674, 693), (693, 697), (697, 714), (714, 719), (719, 738), (738, 755), (755, 774), (774, 780), (780, 800), (800, 820)]
def rawP0 : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8, bigNat_9, bigNat_10]
def TG0 : ℕ := bigNat_11
def I : Inst := ⟨NN0, AA0, HX0, HY0, segsX0, segsY0, rawP0, TG0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok0 : segsX0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok0 : segsY0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq0 : HX0 = bitsOf segsX0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq0 : HY0 = bitsOf segsY0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG0 : AA0 &&& TG0 = AA0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt0 : TG0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt0 : AA0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good0 : rawP0.all (fun w => segsX0.all (segGood w 0) && segsY0.all (segGood w NN0)) = true := by decide +kernel
lemma IOk : InstOk I := ⟨segX_ok0, segY_ok0, HX_eq0, HY_eq0, AA_TG0, TG_lt0, AA_lt0, raw_good0, rfl⟩

section engine

noncomputable section core
abbrev sp := spC I.NN
abbrev cov := covC I.NN
abbrev twice := twiceC I.NN
abbrev hit := hitC I.HX I.HY
abbrev hits := hitsC I.HX I.HY
abbrev flag := flagC I.NN I.AA
abbrev rect := rectC I.NN I.AA I.HX I.HY
abbrev join := joinC I.HX I.HY
abbrev bip := bipC I.NN I.AA I.HX I.HY
abbrev anyE := anyEC I.HX I.HY
abbrev rmF := rmFC I.HX I.HY
abbrev star := starC I.HX I.HY
abbrev flk := flkC I.NN I.AA
abbrev mkX := mkXC I.NN
abbrev wst := wstC I.NN
abbrev node := nodeC I.NN
abbrev cv := cvC I.NN
abbrev tst := tstC I.NN I.AA I.HX I.HY
abbrev mv := mvC I.NN I.AA I.HX I.HY
abbrev look := lookC I.NN I.AA I.HX I.HY
abbrev look1 := look1C I.NN I.AA I.HX I.HY
end core

lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb I.NN d s i) := by
  cases d <;> simp [sp, spC, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (I.NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov, covC]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq I.NN d S w.s i := by
  simp only [nl, wst, wstC, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this

section engine_ok
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same I.segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same I.segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (I.NN + i) = s.testBit (I.NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all (segOk I.AA) = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → I.AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + I.AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ I.segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ I.segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, hitC, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) I.HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) I.HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [IOk.HX_eq] at a3; rw [IOk.HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg I.NN m T i ∧ I.AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (I.NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb I.NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (I.NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (I.NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : XW := ⟨w, w.s, Nat.shiftRight w.s I.NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Bool.rec (motive := fun _ => Bool) (Nat.beq dc 0) true (Nat.beq da 0) = true := by
        rcases this with h | h
        · simp [h]
        · cases Nat.beq da 0 <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s I.NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → I.AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (I.NN + j1) = w.testBit (I.NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht I.NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → I.AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq I.NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb I.NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht I.NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := I.NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simpa only [cv, cvC, hcov] using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (I.NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (I.NN + i) = (a.s ^^^ m).testBit (I.NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : XW → Bool} {xs : List XW} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : XW → XW → Bool} {xs : List XW} {q : ℕ} {a c : XW} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : XW → XW → Bool} {xs : List XW} {q q' : ℕ} {a c : XW} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : XW => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : XW → XW → Bool} {xs : List XW} (hp : pairsN h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg XW.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look, lookC] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pos_eq] at h
    have h := cv_ok X hs hm.1 h
    rw [bR] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (XW → XW → Bool) → List XW → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1, look1C] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pos_eq] at h
    have h := cv_ok X hs hl h
    rw [bR] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e))
end sound

end engine_ok
def xw (e : ℕ × ℕ) : ℕ := I.rawP.getD e.1 0 ||| I.rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := I.rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ I.NN - 1
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i bad =>
  let a := I.rawP.getD i 0
  let b := Nat.shiftRight a I.NN
  let bad0 := bif Z.testBit i then (a ||| b) &&& FULL else 0
  let bad1 := bif Z.testBit (8+i) then (a &&& b &&& FULL) ^^^ FULL else 0
  bad ||| bad0 ||| bad1) 0
def lz (Z : ℕ) : ℕ := Nat.land I.AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) I.NN)
def tz (Z : ℕ) : ℕ := Nat.land I.TG (mz Z)

section engine_ok2
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg I.NN (mz Z) (tz Z) i ∧ I.AA.testBit i = true := by
  have hA : I.AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : I.TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) IOk.AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (I.NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< I.NN).testBit (I.NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le IOk.TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 IOk.raw_good w (by simpa [rawG, rawL, six] using hw)
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySubC (NN : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (covC NN d l t)) l)) true
    (st (Nat.lor c (spC NN d l w.s)) fun c => ih c fun r => h (w :: r))) v
abbrev anySub := anySubC I.NN
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topCC (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
abbrev topC := topCC I.NN I.AA I.HX I.HY
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startvC (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topCC NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
abbrev startv := startvC I.NN I.AA I.HX I.HY
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : XW → XW → Bool} {xs : List XW} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : XW => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startvC nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
theorem imp_of_live {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
theorem imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 (L - 1) t p.1 p.2 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr h)
lemma one {E Q : List (ℕ × ℕ)} {K t : ℕ} (h : chk E Q 0 K t FF 1 = false) : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩

end engine_ok2

end engine
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
theorem fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

def UniqueNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j

lemma UniqueNot.tail {g : Gate} {gs : List Gate} (h : UniqueNot (g :: gs)) : UniqueNot gs := by
  intro i j hi hj
  let i' : Fin (g :: gs).length := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let j' : Fin (g :: gs).length := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  have he := congrArg Fin.val (h i' j' hi hj)
  apply Fin.ext
  dsimp [i', j'] at he
  omega

lemma UniqueNot.tail_of_head {g : Gate} {gs : List Gate} (h : UniqueNot (g :: gs)) (hg : g.op = .not) :
    ∀ a ∈ gs, a.op ≠ .not := by
  intro a ha hnot
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  let j : Fin (g :: gs).length := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let z : Fin (g :: gs).length := ⟨0, by simp⟩
  have hj : ((g :: gs).get j).op = .not := by
    change (gs.get i).op = .not
    rw [hi, hnot]
  have he := congrArg Fin.val (h z j hg hj)
  dsimp [z, j] at he
  omega

lemma Live.add_binary {m T k t : ℕ} {S : Set ℕ} {S1 : Finset ℕ} {d : Bool} {a b : ℕ}
    (hl : Live Z0 m T k t S1) (hs : (S1 : Set ℕ) ⊆ insert (op d a b) S) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ k' ≤ k + 1, ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ S ∧ Live Z0 m T k' t S' := by
  by_cases hg : op d a b ∈ S1
  · by_cases hab : a = b
    · subst hab
      rw [op_self] at hs
      exact ⟨k, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
    · refine ⟨k + 1, le_rfl, insert a (insert b (S1.erase (op d a b))), ?_,
        .bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

lemma ex_mono_live {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k ≤ gs.length, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k 0 S0 := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact ⟨0, by simp, _, by simpa [ex] using getD_mem hw h0 i, .stop⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → ∃ k ≤ (g :: gs).length, ∃ S0 : Finset ℕ,
        (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k 0 S0 := by
      intro h
      obtain ⟨k, hk, S0, hS0, hl⟩ := ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT
      exact ⟨k, by simp; omega, S0, hS0, hl⟩
    have go := ih (w ++ [gv m w g]) (insert (gv m w g) S) (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    have hop := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    rcases hop with rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        obtain ⟨k, hk, S0, hS0, hl⟩ := go
        obtain ⟨k', hk', S', hS', hl'⟩ := Live.add_binary (d := false) hl hS0 (rd i) (rd j)
        exact ⟨k', by simp; omega, S', hS', hl'⟩
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        obtain ⟨k, hk, S0, hS0, hl⟩ := go
        obtain ⟨k', hk', S', hS', hl'⟩ := Live.add_binary (d := true) hl hS0 (rd i) (rd j)
        exact ⟨k', by simp; omega, S', hS', hl'⟩

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    UniqueNot gs → (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length 1 S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg huniq hnot hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have hwm_stay : gv m w g ∈ S → ∀ x ∈ w ++ [gv m w g], x ∈ S := fun h x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hw x hx; exact h
    have hwm_ins : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact Or.inr (hw x hx); exact Or.inl rfl
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs huniq.tail hnot' hT with hs | ⟨S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs huniq.tail hnot' hT with hs | ⟨S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have hgsMono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
          intro g hg
          have hne := huniq.tail_of_head (by rfl) g hg
          have ho := (hgs g hg).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
          rcases ho with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hne h).elim
        obtain ⟨k, hk, S1, hS1, hl1⟩ := ex_mono_live m gs
          (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S)
          hwm_ins (Or.inr h0) (Or.inr hm) hgsMono hT
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) 1 (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨_, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))

lemma scan_eq_any (p : XW → Bool) (xs : List XW) : scan p xs = xs.any p := by
  induction xs with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (motive := fun _ => Bool) (scan p ws) true (p w) = _
    rw [ih, bR]
    cases h : p w <;> simp [List.any_cons, h]

lemma pairsC_eq (H : ℕ) (f : XW → XW → Bool) (a : XW) (xs : List XW) :
    pairsC H f (a :: xs) =
      (xs.any (fun x => hb H (a.s + x.s) && f a x) || pairsC H f xs) := by
  have he : (fun x : XW => bif hb H (a.s + x.s) then f a x else false) =
      (fun x : XW => hb H (a.s + x.s) && f a x) := by
    funext x
    cases hb H (a.s + x.s) <;> rfl
  change Bool.rec (motive := fun _ => Bool) (pairsC H f xs) true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (f a x) (hb H (a.s + x.s))) xs) = _
  rw [bR, scan_eq_any]
  simp only [bR, he]
  cases xs.any (fun x => hb H (a.s + x.s) && f a x) <;> rfl

def possibleInputPair (H : ℕ) (v : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a rest later =>
      Bool.rec (motive := fun _ => Bool) later true (rest.any fun b => hb H (a.s + b.s))) v

lemma possibleInputPair_cons (H : ℕ) (a : W) (v : List W) :
    possibleInputPair H (a :: v) = ((v.any fun b => hb H (a.s + b.s)) || possibleInputPair H v) := by
  change Bool.rec (motive := fun _ => Bool) (possibleInputPair H v) true
    (v.any fun b => hb H (a.s + b.s)) = _
  cases v.any (fun b => hb H (a.s + b.s)) <;> rfl

lemma mkXC_map (nn : ℕ) (d : Bool) (l o : ℕ) (v : List W) :
    mkXC nn d l o v = v.map (fun w => ⟨w, w.s, Nat.shiftRight w.s nn, Nat.land (spC nn d l w.s) o⟩) := by
  induction v with
  | nil => rfl
  | cons w v ih =>
    change _ :: mkXC nn d l o v = _ :: _
    rw [ih]

lemma fs_eq_filter (xs : List XW) : fs xs = xs.filter (fun x => !Nat.beq x.w.r 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0) = _
    rw [ih]
    cases h : Nat.beq x.w.r 0 <;> simp [h]

lemma fr_eq_filter (xs : List XW) : fr xs = xs.filter (fun x => Nat.beq x.w.r 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0) = _
    rw [ih]
    cases h : Nat.beq x.w.r 0 <;> simp [h]

lemma pairImpossible {H nn l o : ℕ} {d : Bool} {v : List W} (f : XW → XW → Bool)
    (h : possibleInputPair H v = false) :
    pairsC H f (fs (mkXC nn d l o v)) = false := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [possibleInputPair_cons, Bool.or_eq_false_iff] at h
    let a' : XW := ⟨a, a.s, Nat.shiftRight a.s nn, Nat.land (spC nn d l a.s) o⟩
    change pairsC H f (Bool.rec (motive := fun _ => List XW)
      (a' :: fs (mkXC nn d l o v)) (fs (mkXC nn d l o v)) (Nat.beq a.r 0)) = _
    cases ha : Nat.beq a.r 0
    · change pairsC H f (a' :: fs (mkXC nn d l o v)) = false
      rw [pairsC_eq, ih h.2, Bool.or_false]
      apply List.any_eq_false.mpr
      intro x hx
      rw [fs_eq_filter, List.mem_filter, mkXC_map, List.mem_map] at hx
      obtain ⟨⟨w, hw, rfl⟩, _⟩ := hx
      intro hit
      simp only [Bool.and_eq_true] at hit
      exact List.any_eq_false.mp h.1 w hw hit.1
    · exact ih h.2

lemma noGenerated {nn l o : ℕ} {d : Bool} {v : List W}
    (h : v.any (fun w => Nat.beq w.r 0) = false) : fr (mkXC nn d l o v) = [] := by
  rw [fr_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  rw [mkXC_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact List.any_eq_false.mp h w hw

lemma noMoves {v : List W} (h : v.any (fun w => Nat.beq w.r 0) = false)
    (nn aa hx hy l m g k z y : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool) :
    mvC nn aa hx hy F l m g k 0 z v y = false := by
  have hp (f : XW → XW → Bool) : pairsN f (mkXC nn false l (wstC nn false l v) v) = false := by
    rw [pairsN, noGenerated h]; rfl
  have hnode : nodeC nn (F (Nat.sub k 1) 0) false l m g
      (Nat.sub (Nat.sub k 0) y) v.length z v pairsN = false := by
    simp only [nodeC, hp, bR, Bool.cond_self]
  simp only [mvC, show pos 0 = false from rfl, hnode, show ∀ f, prd 0 f = false by intro; rfl, bR]

lemma noNode {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodeC nn f d l m g e n z v (fun h xs => pairsC H h (fs xs)) = false := by
  simp only [nodeC, pairImpossible _ h, bR, Bool.cond_self]

lemma tst_const_false (nn aa hx hy : ℕ) (d : Bool) (l e : ℕ) (v : List W) :
    tstC nn aa hx hy d l e v (fun _ => false) = false := by
  simp only [tstC, bR, Bool.cond_self]

def relevantStart (t H ph : ℕ) (v : List W) : Bool :=
  (Nat.ble v.length 1 || (Nat.beq ph 1 && (pos t || v.any fun w => Nat.beq w.r 0))) ||
    possibleInputPair H v

lemma relevantStart_facts {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false) :
    Nat.ble v.length 1 = false ∧
      (Nat.beq ph 1 = false ∨ (t = 0 ∧ v.any (fun w => Nat.beq w.r 0) = false)) ∧
      possibleInputPair H v = false := by
  simp only [relevantStart, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
  refine ⟨h.1.1, h.1.2.imp_right ?_, h.2⟩
  rintro ⟨ht, hv⟩
  exact ⟨by cases t <;> simp [pos] at ht ⊢, hv⟩

lemma inactiveTop {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) :
    topCC nn aa hx hy l m g K H ph k t z v = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topCC, hl, noNode hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMoves hv, Bool.cond_self, tst_const_false]

def guardStart (t H ph : ℕ) (test : List W → Bool) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (test v) (relevantStart t H ph v)

lemma guardStart_eq {t H ph : ℕ} {test : List W → Bool}
    (h : ∀ v, relevantStart t H ph v = false → test v = false) :
    guardStart t H ph test = test := by
  funext v
  unfold guardStart
  cases hv : relevantStart t H ph v
  · exact (h v hv).symm
  · rfl

lemma inactiveStart {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) :
    startvC nn aa hx hy l m g B K t p H ph v = false := by
  simp only [startvC, child, st_eq, inactiveTop h, bR, Bool.cond_self]

noncomputable def searchInputs (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (guardStart t H ph (test nn aa hx hy l m g B p))))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma searchInputs_eq {E Q : List (ℕ × ℕ)} {Z K t H ph : ℕ}
    {test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool}
    (h : ∀ nn aa hx hy l m g B p v, relevantStart t H ph v = false →
      test nn aa hx hy l m g B p v = false) :
    searchInputs E Q Z K t H ph test =
      (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
        frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
          st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
          anySubC nn (pos t) l v 0 (test nn aa hx hy l m g B p)))
        (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z) := by
  simp only [searchInputs, guardStart_eq (h _ _ _ _ _ _ _ _ _)]

noncomputable def chkFast (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p =>
    startvC nn aa hx hy l m g B K t p H ph)

lemma chkFast_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkFast E Q Z K t H ph = chk E Q Z K t H ph := by
  unfold chkFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStart h nn aa hx hy l m g B K p)]
  rfl
set_option maxHeartbeats 0 in
noncomputable def notCandidate (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v : List W) (a : W) : Bool :=
  nots f m g e n z q v [a]

set_option maxHeartbeats 0 in
lemma nots_cons (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v : List W) (a : W) (r : List W) :
    nots f m g e n z q v (a :: r) =
      (notCandidate f m g e n z q v a || nots f m g e n z q v r) := by
  unfold notCandidate
  unfold nots
  dsimp only
  simp only [bR]
  have fact (d x : Bool) : (bif d then true else x) = ((bif d then true else false) || x) := by
    cases d <;> rfl
  exact fact _ _

set_option maxHeartbeats 0 in
lemma nots_true_iff (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) :
    nots f m g e n z q v r = true ↔
      ∃ a ∈ r, notCandidate f m g e n z q v a = true := by
  induction r with
  | nil => simp [nots]
  | cons a r ih =>
    rw [nots_cons, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨b,hb,ht⟩)
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp [hb], ht⟩
    · rintro ⟨b,hb,ht⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl ht
      · exact Or.inr ⟨b,hb,ht⟩

set_option maxHeartbeats 0 in
lemma nots_some_bin (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W)
    (h : nots f m g e n z q v r = true) :
    ∃ b : Fin 8, nots f m g e n z q v (r.filter fun a => a.s % 8 == b.val) = true := by
  obtain ⟨a,ha,hit⟩ := (nots_true_iff _ _ _ _ _ _ _ _ _).mp h
  refine ⟨⟨a.s % 8, Nat.mod_lt _ (by decide)⟩,
    (nots_true_iff _ _ _ _ _ _ _ _ _).mpr ⟨a, ?_, hit⟩⟩
  simp [ha]

set_option maxHeartbeats 0 in
def picked {X : Type} (F : X → Bool) (G : Fin 8 → X → Bool) : Prop :=
  ∀ x, F x = true → ∃ b, G b x = true

set_option maxHeartbeats 0 in
lemma Bool_pick (base : Bool) (F : Bool) (G : Fin 8 → Bool)
    (h : F = true → ∃ b, G b = true) :
    base || F = true → ∃ b, base || G b = true := by
  cases base
  · simpa using h
  · intro _
    exact ⟨0, rfl⟩

set_option maxHeartbeats 0 in
lemma tst_picked (nn aa hx hy : ℕ) (d : Bool) (l e : ℕ) (v : List W)
    (F : ℕ → Bool) (G : Fin 8 → ℕ → Bool) (hp : picked F G) :
    tstC nn aa hx hy d l e v F = true →
      ∃ b : Fin 8, tstC nn aa hx hy d l e v (G b) = true := by
  simp only [tstC, bR]
  cases h : Nat.beq v.length e
  · simp only [h, Bool.cond_false]
    cases hnext : Nat.beq v.length.succ e
    · simp only [hnext, Bool.cond_false]
      exact hp 0
    · simp only [hnext, Bool.cond_true]
      cases hb : bipC nn aa hx hy l (wstC nn d l v) v []
      · simp only [hb, Bool.cond_false]
        cases hs : flkC nn aa l (wstC nn d l v) v (starC hx hy)
        · simp only [hs, Bool.cond_false]
          exact hp 1
        · simp only [hs, Bool.cond_true]
          exact hp 0
      · simp [hb]
  · simp only [h, Bool.cond_true]
    cases hr : rectC nn aa hx hy d l (wstC nn d l v) v []
    · simp only [hr, Bool.cond_false]
      exact hp 0
    · simp [hr]

set_option maxHeartbeats 0 in
noncomputable def mvPicked (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) (y : Nat) (b : Fin 8) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (v.filter fun a => a.s % 8 == b.val))) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length

set_option maxHeartbeats 0 in
lemma mv_picked (nn aa hx hy : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) :
    mvC nn aa hx hy F l m g k t z v y = true →
      ∃ b : Fin 8, mvPicked nn aa hx hy F l m g k t z v y b = true := by
  simp only [mvC, mvPicked, bR]
  cases hnode : nodeC nn (F (k-1) t) (pos t) l m g (k-t-y) v.length z v pairsN
  · simp only [hnode, Bool.cond_false]
    cases t with
    | zero => simp [prd]
    | succ t =>
      simp only [prd, Nat.rec]
      exact nots_some_bin _ _ _ _ _ _ _ _ _
  · simp only [hnode, Bool.cond_true]
    intro _
    exact ⟨0,by simp⟩

set_option maxHeartbeats 0 in
noncomputable def topPicked (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) (b : Fin 8) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvPicked NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y b) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)

set_option maxHeartbeats 0 in
lemma top_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topCC nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPicked nn aa hx hy l m g K H ph k t z v b = true := by
  simp only [topCC, topPicked, bR]
  cases h : Nat.ble v.length 1
  · simp only [h, Bool.cond_false]
    apply tst_picked
    intro y
    cases hm : nodeC nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hm, Bool.cond_false]
      cases hc : Nat.beq ph 1
      · simp [hc]
      · simp only [hc, Bool.cond_true]
        exact mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _
    · simp only [hm, Bool.cond_true]
      intro _
      exact ⟨0,by simp⟩
  · simp only [h, Bool.cond_true]
    intro _
    exact ⟨0,by simp⟩

set_option maxHeartbeats 0 in
noncomputable def startPicked (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (b : Fin 8) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPicked NN AA HX HY l m g K H ph K t z r b) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

set_option maxHeartbeats 0 in
lemma start_picked (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startvC nn aa hx hy l m g B K t p H ph)
      (fun b v => startPicked nn aa hx hy l m g B K t p H ph v b) := by
  intro v
  simp only [startvC, startPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact top_picked _ _ _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 0 in
lemma anySub_picked (nn : ℕ) (d : Bool) (l : ℕ) (v : List W)
    (F : List W → Bool) (G : Fin 8 → List W → Bool) (hp : picked F G) (bits : ℕ) :
    anySubC nn d l v bits F = true → ∃ b : Fin 8, anySubC nn d l v bits (G b) = true := by
  induction v generalizing F G bits with
  | nil => exact hp []
  | cons a v ih =>
    let inc := Nat.lor bits (spC nn d l a.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l v)) l
    have hu (J : List W → Bool) : anySubC nn d l (a :: v) bits J =
        (bif anySubC nn d l v inc (fun r => J (a :: r)) then true else
          (bif skip then anySubC nn d l v bits J else false)) := by
      change Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l v bits J) skip)
        true (st inc fun c => anySubC nn d l v c (fun r => J (a :: r))) = _
      simp only [st_eq, bR]
    simp only [hu]
    have hs := ih (fun as => F (a :: as)) (fun b as => G b (a :: as))
      (fun as => hp (a :: as)) inc
    cases ht : anySubC nn d l v inc (fun as => F (a :: as))
    · simp only [ht, Bool.cond_false]
      cases hc : skip
      · simp [hc]
      · simp only [hc, Bool.cond_true]
        intro h
        obtain ⟨b,hb⟩ := ih F G hp bits h
        refine ⟨b, ?_⟩
        rw [hb]
        cases anySubC nn d l v inc (fun as => G b (a :: as)) <;> rfl
    · simp only [ht, Bool.cond_true]
      intro _
      obtain ⟨b,hb⟩ := hs ht
      exact ⟨b, by rw [hb]; rfl⟩

set_option maxHeartbeats 0 in
noncomputable def chkPicked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (b : Fin 8) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPicked nn aa hx hy l m g B K t p H ph r b)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

set_option maxHeartbeats 0 in
lemma chk_picked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Fin 8, chkPicked E Q Z K t H ph b = false) : chk E Q Z K t H ph = false := by
  suffices chk E Q Z K t H ph = true → False by
    cases he : chk E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chk, chkPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (start_picked _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h b).symm.trans hb)

section BinaryPartition

noncomputable def pairOne (d : Bool) (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool)
    (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' =>
    bif d then h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)
    else h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s')
      (Nat.lor a.a c.a) (Nat.land a.b c.b)) c) a

def cvOp (b : Fin 8) : Bool := b.val % 2 == 1

lemma pair_picked (h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a c : XW) :
    pair h a c = true → ∃ b : Fin 8, pairOne (cvOp b) h a c = true := by
  have h0 : cvOp 0 = false := rfl
  have h1 : cvOp 1 = true := rfl
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,pairOne,bR]
  intro h'
  cases hon : h w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · rw [hon, Bool.cond_false] at h'
    exact ⟨1, by simpa only [h1, Bool.cond_true] using h'⟩
  · exact ⟨0, by simpa only [h0, Bool.cond_false] using hon⟩

lemma scan_picked (f : XW → Bool) (q : Fin 8 → XW → Bool) (v : List XW)
    (hp : picked f q) :
    scan f v = true → ∃ b, scan (q b) v = true := by
  induction v with
  | nil => simp [scan]
  | cons a v ih =>
    have hu (F : XW → Bool) :
        scan F (a :: v) = (bif F a then true else scan F v) := by
      change Bool.rec (motive := fun _ => Bool) (scan F v) true (F a) = _
      rw [bR]
    simp only [hu]
    cases h : f a
    · simp only [h, Bool.cond_false]
      intro hr
      obtain ⟨b,hb⟩ := ih hr
      exact ⟨b,by rw [hb]; cases q b a <;> rfl⟩
    · intro _
      obtain ⟨b,hb⟩ := hp a h
      exact ⟨b,by rw [hb]; rfl⟩

lemma pairsC_picked (H : ℕ) (a : XW → XW → Bool) (q : Fin 8 → XW → XW → Bool)
    (hp : ∀ x, picked (a x) (fun b => q b x)) (xs : List XW) :
    pairsC H a xs = true → ∃ b, pairsC H (q b) xs = true := by
  induction xs with
  | nil => simp [pairsC]
  | cons x xs ih =>
    have hu (F : XW → XW → Bool) : pairsC H F (x :: xs) =
        (bif scan (fun e => bif hb H (x.s + e.s) then F x e else false) xs
          then true else pairsC H F xs) := by
      change Bool.rec (motive := fun _ => Bool) (pairsC H F xs) true
        (scan (fun e => Bool.rec (motive := fun _ => Bool) false (F x e) (hb H (x.s + e.s))) xs) = _
      simp only [bR]
    have hp' : picked (fun e => bif hb H (x.s + e.s) then a x e else false)
        (fun b e => bif hb H (x.s + e.s) then q b x e else false) := by
      intro e
      cases hc : hb H (x.s + e.s)
      · simp [hc]
      · simpa [hc] using hp x e
    simp only [hu]
    cases hc : scan (fun e => bif hb H (x.s + e.s) then a x e else false) xs
    · simp only [hc, Bool.cond_false]
      intro h
      obtain ⟨b,hb⟩ := ih h
      refine ⟨b, ?_⟩
      rw [hb]
      cases scan (fun e => bif PEqualNP.Outside.L_meta_51640_aux.hb H (x.s + e.s) then q b x e else false) xs <;> rfl
    · intro _
      obtain ⟨b,hb⟩ := scan_picked _ _ xs hp' hc
      exact ⟨b, by rw [hb]; rfl⟩

noncomputable def nodePicked (NN : Nat) (f : Nat → List W → Bool) (d : Bool)
    (l m g e n z : Nat) (v : List W) (H : Nat) (kind : Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool)
    (pairsC H (pairOne kind (f0 h)) (fs xs))
    (Bool.rec (motive := fun _ => Bool) (pairsC H (pairOne kind (f1 h)) (fs xs))
      (pairsC H (pairOne kind (f2 h)) (fs xs)) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v)) (mid f m g e (Nat.pred n) z v)

lemma node_picked (nn : ℕ) (f : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) (H : ℕ) :
    nodeC nn f d l m g e n z v (fun h xs => pairsC H h (fs xs)) = true →
      ∃ b : Fin 8, nodePicked nn f d l m g e n z v H (cvOp b) = true := by
  simp only [nodeC, nodePicked, bR]
  cases hn : Nat.ble n e
  · simp only [hn, Bool.cond_false]
    exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _
  · simp only [hn, Bool.cond_true]
    cases hs : Nat.ble n.succ e
    · simp only [hs, Bool.cond_false]
      exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _
    · simp only [hs, Bool.cond_true]
      exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _

noncomputable def topPairPicked (NN AA HX HY l m g K H ph k t z : ℕ)
    (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodePicked NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v H kind))) true (Nat.ble v.length 1)

lemma topPair_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topCC nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPairPicked nn aa hx hy l m g K H ph k t z v (cvOp b) = true := by
  simp only [topCC, topPairPicked, bR]
  cases ht : Nat.ble v.length 1
  · simp only [ht, Bool.cond_false]
    apply tst_picked
    intro y h
    dsimp only at h ⊢
    cases hx' : nodeC nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hx', Bool.cond_false] at h
      refine ⟨0, ?_⟩
      rw [h]
      cases nodePicked nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v H (cvOp 0) <;> rfl
    · obtain ⟨b,hb⟩ := node_picked _ _ _ _ _ _ _ _ _ _ _ hx'
      exact ⟨b, by simp only [hb, Bool.cond_true]⟩
  · simp only [ht, Bool.cond_true]
    exact fun _ => ⟨0,by simp⟩

noncomputable def startPairPicked (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPairPicked NN AA HX HY l m g K H ph K t z r kind) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

lemma startPair_picked (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startvC nn aa hx hy l m g B K t p H ph)
      (fun b v => startPairPicked nn aa hx hy l m g B K t p H ph v (cvOp b)) := by
  intro v
  simp only [startvC, startPairPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact topPair_picked _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def chkPairPicked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPairPicked nn aa hx hy l m g B K t p H ph r kind)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma noNodePicked {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d kind : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodePicked nn f d l m g e n z v H kind = false := by
  simp only [nodePicked, pairImpossible _ h, bR, Bool.cond_self]

lemma inactiveTopPicked {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) (kind : Bool) :
    topPairPicked nn aa hx hy l m g K H ph k t z v kind = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topPairPicked, hl, noNodePicked hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMoves hv, Bool.cond_self, tst_const_false]

lemma inactiveStartPicked {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) (kind : Bool) :
    startPairPicked nn aa hx hy l m g B K t p H ph v kind = false := by
  simp only [startPairPicked, child, st_eq, inactiveTopPicked h, bR, Bool.cond_self]

noncomputable def chkPairFast (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p v =>
    startPairPicked nn aa hx hy l m g B K t p H ph v kind)

lemma chkPairFast_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) :
    chkPairFast E Q Z K t H ph kind = chkPairPicked E Q Z K t H ph kind := by
  unfold chkPairFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStartPicked h nn aa hx hy l m g B K p kind)]
  rfl

lemma chkPair_picked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Bool, chkPairPicked E Q Z K t H ph b = false) : chk E Q Z K t H ph = false := by
  suffices chk E Q Z K t H ph = true → False by
    cases he : chk E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chk, chkPairPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (startPair_picked _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h (cvOp b)).symm.trans hb)

end BinaryPartition

lemma ins_distribute (o : W) (v : List W) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (h : picked f g) : ins o v f = true → ∃ b, ins o v (g b) = true := by
  induction v generalizing f g with
  | nil => exact h [o]
  | cons a r ih =>
    have step (u : List W → Bool) : ins o (a :: r) u =
        (bif Nat.ble a.s o.s then (bif Nat.beq o.s a.s then false else u (o :: a :: r))
          else ins o r (fun ws => u (a :: ws))) := by
      change Bool.rec (motive := fun _ => Bool) (ins o r (fun ws => u (a :: ws)))
        (Bool.rec (motive := fun _ => Bool) (u (o :: a :: r)) false (Nat.beq o.s a.s))
        (Nat.ble a.s o.s) = _
      rw [bR,bR]
    simp only [step]
    cases hle : Nat.ble a.s o.s
    · simp only [hle,Bool.cond_false]
      exact ih (f := fun ws => f (a :: ws)) (g := fun b ws => g b (a :: ws)) (fun ws => h (a :: ws))
    · cases he : Nat.beq o.s a.s
      · simpa only [he,hle,Bool.cond_true,Bool.cond_false] using h (o :: a :: r)
      · simp [he,hle]

lemma put_distribute (m s x y : ℕ) (v : List W) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (h : picked f g) : put m s x y v f = true → ∃ b, put m s x y v (g b) = true := by
  simp only [put,st_eq,bR]
  cases h0 : Nat.beq s 0 <;> cases h1 : Nat.beq s m <;> simp only [h0,h1,Bool.cond_true,Bool.cond_false,Bool.false_eq_true,false_implies]
  exact ins_distribute _ _ h

lemma child_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (free z : ℕ) (mk : (List W → Bool) → Bool) (mk_distribute : ∀ p q, picked p q → mk p = true → ∃ b, mk (q b) = true)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    child f free mk z = true → ∃ b, child (g b) free mk z = true := by
  simp only [child,st_eq,bR]
  cases hb : Nat.beq (z &&& free) free
  · simp [hb]
  · simpa only [hb,Bool.cond_true] using mk_distribute (f z) (fun b => g b z) (h z)

lemma kids_unfold (ch : ((List W → Bool) → Bool) → ℕ → Bool) (e n z x y a c : ℕ)
    (oa oc : Bool) (mk : (List W → Bool) → Bool) :
    kids ch e n z x y a c oa oc mk =
      ((oa && oc && ch (fun f => mk (fun r => rm a c r f)) z) ||
      ((oc && Nat.ble (n+1) e && ch (fun f => mk (fun r => rm c c r f)) (z-x)) ||
      ((oa && Nat.ble (n+1) e && ch (fun f => mk (fun r => rm a a r f)) (z-y)) ||
       (Nat.ble (n+2) e && ch mk (z-x-y))))) := by
  simp only [kids,bR]
  cases oa <;> cases oc <;> cases Nat.ble (n+1) e <;> cases Nat.ble (n+2) e <;> simp <;>
    (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> (try simp only [← Bool.not_eq_true]) <;> tauto

lemma kids_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (free e n z x y a c : ℕ) (oa oc : Bool) (mk : (List W → Bool) → Bool)
    (hm : ∀ p q, picked p q → mk p = true → ∃ b, mk (q b) = true)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    kids (child f free) e n z x y a c oa oc mk = true →
    ∃ b, kids (child (g b) free) e n z x y a c oa oc mk = true := by
  have cm (p q k : ℕ) : child f free (fun f => mk fun r => rm p q r f) k = true →
      ∃ b, child (g b) free (fun f => mk fun r => rm p q r f) k = true := by
    refine child_distribute free k _ ?_ h
    intro u v huv
    simp only [rm_eq]
    exact hm (fun r => u (r.filter _)) (fun b r => v b (r.filter _)) (fun r => huv (r.filter _))
  rw [kids_unfold]
  simp only [Bool.or_eq_true,Bool.and_eq_true]
  rintro (⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩)
  · obtain ⟨b,hb⟩ := cm a c z h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inl ⟨h1,hb⟩
  · obtain ⟨b,hb⟩ := cm c c (z-x) h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inl ⟨h1,hb⟩)
  · obtain ⟨b,hb⟩ := cm a a (z-y) h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inr (Or.inl ⟨h1,hb⟩))
  · obtain ⟨b,hb⟩ := child_distribute free (z-x-y) mk hm h h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inr (Or.inr ⟨h1,hb⟩))

lemma mid_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (m free e n z : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    mid f m free e n z v a c da dc s x y = true →
      ∃ b, mid (g b) m free e n z v a c da dc s x y = true := by
  simp only [mid,st_eq,bR]
  cases hb : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) free) free
  · simp [hb]
  · simpa only [hb,Bool.cond_true] using
      kids_distribute free e n (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) a.c c.c a.s c.s
        (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)
        (fun _ _ => put_distribute m s x y v) h

lemma pairs_distribute (f : XW → XW → Bool) (g : Fin 8 → XW → XW → Bool)
    (h : ∀ x, picked (f x) (fun b => g b x)) (v : List XW) :
    pairs f v = true → ∃ b, pairs (g b) v = true := by
  induction v with
  | nil => simp [pairs]
  | cons a r ih =>
    have he (u : XW → XW → Bool) : pairs u (a::r) = bif scan (u a) r then true else pairs u r := by
      change Bool.rec (motive := fun _ => Bool) (pairs u r) true (scan (u a) r) = _
      rw [bR]
    simp only [he]
    cases hb : scan (f a) r
    · simp only [hb,Bool.cond_false]
      intro ht
      obtain ⟨b,hb⟩ := ih ht
      exact ⟨b, by rw [hb]; cases scan (g b a) r <;> rfl⟩
    · simp only [hb,Bool.cond_true]
      intro _
      obtain ⟨b,hb⟩ := scan_picked _ _ r (h a) hb
      exact ⟨b,by rw [hb]; rfl⟩

lemma mode_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (m free e n z : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    modeF n e (mid f m free e n.pred z v) a c da dc s x y = true →
      ∃ b, modeF n e (mid (g b) m free e n.pred z v) a c da dc s x y = true := by
  have mid' := mid_distribute m free e n.pred z v a c da dc s x y h
  unfold modeF
  cases hn : Nat.ble n e
  · simp only [hn,Bool.cond_false,f0,bR]
    cases ha : Nat.beq (Nat.lor da dc) 0
    · simp [ha]
    · simpa only [ha,Bool.cond_true] using mid'
  · simp only [hn,Bool.cond_true]
    cases hs : Nat.ble n.succ e
    · simp only [hs,Bool.cond_false,f1,bR]
      cases ha : (bif Nat.beq da 0 then true else Nat.beq dc 0)
      · simp [ha]
      · simpa only [ha,Bool.cond_true] using mid'
    · simpa only [hs,Bool.cond_true,f2] using mid'

lemma pairOne_distribute (d : Bool) {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pairOne d f a c = true → ∃ b, pairOne d (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  cases d <;> simp only [pairOne,Bool.cond_false,Bool.cond_true] <;> exact h _ _ _ _ _ _ _

lemma nodeC_as_mode (NN : ℕ) (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    nodeC NN f d l m g e n z v go = go (pair (modeF n e (mid f m g e n.pred z v))) (mkXC NN d l (wstC NN d l v) v) := by
  unfold nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma pickedNode_as_mode (NN : ℕ) (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (H : ℕ) (kind : Bool) :
    nodePicked NN f d l m g e n z v H kind =
      pairsC H (pairOne kind (modeF n e (mid f m g e n.pred z v))) (fs (mkXC NN d l (wstC NN d l v) v)) := by
  unfold nodePicked modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma nodePicked_distribute {f : ℕ → List W → Bool} {branches : Fin 8 → ℕ → List W → Bool}
    (NN : ℕ) (d : Bool) (l m g e n z : ℕ) (v : List W) (H : ℕ) (kind : Bool)
    (h : ∀ j, picked (f j) (fun b => branches b j)) :
    nodePicked NN f d l m g e n z v H kind = true →
      ∃ b, nodePicked NN (branches b) d l m g e n z v H kind = true := by
  simp only [pickedNode_as_mode]
  exact pairsC_picked H _ _ (fun x y => pairOne_distribute kind
    (fun _ _ _ _ _ _ _ => mode_distribute m g e n z v _ _ _ _ _ _ _ h) x y) _

lemma look1C_step (nn aa hx hy l m g K fuel k t z : ℕ) (v : List W) :
    look1C nn aa hx hy l m g K fuel.succ k t z v =
      cvC nn (pos t) l v (bif Nat.ble v.length 1 then true else
        tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y)) := by
  change cvC nn (pos t) l v (Bool.rec (motive := fun _ => Bool)
      (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y) true
          (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) = _
  simp only [bR]

noncomputable def demanded (Z : ℕ) : List W :=
  let bank := avl [] (mz Z) (rawL [])
  bank.filter (fun w => !Nat.beq (Nat.land (sp true (lz Z) w.s) (wst true (lz Z) bank)) 0)

lemma demanded_bound {Z L : ℕ} (enough : L < (demanded Z).length) : Imp [] Z L := by
  classical
  intro q hq solution
  let existsSol : ∃ n, Sol Z0 (mz Z) (tz Z) n (C (mz Z) (WZ [] Z)) := ⟨q, solution⟩
  obtain ⟨k, hk, t, S, hS, live⟩ := (Nat.find_spec existsSol).live
  have leSize := le_trans hk (Nat.find_min' existsSol solution)
  have ambient : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have minimal : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨live, fun n hn smaller => Nat.find_min existsSol (lt_of_lt_of_le hn hk) (smaller.mono le_rfl ambient)⟩
  let bank := avl [] (mz Z) (rawL [])
  let all := (bank.map W.s).toFinset
  obtain ⟨sorted, _, hasWire⟩ := avl_spec [] (mz Z) (rawL [])
  have nodup : (bank.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact sorted.imp fun h => Nat.ne_of_gt h
  have bankRep : Rep bank all := ⟨nodup, rfl⟩
  have contained : (demanded Z |>.map W.s).toFinset ⊆ S := by
    intro x hx
    obtain ⟨w, hwLat, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    have hwMem : w ∈ bank ∧ (!Nat.beq (Nat.land (sp true (lz Z) w.s) (wst true (lz Z) bank)) 0) = true :=
      List.mem_filter.mp hwLat
    have nonzero : Nat.land (sp true (lz Z) w.s) (wst true (lz Z) bank) ≠ 0 := by
      intro eq; rw [eq] at hwMem; simp at hwMem
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero nonzero
    obtain ⟨hmask, hu⟩ := uq_of bankRep hwMem.1 hi
    obtain ⟨⟨hm1,hm2,ht1,ht2⟩, _⟩ := lz_lg Z i hmask
    obtain ⟨u, hU, sign⟩ := live.cov hm1 hm2 ht1 ht2
    have sign := sepb_weak (pos' t) sign
    have notZero : u ≠ 0 := by rintro rfl; simp [sepb] at sign
    have notFull : u ≠ mz Z := by rintro rfl; simp [sepb, hm1, hm2] at sign
    have hIn : u ∈ all := by
      rcases hS hU with hu | hc
      · obtain ⟨r,hr,rfl⟩ := hu
        obtain ⟨w',hw',same⟩ := hasWire r hr notZero notFull
        exact bankRep.mem.mpr ⟨w',hw',same⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        exact False.elim (hc.elim notZero notFull)
    have equal : u = w.s := by
      by_contra he
      rw [hu.2 u hIn he] at sign
      simp at sign
    exact equal ▸ hU
  have allNodup : ((demanded Z).map W.s).Nodup :=
    nodup.sublist (List.filter_sublist.map W.s)
  have card := Finset.card_le_card contained
  rw [List.toFinset_card_of_nodup allNodup, List.length_map] at card
  have sz := minimal.size.1
  omega

noncomputable def demandedRow (T : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  (Nat.ble e.2 6 && Nat.ble (e.2 + 1) (demanded e.1).length) || okE [] (pr T e.1) e

lemma demandedAll {T U : List (ℕ × ℕ)} (h : U.all (demandedRow T) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := by
  intro e he
  have checked := List.all_eq_true.mp h e he
  simp only [demandedRow, Bool.or_eq_true, Bool.and_eq_true] at checked
  rcases checked with ⟨_, short⟩ | ordinary
  · exact demanded_bound (Nat.le_of_ble_eq_true short)
  · exact imp_okE (Or.inl rfl) ordinary (fun r hr => hT r (List.mem_of_mem_filter hr))

section inst_data
def r5 : List (ℕ × ℕ) := [(31, 1), (47, 2), (55, 1), (59, 2), (61, 1), (62, 1), (79, 2), (87, 2), (91, 4), (93, 4), (94, 1), (103, 2), (107, 2), (109, 4), (110, 2), (115, 2), (117, 2), (118, 2), (121, 2), (122, 1), (124, 1), (143, 1), (155, 2), (157, 1), (158, 1), (167, 1), (171, 2), (173, 2), (174, 4), (179, 1), (182, 2), (185, 1), (186, 2), (188, 1), (203, 1), (205, 2), (206, 1), (211, 1), (213, 1), (214, 1), (217, 2), (218, 1), (220, 1), (229, 1), (230, 2), (233, 1), (234, 1), (236, 2), (242, 1), (244, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk5 : r5.all (demandedRow []) = true := by decide +kernel
lemma i5 : ∀ e ∈ r5, Imp [] e.1 e.2 := demandedAll (T := []) chk5 (by simp)
def rs5 : List (ℕ × ℕ) := r5
lemma is5 : ∀ e ∈ rs5, Imp [] e.1 e.2 := i5
def r4 : List (ℕ × ℕ) := [(15, 4), (23, 2), (27, 5), (29, 4), (30, 3), (39, 4), (43, 3), (45, 5), (46, 5), (51, 4), (53, 2), (54, 4), (57, 4), (58, 4), (60, 3), (71, 3), (75, 5), (77, 5), (78, 4), (83, 5), (85, 5), (86, 4), (89, 5), (90, 4), (92, 4), (99, 3), (101, 5), (102, 3), (105, 5), (106, 4), (108, 5), (113, 3), (114, 4), (116, 4), (120, 2), (135, 1), (139, 4), (141, 4), (142, 4), (147, 2), (149, 1), (150, 2), (153, 4), (154, 4), (156, 3), (163, 2), (165, 2), (166, 5), (169, 4), (170, 5), (172, 5), (177, 1), (178, 4), (180, 2), (184, 2), (195, 1), (197, 2), (198, 2), (201, 4), (202, 3), (204, 4), (209, 2), (210, 3), (212, 3), (216, 2), (225, 1), (226, 2), (228, 4), (232, 2), (240, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk4 : r4.all (demandedRow rs5) = true := by decide +kernel
lemma i4 : ∀ e ∈ r4, Imp [] e.1 e.2 := demandedAll (T := rs5) chk4 is5
def rs4 : List (ℕ × ℕ) := r4 ++ rs5
lemma is4 : ∀ e ∈ rs4, Imp [] e.1 e.2 := apI i4 is5
def r3 : List (ℕ × ℕ) := [(7, 5), (11, 6), (13, 7), (14, 7), (19, 6), (21, 5), (22, 5), (25, 7), (26, 7), (28, 6), (35, 5), (37, 6), (38, 6), (41, 6), (42, 6), (44, 8), (49, 5), (50, 7), (52, 5), (56, 5), (67, 6), (69, 6), (70, 5), (73, 7), (74, 7), (76, 7), (81, 6), (82, 7), (84, 7), (88, 5), (97, 6), (98, 5), (100, 6), (104, 6), (112, 5), (131, 4), (133, 4), (134, 5), (137, 7), (138, 7), (140, 7), (145, 4), (146, 5), (148, 4), (152, 5), (161, 4), (162, 6), (164, 6), (168, 6), (176, 4), (193, 4), (194, 4), (196, 5), (200, 5), (208, 4), (224, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk3 : r3.all (demandedRow rs4) = true := by decide +kernel
lemma i3 : ∀ e ∈ r3, Imp [] e.1 e.2 := demandedAll (T := rs4) chk3 is4
def rs3 : List (ℕ × ℕ) := r3 ++ rs4
lemma is3 : ∀ e ∈ rs3, Imp [] e.1 e.2 := apI i3 is4
def r2 : List (ℕ × ℕ) := [(3, 8), (5, 8), (6, 8), (9, 10), (10, 9), (12, 10), (17, 8), (18, 9), (20, 8), (24, 8), (33, 8), (34, 9), (36, 9), (40, 9), (48, 8), (65, 9), (66, 8), (68, 9), (72, 9), (80, 8), (96, 8), (129, 7), (130, 8), (132, 8), (136, 9), (144, 7), (160, 8), (192, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk2 : r2.all (demandedRow rs3) = true := by decide +kernel
lemma i2 : ∀ e ∈ r2, Imp [] e.1 e.2 := demandedAll (T := rs3) chk2 is3
def rs2 : List (ℕ × ℕ) := r2 ++ rs3
lemma is2 : ∀ e ∈ rs2, Imp [] e.1 e.2 := apI i2 is3
def r1 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk1 : r1.all (demandedRow rs2) = true := by decide +kernel
lemma i1 : ∀ e ∈ r1, Imp [] e.1 e.2 := demandedAll (T := rs2) chk1 is2
def rs1 : List (ℕ × ℕ) := r1 ++ rs2
lemma is1 : ∀ e ∈ rs1, Imp [] e.1 e.2 := apI i1 is2
def pin4 : List (ℕ × ℕ) := [(270, 3), (278, 3), (282, 5), (284, 5), (294, 2), (298, 3), (300, 3), (306, 3), (308, 3), (312, 3), (326, 3), (330, 5), (332, 5), (338, 5), (340, 5), (344, 5), (354, 3), (356, 3), (360, 3), (368, 3), (390, 2), (394, 3), (396, 3), (402, 3), (404, 3), (408, 3), (418, 2), (420, 2), (424, 1), (432, 1), (450, 3), (452, 3), (456, 3), (464, 3), (480, 1), (525, 2), (533, 1), (537, 3), (540, 3), (549, 1), (553, 3), (556, 3), (561, 2), (564, 3), (568, 3), (581, 2), (585, 2), (588, 2), (593, 1), (596, 3), (600, 1), (609, 1), (612, 3), (616, 1), (624, 2), (645, 1), (649, 3), (652, 3), (657, 2), (660, 3), (664, 3), (673, 2), (676, 3), (680, 3), (688, 4), (705, 1), (708, 3), (712, 1), (720, 2), (736, 2), (1035, 2), (1043, 2), (1049, 2), (1050, 2), (1059, 1), (1065, 3), (1066, 3), (1073, 1), (1074, 3), (1080, 1), (1091, 1), (1097, 3), (1098, 3), (1105, 1), (1106, 3), (1112, 1), (1121, 2), (1122, 3), (1128, 3), (1136, 2), (1155, 1), (1161, 3), (1162, 3), (1169, 1), (1170, 3), (1176, 1), (1185, 2), (1186, 3), (1192, 3), (1200, 2), (1217, 2), (1218, 3), (1224, 3), (1232, 2), (1248, 4), (2055, 2), (2067, 3), (2069, 2), (2070, 1), (2083, 3), (2085, 3), (2086, 3), (2097, 2), (2098, 3), (2100, 1), (2115, 2), (2117, 3), (2118, 1), (2129, 3), (2130, 3), (2132, 3), (2145, 2), (2146, 1), (2148, 3), (2160, 1), (2179, 4), (2181, 4), (2182, 2), (2193, 4), (2194, 3), (2196, 2), (2209, 4), (2210, 3), (2212, 3), (2224, 2), (2241, 4), (2242, 2), (2244, 3), (2256, 3), (2272, 2), (4103, 1), (4107, 3), (4109, 2), (4110, 2), (4131, 1), (4133, 2), (4134, 2), (4137, 2), (4138, 2), (4140, 3), (4163, 2), (4165, 1), (4166, 1), (4169, 3), (4170, 3), (4172, 2), (4193, 1), (4194, 1), (4196, 2), (4200, 2), (4227, 2), (4229, 1), (4230, 1), (4233, 3), (4234, 3), (4236, 2), (4257, 1), (4258, 1), (4260, 2), (4264, 2), (4289, 2), (4290, 2), (4292, 1), (4296, 3), (4320, 1), (8199, 2), (8203, 3), (8205, 3), (8206, 5), (8211, 1), (8213, 1), (8214, 3), (8217, 2), (8218, 3), (8220, 3), (8259, 1), (8261, 1), (8262, 3), (8265, 2), (8266, 3), (8268, 3), (8273, 2), (8274, 3), (8276, 3), (8280, 2), (8323, 2), (8325, 2), (8326, 5), (8329, 3), (8330, 5), (8332, 5), (8337, 1), (8338, 3), (8340, 3), (8344, 3), (8385, 1), (8386, 3), (8388, 3), (8392, 3), (8400, 3), (16391, 3), (16395, 3), (16397, 5), (16398, 3), (16403, 3), (16405, 5), (16406, 3), (16409, 5), (16410, 3), (16412, 5), (16419, 3), (16421, 3), (16422, 3), (16425, 3), (16426, 2), (16428, 3), (16433, 3), (16434, 3), (16436, 3), (16440, 3), (16515, 1), (16517, 2), (16518, 1), (16521, 3), (16522, 2), (16524, 3), (16529, 2), (16530, 1), (16532, 2), (16536, 3), (16545, 1), (16546, 2), (16548, 1), (16552, 2), (16560, 1), (32775, 2), (32779, 2), (32781, 2), (32782, 3), (32787, 2), (32789, 2), (32790, 3), (32793, 2), (32794, 3), (32796, 3), (32803, 2), (32805, 2), (32806, 3), (32809, 2), (32810, 3), (32812, 3), (32817, 2), (32818, 3), (32820, 3), (32824, 3), (32835, 3), (32837, 3), (32838, 2), (32841, 3), (32842, 2), (32844, 2), (32849, 3), (32850, 2), (32852, 2), (32856, 2), (32865, 3), (32866, 2), (32868, 2), (32872, 2), (32880, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4 : pin4.all (demandedRow rs1) = true := by decide +kernel
lemma h4 : ∀ e ∈ pin4, Imp [] e.1 e.2 := demandedAll (T := rs1) v4 is1
def pv4 : List (ℕ × ℕ) := rs1 ++ pin4
lemma hv4 : ∀ e ∈ pv4, Imp [] e.1 e.2 := apI is1 h4
def pin3 : List (ℕ × ℕ) := [(262, 4), (266, 6), (268, 6), (274, 6), (276, 6), (280, 6), (290, 4), (292, 4), (296, 4), (304, 4), (322, 6), (324, 6), (328, 6), (336, 6), (352, 4), (386, 4), (388, 4), (392, 4), (400, 4), (416, 2), (448, 4), (517, 2), (521, 4), (524, 4), (529, 3), (532, 4), (536, 4), (545, 3), (548, 4), (552, 4), (560, 5), (577, 2), (580, 4), (584, 2), (592, 3), (608, 3), (641, 3), (644, 4), (648, 4), (656, 5), (672, 5), (704, 3), (1027, 2), (1033, 4), (1034, 4), (1041, 2), (1042, 4), (1048, 2), (1057, 3), (1058, 4), (1064, 4), (1072, 3), (1089, 3), (1090, 4), (1096, 4), (1104, 3), (1120, 5), (1153, 3), (1154, 4), (1160, 4), (1168, 3), (1184, 5), (1216, 5), (2051, 5), (2053, 5), (2054, 3), (2065, 5), (2066, 4), (2068, 3), (2081, 5), (2082, 4), (2084, 4), (2096, 3), (2113, 5), (2114, 3), (2116, 4), (2128, 4), (2144, 3), (2177, 7), (2178, 5), (2180, 5), (2192, 5), (2208, 5), (2240, 5), (4099, 3), (4101, 2), (4102, 2), (4105, 4), (4106, 4), (4108, 3), (4129, 2), (4130, 2), (4132, 3), (4136, 3), (4161, 3), (4162, 3), (4164, 2), (4168, 4), (4192, 2), (4225, 3), (4226, 3), (4228, 2), (4232, 4), (4256, 2), (4288, 3), (8195, 3), (8197, 3), (8198, 6), (8201, 4), (8202, 6), (8204, 6), (8209, 2), (8210, 4), (8212, 4), (8216, 4), (8257, 2), (8258, 4), (8260, 4), (8264, 4), (8272, 4), (8321, 3), (8322, 6), (8324, 6), (8328, 6), (8336, 4), (8384, 4), (16387, 4), (16389, 6), (16390, 4), (16393, 6), (16394, 4), (16396, 6), (16401, 6), (16402, 4), (16404, 6), (16408, 6), (16417, 4), (16418, 4), (16420, 4), (16424, 4), (16432, 4), (16513, 3), (16514, 2), (16516, 3), (16520, 4), (16528, 3), (16544, 2), (32771, 3), (32773, 3), (32774, 4), (32777, 3), (32778, 4), (32780, 4), (32785, 3), (32786, 4), (32788, 4), (32792, 4), (32801, 3), (32802, 4), (32804, 4), (32808, 4), (32816, 4), (32833, 4), (32834, 3), (32836, 3), (32840, 3), (32848, 3), (32864, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v3 : pin3.all (demandedRow pv4) = true := by decide +kernel
lemma h3 : ∀ e ∈ pin3, Imp [] e.1 e.2 := demandedAll (T := pv4) v3 hv4
def pv3 : List (ℕ × ℕ) := pv4 ++ pin3
lemma hv3 : ∀ e ∈ pv3, Imp [] e.1 e.2 := apI hv4 h3
def pin2 : List (ℕ × ℕ) := [(258, 7), (260, 7), (264, 7), (272, 7), (288, 5), (320, 7), (384, 5), (513, 4), (516, 5), (520, 5), (528, 6), (544, 6), (576, 4), (640, 6), (1025, 4), (1026, 5), (1032, 5), (1040, 4), (1056, 6), (1088, 6), (1152, 6), (2049, 8), (2050, 6), (2052, 6), (2064, 6), (2080, 6), (2112, 6), (2176, 8), (4097, 4), (4098, 4), (4100, 3), (4104, 5), (4128, 3), (4160, 4), (4224, 4), (8193, 4), (8194, 7), (8196, 7), (8200, 7), (8208, 5), (8256, 5), (8320, 7), (16385, 7), (16386, 5), (16388, 7), (16392, 7), (16400, 7), (16416, 5), (16512, 4), (32769, 4), (32770, 5), (32772, 5), (32776, 5), (32784, 5), (32800, 5), (32832, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2 : pin2.all (demandedRow pv3) = true := by decide +kernel
lemma h2 : ∀ e ∈ pin2, Imp [] e.1 e.2 := demandedAll (T := pv3) v2 hv3
def pv2 : List (ℕ × ℕ) := pv3 ++ pin2
lemma hv2 : ∀ e ∈ pv2, Imp [] e.1 e.2 := apI hv3 h2
def pin1 : List (ℕ × ℕ) := [(256, 8), (512, 7), (1024, 7), (2048, 9), (4096, 5), (8192, 8), (16384, 8), (32768, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1 : pin1.all (demandedRow pv2) = true := by decide +kernel
lemma h1 : ∀ e ∈ pin1, Imp [] e.1 e.2 := demandedAll (T := pv2) v1 hv2
def pv1 : List (ℕ × ℕ) := pv2 ++ pin1
lemma hv1 : ∀ e ∈ pv1, Imp [] e.1 e.2 := apI hv2 h1
def rStrong : List (ℕ × ℕ) := [(1, 12), (2, 12), (4, 12), (8, 13), (16, 11), (32, 11), (64, 11), (128, 11)]
def e8Q : List (ℕ × ℕ) := (pr pv1 8).filter (fun e => e.2 ≥ 4)


def allInputsNeeded (nn : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun w ws rest bits =>
      !Nat.beq (Nat.lor bits (covC nn d l ws)) l &&
        rest (Nat.lor bits (spC nn d l w.s))) v

lemma anySub_allInputs {nn : ℕ} {d : Bool} {l : ℕ} {v : List W} {bits : ℕ}
    (needed : allInputsNeeded nn d l v bits = true) (test : List W → Bool) :
    anySubC nn d l v bits test = test v := by
  induction v generalizing bits test with
  | nil => rfl
  | cons w ws ih =>
    let included := Nat.lor bits (spC nn d l w.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l ws)) l
    change (!skip && allInputsNeeded nn d l ws included) = true at needed
    simp only [Bool.and_eq_true] at needed
    have mustKeep : skip = false := Bool.eq_false_iff.mpr (fun h => by rw [h] at needed; simp at needed)
    change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l ws bits test) skip)
      true (st included (fun c => anySubC nn d l ws c (fun r => test (w :: r)))) = _
    rw [st_eq, ih needed.2, mustKeep]
    cases test (w :: ws) <;> rfl

def e8Words : List W := [
  ⟨0x1beff9f3ff9b000000000000000000000000000000000000000000000000000000000000000000000000000004814c04e000005c00000000004e0002700000000000180000000180000c000000000000c000060000000018000600000000000000000000000000df600f9e00d800007c000000003e000000003e0000ec0008000000f800400000000370004360023600203600340b6237575e0aeadbc000002b756bdbab5e000000000000000000000000000000000000000000000000000000000000000000286300291105a84, 0x100000004000000100001000000800000400000000002100000000200002108421084210000000000000000000008421084000000000000000000040000000, 0x8000000010842000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x8000000010842100000004000000100001000000800000400000000002100000000200002108421084210000000000000000000008421084000000000000000000040000000, 3⟩,
  ⟨0x1beff800000000000ffff0000007fffb80000000000000000000000000000000000000000000000000000000068168008a000011400000000008a00045000200b40052c00000212c0049600000000000940004a0000000128004a0000000000000000000000000dc1c0801c000000043f800000021fc1c000001e00003c000000000078020000000000f00201e0101c00201c0340b600000000000000000000000000000001805b00ad6dbc005ad6d7b6b6be0000000000000000000000000000000000000080c7b002b53042a0, 0x200000008000080000000000020000000000000421000010842100000000000842108421080000000008000000210842000000000000002000000, 0x400000000000108421080000000000000000000000000000000010840000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000108421080200000008000080000000000020000010840000421000010842100000000000842108421080000000008000000210842000000000000002000000, 3⟩,
  ⟨0x1f3ff800000000000000000000000000000001dfdf8000000000000000000006fff806ffc06ffc06000000004064043804808700000046404632023000002000808700084808c24047800080046408632043000414810c2043c000000000000000000000004044d14440000000048800000000c440000002440826a40000000008508000000004594004b6004ea03004400006030000002000000000023000018000000003000000000042000036b6be000c002300001800000021a0000356df00000083132002ec74c830, 0x80000002000020000010000008000000000840000000000010840100020080210002000401080200842100000004000002000020004010800000001, 0x200000000000000000000000000000000000000421084200000000421084000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000080000002000020000010000008421084200840000421084010840100020080210002000401080200842100000004000002000020004010800000001, 3⟩,
  ⟨0xffff00000000000000007fff81dfdf9c0000000000000000000000000000000000000000200004208e000011800000000008c0004600300a60002180000002180010c000258000411c0208e0000000230008c000000000000000000000000820306003080000063c60000001103000000311f00c22f0e0000008070000000000200e0120180a03010203030000237575e0000000000000000000000001805b000000000000000000000001ac002b6aebdb575e0000000000000000000080951010e9701204, 0x10000008000000000000000000004000040000001000000000000000000210000008420000000842000000004210800000400000200000108420000000000100000, 0x20000000000000000004210842000000000000000000000000000002108000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000010000008000004210842000000004000040000001000000002108000000210000008420000000842000000004210800000400000200000108420000000000100000, 3⟩,
  ⟨0x7fff80000000000000000000000000000000000006fff8f000006ffc700000000200002028000405000000500204101038000100040805000b0080860405000000050040410203800484080e0202800000000000000000000000821800618080000048300000023a9800000020980040382000000081a100000000054b878000006bc3802180003000000000000000000002800001bab5e0001800200000005800003000000020002800001b575e002c2d5b780000000000009290123c70d890, 0x2000001000000040000400000200000000000000200000108001004200040000401004010040008020084010002100000080000040000400080200800000020, 0x4000000000000000000000000000000000842108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4000002000001000000040000400000200842108000000200000108001004200040000401004010040008020084010002100000080000040000400080200800000020, 3⟩,
  ⟨0x7fff80000000000001fffef000000000000000000000000000000000040008801001300000000000900004801000001001300000001200009000350000001100008800012002600098000000000000000000000004110c1810c400000122180000008c0d00000299cc02120c0000000664f7800000001081c091060110e09110c0400020000000aeadbc000000000000000001800000ad6dbc0000000000000001ac00000000000000002dad5b7b56df00000001d70000c4248294, 0x800000400000010000000000000000002000000080010800000400084000840000001080000000108400004200042000020000010000100001084000000008000, 0x1000000000000000000000000108420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000800000400000010000108420000000002000000080010800000400084000840000001080000000108400004200042000020000010000100001084000000008000, 3⟩,
  ⟨0x1fffe0000000006fff8f6ffc700000000000000000000b01000260000005200170000a000000010002600094002e0001600100005200170000a0005b00048001300000000000000000000000104a0018a010000009140000000432080000045200088c04000000556c000000000066d0786dc380000004a00008000000000800000000002b756bc000000004000800000005ad6d78000000180002b6aebc00000002d800000000000000002138000dd24c220, 0x40000020000000800000000000000000100000004010042008020080210802008000004200800100021000010840100001000000800008001000210000000400, 0x80000000000000000000000000001084210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x80000040000020000000800000001084210000100000004010042008020080210802008000004200800100021000010840100001000000800008001000210000000400, 3⟩]

def e8M : ℕ := 0x1beff9f3ff9b00000ffff0000007fffb800007fff81dfdf9c000001fffef000000006fff8f6ffc76ffc766ff86816c46eaebc15d5b780000056ead7b756bc300b6015adb7800b5adaf6d6d7c03580056d5d7b6aebc005b5ab6f6adbe0000000000000000000000df7fcf9ffcd800007fff8000003fffdc00003fffc0efefce000000ffff78000000037ffc7b7fe3b7fe3b37fc340b6237575e0aeadbc000002b756bdbab5e1805b00ad6dbc005ad6d7b6b6be01ac002b6aebdb575e002dad5b7b56df00000083d7b012fd74dab4

def e8G : ℕ := 0x84210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210

def e8B : ℕ := 0xbd6b7bdeb8c6318c5ad8b5b18b5b18c6318c6318c6318c62d8b5ad7bdef7bdef7bdf18c6318bdf18c6318be2f8c5f17be317be2f8bdaf5ad6d7ad6b7a5ad6ad6b5b4e73a4a72

def e8L : ℕ := 0xdf7fcf9ffcd800007fff8000003fffdc00003fffc0efefce000000ffff78000000037ffc7b7fe3b7fe3b37fc340b6237575e0aeadbc000002b756bdbab5e1805b00ad6dbc005ad6d7b6b6be01ac002b6aebdb575e002dad5b7b56df0000000000000000000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8Words_eq : avl (PZ e8Q) (mz 8) (rawL []) = e8Words := Eq.refl e8Words

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8M_eq : mz 8 = e8M := Eq.refl e8M

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8G_eq : pL (e8Q.map fun _ => 16) = e8G := Eq.refl e8G

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8B_eq : pL (e8Q.map fun e => 16 + (12 - e.2)) = e8B := Eq.refl e8B

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8L_eq : lz 8 = e8L := Eq.refl e8L

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allE8Inputs (d : Bool) :
    allInputsNeeded I.NN d e8L e8Words 0 = true := by
  cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma searchInputs_e8 (t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    searchInputs [] e8Q 8 12 t H ph test =
      guardStart t H ph (test I.NN I.AA I.HX I.HY e8L e8M e8G e8B 0) e8Words := by
  simp only [searchInputs, frc_eq, st_eq, e8Words_eq, e8M_eq, e8G_eq, e8B_eq, e8L_eq]
  change anySubC I.NN (pos t) e8L e8Words 0 _ = _
  rw [anySub_allInputs (allE8Inputs (pos t))]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8Ok : pOk 8 e8Q = true := by decide +kernel

def e8Cases : List (ℕ × ℕ) := [(0x4000, 0), (0x100000, 0), (0x10000000, 0), (0x400000000, 0), (0x40000000000, 0), (0x1000000000000, 0), (0x400000000000000000000000000000000, 0), (0x40000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000, 0), (0x1000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000000000000, 0), (0x10000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000, 0), (0x10000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000, 0), (0x1000000000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000000000, 0), (0x2fefafaebefefffffbfbfbfffffffffffffffffffefbfbefefbfff, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8Full : mFull e8Cases = true := by decide +kernel

namespace CofactorEight

abbrev rootPreparedMask : ℕ := e8M
abbrev rootPreparedSlots : ℕ := e8G
abbrev rootPreparedBudget : ℕ := e8B
abbrev rootPreparedWords : List W := e8Words



lemma pair_distribute {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pair f a c = true → ∃ b, pair (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,bR]
  cases hb : f w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · simp only [hb,Bool.cond_false]
    intro hor
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hor
    refine ⟨b, ?_⟩
    rw [hb]
    simp
  · intro _
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hb
    exact ⟨b,by rw [hb]; rfl⟩



noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f false e8L rootPreparedMask rootPreparedSlots 12 7
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootStart_eq (H : ℕ) (kind : Bool) :
    startPairPicked I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots rootPreparedBudget
      12 0 0 H 0 rootPreparedWords kind =
    initialBinary H kind (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0) := by
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 7 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  simp only [startPairPicked, child, st_eq, topPairPicked, bR, haveRequired, len, budget,
    show Nat.ble 7 (Nat.sub 13 0) = true from rfl, show Nat.ble 7 1 = false from rfl,
    Bool.cond_true, Bool.cond_false]
  change (bif initialBinary H kind (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots
      12 12 11 0) then true else false) = _
  cases initialBinary H kind (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots
      12 12 11 0) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialBinary_of_check (H : ℕ) (kind : Bool)
    (h : chkPairPicked [] e8Q 8 12 0 H 0 kind = true) :
    initialBinary H kind
      (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0) = true := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8] at h
  simp only [guardStart, rootStart_eq, bR] at h
  cases hp : relevantStart 0 H 0 rootPreparedWords
  · simp [hp] at h
  · simpa [hp] using h

def wordEquals (a b : W) : Bool :=
  (a.s == b.s) && (a.a == b.a) && (a.b == b.b) && (a.c == b.c) && (a.r == b.r)

lemma wordEquals_spec {a b : W} (h : wordEquals a b = true) : a = b := by
  cases a
  cases b
  simp [wordEquals, Bool.and_eq_true] at h ⊢
  rcases h with ⟨⟨⟨⟨hs, ha⟩, hb⟩, hc⟩, hr⟩
  exact ⟨hs, ha, hb, hc, hr⟩

def frontierMissing (states : List (ℕ × List W)) (z : ℕ) (v : List W) : Bool :=
  !(states.any fun state => (z == state.1) && List.isEqv v state.2 wordEquals)

noncomputable def rootWithGate (i j mask : ℕ) (kind : Bool) : List W :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD i zero
  let b := rootPreparedWords.getD j zero
  let keep := (rootPreparedWords.zipIdx.filter fun e => mask.testBit e.2).map Prod.fst
  addS (opW kind a b) keep

lemma frontierMissing_false {states : List (ℕ × List W)} {z : ℕ} {v : List W}
    (h : frontierMissing states z v = false) : (z, v) ∈ states := by
  simp only [frontierMissing, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨j, w⟩, membership, rfl, he⟩ := h
  have hw : v = w := by
    clear membership
    induction v generalizing w with
    | nil => cases w <;> simp_all [List.isEqv]
    | cons a v ih =>
      cases w with
      | nil => simp [List.isEqv] at he
      | cons b w =>
        simp only [List.isEqv, Bool.and_eq_true] at he
        rw [wordEquals_spec he.1, ih w he.2]
  rwa [hw]

lemma initialBinary_from_frontier (H : ℕ) (kind : Bool) (states : List (ℕ × List W))
    (complete : initialBinary H kind (frontierMissing states) = false)
    (checked : ∀ state ∈ states,
      look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0 state.1 state.2 = false) :
    chkPairPicked [] e8Q 8 12 0 H 0 kind = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  have original := initialBinary_of_check H kind h
  unfold initialBinary at original complete
  obtain ⟨_, hit⟩ := nodePicked_distribute
    (branches := fun _ => frontierMissing states)
    I.NN false e8L rootPreparedMask rootPreparedSlots 12 7
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind
    (fun z v hit => by
      refine ⟨0, ?_⟩
      cases hm : frontierMissing states z v
      · exact Bool.noConfusion ((checked (z,v) (frontierMissing_false hm)).symm.trans hit)
      · exact hm)
    original
  exact Bool.noConfusion (complete.symm.trans hit)

abbrev SearchState := ℕ × List W

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f false e8L rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 11 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12)
      e8L rootPreparedMask rootPreparedSlots 11 0 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 11 10 0 z v))

lemma pureAt_of_covered (e : ℕ) (state : SearchState) (remaining : SearchState → Bool)
    (miss : ℕ → List W → Bool)
    (complete : pureAt e state miss = false)
    (covered : ∀ z v, miss z v = false → remaining (z,v) = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => miss)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : miss z v
        · exact Bool.noConfusion ((covered z v missed).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma pureAt_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : pureAt e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    pureAt e state (fun z v => remaining (z,v)) = false :=
  pureAt_of_covered e state remaining (frontierMissing states) complete
    (fun z v h => checked (z,v) (frontierMissing_false h))

lemma pureSecond_from_frontier (state : SearchState) (states : List SearchState)
    (complete : pureSecond state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, afterSecond x = false) :
    pureSecond state (fun z v => afterSecond (z,v)) = false :=
  pureAt_from_frontier 11 state states afterSecond complete checked

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 11)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false e8L 12 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 12 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 12 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (12 : ℕ) = Nat.succ 11 from rfl, look1C_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 0) e8L state.2 (tstC I.NN I.AA I.HX I.HY false e8L 12 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 0) e8L state.2 (bif pureSecond state
      (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 11 10 0)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def secondTransition (state : SearchState) (i j kept : ℕ) (kind : Bool) : SearchState :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := state.2.getD i zero
  let b := state.2.getD j zero
  let word := opW kind a b
  let keptWords := (state.2.zipIdx.filter fun e => kept.testBit e.2).map Prod.fst
  let budget := Nat.sub (Nat.add state.1 (Nat.land a.c b.c)) word.c
  let usedA := if kept.testBit i then a.c else 0
  let usedB := if kept.testBit j then b.c else 0
  (Nat.sub (Nat.sub budget usedA) usedB, addS word keptWords)

noncomputable def firstStates : List SearchState := [
  ⟨0xace96b5a95ad6b4ace759ca96a52d4a5ad4a5ad6a5ad6b5256a52939ce52a4a52a525294a7394a739ce7394e539ca72956b4a56959ca718c6538c635952949ce73a42129c651, rootWithGate 0 1 127 false⟩,
  ⟨0xa4a96b5a94a5294a4a5494eb6a52d5adad5adad6adad6b5676a529294a73a4e73a52739ce739ce94a52949d274a4e939d6b4a56959ce9294a7494a55952949ce73a46329c651, rootWithGate 0 1 127 true⟩,
  ⟨0xa5296b5a54a5295b52969ced6a52b5b5ab5b5ad5adad6ad25494a549ce73a4a5294a739ce939ce749d273a5675aceb39d6949d274a4e92946959ce55952749ca729c6529c650, rootWithGate 0 2 127 true⟩,
  ⟨0xad276b5a94ad6b4a5296a4ab59ceb4b5ad4b52d6a52d6b5294a5294a52529d294a5252a527394a739ce7394e55ad2b4a4e72956959ca718c6559ce7384a549ce73a42509c651, rootWithGate 0 3 127 false⟩,
  ⟨0xa5256b5a94a5295ad296a4a9494a95b5ad5b56d6ad6d6b5695a5294a525295294a5253a529494a74a52949d275ad2b4a52939d695a4a9294a759ce748ce749ce73a46519c651, rootWithGate 0 3 127 true⟩,
  ⟨0xad296b5695ad694b5294a4ad6a4ad4b52d4b5a96a56b5ad296a5254a525295292a4a54a4a7394a739ce73a4e959d27494eb2a56539ca718c6959c67594a948ce33942529c611, rootWithGate 0 4 127 false⟩,
  ⟨0xa5296b5294a5295b5295a4ed6a4ed5b56d5b5ab6a5294a5696a5274a52729d293a4e54a4e949ca93a4e93a5295a52949d2b3a5674a4e928ca959ca7594e9494e539c6529c631, rootWithGate 0 4 127 true⟩,
  ⟨0xad295b5a95a56b4b4a96a4ad4a52d4ad6b4b5ad6a5a96b52969529295252a4a9494a5494a7394a739ce73a56939cab4a4e74a4e559ca718c6939ce73952928c673a42528c651, rootWithGate 0 5 127 false⟩,
  ⟨0xa5294b5a94a5295b4e96a4ed5a52d4a5295b5ad6adab6b56969d2939d273a4e949ce749ce949ce939d294a5694a4eb4a5294a5275a4e7294a949ce749529394a73a465294651, rootWithGate 0 5 127 true⟩,
  ⟨0xa5296a5a94a5295b5276a4ed69d2d5b5ad4a5294adad5b5696a4e93a4e539d2749d2539d27494e94a4e749d694ad293a56b39d294a4e9194a9594e758d2939ce52a46529c251, rootWithGate 0 6 127 true⟩,
  ⟨0xb4a96b5a56b5ad4a4a54952b6a52b6adab6adad5b5ad6ad25494a5294a94a4a5294a9294a93a5295a56949d254a4a92956949d274a52b39ca7494a35952749ca729ca329c650, rootWithGate 1 2 127 true⟩,
  ⟨0xb4e76b5a94b5ad5a4e759ce959ceb6a5ad6a52d6b52d6b5a54a52939ce739ca52a525294a7394a75ad6b594e539ca7294e72956959cab39ce538c63384a549ce73a4a109c651, rootWithGate 1 3 127 false⟩,
  ⟨0xb4a56b5a95b5ad4a4a5494a9494a96adad6ad6d6b56d6b5a75a529294a5294e73a52729ce949ce95ad6b594e54a4e939d2939d695a4eb39ce5494a548ce749ce73a4a319c651, rootWithGate 1 3 127 true⟩,
  ⟨0xb4e96b5696b5a95ace749d296a4ad6a52d6a5a96ad6b5ada56a52539ce9294a52a4a5294a73a4ab3aceb394e539ca7294eb2a56539d2b38ce538c63594a948ce3394a129c611, rootWithGate 1 4 127 false⟩,
  ⟨0xb4a96b5296b5ab4a4a54952b6a4ed6ad6d6adab6a5294a5a76a527294a939ce72a4e739ca94a4eb4ad2b49ce749ce73952b3a5674a52b394e749465594e9494e539ca329c631, rootWithGate 1 4 127 true⟩,
  ⟨0xb4e95b5a96a5ad5aca759d294a52d5a56b6a5ad6b5a96b5a569529294e94a4a5294a9294a73a52b39d6b594e539ca7294e74a4e559d2739ce538c633952928c673a4a128c651, rootWithGate 1 5 127 false⟩,
  ⟨0xb4a94b5a96adad4a4a54952b5a52d4a5296adad6b5ab6b5a769d29294a94a4a739ce9394a94a52b4a56b59d2739ca939d294a5275a52939ce7394a549529394a73a4a3294651, rootWithGate 1 5 127 true⟩,
  ⟨0xb4a96a5a96b56d4a4a54952b69d2d6adad4a5294b5ad5b5a76a4e9294a749ce539d27294e749d2b5ad29595273a4e729d6b39d294a52b29ce748ca558d2939ce52a4a329c251, rootWithGate 1 6 127 true⟩,
  ⟨0xb5256b5a55b5ad6ad2969ca9494a96b5ab6b56d5b56d6ad25494a549ce5294a5294a729ceb49ce75a56949d255aceb39d27395274aceb39ca759ce548ce549ca729ca519c650, rootWithGate 2 3 127 true⟩,
  ⟨0xb5296b5256b5ab6b52959d2d6a4eb6b56b6b5ab5a5294a525494a549ce939ca5294a739cab4a4e94a5293a5275a4e93952939d253ad2b394a959ca5594e7494a5294a529c630, rootWithGate 2 4 127 true⟩,
  ⟨0xb5294b5a56adad6b4e969d2d5a52b4a5296b5ad5b5ab6ad25494a5394e94a4a5294a9394ab4a52949d694a5674a4ab39d2749ce54ad2939ca949ce5495273946729ca5294650, rootWithGate 2 5 127 true⟩,
  ⟨0xb5296a5a56b56d6b52769d2d69d2b6b5ab4a5294b5ad5ad25494a539ca749ca5294a7294e949d295a52749d674ace929d69394e73ad2b29ca9594e558d2739ca519ca529c250, rootWithGate 2 6 127 true⟩,
  ⟨0xb5276b5694b5a96a5294a4eb59cab6b52d6b5296ad2b5ada94a5254a527295292a4a52a4ab594a73aceb394e559d27494e7295653acab38ce559c67384a548ce3394a509c611, rootWithGate 3 4 127 false⟩,
  ⟨0xb5256b5295b5ab6ad295a4a9494a96b56d6b56b6a5294a5a95a5274a525295293a4e53a4eb59ca94ad2b49ce75a52949ce929d674aceb394e759ca748ca7494e539ca519c631, rootWithGate 3 4 127 true⟩,
  ⟨0xb5275b5a94a5ad6a4a96a4eb49ceb5ad6b6b52d6b5296b5a9495292952739ca9494a5294ab594a739d6b594e539cab4a4e7294e55aca739ce539ce7384a528c673a4a508c651, rootWithGate 3 5 127 false⟩,
  ⟨0xb5254b5a95adad6ace96a4a9494a94a5296b56d6b56b6b5a959d2939d25294e949ce739ceb59ce94a56b59d274a4eb4a4e739d275ace939ce749ce738ce7394a73a4a5194651, rootWithGate 3 5 127 true⟩,
  ⟨0xb5256a5a95b56d6ad276a4a9494a96b5ad4a5294b56d5b5a95a4e93a4e52952749d2529d29594e95ad29595274ad293a529295294aceb29ce7594e7484e739ce52a4a519c251, rootWithGate 3 6 127 true⟩,
  ⟨0xb5295b5696a5a96b4a94a52d4a4ad5ad2b6b5a96ad695ada96952529529294a9294a5494ab5a4ab39ceb3a4e939ca7494e72a4e53ad2738ce939c67394a928c63394a528c611, rootWithGate 4 5 127 false⟩,
  ⟨0xb5294b5296adab6b4e95a52d5a4ed4a5296b5ab6a5294a5a969d2739d2939ce939ca749cab5a4eb3a52b4a52949ce949ce93a5254ad29394e949ca7494e938ca539ca5294631, rootWithGate 4 5 127 true⟩,
  ⟨0xb5296a5296b56b6b5275a52d69ced6b56d4a5294a5294a5a96a4e73a4e73952739ce539ce959ceb4ace949d294a52739d2b29d273ad2b294e9594a758ce9394e329ca529c231, rootWithGate 4 6 127 true⟩,
  ⟨0xb5294a5a96ad6d6b4e76a52d59d2d4a5294a5294b5ab5b5a969ce929ce749ce7494e7394e959d2b4a52959d693a4e93a52939ce74ad2929ce9494e748d29294a52a4a5294251, rootWithGate 5 6 127 true⟩]

def firstCount : ℕ := 31

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def decodeStep (width : ℕ) (parent : ℕ → SearchState) (entry : ℕ) : SearchState :=
  let before := parent (entry % 2 ^ width)
  let left := (entry >>> width) % 16
  let right := (entry >>> (width + 4)) % 16
  let dropLeft := if entry.testBit (width + 8) then 2 ^ left else 0
  let dropRight := if entry.testBit (width + 9) then 2 ^ right else 0
  let kept := 2 ^ before.2.length - 1 - dropLeft - dropRight
  secondTransition before left right kept (entry.testBit (width + 10))


def secondCount : ℕ := 333

def secondCodes : List ℕ := [0x88634210e391159128eaa464123b331c828a88c4324329315008843c2114288718cccea4c410e3222194a8c8046518320314d08647c63123b2910ce0a4247637321118d1, 0xca84644e191218868a435743232a11d488eabc7330311314898e624522aba0958818ea1442222a1954448eacc420ab88918818c864410a30891d828ec44541239811d97, 0x8cabd623a208f0c8d8a42c6566bb211cc1ca835734e311c19068c20d7106188315018a218642a32a954c28643c6404321d148b88684711a190d14458c60c53222a2758d3, 0x8c875430abaa75d998c6485226299f18850caa864433aab18ce886445448328419488caac644ab1151d008c4345316108e1959cecac652e29079cd18c44c650a31151948, 0x8c234541a39191d400a80c511eb22f14428ec24744e38851cce8e244542619111c848a855632a320d188f8c84d734abb111d800c444433e290514888a874642a318c1882, 0x8863c754f32b31c818a63c620a311115108a664656a322114c48ec9d654e29a3591ba620c7532b99558410c81064223a0318d08a6047512398d90ccae460421a21091d8c, 0x8c45c743aba8d10c08c644545029041488ca670542a32891d418ece54206322919518c66c621e21039d91cca446502ba9d5c818e680311c32b510418ec0c63173ab5188d, 0x8a8ac654eb08c108208444741a219918428c8ac5422188a194c8a814742a218958c28ec94642229831d5c8868c6516391b19028c8b8651232b718450ca8e7676319f194c, 0xac86554123a2198d00c804511221131d8688455651aa91959048841c721a321f1d4e8ca0c711219095cc20a884762a29191c8a0c424653e29091d8eaca747322391d1d52, 0x8e20c6232328e15088642c611e190219520a815520631091d90aeabc74522a071c908e66c5206298d1952ce84c53242a2918c78ea34423e299d10c1aa694421a3a941941, 0x119498ca54641eb0859d898e814742231811d508623c653a28821913]

noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := secondCodes.getD (i / 32) 0
  decodeStep 6 firstAt ((block >>> (17 * (i % 32))) % 131072)

def secondBuckets : List ℕ := [0x8034200c00000000000000000000000000000000000000000200b000000000100240000080202007080184004000002003080082001000000000000000000000002000000000000, 0x806c00000806820190000000000806000000805c0000000002016000002015000000000000000000000002014000002013100442010100380000000000000, 0x202c00000000000000000000000202b080a80000080a40000000000000080a0202708098402418084202000000000000000201f00000201e00000000008074000000000201c, 0x80e40000000002038080dc2036000000000000000000000002035000004033100c4203000000202f000000000000000000000000000000000000080b8202d000000000000000000, 0x203e080f4000000000000000000000000000000000000203c00000203b00000203a000000000000000000000000000000000000, 0x4048000002047000000000000000000000000000000002046081144043081082041000000000000000000100fc0000000000000000000000, 0x8144000008140204f08138204d00000204c0000000000000000000000000000000000000000000000812c0000000000000081280000000000000000000000000000000000000000, 0x815c00000000000000815800000000020550000000000000020540000000000000000000000000000814c0000000000000000000000000000000081480000000000000000000000, 0x406210180205f00000000008178000000000000000000000000000000008174205c0000000000000000000000000000816c205a000000000081642058000000000, 0x81bc0000081b8000000000406c00000000000000000000000206b081a820690000000000000000000000020680819c0000000004065000000000000000000000000000081900000, 0x2075000000000000000000000000000081d02073081c80000000000000000000000000000000000000000000000000000000000000002071081c00000, 0x101f80000081f40000081f00000000000000081ec000000000207a000002079000000000000000000000002078000000000000000000000000000081dc0000000002076000000000, 0x82240000000002088000000000000000000000002087102142084102080000000000000082040000000000000000000000000002080000000000000000000000000000000000000, 0x209600000000008254409318240208f00000000000000000008238000000000000000000208d0823000000000000000000000000000000000822c208a000000000, 0x20a30828800000000000000828420a000000000000000000000000000000000209f08278209d00000000008270209b00000209a0826400000000000000000020980825c0000, 0x82ac40a9082a000000000020a70000000000000000000000000000000000000000020a60000000000000000000000000000000000000000000000829400000000000000000020a4, 0x82d020b30000020b20000000000000000000000000000000020b1082c000000000000000000000000000000000000000000000020af182b00000000000000000000000000000000, 0x82e820b9082e000000000000000000000000000020b70000000000000000000000000000000000000000020b6000000000082d40000000000000000000000000000000000000000, 0x830800000000020c10830020bf000000000000000000000000000082f80000000000000082f40000082f000000000000000000000000000020bb, 0x833820cd0000000000000000000000000000000020cc0000000000832c00000000020ca0000000000000040c80000000000000040c61031020c3, 0x836c20da0836420d80835c20d60000000000000000001035020d30000000000000000000000020d20000000000000040d00000000000833c0000, 0x20ed083b00000103a820e9000000000083a000001039820e50000000000839000000000000000000000000000020e30838800000838440df0837800000000020dd083700000, 0x83e40000083e020f7083d80000000000000000000000083d400000000000000000000000000020f4083cc00000000020f20000040f0103b80000000000000000000000, 0x21020840400000000000000000000000000000000000021000000000000000000000000020ff0000020fe0000020fd0000020fc083ec0000000000000000000000083e80000, 0x842400000000000000000000000000000000000000000000000000000000000842000000000000000000000000000021070841821050841000000840c0000000000000000000000, 0x211500000211400000211308448211100000211000000000000000000000000000000000210f00000210e10430410a000000000000000000000000000000000000000000000, 0x21230000000000848800000848400000000000000000021200847c000000000211e1047000000846c000000000000000000000000000000000000211a104602117084580000, 0x84a00000000002127000000000000000000000000000000000000000000000084980000104900000000000000000000000, 0x84b0212b000000000000000000000000000000000000084a80000000000000084a40000000000000000000000, 0x213a000000000084e40000084e02137084d80000000000000000002135084d00000000000000000000000084cc4131000000000184b80000000000000000000000084b40000, 0x85082141000000000000000000085000000000000000084fc0000084f8213d00000213c00000000000000000000000213b, 0x8530214b085280000085242148000000000000000000000000000000002147085180000000002145000000000000000000000000000000004143]

def thirdCount : ℕ := 1040

def thirdCodes : List ℕ := [0x90c6b8c8fdae8f8b0e08b04f8d0e3dcea84ccb2dccb14d0c33cea31ce6a38ec368ca3a90a918e9058eaf88a8f0cc887acb358e88eec8858e722ce8528c8538caed8a81daed498ea5ed0e388c6fdae8ed, 0xd0c3daec818cb028c863aea06aea048e90e8a8348e912d0a638c90790c730a8aceea77b0cb4aec7fae498ac851d0e468eb028a8fd88630ccb1fae8d7d0c36cea91cea3acea35d0c348ea6d8caf88ec3d, 0x8ca4f8e9220c42ceeaf68e8af8c6258eb0d8c90c8eb12b0e250c429b0cb88a4298e6fdb08ed0e6260e6258ec4a8a9078c626b0cb790e8590e83084fdaec85aec1caec84aec838e91accb418e91990e81, 0xaec988642990c81aea17ac62a90e8d8ec53aec96f08b1ae9078ec50aec8d90905b0b0588625b08f890698b0e2e8cb0d8a90caec9490e8f8a42c8e8acf0f30aec308ca52ae90d8ea7ecec528ec51aca06, 0xce8b98cb1caeca2b0b0dae73fb0e3eac82ceec3e8e741b0e39f0c9490e98ce6c8f0c9290e9fac8298ec58aec9faec9eac62ed0e58aea26aea258642c8ec99ceaa89069fcec5690c8490c82cc8acac713, 0xaa82ceec42d0c588ec63b0cda0e646c86a3cea56ae7418a8538ec648eca4ae915aea33f0f44aca25ac87390ab98865290c9190c8fd0e63f0c96aa829aeca5aea2a8ea8eaea2ed0a7baca2690abacea52, 0xaa851aecb4b0ced8865eae4acb0e4aca82c886468e93f8c890ccb49d0c63aecb1ae92aae4aff0ca58e935ced46ee8baaa451b0e47ceab9b090dae4c48ecaf8ca65aea368eb2aaca33aec44b0e4290922, 0xb0924d0e7b8e626cec0d8cb35a84ac90eb8d0e7af0e0d8a86bb0cf6cec7d8eaaf90eb78eaacaecb78cb308ead78a863b0e53a84af8c9368e9418eb35b0cf3ae92daea418c8938c40ed0a95d0a9390eb4, 0xceadb90935b0b35f08eb90ec4cca1c8c42c90aedcca4590cb5906c4ac41e8cb3ecec1dac653ac895f0e1d8e625b0cfe8a6a3aa452b0e5aaeafdca83c8cb3990adbcca3b8c4298ec7bac6518a936ac40e, 0x8a949d0e92d0e90b092d8c60eaec6dac749eeac5aca57aa8a490af8f0e2b8e8f0d0e95d0e948ec8bd0c7bcec2590cbab0e6090cb98c94990cb8d0e8bcec8aaec5eb0541b0d05aea50b06c48e6038a6ac, 0xd0c958c6298e646c86d2aeb158eccbcea8aae63b8a8848ca0690eda8e8fdcc905ceaf88ecd78ec93d0e9caec70aa6af90ed58ca00d0c8b8ec96f0e388ec95b0e6bcec2e8ea068ec9090941ae634d0e93, 0x8c8c490eedaeb23ae645b0a06aeced8ea1db0d22ceb02d0ea68c62cf09088ead2d0c96cc8fd90cd18ca10d0c93aeb1e8caa4d0ea5f0b198ea188caa38e825cec3ececa3ae63df0b0eb0e73d0912aecde, 0x8ca28ccab090ef68c830ae8268caaf8caacb0a10b0426ae749906f8cecad8ca1dd0eb1f0cde8e834aea73ac61eca7158eca9cec4290ef390cdb90cda90eeeaec79b0d258a6c8b0e7fd0eae8ca18eec7f, 0xeec8d8a8308e846ae51aac87ed0ca98eaf08a6d2ac45290cee8a6f8cca6bae6518eb1c8ecb490ced8c835ac4268ea348ecfdcec4aaec87acafdb0e8490ce8b0e82eec84b04258e4fdaecfaae82ad0ca5, 0x9082e8ea45aeb36b0a2e8e62caea838c693ae82c8ea3d886acaec998ed0790cf8b0e91f0cfa90f05b0a2aaed0590b25884fd0e6938a835b0d2d8c695ceaad90825b0a26b0e8d90705b0a25cec53ae653, 0x8ca42aed12b0d42ae8458cac8b0d41ae842eea2eaea908a840aea8f8c652cecc9cecc88ecc4b082690f0d8c64fb081fd0cb68ea4288693b0e9f8ca3deec9f8c840ac88aae83deea258eafdf0cffd0ebe, 0xcecdd90f2290d0daed22aecac8ea518cad2ca736907228ed1ece9358c84cd0cc7cca81d0ed48a6fdc8715aca90b082a8ca47aed1a8ed16d0ed0acb158ed148869f8ca458eb07a86afacb138ca43f0e63, 0x8ed1ccca988ea588ca53d0eebac8f88c8568ecdeb0451cec738a852b0c0ab0c08aa4afaa4acb0eb5b0c04cece4886c88ca51ac8a38a7078c905ae85190f248ea538a84c8e936b072290d0f8c852acb23, 0xd0ef78a85e8c919ccaa590f2dceae1aed2d90853d0cde8a715aeab48ea64b08428c9128ecf28ea6390d248e949cec7fb0eb9b0eb88c85e8ca58cca9fac451b0845ae5418eceb8a856aed2ab0ebab0453, 0xac66d8e69f90f35d0cf28ca6bca60eee829d0f00aea2c90a08aeab8d0f028e693d0effcec84cec828c86daeab7f0d2acc949f0e8bd081dacab48ca648ea6b8e6958ca63907358c6c4b0c1fae685ae684, 0xee808b0ed8d0d02d0cff8eb369086bced0c90f4190d35aed41aeac4f08180a830cca99cec93cec918ed05ec804f0e93d0cf7886c4b08518e6a190741b0ed1ae691ac6c48a86dacb36cec8b8e8128e698, 0xb0c428cb14b0c41b0ee8b0eee8ea818ed12aea408ca7b8e890ecb1aac8d2cc834d0f10cc630cea1d886fd8ea85ac9248ed0dae426b0c3ed0f0ed0f12d0b2aacac48ea7bb0edbaea3c8e549b0c3bb0741, 0x8ea948cb1faca0e8ca848ea8feea738c9350ed0d8cb1eb0ef88e89f8ca81aa8f88c88ecc83bac4afae66dac4acceb0caeadad0f218e8938ed198e83090e068854990e048cb15d0f198ea84b0c45aec04, 0x90626906258e8408ca918a4fdae895b0873ae8918a912aecfd90c06b0c50d0d19cecb5ecafd8ec01aea4caeaeb8ed24d0b3f8ea918a88e8ed1dd0f27b0ef68e83c8c93fccaac8e8a18eb498a7368c6f8, 0xb062acc64faeaffcea4290e2aced33b049f8ed2bcecb98ec2c8eaa5aca2c8e84490a428ed2aaeaf6864fd8e42c90c10d0f2a8e6c490e2690e2590a4590a43ae89890e1fd0d1deea15aec1faeaf390884, 0xb0c6b8a8acaed14aa7490e71a90a5190a5390e3baec3b90c2aac9078e84c8a8afaeb05d0d2a9089f8ed35ac6af8c8ad8c8ac8eab1ca82eb062eb0c5f8ed32aea5e0e70e8c70dae6c48c8afaec34f0ec7, 0x90e41d0f44ac719aec42ea82aaec41cea53ca8fdae8b4acb05aeb0dca65eaed1faca40d0d328c81d8cab1aea708ea30f0c34aa9078ed3f8870ececd1ae451aec3e90c2eb0891906458cb36d0f3f8a8ad, 0x8caba887368cab9ac8168ed468a9358a6458c82ed0f4cae8b78c825ce863acb0d8ed47ac915cecdb8e6ac8eab98eab88e85ecc65e0ed358e85bd0d3f8a629b0c748871ab089890e458e8c4aec46aec45, 0xb0ab7ccb1290c47ee861ae6afd0d46aeb2490e51b0c7f8c8c890c45ce8358ec0690c4390c42ac923d0a348e86dcece8ceceef0c46aca4cd0d478ea408cabc90a6bce86b8c834b0ab48a630ae8a48a62c, 0x90a748ec578ec16d0e18ac4c4d0e17d0a3dcecf7aca56d0e16cecf690c4ab04c4aea86b0c85b0651b0c84b0653b0c838a8c8d0d4cac82a8cac7b0c818ec0dcecf890e508c4fdd0e0dcec15ac826f0ef7, 0xac8d78e70d8ec25a845290c53ae705aa651aca5e8ca1eb08b7908c48ec1db0ac48eada8ec17ced02cec2990c518cad7d0e1db0c8db08b4f0f02ccafd8e705cecfb8ea4cb0c8fd0e1bec66db0f358ec18, 0xae8d2d0e2fd0e378e71aa87498e88790e6b8ec2a8ec2e90a85aec6bac73fb0c9f90a81d0e338e70e8ca2cea82c9066bd0c168eaedaea998cadbaa653eea568ca29cc884d0890d0e2bccb25b0c988ec26, 0xd0e368a65290a848ec348ec338ca31cea298c8f08ca3088741cec35aeb358a549d0e34ae70d8a64f]

noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdCodes.getD (i / 32) 0
  decodeStep 9 secondAt ((block >>> (20 * (i % 32))) % 1048576)

def thirdBuckets : List ℕ := [0x401f10074201c0806c00001006420180805c201608054000008050201308048201108040200f08038200d08030400a0000000001002020070801800000801420040800c6000, 0x2036080d42034080cc0000100c42030000000000000000000100b8202d100ac202a0000020291809820250000000000000000000809000000808c2022000002021000000000, 0x816840580815c00000815800000815400001014c405100000000008140404e10130404a00000604710114204410108404000000403e000000000080f4203c080ec4039080e02037, 0x82102083102042080081fc207e081f4407b000004079201d44073201bc606c101a80000101a060650819000000000000001018820610000020600817c000000000405d1016c0000, 0x102a020a70000020a61029000001028840a00827c809b0000040990000020980000000000825c00000000080932023c000008238208d00000408b082282089082204086082140000, 0x831400000000040c30000000000830840c0082fc20be082f420bc0000040ba0000020b90000040b7082d800000000040b4082cc20b2102c040ae082b40000000000000082b040aa, 0x20e30000000000838860df0000040dd1036c20da0836400000836020d70000040d50835000000834c00000834800000834440cf0000020ce0000040cc2831c00000000020c6, 0x2101103fc0000103f420fc103e840f8000000000083dc20f6083d440f3103c40000083c040ee000000000183ac40e90000000000000000001039c00000839800000000040e4, 0x411e08474411b0846800000846400000846000000845c000008458211508450211308448211108440000000000210f08438000000000610b000004109084202107184104102, 0x8504413f104f40000104ec213a084e40000104dc4135000000000000000000000006132084c4213000000212f104b4612a104a02127000002126084946122000004120, 0x1058421600857c215e00000415c00000215b0856800001056041560855421541054841500853c214e08534000000000214c0852c0000085280000085240000085202147085188142, 0x1861000000860c418108600217f085f8617b085e82179085e06175000004173000000000105c42170000000000105b8216d105ac4169085a00000000002167000004165000004163, 0x869400000869000000868c21a208684419f08678000000000419c0000000001066821991065c000008658219508650219308648818e10630418a000000000086242188000002187, 0x21cd0873021cb1872061c52070421c0106f80000186ec0000000000000086e861b7086d821b5000000000086d021b30000061b0106b80000106b021ab106a400001069c21a6, 0x87b021eb107a421e80879c00000000041e50879021e30000021e20000000002877421dc0000000000000000000000021db1876021d70875800001874c41d10874021cf087380000, 0x220d1082c220a0000000000882400001081c00000881862031080461fe000000000187ec21fa187dc61f40000061f1000000000087c021ef000000000087b800000000021ed, 0x1089000000000022230000000000000042211087c221e08874421b00000221a088640000088600000000002217188500000000000000000004212000002211088400000108380000, 0x89042240000000000108f80000000000000088f4223c00000000000000223b088e86237088d82235088d00000108c82231088c0822c000000000108a80000108a04226, 0x8980425e00000625b0000042590896022570895800000895422540000042520894400001093c224e00000000010930424a089240000089202247109142244000004242000000000, 0x8a0c428108a00627d189e82279000004277089d80000000000000189cc2272000000000089c42270089bc426d089b0226b109a422680899c00000899800001898c2262000002261, 0x229800000429600000000000000000008a54229408a4c000010a44229008a3c228e00000228d08a30000000000000000000000000000428a10a20000000000628508a100000, 0x8ae082b400000000008acc42b120ab400000000000000000022ac00000000008aac42a90000022a800000000010a9822a50000000000000062a20000042a010a78229d10a6c4299, 0x10b84000008b8062dd08b7082d810b58000008b5442d308b48000010b4042ce00000000008b3462ca0000022c900000000008b2042c628b04000018af842bc08aec42b9000000000, 0x8bf842fc00000000010be8000018bdc000018bd022f310bc400000000042ef08bb800000000022ed08bb000000000022eb08ba8000010ba022e708b9822e50000022e40000022e3, 0x8c64000000000000008c60000010c58231508c50000000000231308c48231100000000018c38230d10c2c000000000230a08c24000000000230808c1c230608c14430310c0442ff, 0x233200000433010cb8432c00000232b08ca8000008ca4232808c9c000008c98232500000000008c90432208c84000008c80000008c7c231e00000231d00000000010c6c231a, 0x235208d44235010d38234d00000000000000000008d30434a00000000008d24434730d04633e00000000000000000010cf0233b08ce8233908ce0000008cdc000008cd86333, 0x237808ddc000000000000000000237600000237518dc8437008dbc000008db8836a10da0236708d98000000000000010d90436208d84236008d7c835b10d64000020d544353, 0x239a00000000008e64239810e58000008e54639208e44438f08e38238d18e28238908e20238710e14000008e10238308e08000008e04637e08df4237c08dec000008de82379, 0x18f0423c000000000008efc23be18eec000010ee4000008ee063b508ed000000000023b318ec043ae10eb023ab08ea8000010ea023a710e94000008e90000018e84000018e78639b, 0x8fa043e610f9063e10000000000000023e028f6c000000000000008f68000008f6423d808f5c23d608f5443d310f4443cf08f3823cd08f3043ca10f20000008f1c43c508f100000, 0x440e00000240d1102c240a2101824051100c440109000000008ffc23fe0000063fb18fe043f608fd423f40000023f30000023f220fb8000008fb4000008fb023eb08fa823e9]

def bucketMissing (count : ℕ) (atState : ℕ → SearchState)
    (table : List ℕ) (z : ℕ) (v : List W) : Bool :=
  st (z % 65521 % 1024) fun tag =>
    st (((table.getD (tag / 32) 0) >>> (18 * (tag % 32))) % 262144) fun code =>
      let a := code % 8192
      let n := code / 8192
      if a + n ≤ count then frontierMissing ((List.range' a n).map atState) z v else true

lemma bucketMissing_found {count : ℕ} {atState : ℕ → SearchState} {table : List ℕ}
    {z : ℕ} {v : List W} (h : bucketMissing count atState table z v = false) :
    ∃ i < count, atState i = (z,v) := by
  unfold bucketMissing at h
  simp only [st_eq] at h
  split at h
  · rename_i ok
    obtain ⟨i, hi, same⟩ := List.mem_map.mp (frontierMissing_false h)
    exact ⟨i, lt_of_lt_of_le (List.mem_range'_1.mp hi).2 ok, same⟩
  · contradiction


noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12)
      e8L rootPreparedMask rootPreparedSlots 10 0 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 10 9 0 z v))

lemma afterSecond_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 10)
    (mixed : mixedFromSecond state = false)
    (pure : pureAt 10 state (fun z v => afterThird (z,v)) = false) :
    afterSecond state = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false e8L 11 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 11 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 11 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [afterSecond, frc_eq, st_eq, show (11 : ℕ) = Nat.succ 10 from rfl, look1C_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 0) e8L state.2 (tstC I.NN I.AA I.HX I.HY false e8L 11 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 0) e8L state.2 (bif pureAt 10 state
      (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 10 9 0)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeCheck_append (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all



noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  (!pureAt 10 state (bucketMissing thirdCount thirdAt thirdBuckets)) &&
    (decide (1 < state.2.length) && decide (state.2.length < 10))

noncomputable def thirdTest (j : ℕ) : Bool := !afterThird (thirdAt j)
noncomputable def secondMixedTest (j : ℕ) : Bool := !mixedFromSecond (secondAt j)

lemma checkedAfterSecond (i : ℕ) (hi : i < secondCount)
    (ready : rangeCheck readyForThird 0 secondCount = true)
    (mixed : rangeCheck secondMixedTest 0 secondCount = true)
    (third : rangeCheck thirdTest 0 thirdCount = true) :
    afterSecond (secondAt i) = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForThird, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, htwo, hsmall⟩ := h
  refine afterSecond_false (secondAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 10 (secondAt i) afterThird
    (bucketMissing thirdCount thirdAt thirdBuckets) (boolOfNeg hc) ?_
  intro z words found
  obtain ⟨j, hj, eq⟩ := bucketMissing_found found
  rw [← eq]
  exact boolOfNeg (rangeCheck_at third hj)

noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  (!pureSecond state (bucketMissing secondCount secondAt secondBuckets)) &&
    (decide (1 < state.2.length) && decide (state.2.length < 11))

noncomputable def mixedSecondPicked (state : SearchState) (b : Fin 8) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvPicked I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12)
      e8L rootPreparedMask rootPreparedSlots 11 0 z v 0 b))

lemma mixedSecondPicked_all (state : SearchState)
    (checked : ∀ b, mixedSecondPicked state b = false) : mixedSecond state = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  simp only [mixedSecond, frc_eq, st_eq] at h
  obtain ⟨b,hb⟩ := mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hc := checked b
  simp only [mixedSecondPicked, frc_eq, st_eq] at hc
  exact Bool.noConfusion (hc.symm.trans hb)

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 11 (firstAt i) afterSecond
    (bucketMissing secondCount secondAt secondBuckets) (boolOfNeg hc) ?_
  intro z words found
  obtain ⟨j, hj, eq⟩ := bucketMissing_found found
  rw [← eq]
  exact next j hj


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk3 : rangeCheck readyForSecond 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk4 : rangeCheck readyForSecond 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk5 : rangeCheck readyForSecond 20 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk6 : rangeCheck readyForSecond 24 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk7 : rangeCheck readyForSecond 28 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 firstCount = true := by
  exact (@rangeCheck_append readyForSecond 0 16 15
    (@rangeCheck_append readyForSecond 0 8 8
    (@rangeCheck_append readyForSecond 0 4 4
    firstCoverageChunk0 firstCoverageChunk1) (@rangeCheck_append readyForSecond 8 4 4
    firstCoverageChunk2 firstCoverageChunk3)) (@rangeCheck_append readyForSecond 16 8 7
    (@rangeCheck_append readyForSecond 16 4 4
    firstCoverageChunk4 firstCoverageChunk5) (@rangeCheck_append readyForSecond 24 4 3
    firstCoverageChunk6 firstCoverageChunk7)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 16 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 firstCount = true := by
  exact (@rangeCheck_append firstMixedTest 0 16 15
    firstMixedChunk0 firstMixedChunk1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 12 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 24 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 36 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 48 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 60 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 72 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 84 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 96 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 108 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 120 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 132 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk12 : rangeCheck readyForThird 144 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk13 : rangeCheck readyForThird 156 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk14 : rangeCheck readyForThird 168 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk15 : rangeCheck readyForThird 180 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk16 : rangeCheck readyForThird 192 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk17 : rangeCheck readyForThird 204 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk18 : rangeCheck readyForThird 216 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk19 : rangeCheck readyForThird 228 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk20 : rangeCheck readyForThird 240 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk21 : rangeCheck readyForThird 252 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk22 : rangeCheck readyForThird 264 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk23 : rangeCheck readyForThird 276 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk24 : rangeCheck readyForThird 288 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk25 : rangeCheck readyForThird 300 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk26 : rangeCheck readyForThird 312 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk27 : rangeCheck readyForThird 324 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 secondCount = true := by
  exact (@rangeCheck_append readyForThird 0 168 165
    (@rangeCheck_append readyForThird 0 84 84
    (@rangeCheck_append readyForThird 0 36 48
    (@rangeCheck_append readyForThird 0 12 24
    secondCoverageChunk0 (@rangeCheck_append readyForThird 12 12 12
    secondCoverageChunk1 secondCoverageChunk2)) (@rangeCheck_append readyForThird 36 24 24
    (@rangeCheck_append readyForThird 36 12 12
    secondCoverageChunk3 secondCoverageChunk4) (@rangeCheck_append readyForThird 60 12 12
    secondCoverageChunk5 secondCoverageChunk6))) (@rangeCheck_append readyForThird 84 36 48
    (@rangeCheck_append readyForThird 84 12 24
    secondCoverageChunk7 (@rangeCheck_append readyForThird 96 12 12
    secondCoverageChunk8 secondCoverageChunk9)) (@rangeCheck_append readyForThird 120 24 24
    (@rangeCheck_append readyForThird 120 12 12
    secondCoverageChunk10 secondCoverageChunk11) (@rangeCheck_append readyForThird 144 12 12
    secondCoverageChunk12 secondCoverageChunk13)))) (@rangeCheck_append readyForThird 168 84 81
    (@rangeCheck_append readyForThird 168 36 48
    (@rangeCheck_append readyForThird 168 12 24
    secondCoverageChunk14 (@rangeCheck_append readyForThird 180 12 12
    secondCoverageChunk15 secondCoverageChunk16)) (@rangeCheck_append readyForThird 204 24 24
    (@rangeCheck_append readyForThird 204 12 12
    secondCoverageChunk17 secondCoverageChunk18) (@rangeCheck_append readyForThird 228 12 12
    secondCoverageChunk19 secondCoverageChunk20))) (@rangeCheck_append readyForThird 252 36 45
    (@rangeCheck_append readyForThird 252 12 24
    secondCoverageChunk21 (@rangeCheck_append readyForThird 264 12 12
    secondCoverageChunk22 secondCoverageChunk23)) (@rangeCheck_append readyForThird 288 24 21
    (@rangeCheck_append readyForThird 288 12 12
    secondCoverageChunk24 secondCoverageChunk25) (@rangeCheck_append readyForThird 312 12 9
    secondCoverageChunk26 secondCoverageChunk27)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 12 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 24 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 36 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 48 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 60 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 72 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 84 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk8 : rangeCheck secondMixedTest 96 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk9 : rangeCheck secondMixedTest 108 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk10 : rangeCheck secondMixedTest 120 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk11 : rangeCheck secondMixedTest 132 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk12 : rangeCheck secondMixedTest 144 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk13 : rangeCheck secondMixedTest 156 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk14 : rangeCheck secondMixedTest 168 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk15 : rangeCheck secondMixedTest 180 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk16 : rangeCheck secondMixedTest 192 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk17 : rangeCheck secondMixedTest 204 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk18 : rangeCheck secondMixedTest 216 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk19 : rangeCheck secondMixedTest 228 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk20 : rangeCheck secondMixedTest 240 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk21 : rangeCheck secondMixedTest 252 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk22 : rangeCheck secondMixedTest 264 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk23 : rangeCheck secondMixedTest 276 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk24 : rangeCheck secondMixedTest 288 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk25 : rangeCheck secondMixedTest 300 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk26 : rangeCheck secondMixedTest 312 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk27 : rangeCheck secondMixedTest 324 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 secondCount = true := by
  exact (@rangeCheck_append secondMixedTest 0 168 165
    (@rangeCheck_append secondMixedTest 0 84 84
    (@rangeCheck_append secondMixedTest 0 36 48
    (@rangeCheck_append secondMixedTest 0 12 24
    secondMixedChunk0 (@rangeCheck_append secondMixedTest 12 12 12
    secondMixedChunk1 secondMixedChunk2)) (@rangeCheck_append secondMixedTest 36 24 24
    (@rangeCheck_append secondMixedTest 36 12 12
    secondMixedChunk3 secondMixedChunk4) (@rangeCheck_append secondMixedTest 60 12 12
    secondMixedChunk5 secondMixedChunk6))) (@rangeCheck_append secondMixedTest 84 36 48
    (@rangeCheck_append secondMixedTest 84 12 24
    secondMixedChunk7 (@rangeCheck_append secondMixedTest 96 12 12
    secondMixedChunk8 secondMixedChunk9)) (@rangeCheck_append secondMixedTest 120 24 24
    (@rangeCheck_append secondMixedTest 120 12 12
    secondMixedChunk10 secondMixedChunk11) (@rangeCheck_append secondMixedTest 144 12 12
    secondMixedChunk12 secondMixedChunk13)))) (@rangeCheck_append secondMixedTest 168 84 81
    (@rangeCheck_append secondMixedTest 168 36 48
    (@rangeCheck_append secondMixedTest 168 12 24
    secondMixedChunk14 (@rangeCheck_append secondMixedTest 180 12 12
    secondMixedChunk15 secondMixedChunk16)) (@rangeCheck_append secondMixedTest 204 24 24
    (@rangeCheck_append secondMixedTest 204 12 12
    secondMixedChunk17 secondMixedChunk18) (@rangeCheck_append secondMixedTest 228 12 12
    secondMixedChunk19 secondMixedChunk20))) (@rangeCheck_append secondMixedTest 252 36 45
    (@rangeCheck_append secondMixedTest 252 12 24
    secondMixedChunk21 (@rangeCheck_append secondMixedTest 264 12 12
    secondMixedChunk22 secondMixedChunk23)) (@rangeCheck_append secondMixedTest 288 24 21
    (@rangeCheck_append secondMixedTest 288 12 12
    secondMixedChunk24 secondMixedChunk25) (@rangeCheck_append secondMixedTest 312 12 9
    secondMixedChunk26 secondMixedChunk27)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 48 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 96 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 144 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 192 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 240 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 288 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 336 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 384 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 432 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 480 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 528 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 576 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 624 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 672 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 720 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 768 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk17 : rangeCheck thirdTest 816 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk18 : rangeCheck thirdTest 864 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk19 : rangeCheck thirdTest 912 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk20 : rangeCheck thirdTest 960 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk21 : rangeCheck thirdTest 1008 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 thirdCount = true := by
  exact (@rangeCheck_append thirdTest 0 528 512
    (@rangeCheck_append thirdTest 0 240 288
    (@rangeCheck_append thirdTest 0 96 144
    (@rangeCheck_append thirdTest 0 48 48
    thirdTailChunk0 thirdTailChunk1) (@rangeCheck_append thirdTest 96 48 96
    thirdTailChunk2 (@rangeCheck_append thirdTest 144 48 48
    thirdTailChunk3 thirdTailChunk4))) (@rangeCheck_append thirdTest 240 144 144
    (@rangeCheck_append thirdTest 240 48 96
    thirdTailChunk5 (@rangeCheck_append thirdTest 288 48 48
    thirdTailChunk6 thirdTailChunk7)) (@rangeCheck_append thirdTest 384 48 96
    thirdTailChunk8 (@rangeCheck_append thirdTest 432 48 48
    thirdTailChunk9 thirdTailChunk10)))) (@rangeCheck_append thirdTest 528 240 272
    (@rangeCheck_append thirdTest 528 96 144
    (@rangeCheck_append thirdTest 528 48 48
    thirdTailChunk11 thirdTailChunk12) (@rangeCheck_append thirdTest 624 48 96
    thirdTailChunk13 (@rangeCheck_append thirdTest 672 48 48
    thirdTailChunk14 thirdTailChunk15))) (@rangeCheck_append thirdTest 768 144 128
    (@rangeCheck_append thirdTest 768 48 96
    thirdTailChunk16 (@rangeCheck_append thirdTest 816 48 48
    thirdTailChunk17 thirdTailChunk18)) (@rangeCheck_append thirdTest 912 48 80
    thirdTailChunk19 (@rangeCheck_append thirdTest 960 48 32
    thirdTailChunk20 thirdTailChunk21)))))

def initialIndices (kind : Bool) : List ℕ := if kind then [1, 2, 4, 6, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 29, 30] else [0, 3, 5, 7, 11, 13, 15, 22, 24, 27]

noncomputable def initialStates (kind : Bool) : List SearchState := (initialIndices kind).map firstAt

lemma allInitialIndices (kind : Bool) : (initialIndices kind).all (fun i => decide (i < firstCount)) = true := by
  cases kind <;> decide +kernel

lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) : chkPairPicked [] e8Q 8 12 0 FF 0 kind = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : chk [] e8Q 8 12 0 FF 0 = false :=
  chkPair_picked [] e8Q 8 12 0 FF 0 binaryCertificate


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked0 : chkPicked [] e8Q 8 12 0 0 1 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked1 : chkPicked [] e8Q 8 12 0 0 1 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked2 : chkPicked [] e8Q 8 12 0 0 1 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked3 : chkPicked [] e8Q 8 12 0 0 1 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked4 : chkPicked [] e8Q 8 12 0 0 1 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked5 : chkPicked [] e8Q 8 12 0 0 1 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked6 : chkPicked [] e8Q 8 12 0 0 1 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked7 : chkPicked [] e8Q 8 12 0 0 1 7 = false := by decide +kernel

lemma unaryChecked : chk [] e8Q 8 12 0 0 1 = false := by
  apply chk_picked
  intro b
  fin_cases b
  · exact unaryChecked0
  · exact unaryChecked1
  · exact unaryChecked2
  · exact unaryChecked3
  · exact unaryChecked4
  · exact unaryChecked5
  · exact unaryChecked6
  · exact unaryChecked7


def rootCases : List (ℕ × ℕ) := [(FF, 0), (0, 1)]

lemma rootCases_full : mFull rootCases = true := by decide +kernel

lemma certify_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] e8Q 8 12 0 p.1 p.2 = false := by
  refine ⟨rootCases, rootCases_full, ?_⟩
  intro p hp
  simp only [rootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked



end CofactorEight

lemma e8_0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧
    ∀ p ∈ M, chk [] e8Q 8 12 0 p.1 p.2 = false :=
  CofactorEight.certify_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case0_false : chkPairPicked [] e8Q 8 12 1 0x4000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case0_true : chkPairPicked [] e8Q 8 12 1 0x4000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case0 : chk [] e8Q 8 12 1 0x4000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case0_false
  · exact e8_1_case0_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case1_false : chkPairPicked [] e8Q 8 12 1 0x100000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case1_true : chkPairPicked [] e8Q 8 12 1 0x100000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case1 : chk [] e8Q 8 12 1 0x100000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case1_false
  · exact e8_1_case1_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case2_false : chkPairPicked [] e8Q 8 12 1 0x10000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case2_true : chkPairPicked [] e8Q 8 12 1 0x10000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case2 : chk [] e8Q 8 12 1 0x10000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case2_false
  · exact e8_1_case2_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case3_false : chkPairPicked [] e8Q 8 12 1 0x400000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case3_true : chkPairPicked [] e8Q 8 12 1 0x400000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case3 : chk [] e8Q 8 12 1 0x400000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case3_false
  · exact e8_1_case3_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case4_false : chkPairPicked [] e8Q 8 12 1 0x40000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case4_true : chkPairPicked [] e8Q 8 12 1 0x40000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case4 : chk [] e8Q 8 12 1 0x40000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case4_false
  · exact e8_1_case4_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case5_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case5_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case5 : chk [] e8Q 8 12 1 0x1000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case5_false
  · exact e8_1_case5_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case6_false : chkPairPicked [] e8Q 8 12 1 0x400000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case6_true : chkPairPicked [] e8Q 8 12 1 0x400000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case6 : chk [] e8Q 8 12 1 0x400000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case6_false
  · exact e8_1_case6_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case7_false : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case7_true : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case7 : chk [] e8Q 8 12 1 0x40000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case7_false
  · exact e8_1_case7_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case8_false : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case8_true : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case8 : chk [] e8Q 8 12 1 0x4000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case8_false
  · exact e8_1_case8_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case9_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case9_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case9 : chk [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case9_false
  · exact e8_1_case9_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case10_false : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case10_true : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case10 : chk [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case10_false
  · exact e8_1_case10_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case11_false : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case11_true : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case11 : chk [] e8Q 8 12 1 0x4000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case11_false
  · exact e8_1_case11_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case12_false : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case12_true : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case12 : chk [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case12_false
  · exact e8_1_case12_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case13_false : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case13_true : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case13 : chk [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case13_false
  · exact e8_1_case13_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case14_false : chkPairPicked [] e8Q 8 12 1 0x400000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case14_true : chkPairPicked [] e8Q 8 12 1 0x400000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case14 : chk [] e8Q 8 12 1 0x400000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case14_false
  · exact e8_1_case14_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case15_false : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case15_true : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case15 : chk [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case15_false
  · exact e8_1_case15_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case16_false : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case16_true : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case16 : chk [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case16_false
  · exact e8_1_case16_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case17_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case17_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case17 : chk [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case17_false
  · exact e8_1_case17_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case18_false : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case18_true : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case18 : chk [] e8Q 8 12 1 0x100000000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case18_false
  · exact e8_1_case18_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case19 : chk [] e8Q 8 12 1 0x2fefafaebefefffffbfbfbfffffffffffffffffffefbfbefefbfff 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

lemma e8_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧
    ∀ p ∈ M, chk [] e8Q 8 12 1 p.1 p.2 = false := by
  refine ⟨e8Cases, e8Full, ?_⟩
  intro p hp
  simp only [e8Cases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e8_1_case0
  · exact e8_1_case1
  · exact e8_1_case2
  · exact e8_1_case3
  · exact e8_1_case4
  · exact e8_1_case5
  · exact e8_1_case6
  · exact e8_1_case7
  · exact e8_1_case8
  · exact e8_1_case9
  · exact e8_1_case10
  · exact e8_1_case11
  · exact e8_1_case12
  · exact e8_1_case13
  · exact e8_1_case14
  · exact e8_1_case15
  · exact e8_1_case16
  · exact e8_1_case17
  · exact e8_1_case18
  · exact e8_1_case19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_2 : chk [] e8Q 8 12 2 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_3 : chk [] e8Q 8 12 3 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_4 : chk [] e8Q 8 12 4 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_5 : chk [] e8Q 8 12 5 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_6 : chk [] e8Q 8 12 6 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_7 : chk [] e8Q 8 12 7 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_8 : chk [] e8Q 8 12 8 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_9 : chk [] e8Q 8 12 9 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_10 : chk [] e8Q 8 12 10 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_11 : chk [] e8Q 8 12 11 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_12 : chk [] e8Q 8 12 12 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

lemma one_e8 {t : ℕ} (h : chk [] e8Q 8 12 t FF 1 = false) :
    ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] e8Q 8 12 t p.1 p.2 = false :=
  ⟨[(FF,1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h⟩

lemma strongRow8 : Imp [] 8 13 := by
  apply imp_of (Or.inl rfl) e8Ok (by decide)
  · intro e he
    unfold e8Q pr at he
    exact hv1 e (List.mem_of_mem_filter (List.mem_of_mem_filter he))
  · right
    intro t ht
    interval_cases t
    · exact e8_0
    · exact e8_1
    · exact one_e8 e8_2
    · exact one_e8 e8_3
    · exact one_e8 e8_4
    · exact one_e8 e8_5
    · exact one_e8 e8_6
    · exact one_e8 e8_7
    · exact one_e8 e8_8
    · exact one_e8 e8_9
    · exact one_e8 e8_10
    · exact one_e8 e8_11
    · exact one_e8 e8_12

def oneQ : List (ℕ × ℕ) := (pr pv1 1).filter (fun e => e.2 ≥ 4)

def oneInp : List W := [
  ⟨0x1f7f7000001f000000000000000000000000000000000000000000000000000000000000000000000000000004894000a000001400000280000a000050000000000010000000010000000000000000008000040000000010000000000000000000000000000000fbe0000000fbf0007c003f00043e0001f8003e0010000008fc0010f80043f000421000004000020000203e00b56b0a85fde2a8bfbc5517b8885fdcc2fee60000000000000000000000000000000000000000000000000000000000000000004841900118312c7, 0x2000000000000042108400004210840000000000000000008421084000000000000000000040000000, 0x10000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000020000000002000000000000042108400004210840000000000000000008421084000000000000000000040000000, 3⟩,
  ⟨0x1f7f700000007fdb8ff6e7feb8e7fe730000000000000000000000000000000000000000000000000000000016ad60009e000013c00002600009e0004f001258b02857c00240217c0000000000000000bc0005e000000017800000000000000000000000000000f818000000020ec043b020f40721f018070001c0000000000380080700200e00200000002000010000000180b56b00000000000000000000000000000000dac5856abfbc5b018bfb98000000000000000000000000000000000000000000004c4992011090681, 0x20000000000100000000000040000021084000002108421080000000008000000210842000000000000002000000, 0x800000001084210000000000000210800000000000000000000000000000000000000000000000000000000000000000000, 0x800000021084210000100000000210840000021084000002108421080000000008000000210842000000000000002000000, 3⟩,
  ⟨0x7fdb8ff6e000000000003fedc7fb73800001c0000000000000000000000000000000000000001200015019a0000330000050000198000cc01b50a00006300000006300000001224090003340019a000000066000000000000000000000000000008203000000830e186386108180110301846c311b1c00000e80380080700200e0110000001000008000102030b0000a85fde2000000000000000000000000dac580000000000000000000000d1a16c085fbcc2fde60000000000000000000004a45018018b160e, 0x1000000000008000000000002000020000200002100000004210800000400000200000108420000000000100000, 0x40000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x40000001000000800008000000000002000020000200002100000004210800000400000200000108420000000000100000, 3⟩,
  ⟨0x7fdb800007feb8e000003fedc000038000001ff7a38000007fdf0e72000000000000000000001024011015141402a482a077000152800a94185800ac05248360005250000001a002d8002a280151418c00054900000000000000000000000000002080000000224e00000024d007000001246000001c00000052241c000000c490739000000000000000000800816008800000a000001517b8800000000000c2c0056000001b0000000000000d0016c000000000000c600000000000000000004204928028b044b, 0x4000840000000084200800000021084210842008001084010042100001000000800008001000210000000400, 0x100000000000002108421000000042108400000000000000000000000000000000000000000000000000000000000000, 0x100000004000842108421084200842108421084210842008001084010042100001000000800008001000210000000400, 3⟩,
  ⟨0x7feb807fe7000000000000000000000000000007fdf007000000f000000000700000020200006040000c08220220100608003048008102041808300301810000000000208100c08006048840801812000000000000000000000000000082180000008120c048321d0c023a1800826020984000002040d04081a1094b803800000780000000038021801030000000000000011000008000002fee600c18102000018018000000000010210c08000002fde6c60c0bf79800000000000080d938120a1080, 0x10000000001000000000000400080000040000020080200802100000004000002000020004010800000001, 0x400000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000010000000001004000000000400080000040000020080200802100000004000002000020004010800000001, 3⟩,
  ⟨0x3fedc7fb700000001ff7a39fef4e000000000000000000000000000000000140019815003700001400001b0000d80900008500370000000360000001a340000003300019810810006e00000000000000000000000000004110800000408884122108604208c091466229988000000063251c664a71081800800000080000000008110804000a000000a8bfbc400000000000000000d800056abfbc400000000000000d1a000000000000000c60c0bf798000000000000e4482002820685, 0x80000000000400000210000100001080010000008420004200042000020000010000100001084000000008000, 0x2000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000080000040000400000210000100001080010000008420004200042000020000010000100001084000000008000, 3⟩,
  ⟨0x1ff7a01fef407fdf0e0000000f0000700000000000000000001c11000682800601000390001c00000081000681201000720000008102401000390001c18018000d0000000000000000000000000000104a000000102450091402150104320811480452080000044ab400556800a6d07000000078000380000004a0000800000000880000140000085fdcc000000204040800001b018bfb9800000c18160085fbcc00000c00c00000000000000000020c90811010608, 0x200000000020000010800008021000000800100401000010840100000080000040000400080200800000020, 0x8000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000, 0x8000000200000000020080010800008021000000800100401000010840100000080000040000400080200800000020, 3⟩]

def oneM : ℕ := 0x1f7f7000001f7fdb8ff6e7feb8e7fe733fedc7fb73800001dff7a39fef4e7fdf0e7200000f000070000707f716ad6150bfbc5517f78aa2f7110bfb985fdcdb58b0ad57f78b60317f73000001a342d810bf7985fbcd8c1817ef3000000000000000000000000000fbfb800000fbfedc7fb73ff5c73ff399ff6e3fdb9c00000effbd1cff7a73fef8739000007800038000383fb8b56b0a85fde2a8bfbc5517b8885fdcc2fee6dac5856abfbc5b018bfb9800000d1a16c085fbcc2fde6c60c0bf798000000000004e4d938138b16cf

def oneG : ℕ := 0x108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210

def oneB : ℕ := 0x17a5ef3bdef7ad6b7bde96b5ad6bded6b5ef7bdef7bdef7bded6b5ad6b5ef6bded7bdef4bdeb5a56b6ad6d4b5695b52539c673

def oneL : ℕ := 0xfbfb800000fbfedc7fb73ff5c73ff399ff6e3fdb9c00000effbd1cff7a73fef8739000007800038000383fb8b56b0a85fde2a8bfbc5517b8885fdcc2fee6dac5856abfbc5b018bfb9800000d1a16c085fbcc2fde6c60c0bf79800000000000000000000000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneInp_eq : avl (PZ oneQ) (mz 1) (rawL []) = oneInp := Eq.refl oneInp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneM_eq : mz 1 = oneM := Eq.refl oneM

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneG_eq : pL (oneQ.map fun _ => 16) = oneG := Eq.refl oneG

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneB_eq : pL (oneQ.map fun e => 16 + (11 - e.2)) = oneB := Eq.refl oneB

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneL_eq : lz 1 = oneL := Eq.refl oneL

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneInputs (d : Bool) : allInputsNeeded I.NN d oneL oneInp 0 = true := by
  cases d <;> decide +kernel

noncomputable def oneFast (t H ph : ℕ) : Bool :=
  guardStart t H ph (startvC I.NN I.AA I.HX I.HY oneL oneM oneG oneB 11 t 0 H ph) oneInp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneFast_eq (t H ph : ℕ) : chk [] oneQ 1 11 t H ph = oneFast t H ph := by
  rw [← chkFast_eq]
  simp only [chkFast, searchInputs, frc_eq, st_eq, oneInp_eq, oneM_eq, oneG_eq, oneB_eq, oneL_eq]
  change anySubC I.NN (pos t) oneL oneInp 0 _ = _
  rw [anySub_allInputs (oneInputs (pos t))]
  rfl

def oneCases : List (ℕ × ℕ) := [(0x2000000000000010000000000000400000000000, 0), (0x800000080000000000000000000000000000000000000000020, 0), (0x800000080000000000000000000000000000000400000, 0), (0x40004000000000000001000000000000000000, 0), (0x8800000000000000000000000000000000000000000008000, 0), (0x200000020400001000000100008000000000, 0), (0x3ff7f77ff77fffdf3fdfbffffdfbefffeffefffeffbf7fffbf7fdf, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneFull : mFull oneCases = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma onePOk : pOk 1 oneQ = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch0 : oneFast 0 0x2000000000000010000000000000400000000000 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch1 : oneFast 0 0x800000080000000000000000000000000000000000000000020 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch2 : oneFast 0 0x800000080000000000000000000000000000000400000 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch3 : oneFast 0 0x40004000000000000001000000000000000000 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch4 : oneFast 0 0x8800000000000000000000000000000000000000000008000 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch5 : oneFast 0 0x200000020400001000000100008000000000 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneBranch6 : oneFast 0 0x3ff7f77ff77fffdf3fdfbffffdfbefffeffefffeffbf7fffbf7fdf 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneRest : (List.range' 1 11).all (fun t => !(oneFast t FF 1)) = true := by decide +kernel

lemma strongRow1 : Imp [] 1 12 := by
  apply imp_of (Or.inl rfl) onePOk (by decide)
  · intro e he
    unfold oneQ pr at he
    exact hv1 e (List.mem_of_mem_filter (List.mem_of_mem_filter he))
  · right
    intro t ht
    by_cases hzero : t = 0
    · subst t
      refine ⟨oneCases, oneFull, fun p hp => ?_⟩
      simp only [oneCases, List.mem_cons, List.not_mem_nil, or_false] at hp
      rw [oneFast_eq]
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact oneBranch0
      · exact oneBranch1
      · exact oneBranch2
      · exact oneBranch3
      · exact oneBranch4
      · exact oneBranch5
      · exact oneBranch6
    · have hmem := (List.mem_range'_1).mpr (show 1 ≤ t ∧ t < 1+11 from ⟨by omega, by omega⟩)
      have hcheck := List.all_eq_true.mp oneRest t hmem
      have result : oneFast t FF 1 = false := Bool.not_eq_true'.mp hcheck
      refine ⟨[(FF,1)],ffull,fun p hp => ?_⟩
      simp only [List.mem_singleton] at hp
      subst hp
      rw [oneFast_eq]
      exact result

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked2 : okE [] (pr pv1 2) (2,12) = true := by decide +kernel

lemma strongRow2 : Imp [] 2 12 :=
  imp_okE (Or.inl rfl) strongChecked2 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked4 : okE [] (pr pv1 4) (4,12) = true := by decide +kernel

lemma strongRow4 : Imp [] 4 12 :=
  imp_okE (Or.inl rfl) strongChecked4 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked16 : okE [] (pr pv1 16) (16,11) = true := by decide +kernel

lemma strongRow16 : Imp [] 16 11 :=
  imp_okE (Or.inl rfl) strongChecked16 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked32 : okE [] (pr pv1 32) (32,11) = true := by decide +kernel

lemma strongRow32 : Imp [] 32 11 :=
  imp_okE (Or.inl rfl) strongChecked32 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked64 : okE [] (pr pv1 64) (64,11) = true := by decide +kernel

lemma strongRow64 : Imp [] 64 11 :=
  imp_okE (Or.inl rfl) strongChecked64 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked128 : okE [] (pr pv1 128) (128,11) = true := by decide +kernel

lemma strongRow128 : Imp [] 128 11 :=
  imp_okE (Or.inl rfl) strongChecked128 (fun e he => hv1 e (List.mem_of_mem_filter he))

lemma strongRows_sound : ∀ e ∈ rStrong, Imp [] e.1 e.2 := by
  intro p hp
  simp only [rStrong, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact strongRow1
  · exact strongRow2
  · exact strongRow4
  · exact strongRow8
  · exact strongRow16
  · exact strongRow32
  · exact strongRow64
  · exact strongRow128

def rootBounds : List (ℕ × ℕ) :=
  (rStrong ++ pv1.filter (fun e => !(rStrong.any fun t => t.1 == e.1))).filter (fun p => p.2 ≥ 5)
lemma rootBounds_sound : ∀ p ∈ rootBounds, Imp [] p.1 p.2 := by
  intro p hp
  rcases List.mem_append.mp (List.mem_of_mem_filter hp) with h | h
  · exact strongRows_sound p h
  · exact hv1 p (List.mem_of_mem_filter h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_p : pOk 0 rootBounds = true := by decide +kernel

private def graph : (Fin 8 → Bool) → Bool := fun x =>
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

private def witness : Circuit := ⟨[
   ⟨.or, [4, 3]⟩,
   ⟨.or, [7, 0]⟩,
   ⟨.and, [8, 9]⟩,
   ⟨.and, [1, 4]⟩,
   ⟨.or, [2, 1]⟩,
   ⟨.or, [7, 5]⟩,
   ⟨.and, [12, 13]⟩,
   ⟨.or, [4, 2]⟩,
   ⟨.or, [15, 0]⟩,
   ⟨.and, [16, 6]⟩,
   ⟨.and, [5, 7]⟩,
   ⟨.or, [10, 11]⟩,
   ⟨.or, [19, 14]⟩,
   ⟨.or, [20, 17]⟩,
   ⟨.or, [21, 18]⟩], 22⟩

lemma witness_basis : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

lemma witness_size : witness.gates.length = 15 := rfl

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)

lemma f_graph (x : Fin 8 → Bool) : f x = graph x := by
  have hx : f x = true ↔ (x 0 = true ∧ x 3 = true) ∨ (x 0 = true ∧ x 4 = true) ∨ (x 1 = true ∧ x 4 = true) ∨ (x 1 = true ∧ x 5 = true) ∨ (x 2 = true ∧ x 5 = true) ∨ (x 0 = true ∧ x 6 = true) ∨ (x 2 = true ∧ x 6 = true) ∨ (x 4 = true ∧ x 6 = true) ∨ (x 1 = true ∧ x 7 = true) ∨ (x 2 = true ∧ x 7 = true) ∨ (x 3 = true ∧ x 7 = true) ∨ (x 4 = true ∧ x 7 = true) ∨ (x 5 = true ∧ x 7 = true) := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  unfold graph
  rw [Bool.eq_iff_iff, hx, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h)
    · exact ⟨0, by decide, by simpa using h⟩
    · exact ⟨1, by decide, by simpa using h⟩
    · exact ⟨2, by decide, by simpa using h⟩
    · exact ⟨3, by decide, by simpa using h⟩
    · exact ⟨4, by decide, by simpa using h⟩
    · exact ⟨5, by decide, by simpa using h⟩
    · exact ⟨6, by decide, by simpa using h⟩
    · exact ⟨7, by decide, by simpa using h⟩
    · exact ⟨8, by decide, by simpa using h⟩
    · exact ⟨9, by decide, by simpa using h⟩
    · exact ⟨10, by decide, by simpa using h⟩
    · exact ⟨11, by decide, by simpa using h⟩
    · exact ⟨12, by decide, by simpa using h⟩
  · rintro ⟨i, hi, h⟩
    have hi' : i < 13 := hi
    interval_cases i <;> simp_all

set_option maxHeartbeats 5000000 in
lemma witness_eval (x : Fin 8 → Bool) : witness.eval (List.ofFn x) = graph x := by
  rw [← f_graph]
  simp only [witness, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  change ((((((x 4 || x 3) && (x 7 || x 0)) || (x 1 && x 4)) || ((x 2 || x 1) && (x 7 || x 5))) || (((x 4 || x 2) || x 0) && x 6)) || (x 5 && x 7)) = f x
  unfold f
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

def EF : ℕ := (((((((((((((rawP0.getD 0 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 5 0 &&& rawP0.getD 7 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP0.getD v.val 0).testBit b) = rawP0.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len0]
  · intro i h1 h2
    have : i < rawP0.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨out, hout⟩
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hu : UniqueNot gates) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length 1 S0 := by
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD o 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) o
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD o false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hu hnot ⟨o, hout⟩

def rootPreparedWords : List W := [
  ⟨0x1ffffdffffdf000000000000000000000000000000000000000000000000000000000000000000000000000004894c04e000005c00000b80004e0002700000000000180000000180000c000000000000c000060000000018000600000060000000000000000000ffe00ffe00fbf0007c003f00043e0001f8003e0010fc0008fc0010f80043f0004213f00043e0023e00203e00b56b6ab7fffeaaffffd55fffab7fffdbfffe0000000000000000000000000000000000000000000000000000000000000000026863f8391937ac7, 0x80000000100000000200000100000080000000000000004210000108421080000002100420000000000000000004210000000000084200000000000000210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x40000000004210840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x40000000004210840000000080000000100000000200000100000080000000000000004210000108421080000002100420000000000000000004210000000000084200000000000000210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 3⟩,
  ⟨0x1ffffc0000007fffeffff7fffef7fffb8000000000000000000000000000000000000000000000000000000016ad68009e000013c00002600009e0004f00125ab42857c0024a217c004be00000000000bc0005e0000000178005e0000058000000000000000000fc1c0801c0020fe043f820fe07a1fc1c078001e00003c00003c0080780200f0020000f00201e0101c00201c0b56b60000000000000000000000000000000dad5b56affffdb55affffb7fffe00000000000000000000000000000000000000a4cfbb63b53967a1, 0x4000000008000000010000000000004000000000000000000000100000004000002008000084210000000000000000042108400000010842108420000210000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x2000000000000002108421000000000000000000000000000000000000000108421080000000000000000000000000000000000000000421080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000000000002108421004000000008000000010000000000004000000108421080000000100000004000002008000084210000000421080000042108400000010842108420000210000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 3⟩,
  ⟨0x1ffffc00000000000000000000000000000001ffffc000000000000000000007fffe07fff07fff07000000004064043804808700908e46404632023000002000808700084808c24047800080146408632043000414810c2043c49223c000000000000000004046d54460001230048800a30800c440091802442827a600042c2008508010708484597004b7804eb83804600006030000002000000400023000018000000103000000000542000037fffe040c01a3000018000010a1a00003ffff6dbffffb1b26c7ec74e930, 0x1000000000000000004000000000000000000000000401080000000000000084210840000000000000000000021080000000000000000000842108420084000000000001000000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x80000000000000000000000000000000000000000000084210842000000000000000000000000000000000000084210842108000000000042108421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x80000000000001000000000000000004000000000000084210842000401080000000000000084210840000000084210842108021080000042108421000000842108420084000000000001000000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 3⟩,
  ⟨0x7fffeffff000000000003ffff7fffbdffffdc0000000000000000000000000000000000000001200015219e000033800005800019c000ce01b52a60006380000006380031c012a58930433c0219e0000000670019c0000160000000000000000008203060030830f1863c6108180110301847c311f1ec23f0e80380080700200e0110200e0120180a030102030b0000ab7fffe000000000000000000000000dad5b0000000000000000000000d5ad6dab7fffdbfffe0000000000000000000084bd5419e9fb170e, 0x4000002000000000000000000400000000800008000000200000000000000000000008000000200000108401000000000000000000000000000000084210840000001080000842000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x100000000000000000000084210840000000000000000000000000000000000000004210842000000000000000000000000000000000000004210800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000004000002000000084210840000400000000800008000000200000000000004210842008000000200000108401000000000000000004210800000000084210840000001080000842000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 3⟩,
  ⟨0x7fffe00007fffef000003ffff00003c000001ffffbc000007fffef7b000000000000000000001024011015141402a482a077000152800a94185a00ac0524836a005250029281a802da002a28015141ad000549015240921dc000000000000000002080206002224f01000024d817800001247080001e10102052265e000000c4937bd880030080180801808802816008800000a00000155fff800000000000c2d0056000001b5000000000000d4016d800000000000d68000000000006dbfff7c284fed028b254b, 0x10000008000000010002000000000000040000020000000800100021004000840000000000000000000000004000800108420084200840008421084010802000421084200800100421000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x400000000000000000000000000108421084000000000000000000000000000000000000108421084210840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000010000008000000010002108421084000040000020000000800100021004000840108421084210840000000004000800108420084200840008421084010802000421084200800100421000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 3⟩,
  ⟨0x7fffe07fff800000000000000000000000000007fffe0787fffef000007fff700000020200006068000c0d22022a50060c10307800810204180d308b0181860c0d0000208500c0c10607884484181e06068c308a80000000000000000082180061808120c048321d8c023a9800826020984040382040d04081a1094ba03c054ba78000006bd3802180103000000000000001100002800001bfffe00c18102000018458000030000010210c2800001bfffec62c2ffff80000618000289adfbe3e7ad990, 0x40000020000000040000000080000002000000000000002000000000010042000001000000040000000000010002008000000210800100401004200000008021004000002008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x1000000000000000000000000000000000000000108421000000000000000000000000000000000000000000421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000040000020000000040000000080000002108421000000002000000000010042000001000000040000421000010002008000000210800100401004200000008021004000002008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 3⟩,
  ⟨0x3ffff7fff80000001ffffbdfffef000000000000000000000000000000000140019815003700001400001b0000d80900008500370000000360001b01ab50000003300019812912006e001b8000050000000000000000004110c1810c408886122188606208c0d14673299cc02120c063279e664f79081c0081081c091060110e09110c04000a000000aaffffc00000000000000000d800056affffc00000000000000d5ac00000000000000d6adaffffbffff00000051ff4ca4c6a68795, 0x200000100000000200000000020000000000000400000010000108400000000000000400000010000000021080000842000421000000042100021000000002108000004000000108000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x8000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x8000000200000100000000200002000020000000000000400000010000108400000000000000400000010000000021080000842000421000000042100021000000002108000004000000108000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 3⟩,
  ⟨0x1ffff81fffe07fffef007fffef7fff700000000000000000001f110006e28006c52003f0001e000000810006e12094007e0003e081024052003f0001e1a05b000d800370d801b00000000000000000104a0018a010245009140215010432081148045208088c044ab600556c00a6d2780066d2786dd380000004a00008000000008800001400002b7fffc000000204040800001b05affff800000c181602b7fffc00000d02d80000000006c00003a33cd08dd25e728, 0x800000400000000800000001000000000000001000000040008020080200802000020000000800000000000200040100401084010802008020080210040100401080010040000400080010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x20000000000000000000000000000000000210842000000000000000000000000000000000000000000002108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000800000400000000800000001000210842000001000000040008020080200802000020000000802108000000200040100401084010802008020080210040100401080010040000400080010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 3⟩]
def rootPreparedMask : ℕ := 0x1ffffdffffdf7fffeffff7fffef7fffbbffff7fffbdffffddffffbdfffef7fffef7b7fffef7fff77fff777ffd6ad6d56ffffd55ffffaabfff56ffffb7fffdb5ab6ad5ffffb6ab5ffff6ffffdab5adb56ffffb7fffdad5b5ffff7fffedb7ffe0000000000000000ffffeffffefbffff7fffbffff7bfffddffffbfffdeffffeeffffdeffff7bffff7bdbffff7bfffbbfffbbbffeb56b6ab7fffeaaffffd55fffab7fffdbfffedad5b56affffdb55affffb7fffed5ad6dab7fffdbfffed6adaffffbffff6dbfffffffffffffffffff
def rootPreparedSlots : ℕ := 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
def rootPreparedBudget : ℕ := 0x62d6cd6f7b6739ce737bdf37be737bdf36c6318c5b18c6738c6339cdf37bdef8c6318c6318c6319ce739be739ce739ce739c6318c6318c6739ce739ce739ce739ce739ce739ce739ce739c6319cdef7ce718ce337be2f7be718ce6f9b6318c6717be738bdf19bdaf5b5af6b56b6adab5adad6ada95a5ad69ce738ca52

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedWords_eq : avl (PZ rootBounds) (mz 0) (rawL []) = rootPreparedWords :=
  Eq.refl rootPreparedWords
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedMask_eq : mz 0 = rootPreparedMask := Eq.refl rootPreparedMask
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedSlots_eq : pL (rootBounds.map fun _ => 16) = rootPreparedSlots := Eq.refl rootPreparedSlots
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedBudget_eq : pL (rootBounds.map fun e => 16 + (14 - e.2)) = rootPreparedBudget :=
  Eq.refl rootPreparedBudget
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedL_eq : lz 0 = I.AA := Eq.refl I.AA
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allRootInputsNeeded (d : Bool) :
    allInputsNeeded I.NN d I.AA rootPreparedWords 0 = true := by
  cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma searchInputs_atRoot (t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    searchInputs [] rootBounds 0 14 t H ph test =
      guardStart t H ph (test I.NN I.AA I.HX I.HY I.AA rootPreparedMask
        rootPreparedSlots rootPreparedBudget 0) rootPreparedWords := by
  simp only [searchInputs, frc_eq, st_eq, rootPreparedWords_eq, rootPreparedMask_eq,
    rootPreparedSlots_eq, rootPreparedBudget_eq, rootPreparedL_eq]
  change anySubC I.NN (pos t) I.AA rootPreparedWords 0 _ = _
  rw [anySub_allInputs (allRootInputsNeeded (pos t))]
  rfl






lemma pair_distribute {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pair f a c = true → ∃ b, pair (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,bR]
  cases hb : f w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · simp only [hb,Bool.cond_false]
    intro hor
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hor
    refine ⟨b, ?_⟩
    rw [hb]
    simp
  · intro _
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hb
    exact ⟨b,by rw [hb]; rfl⟩



noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootStart_eq (H : ℕ) (kind : Bool) :
    startPairPicked I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots rootPreparedBudget
      14 1 0 H 0 rootPreparedWords kind =
    initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) := by
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 8 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  simp only [startPairPicked, child, st_eq, topPairPicked, bR, haveRequired, len, budget,
    show Nat.ble 8 (Nat.sub 15 1) = true from rfl, show Nat.ble 8 1 = false from rfl,
    Bool.cond_true, Bool.cond_false]
  change (bif initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) then true else false) = _
  cases initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialBinary_of_check (H : ℕ) (kind : Bool)
    (h : chkPairPicked [] rootBounds 0 14 1 H 0 kind = true) :
    initialBinary H kind
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = true := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_atRoot] at h
  simp only [guardStart, rootStart_eq, bR] at h
  cases hp : relevantStart 1 H 0 rootPreparedWords
  · simp [hp] at h
  · simpa [hp] using h

def wordEquals (a b : W) : Bool :=
  (a.s == b.s) && (a.a == b.a) && (a.b == b.b) && (a.c == b.c) && (a.r == b.r)

lemma wordEquals_spec {a b : W} (h : wordEquals a b = true) : a = b := by
  cases a
  cases b
  simp [wordEquals, Bool.and_eq_true] at h ⊢
  rcases h with ⟨⟨⟨⟨hs, ha⟩, hb⟩, hc⟩, hr⟩
  exact ⟨hs, ha, hb, hc, hr⟩

def frontierMissing (states : List (ℕ × List W)) (z : ℕ) (v : List W) : Bool :=
  !(states.any fun state => (z == state.1) && List.isEqv v state.2 wordEquals)

noncomputable def rootWithGate (i j mask : ℕ) (kind : Bool) : List W :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD i zero
  let b := rootPreparedWords.getD j zero
  let keep := (rootPreparedWords.zipIdx.filter fun e => mask.testBit e.2).map Prod.fst
  addS (opW kind a b) keep

lemma frontierMissing_false {states : List (ℕ × List W)} {z : ℕ} {v : List W}
    (h : frontierMissing states z v = false) : (z, v) ∈ states := by
  simp only [frontierMissing, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨j, w⟩, membership, rfl, he⟩ := h
  have hw : v = w := by
    clear membership
    induction v generalizing w with
    | nil => cases w <;> simp_all [List.isEqv]
    | cons a v ih =>
      cases w with
      | nil => simp [List.isEqv] at he
      | cons b w =>
        simp only [List.isEqv, Bool.and_eq_true] at he
        rw [wordEquals_spec he.1, ih w he.2]
  rwa [hw]

lemma initialBinary_from_frontier (H : ℕ) (kind : Bool) (states : List (ℕ × List W))
    (complete : initialBinary H kind (frontierMissing states) = false)
    (checked : ∀ state ∈ states,
      look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false) :
    chkPairPicked [] rootBounds 0 14 1 H 0 kind = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  have original := initialBinary_of_check H kind h
  unfold initialBinary at original complete
  obtain ⟨_, hit⟩ := nodePicked_distribute
    (branches := fun _ => frontierMissing states)
    I.NN true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind
    (fun z v hit => by
      refine ⟨0, ?_⟩
      cases hm : frontierMissing states z v
      · exact Bool.noConfusion ((checked (z,v) (frontierMissing_false hm)).symm.trans hit)
      · exact hm)
    original
  exact Bool.noConfusion (complete.symm.trans hit)

abbrev SearchState := ℕ × List W

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f true I.AA rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 12 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1 z v))

lemma pureAt_of_covered (e : ℕ) (state : SearchState) (remaining : SearchState → Bool)
    (miss : ℕ → List W → Bool)
    (complete : pureAt e state miss = false)
    (covered : ∀ z v, miss z v = false → remaining (z,v) = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => miss)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : miss z v
        · exact Bool.noConfusion ((covered z v missed).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (14 : ℕ) = Nat.succ 13 from rfl, look1C_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureSecond state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def firstStates : List SearchState := [
  ⟨0x5a95c52d6adad6b5ad4a52d49d6f5ad6f2a5ad6b5294b5ef4b5af7acef5ad6b4a5294a4e73ad6b4a5294952d6b5a94a52969ce73ad6b5ad294a4e73ace739ceb59ce739ce739ce75ad6949ce74a4a52a5273a4e9294e5295273b5a969d6b5adab4a5ad5a52b69ca7194a72946328d2739d2949d253952948425284631, rootWithGate 0 1 255 false⟩,
  ⟨0x5675c52d6ad6b5ad6b39ceb3a5af5ad6f3adad6b52b5b5ef5b5af7b52f5ad6b39ce739d294ad6b4ad6b59d6d6b5a95ad6b6a5294ad6b5ace739d294ad294a52b5a5294a5294a5295ad694a5295ace73ad694ad2b39d2739d694b5a969d6b5adab4a5ad5a52b69ce929ce939ca53952739d2949d253952948c65284631, rootWithGate 0 1 255 true⟩,
  ⟨0x56b5c52d69d6b5ad6f5ad6f4a5ef5ad6f3b5ad6b4eb6b5ef5b5af7aceb39ce75ad2b4a5294ad6b5ad6b5956b5ad6b5b56b69ce739ce739d694a5294ace739ce73a5295a5294a5295a52b5a5295ace72adab5b52d4a52949da94b5a959d695a56b49dab4a4e95a4e929ce74a4e74952739ce949ce538d2738ca5284630, rootWithGate 0 2 255 true⟩,
  ⟨0x5ab4c52d6ad6d6b5ab5ad6f59dad4a52f2b52d6b5296a5ef4a5af7ad6b5ad6b5ad6b5ace73a5294a529495a96b5a94a5294ad6b5ad6b5ad6b5ace73a56b5ad6b59ce739ceb5ad6b39d6949ce74a4a52a5273a4ed4a5694a5ab5a52548ce739d2b4a5ad5a52b69ca7194a72a4e749ca318ca949d2539529484a1284631, rootWithGate 0 3 255 false⟩,
  ⟨0x56b3c52d6ad6b5ad6d5ad6f59d6b39cef3b56d6b52b6adef5adaf7b56d5ad6b5ad6b5ace739ce75a56b59dab6b5ab4ad2b5ad6b5ad6b5ad6b5ace739d6b5ad6b59ce74a52b5ad6b4a56b59ce75ace73ad694ad2d4a5694a5ab5ad67595294a56b4a5ad5a52b6a4a929ce93a4e749ce5294e949d253952948ca3284631, rootWithGate 0 3 255 true⟩,
  ⟨0x56b5c52d4ad6b5ad6f5ad6d5a5ef5ad2f3b5ad6ad2b6b5ed4a52b5b56f5ad695ad6b5ad293ad295ad6b49dad6b56b5b5294ad6b4ad695a56b5ad273a56b4ad2b4a4e75ad6b5a5694ad2b5a5275a4e53a5ab5ad6d49d693a56b4b5a769d2b4ad6b3a56d49d295a4e929ca94a4e739d273952949525294e938ca5284611, rootWithGate 0 5 255 true⟩,
  ⟨0x5ab5bd2d6adab6b5af3ad6f59deb5ad6d2b5a96b5296b5ef4b52f7ad6f3ad6b39ceb5ace73ad6b4a529495ad4b5a94b52949d6b59ce75ace73ace73ace73ad6739ce75ad6739d6b5ace949ce74a4a52a52b5b569294e94a5ab5a52549d6b5ada7295293a52b69ca7194a7494e749ca739d2528ca539529484a5084631, rootWithGate 0 6 255 false⟩,
  ⟨0x56b5b52d6ad6b5ad6f4ad6f5a5ed5ad6b3b5ab6b52b6b5ef5b56f7b56f4ad6b4a52b5ad294ad6b5ad2b59dad5b5ab5b5695a56b5a5295ad294ad294ad294ad694a5295ad694a56b5ad2b5a5294a4e73ad6b5b56b39d294a5ab5ad6759d6b5ada939d6b4a52b6a4e729ce949ce749ce739d27394e53952948ca5184631, rootWithGate 0 6 255 true⟩,
  ⟨0x56b5c5296ad6b5ad6f5ad2f5a5ef5a56f3b5ad5b5294a56b5b5af6b56f5ad2b5a5695a5274a5695ad6959dad6ada94a56b6ad695ad2b4ad2b4a4e93a5695a56959d274ad2b4ad2b4a56b4a4e95aca73a5ab4b56d3a5674a5695b5696956b4a5a94a56b59ceb5a4e9294e94a4e549d2729d2939d23394e748ca5284231, rootWithGate 0 7 255 true⟩,
  ⟨0x5e75c52d69def7bdeb39ceb3adaf5ad6f4adad6b4ed5b5ef6b5af7aceb39ce739ce739d6b5ad6b5b5ad69d2b5ad6b6adad69ce739ce739ce739d6b5ace739ce73ad6b49ce739ce75a52b5ad6b6b5293b5694aceb39ce7395673b5a959d695a56b49dab4a4e95a52b3a52939ca538d2739ce949ce538d2739465284630, rootWithGate 1 2 255 true⟩,
  ⟨0x5e94c52d6ad6f7bdeb4a52d4a56d4a52f4a52d6b52d4a5ef6a5af7bceb5ad6b4a5294a5294a5294a5ad6a5296b5a94a52d49ce73ad6b5ad294a5294a4e739ceb59ce739ce739ce739d6949ce76b5294b5273a4e9294e5295273a52548ce739d2b4a5ad5a52b69cab3a52b2946328ca318ca949d253952949421284631, rootWithGate 1 3 255 false⟩,
  ⟨0x5e73c52d6adaf7bdeb39ceb39d6b39cef4ad6d6b52d5adef6adaf7bd2d5ad6b39ce739ce739ce75adad6a56b6b5ab5a56d5a5294ad6b5ace739ce739d294a52b5a52939ce94a5294a56b5a5296b5294b5273a4eb39d2739d694ad67595294a56b4a5ad5a52b6a4eb3a52b29ca5394e5294e949d253952949463284631, rootWithGate 1 3 255 true⟩,
  ⟨0x5e75c52d4adef7bdab39ceb3adaf5ad2f4adad6ad2d5b5ed4a52b5bd2f5ad6939ce739d6b4ad295b5ad5a56d6b56b6ad294a5293ad695a4e739d694a5293a4eb4ad294a52949d274ad2b5ad696ad274ad694a52b3952729d293b5a769d2b4ad6b3a56d49d295a52b3a4eb39ca5295273952949525294e939465284611, rootWithGate 1 5 255 true⟩,
  ⟨0x5e95bd2d6adeb7bded3a52d4ad6b5ad6d4a5a96b52d4b5ef6b52f7bcef3ad6b39ce94a56b5ad6b4b52d6a52d4b5a96a5a949ce739ce75ace73a56b5ace739ce73ad6b39ce739ce75ace94ad6b4a5294b5273a4e9294e5295273a52549d6b5ada7295293a52b69d273a52b2946328ca739d2528ca53952949425084631, rootWithGate 1 6 255 false⟩,
  ⟨0x5e75b52d6aded7bdeb39ceb3adad5ad6b4adab6b52d5b5ef6b56f7bd2f4ad6b39ce739d6b5ad6b5b56d6a56d5b5ab6adab59d294a5295ace739d6b5ace73a5294ad6b4a52739d295ad2b5ad6b5ad294b5294ad29294e739d694ad6759d6b5ada939d6b4a52b6a5293a52b394a5394e739d27394e53952949465184631, rootWithGate 1 6 255 true⟩,
  ⟨0x5e75c5296adef7b5eb39ceb3adaf5a56f4adad5b5294a56b6b5af6bd2f5ad2b39ce739d695a5695b5ab6a56d6ada94a5ad6a5274ad2b4ace739d2b4a52749d295a5693a4e93a4e94a56b4ad2b6b4e94ad693ad2b29d2539d274b5696956b4a5a94a56b59ceb5a52b39d2b39ca33952729d2939d23394e749465284231, rootWithGate 1 7 255 true⟩,
  ⟨0x5eb3c52d69daf7bded5ad6f49d6b39cef4b56d6b4ed6adef6adaf7aceb39ce75ad2b4a4e739ce76adad69d695ad6d5ad6d59ce739ce739d694a4e739ce739ce73a52949ce94a52949d2d6a5296b5293b5694aced4a52949da94ad674952749d2b49dab4a4e95aceb3a5293a4e7494e5294a949ce538d27394a3284630, rootWithGate 2 3 255 true⟩,
  ⟨0x5eb5c52d49def7bdaf5ad6d4adef5ad2f4b5ad6aced6b5ed4a52b5aceb39ce75ad2b4a56b4ad296b5ad59d6b5ad2d6b52949ce739ce739d694a5694a4e739ce73ad295a52949d274a4ed6ad696ad273adab5ad2d49d2939d693b5a759d294a52b39d6b39ce74ad2b3a4e94a4e739527394e9494e528ce7294a5284610, rootWithGate 2 5 255 true⟩,
  ⟨0x5eb5b52d69ded7bdef4ad6f4aded5ad6b4b5ab6b4ed6b5ef6b56f7aceb39ce74a4eb4a56b5ad6b6b56d69d6b4ad6d6b5ab59ce739ce739d273a56b5ace739ce73ad6b5a52739d295a4ed6ad6b5ad293b56b5b52b39ce949da94ad6749d695a569395693a4e95ad293a52949ce7494e739ce7394a538d27394a5184630, rootWithGate 2 6 255 true⟩,
  ⟨0x5eb5c52969def7b5ef5ad2f4adef5a56f4b5ad5b4e94a56b6b5af6aceb39ce75a52949d695a5696b5ab69d6b5a5694a5ad69ce739ce739d2939d2b4a4e739ce73a5694a4e93a4e949d2d5ad2b6b4e93adab4b52d3a52749d674b5695956949d6949d6949ca94ad2b39d294a4e54952729ce939ce338ce5394a5284230, rootWithGate 2 7 255 true⟩,
  ⟨0x5eb3c52d4adaf7bdad5ad6d59d6b39cef4b56d6ad2d6aded4a52b5bd6d5ad695ad6b5ace739ce76adad5a5ab6b56d5ad294ad6b4ad695a56b5ace739d6b4ad2b4a4e74a52b5a5693a52d6a5276ad274ad694a52d49d693a56b4ad65594e93a52b3a56d49d295aceb3a4eb3a4e739ce528ce949525294e9394a3284611, rootWithGate 3 5 255 true⟩,
  ⟨0x5eb4bd2d6ad6b7bdeb3ad6f5a5ab4a52d4b5296b52d6a5ef6a52f7bd6b3ad6b39ceb5ad294a5296a52d6a5a94b5ad4a52949d6b59ce75ace73ad294a4e73ad6739ce739ce739d6b39ced69ce74a5294b5273a4e9294e94a5ab5a52548ce739d27295293a52b6aca73a52b294e749ca318ca528ca539529494a1084631, rootWithGate 3 6 255 false⟩,
  ⟨0x5eb3b52d6adad7bded4ad6f59d6b39ceb4b56b6b52d6adef6ad6f7bd6d4ad6b4a52b5ace739ce76ad6d6a5ab5b5ad5ad6b4a56b5a5295ad294ace739d294ad694a5294a5294a56b4a52d6a5295ad294b5294ad2b39d294a5ab5a525495294a56939d6b4a52b6ace93a52b39ce749ca5294e7394e539529494a3184631, rootWithGate 3 6 255 true⟩,
  ⟨0x5eb3c5296adaf7b5ed5ad2f59d6b39cef4b56d5b5294a56b6adaf6bd6d5ad2b5a5695a4e739ce76adab6a5ab6ada94a56d5ad695ad2b4ad2b4a4e739d695a56959d273a4eb4ad2b39d6d5a4e96b4e94ad693ad2d3a5674a5695ad2758d2939d694a56b59ceb5aceb39d2b3a4e549ce5194e939d23394e7494a3284231, rootWithGate 3 7 255 true⟩,
  ⟨0x5eb5b4ed6aded7bdef4ad6f5aded5ad6d3ad6b5aced6b5ef6b56f7bd6f4ad6b4a52b5ad6b5ad6b5ad6b59d6b5ad6d6b5ab5a56b5a5295ad294ad6b5ad294ad694ad6b5ad694a56b5ad2d6ad6b5ad294b56b5b56b39d294a5ab5ad6759d6b5ada939d6b4a52b6ad293a52b49ce749ce739d27394e539529494a5184631, rootWithGate 4 6 239 true⟩,
  ⟨0x5eb5b52d4aded7bdaf4ad6d5aded5ad2b4b5ab6ad2d6b5ed4a52b5bd6f4ad694a52b5ad6b4ad296b56d5a5ad5b56d6b5294a56b4a5275a5294ad694a5293ad293ad295ad6949d694aced6ad695a5274ad6b5ad6b395293a56b4ad6559d2b4ad6929d2b39d295ad293a4eb49ce739ce73952738ce5294e9394a5184611, rootWithGate 5 6 255 true⟩,
  ⟨0x5eb5c5294adef7b5af5ad2d5adef5a52f4b5ad5ad294a56b4a52b5bd6f5ad295a5695a5694a5276b5ab5a5ad6ad694a5294ad694ad294a52b4a52939d694a5294a5274ad2b4a5293a52d5ad296ace74a5ab4ad6d39d673a5294b5676952b3a5693a52b494e94ad2b39ceb4a4e539d272952939523294a7394a5284211, rootWithGate 5 7 255 true⟩,
  ⟨0x5eb5b5296aded7b5ef4ad2f5aded5a56b4b5ab5b5294a56b6b56f6bd6f4ad2b49d295a5695a5696b56b6a5ad5ada94a5ab5a5695a4e94ace93a52b4a5274a5674a5694ad293a52b4a52d5ad2b5ace94ad6b4b56b29d274a5695ad275956b4a5a739d2949ceb5ad2939d2b49ce549ce729d27294e3394e7494a5184231, rootWithGate 6 7 255 true⟩]

def firstCount : ℕ := 28

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def flatGate (code : ℕ) : W × ℕ :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD (code % 8) zero
  let b := rootPreparedWords.getD ((code >>> 3) % 8) zero
  let gate := opW (code.testBit 6) a b
  (gate, gate.c + (a.c ||| b.c))

noncomputable def flatDecode (depth code : ℕ) : SearchState :=
  let raw := (rootPreparedWords.zipIdx.filter fun e => code.testBit e.2).map Prod.fst
  let gates := (List.range depth).map fun i => flatGate (code >>> (8 + 7 * i))
  (rootPreparedBudget - sumc raw - (gates.foldr (fun e n => e.2 + n) 0),
    gates.foldr (fun e v => addS e.1 v) raw)

def secondCount : ℕ := 317

def secondCodes : List ℕ := [0xd523fed48fff323f7cc8ffe323f78c8ffd323f74c8ffb323f6cc8ffa323ffc48fef123ff848fee123ff448ffb123fe848fea123fff08fffa23ffa88ffe823bfd88ffe623fd988ffd623ffd08ffe423ff508ffb423fc448fc, 0xfb43ffad0ffe943bfdd0ffe743fd9d0ffd743ffd50fbe543ef550fbb543efcd0ffe343fd8d0ffd343fecd0ff3343ffc50ffa1c3fa870ffa1a3fe858fffd23ffec8ffeb23ffa48eff723ff9c8ff6723ff5c8fff523ff948ff, 0xe763ff5d8f7d763ffd58ffe563ff558ffb563ffcd8ffe363fd8d8ffd363fecd8ffa363ffc58fef163ff858ffd163fb458ff31fbfcc7dff31d7fcc74ef31ebfcc72ff31abfcc79ff31c7fd898ff31a7fcc51ff3163dbf50ff, 0x61a7fd859ff6067fd851ff61c2fbf68fffba37fae8dfe9a3bfde8ffe7a3fd9e8ffd7a37fd68ffe5a3fed68fff3a3ff8e8ff63a3fece8ff33a3fe8e8fff1a3ff868fee1a3fff58fffb63ffad8ffe963bfdd8f7f763ff9d8f7, 0xb3e3fccf8ffa3e3fff70bffdc3ffef0ffebc2ffaf0ffe9c2bfa70eff7c3ff9f0bfe7c3ff5f0fff5c3ff970ffd5c3fed70fff3c3ff8f0ffd3c3fecf0ff33c3fe8f0fff1c3fd87dff61effd86bff61ebfd86aff616bfd879ff, 0x33cbfcceaff3367d7f51fffb47ffad1ffe947bfdd1ffe747fd9d1ffd747ffd51fbe547efcd1ffe347f78d1ffd347fecd1fffde1ffef87febe3ffa78eff7e1ff9f8ff67e3ff5f8ffe5e3ff578ffb5e3ff8f8ff63e3ff4f8ff, 0x67a7ffd69ffe5a7ff569dfb5a7ff4f9ffd3c7f74f1fffd67ffed9ffeb67ffa59eff767dfdd9ffe767df9d9ffd767ffd59ffe567ff559ffb567ded59fff367f7cd9ffe367ff4d9fdd367fff19fffa67ffa99ffe867bccfaff, 0xd7e7ffd797fe5e7ff579ffb5e7fff71bffdc7ffef1ffebc7ffa71eff7c7ff9f1ffd7c7ffd71ffe5c6ff971ffd5c7fed71fff3c7fd8fdff63effd8ebff63ebfd8eaff636bfd8f1bdfda7ffee9dfeba77fa69eff7a7ff9e9ff, 0xd7ebfff72fffbcbffaf2ffe9cabfa72eff7cbff9f2ffd7cbfff6afffbab7faeadfe9abbfdeaffe7abfd9eaffe5abeff5afffb6bffadaffe96bbfddaffe76bdf9daffd76bffd5afbd56beff797febe7ffa79efe7e7fd9f9ff, 0x3f7d7ffdd7fff74effbd3bfaf4effbedffafbffe9efbff73bffdcfffef3ffebceffaf3ffe9cfbfdf3ff67f7fd9f3b7fdafffeebdfe9afbfdebffe7afdf9ebfffde9ffefa7febebffa7aefe7ebfd9faff]

noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := secondCodes.getD (i / 32) 0
  flatDecode 2 ((block >>> (22 * (i % 32))) % 4194304)


def successorCodes (row : ℕ) : List ℕ :=
  (List.range (row % 64)).map fun i => (row >>> (6 + 16 * i)) % 65536

set_option maxRecDepth 100000 in
def secondSuccessorsList : List ℕ := [
  0x34031e02cc02b8025c023401ea01ac0176012800c800a80060000d,
  0x300a5a0a0809f409980970092608e808b20864080407e4079a0750070006f40698064e060805fc05bc0564050004ca04a40450040603fc03980360001e,
  0x1c10060ff20fa00f440f1c0ed20e940e700e220dc20da20d7a0d200ce60cb80c680c120bea0bb40b500b3a0af00abc03980359,
  0x2a1354130212ee12ac125e123c11ca11ae1174110810f610a6104d,
  0xa19b21960190e18f218b0184c180a17c41782174c173c16dc16bc1668160e15d415a61556151614fc1498147c140e13e813a610700a8603dc,
  0x141ebc1e6a1e181dfa1d941d4a1d0c1cd61c881c481c321bd81b9e1b601b0a1ae01aa21a6c1a0819ce13e813ba0ad00418,
  0x2e21ac217c210820d820b8206420221fd21fba1f521f121ecc,
  0x1c272826d226b22640262025ec2590255c252824e024aa245c243a23dc2388236c230622f4229e2274223621d21eec1a0819fc14340b500b0a04a4045e,
  0x142b7c2b1a2ac82aba2a442a3829fa29b62956293628c8288e2860281027f82790277621e21a7c1498146a0ba4050004d8,
  0x22f2a2ed82e862e682e022df62db82d562d082ce02c902c462c1e2bce2b90277422121f201a9614f610bc0556,
  0x2a311430c230ae306c301e2ffc2f842f78279e227a1f4a1ad20bcd,
  0x235ea35983546352a34e834843442343833c433b43354333632f432aa3260320631e8319e31442f4e2b9027f422921fa01b1615280c0805fc059d,
  0x12397a392838d638b83852380837d437863764370636f036a036563628319e315e2be0280622e21fe6154810f80c58064e0619,
  0x283b263af63a823a523a3239c2398e285e1b5415b411260c8c,
  0x2c3eb83e623e103dfc3da03d783d303cfa3ca03c6c3c0c3bec3b983b4239a03656360631d02c462c0828ac23181b8e15ee11600cc006f4069c,
  0x24412a40d84094404a400c3fe63f883f663f083ed83b7036aa326032202c88236420321be8160a11ba0d1a07500717,
  0x2843924340432c42d042aa4268422041fc418e41483eec3bb239c636f632f432b628dc23b820481c3c16620d6407a80058,
  0x845b0455e450c44ee4488447c440e43ce41663f0c3bd23a243714333c2f96293a23d8209c16bc11c20d8407c80097,
  0x2847924740472046ec46904668462045ce43c83f603c6c3c063774335e2fc82cf6295c24081c7c16de12220de4082800d8,
  0x84970490e48fa48b6486c482e47fc41a63fba3c823a54378433ac30162d2a244820d61c8c172c12700e3208760117,
  0x2c4ad64ab04a544a2e49ec49ae47e045e041cc3ff03cf63ab833f82d7a29a024bc210c1cc4178217540e6808ac0157,
  0x144b604b2c483c440a400837f62db829ca1d120ea608ea018c,
  0x284d344cde4c804c4c4c384bdc4ba04b2e49ec49b648684608446a4268421440783d123804344234022dc42a1c252824d41d4c180a17dc0ef0093401de,
  0x164df24da04d5c4b944a10466e449042a03d663af8386a34e834a82e3a2a50256c217a1db218b018440f18095c0217,
  0x384ea24e504e204d784bf04a7a48a046ec468c44ec42d840bc3d963886352e30462e482aa025ec25981dce18ee12a00f7409b8025a,
  0xc4ed04e324d804c4c4c0e48c0471e4500432a40d03de838d8354230982e9a2af22640262a1e20190212f20f8809cc0298,
  0x2e4f224e564dde4c944b564ab049124770455243623e283b3a392a359430ea2efc2b1226ae21bc1e72195413060fda0a1e02d9,
  0x2e4f0c4ef84ea84d344cec4ac84968478845a843a4412c3eb83e52394235ea31022f142b5c272826d41e8a19aa135c10300a74031a]

def secondSuccessors (i : ℕ) : List ℕ :=
  successorCodes (secondSuccessorsList.getD i 0)


def thirdCount : ℕ := 1894

def thirdCodes : List ℕ := [0xfbe843ff4f423bf9fa11ffafd08fffbc847ff4e422bfa7211dfef908ffe7c847febe423ffeea11bfd7508dfe9a8477fbd423ff9ea11ffcb508fbe968477f3b423dfd5a11f7aad08fbfc2247e7d1123f3a8891f9d0448ecf62247e731123f198891f9ac448fcf42247e721123f350891f968448fc, 0x674247feba123ffd5091f7ca848fbd54247ddaa123efcd091fbe6848ffe34247ef1a123ff4d091fba6848ffb34247ed9a123ffc5091fd43848fea1a247f50b123fbf7d10fff7a08effbec43ff5f623ffa7b11dffb988bfebcc45ff4e623bd9f3116ffb588fffbac46ff4d623bf9eb11effbd087f, 0xb36247ed9b123fe8d891ffe2c48fee16247f68b123fbf5091fdf6848feeb4247f74a123bbdd091fdce848fe674247f6ba123fbd5091f5ca848fad54247d5aa123ebcd091f9e6848fee34247e71a123fb4d091f9a6848feb34247e59a123fbf5091fff6848ffeb4247ff4a123bfdd091ffce848ff, 0xf5a247ff2d123fed6891ffe7448fdf3a247ff1d123f78e891ff67448fdb3a247fd1d123ffc6891fdc3448fefd6247ffdb123ffad891ffd2c48eff76247bfbb123ff9d891efcec48ffd76247bebb123ffd5891ffcac48ffd56247fdab123ffcd891fbe6c48ffe36247ef1b123ff4d891fba6c48ff, 0xfdc247ffde123ffaf0917fd7848ffe9c2457f4e123bfdf091ffcf848bfe7c247febe123ffd7091ffcb848ffd5c247fdae123ffcf091fbe7848ffe3c247ef1e123ff4f091fba7848ffb3c247ed9e123fe8f091ffe3848fefda247ffdd1237fae891bfd3448eff7a247ff3d123fd9e891ffaf448df, 0xe3e247ef1f123ff4f891fba7c48ffb3e247ed9f123fe8f891fffb848befdc247f7de123fbaf0917dd7848fee9c245774e123bbdf091fdcf848bee7c247f6be123fbd7091fdcb848fed5c247f5ae123fbcf091f9e7848fee3c247e71e123fb4f091f9a7848feb3c247e59e123fa8f091fdfb848bf, 0xe34647ee9a323f6cd191fbfbc487efbe243f75f123fba7891ddefc487ee7e247f33f123fb5f891fdcbc48fed5e247f5af123fb8f891f9c7c48fed3e247e69f123facf891f967c48fea3e247f7ef121ffef890ffd7c48ffe9e2477fbf121ff9f891fecfc48ffd7e247ff2f123ff57891ff6bc48ff, 0xf76647ef3b323d79d991fbaecc8fdf56647ef2b323f755991fb6acc8f5b56647efdb323ffad991ffd2cc8eff76647bfbb323ff9d991efcecc8ffd76647feab323fed5991ef6acc8fff36647ef1b323f74d991fbf68c8ffeb4647ff4a323bfdd191ffce8c8ffd74647ffaa323ef95191f7e68c8fd, 0xf7c647ff3e323ff5f191ffcb8c8bfd5c647fdae323ffcf191fbfb4c8fdfba646ef5d32377a6991dbef4c8fde7a647eb3d323f7d6991fbcb4c8fdd5a646edad323f7ee991bfd74c8dfe9a6477fbd323ff9e991ffab4c8dfb5a647fe9f323f74f191fbfacc8fdfb6647ef5b323f7a5991dbeecc8f5, 0xe9e6476f3f323f59f991fbafcc8fdf5e643ef2f323f757991fb6bcc8fdfde643ff5f323ffa7991dfcfcc8ffd7e647ffaf321ff57991ff6bcc8fffdc645efee323f7ef191fbd78c8fde9c6476fbe323f79f191fbaf8c8fdf5c647ef2e322f797191fbab8c8fdb5c647efee322ffef191ffd38c8ef, 0xfbea43ff5f523ffa7a91dfcfd48ffd7ea47ffde523ffaf291ffd3948afe9ca477fbe523ff9f291ffaf948fffdaa47ffdd5237faea91bfd3548eff7aa47ff3d523fd9ea91ffcb548fbfd6a47ffdb523ffada91ffd2d48eff76a47ff3b523df9da91ffaed48fff56a47deab523eff7990fbd7cc8fd, 0xf342c7ff1a163fd8d0b1ffa6858ffb342c7ff8a163fa870b1fd43458fefdf643ffeeb23fff7491dff7a48efebd2477fdf721ffafb91ffd3dc8effdce45ffee723ffef391ffd79c8bfebce47ff4e723bfdf391fecfec8ff67ce45bfed723ffeeb91bfd35c8eff7ae47ff3d723df9eb91fffbd487f, 0xf14387f7ea1a3ffed0d1bfd6868dfe943477fba1a3ff9d0d1fece868ffd74346ffaa1a3ef950d1f76a868fbf34347ff1a1a3fd8d0d1ff66868ff334347fd0e1a3fbf50b1fff6858ffeb42c7ff4a163bfdd0b1efee858ffe742c7bf3a163ff5d0b1efae858fff542c7df2a163ef550b1f76a858fb, 0xe74385f73a1c3fb5d0e1fdea870fae54387d6aa1c3ead50e1f5e6870fee34387f69a1c3facd0e1fc66870fefd4385ffea1c3ffed0e1ffd6870bfeb4387ff4a1c2bfa50e1dfee870ffe74385ff3a1c3ff5d0e1ffea870fbe54387deaa1c3eed50e1f7e6870ffe34387fe9a1c3fecd0e1fe66870ff, 0xd36687ee9b343ffe99a1ffd0cd0ef33ea87d99e543ecceaa1f666cd0f5fde283ffdf141ffaf8a1ffd3c50eff7e283ff3f143fd9f8a1ffafc50ffe5e287deaf143eed78a1f7c7c50ff63e287fe9f143fecf8a1fe67c50fffd4385f7ea1c3fbed0e1fdd6870beeb4387f74a1c2bba50e1ddee870fe, 0x63aa87db1b543ed8f1a17bfb4d0fffba686ff5d3437fa69a1dfef4d0ffe7a687ffad343ef969a1f7ab4d0dbb5a687de9f343ff4f1a1fbfacd0fffb6687ff5b343ffa59a1dfeecd0f7f76687ff3b343df9d9a1ffaecd0fff56687df2b343ef559a1f76acd0f3b56687df9b343f7cd9a1ffc6cd0ff, 0xfd6a87dfdb543efadaa1f7d2d50ebf76a87df3b543cf9daa1f7aed50fbfde683ff5f343ffa79a1dfcfcd0ffd7e687ffaf341ef979a1f7abcd0fbb5e687dfee342ffef1a1ffd38d0eff7c687ff3e343ff5f1a1ffeb8d0fbe5c685df2e343ef571a1f76b8d0fb63f687fb1f743fd8eba1fec7d50fb, 0xe9ce877fbe743fd9fda1fecf9d0b7fdae87ffdd7437fa6ba1dfef5d0ffe7ae87bf3d743fff7aa0f7f7d507bebea87df4f543af9faa1f6cfd50fbd7ea87dfee543efef2a1f7d7950fbe9ca855f4e543afdf2a1f7cf950fbd7ca87dfed543efeeaa1b7d7550dbe9aa875fbd543ef9eaa1f6cf550fb, 0x31f68ff98eb47fcc74a3de63d51fb31ca8fd98e347f4c71a3fe634d1ff31fac7b18fb63d8c75b1ec63d58f631cac7b18d563d8c79b1ec638d8f66262c7b18d363d8c51b1edfbed07ffdd687ffee943bfef4a1dfd7a50effbee83ff5f743ffa7ba1dffb9d0bffdce87ffde743ffaf3a17fd79d0ff, 0x31fb57f98fbab7cc75d5be63a6aef31cb57d98fde5fcc75f3fe63a79ef31ebcbf98e5e7fcc6af3fe63f71bf31fb8ff98fbc7fcc74e3de63d71ff31cb8df98e5c7fcc6ae3fe63cf1ff62638de98fda7fcc7dd3be63ae9df31d34f798f5a7fcc72d3fe63569df31a7cff98d3c7f4c69e3fe63f51ff, 0xe3a2c7f31d163face8b1fd47458fefda2c7ffdd1637fae8b1bfd3458eff7a2c7bf3d163df5e8b1afaf458dff5a2c7ff2d163ffce8b1ffc7458ff63a2c7fd1d163ffc68b1fdc3458fe31fbebf98fdd3bcc7de9de63a58e631fbd3f98fbe9fcc75f5fe63a7aef31fb97f98fbcbfcc74e55e63a72ef, 0xf7c2c7bfbe163ff9f0b16fcf858f7e7c2c5ff3e163ff5f0b1efaf858fff5c2c7ff2e163ff570b1ff6b858fff3c2c7ff1e163ff4f0b1ff67858ffa3c2c7ff8e163fbf68b1fdf7458deeba2c6f74d163bbde8b1edef458fee7a2c7b73d163fb5e8b1adaf458def5a2c7f72d163fad68b1fde7458fe, 0xe7e2c7f6bf163db5f8b1fdcbc58fed5e2c7f5af163fb8f8b1fcc7c58fed3e2c7f59f163fa8f8b1fdfbc587ffbe2c3ff5f163ffa78b1dfefc5877f7e2c3ff3f163df5f8b1efcbc58ffd5e2c7ff1f163fd8f8b1ffa7c58ffa3e2c7ffee162fff70b1fff7858ffebc2c5ff5e163ffa70b15fd3858ef, 0xe566c7feab363fed59b1efe6cd8fdf366c7ff1b363ff4d9b1fba6cd8fffd46c7ffda363ffad1b1ffd28d8eff746c7bfba363ff9d1b1efce8d8ffd746c7beba363ffd51b1f7ca8d8fbf346c7ff1a363f78d1b1ffa68d8ffb346c7ffef161fbef8b0fdd7c58fee9e2c777bf161dbdf8b0fdcfc58f6, 0xb5c6c7ff9e363fd8fdb1fec7dd8f763eec7fb1d763dd8fab1fec7558ff636ac7fb1e362f7f69b1fff74d8dfeba6c6ff4d363bfde9b1efef4d8ffe7a6c7bf3d363ffd69b1ffcb4d8ffd5a6c6fdad363ff4f9b1ffa78d8fdd3c6c7ffeb363ffad9b1ffd2cd8eff766c7bf3b363df5d9b1efeacd8ff, 0xe96ac77fbb563df9dab1efaed58f7f56ac7deab563eff79b0ffd7cd8ffe9e6c77f3f363df9f9b1ffafcd8f7d7e6c7ffaf361ff979b1ffabcd8ffb5e6c7ffee362fff71b1fff78d8ffebc6c7ff4e363bfdf1b1efef8d8ffe7c6c7bf3e363ff5f1b1efaf8d8fff5c6c7ff2e362ff971b1ffab8d8ff, 0xf7aec7bf3d763dff7ab0fff7d587febeac7ff4f563bf9fab1efcfd58ffd7eac7bebf563fff72b1fff7958ffebcac7ff4e562bfa72b1dfef958f7f7cac7ff3e563df9f2b1ffaf958f7d7cac7ffed563ffeeab1bfd7558dfe9aac77fbd563dfdeab1ffcf558f7e7aac7ff2d563eff5ab1ffd6d58ff, 0xb3c347f99e1a3fe8f0d1ffe3868fefdf6c3ffeeb63fff74b1dff7a58efebd2c77fdf761dfafbb1efd3dd8e7fbeec3ff5f763ffa7bb1dffb9d8b7fdcec7bfde763dfaf3b16fd79d8f7e9cec73fee762fff73b1ffd79d8bfe9cec77fbe763dff6bb1eff75d8d7e9aec73fed763ffeebb1bfd35d8ef, 0xebc344f75e1a37ba70d15dd3868eef7c347f73e1a2fb9f0d1fdaf868def5c347f72e1a3fad70d1fde7868fee3c347f59e1a3f8cf0d1fd47868fefdc345ffee1a3ffef0d1bfd78689febc346ff4e1a2bfa70d1dfef868ffe7c345ff3e1a3ff5f0d1bfeb868ffe5c347fdae1a3ffcf0d1ffc7868ff, 0xea6746ff433a3bccfad1fe67968ff336747afea3a3ffed1d1bfd68e8dfe947477fba3a3ff9d1d1fece8e8ffd74746ffaa3a3ef951d1f7e68e8ffe34747ef1a3a3fecd1d1fffbc687ffbe342ff5f1a37fa78d1dfefc687fd7e346ff2f1a3ff8f8d1fec7c68ffa3e347ffee1a2fbf70d1fdf7868de, 0xfbc746ff5e3a37fa71d1dfef8e8ffe7c747febe3a37fd71d1ffcb8e8bfe5c747fdae3a3ffcf1d1fec7ee8df63ef47fb1d7a37d8fad1fec6d68ff63c745efeb3a3ffed9d1bfd6ce8dfe967477fbb3a3df9d9d1efaece8dff56747ff2b3a3fed59d1efe6ce8fdf36747ff1b3a3fff19d1fff4ce8df, 0xfbeb42ff5f5a37fa7ad1dfcfd68ff67eb47febf5a37ff72d1fff7968dfebcb46ff4e5a2bfa72d1dfef968ffe7cb47febe5a37ff5ad1fff6d68dfeb6b46ff4b5a3bf9dad1efaed68dff56b47dfef3a1ffaf9d1bfd3ce8efe7e747fb3f3a3ff5f9d1bfebce87fe5e747fdaf3a3fff71d17ffb8e8ff, 0x61ef85f30d7c2f987ae17cc3570be616b85f30f3c2f9869e17cc2cf0be606785f30a3c2fbf7dd0bffbae8dffdd3477fde9a33faf4d19ff7de85febef46ff4f7a3bff73d17ffb9e8fffbcf46ff5e7a27faf3d1bfd39e8ef67f746fb3e7a2dff6bd1bfd35e8cff7af46ff3d7a35f9ebd1bffbd687f, 0xe5e387feaf1c3fed78e1ffc7c70ffd3e387fd9f1c3fccf8e1ff47c70ff61f7dbfb0fbaf7d87df4fec35faff61f756fb0f7abfd87ab5f6c355afb61afcffb0f5e5fd87dd3bec3de9ff61ab4efb0f767dd86ab3fec2d59f761e6cfeb0d367f5819b3eac3ed1ff61ee8ffb0d747fd87aa3f6c3ef0be, 0x33cb87f99d5c3fccd9e1ebfa8f0bffd4787ffda3c3ffad1e17fd68f0ffe947857f4a3c3bfdd1e1ffce8f0bfe74787feba3c3ffd51e1f7ca8f0fbf34787ff1a3c3f78d1e1ffa68f0ffb34787ffef1c0fff78e0fff7c707febe385ff5f1c3ffa78e15fd3c70eff7e383ff3f1c2ff9f8e1ffafc70ff, 0xd3e787fe9e3c3f7f59e17ffacf0fffb6787ff5b3c2ffad9e1ffd2cf0afe967877fbb3c3dfdd9e1ffcecf0b7e76787bf3b3c2ff9d9e1ffaecf0fff56787ff2b3c3ff559e1ff6acf0f7b56787ff9b3c3f7cd9e1ffc6cf0ffd36787ee9b3c3fff19e17ff4cf0ffea6785ff433c2bfa19e1de67d70ff, 0xe7e785ff3f3c3ff5f9e1ffebcf07fe5e787feaf3c3fed79e1fffb8f0bffbc787ff5e3c2ffa71e15fef8f0ffe7c785febe3c3ffd71e1ffcb8f0bfd5c787fdae3c3fff69e17ffb4f0fffba786ff5d3c27fae9e1bfd34f0afe9a7877fbd3c3ff9e9e17fcf4f0fff5a787ff2d3c3ff569e1bf6b4f0ff, 0xfdab85ffed5c3ffeeae1bfd75709febab86ff4d5c2bfa6ae1dfef570ffe7ab85ff3d5c3ff96ae1f7fad70bffd6b87ffdb5c3ffadae17fd6d70ffe96b857f4b5c3bfddae1ffced70b7e76b87bf3b5c2ff9dae1ffaed70fff56b87deab5c3eff79e07ffbcf07febe785ff5f3c3ffa79e15fd3cf0ef, 0xf7cf85ffee7c2ffef3e1ffd79f0bfe9cf857fbe7c3fff6be17ffb5f0fffbaf86ff4d7c2bfa6be1dfef5f0ffe7af85bf3d7c3df9ebe17ffbd703ffdeb83ffdf5c1ffafae17fd7d70ffe9eb857f4f5c3bf9fae17fcfd70ffd7eb87ffee5c2ffef2e1ffd7970bfe9cb857fbe5c3ff9f2e17faf970ff, 0xfa67c3ff533e3ffa19f1de67978ff33abc7f99b3e3d7f51f0fff68f87feb47c7ff4a3e3bfdd1f0ffce8f8ff6747c7feba3e3ff951f1f7c68f8fde347c7fe9a3e3fecd1f1fffbef03ffdf783ffeebc2ffef4e15ffba70affbd3877f5e9c2bfefbe0ffd7df0bfebef87ff4f7c2bfa7be1dff79f0bf, 0x63f7c3fb1f7e1fd8ebf1fec7578ff636bc7fb1e3e2f7f69f0fff74f85feba7c6ff4d3e3bfde9f0ffcf4f8ff67a7c7ff2d3e3ff569f1bf6b4f8ffd3c7c7ee9e3e3fff59f0fff6cf87feb67c7ff4b3e3bfdd9f0efeecf87fe767c7bf2b3e3ff559f1ff6acf8f7e367c7fe9b3e3f74d9f1fff8cf87f, 0xe9cbc57f4e5e3bfdf2f0ffcf978ffd7cbc7ffed5e1ffeeaf0bfd7578dfe9abc77fbd5e1ff9eaf1fecf578ffe5abc7dfeb5e1ffedaf0ffd6d78ffe96bc77fbb5e1ff9daf1efaad78fbfdc7c1ffee3e1ffef1f0ffd78f8ffe9c7c77fbe3e1ff9f1f1ffaf8f8ffe5c7c5ff2e3e3ff571f1ff6b8f8ff, 0xf7668fbf3b347df9d9a3ffaecd1fff5668fdf2b347efcd9a3fbc6cd1fdd3668fefeebe1fff74f0dff7a786febd3c77f5f7e1ffa7bf0dffb9f83ffdcfc3ffde7e1ffaf3f17fd79f8ffe9cfc77fbe7e1fd9fdf0fecf9f8b7fdafc3ffdd7e17fa6bf1dfef5f87fe7afc7bfee5e1ffef2f0ffd7978ff, 0xfdc68defee347f7ef1a3fbd78d1fde9c68f6fbe347f79f1a3fbaf8d1fdf5c68fcf2e346e7971a3f3fb8d1bffbc68fff4e347bfdf1a3ffcf8d1ffd7c68fffae347ef971a377cb8d1fbf3c68fefdd3477fae9a3bfd34d1eff7a68fff3d347ffd69a3f7cb4d1fbd3c68fefdb347ffad9a3ffd2cd1ef, 0xe9ce8f7fbe747fd9fda3fecf9d1b7fdae8fffdd7477fa6ba3dfef5d1ffe7ae8fbf3d747fff7aa2f7f7d517bebea8fdf4f547af9faa3f6cfd51fbd7ea8fdfee547efef2a3f7d7951fbe9ca8d5f4e547afdf2a3f7cf951fbd7ca8fdfef345ffaf9a3ffd3cd1efe7e68ffebf347ffd79a2f7cbcd1fb, 0xfdf4cbffde867bfa19b3cbf8cfa7ffa67d3ff433ebbfe99e5ffd0cf2afe867977fd33ab7fa99d5bfd0ceaef33cb57dfe3367d7e99b3ebd4cd9f533eacfa99e567d4ceab3ebfbed17ffdd68fffee947bfef4a3dfd7a51effbee8bff5f747ffa7ba3dffb9d1bffdce8fffde747ffaf3a37fd79d1ff, 0xe7c6cffebe367ff971b37fab8d9ffb5c6cfbdae367ffcf1b3fbfb4d9fdfba6ceef5d36777a69b3dbef4d9f5f7a6cfef3d367d79e9b3fbeb4d9fde5a6cfeead36776d69b3eb6b4d9fdfba6ceff5d3677fa69b3dfef4d9f7f7a6cfff3d367df9e9b3ffab4d9dfb5a6cfbdad367ff4f9b3fba78d9fd, 0xe96acf7fbb567df9dab3efaed59f7f56acfdeab567eff79b2fbd7cd9fde9e6cf6f3f367d79f9b3fbafcd9fdf5e6cbef2f367f7579b3fb6bcd9f5b5e6cfefef365ffaf9b3ffd3cd9efe7e6cfbf3f367ff5f9b3ffebcd97fd5e6cffdaf367dff71b37ff78d9ffe9c6cf7fbe367dfdf1b3ffcf8d9f7, 0xfbeacbff5f567ffa7ab3dfcfd59f7e7eacffebf567ffef2b3ffd7959ffe9cacd7f4e567bfdf2b3efef959ffe7cacfbf3e567ff5f2b3fffb559fffbaaceff5d5677fa6ab3dfef559f7f7aacfff3d567df9eab3ffcb559fbfd6acfbfdb567dfadab3efd2d59e7f56acf9eab567cff5ab3ffd6d59ff, 0xf7a78fff2d3c6ff569e3bfa7cf1fdfdf6cbffeeb67fff74b3dff7a59efebd2cf7fdf765dfafbb3efd3dd9e7fbeecbff5f767ffa7bb3dffb9d9b7fdcecfbfde767dfaf3b36fd79d9f7e9cecf3fee766fff73b3ffd79d9bfe9cecf7fbe767dff6bb3fff75d9dfe9aecf7fbd767df9ebb3effbd597f, 0x67ab4eff2d5a76ff5ad3fff6d69dfeb6b4eff4b5a7bfddad3ffced69f7e76b4fffab5a7ef55ad3b7fb4f97feba7ceff4d3e7bf9e9f3ffeb4f97fd5a7cefdad3e7fff69e37bfb4f1fdfba78eef5d3c777a69e3dbef4f1fde7a78fefad3c7f7969e37bcb4f1fdd5a78eedad3c7f7f69e37ff74f1df, 0xfdf74affeeba77ff74d3dff7a69cfebd34e7fdf7a57fafbd3bfd3de9effdcf4dffee7a7ffef3d3bfd79e99febcf4eff4e7a7bfdf3d3fecfee9df67cf4dbfef5a5ffefad2bfd7d69dfe9eb4f7f3f5a7ffef2d3bfd7969dfe9cb4d7f4e5a7bfdf2d3ffcf969fffdab4eff4d5a73fdead3bfcf569df, 0xf7ab8fff3d5c7ff96ae377cb571fbfd6b8dffdb5c7ffa5ae3dfeed71ffe76b8fbf3b5c7ff5dae3ffead71fbd56b8fdfef3c4ff5f9e3ffebcf17fe5e78dfb1fbedfd8fdd7bec7efa7f63afd7fb1fbab7d8fbd5fec7edaff63ead7db1d56bed8fde37ac7df1bd63af8deb1f5c6f58eae37ac6d71bd, 0xebef8fff4f7c7bff73e37ff79f1ffebcf8dffbe7c7fff6be37ffb5f1fffbaf8eff4d7c7bfdebe3ffcf5f1f7fdeb89ffef5c5ffefae2ffd3d71efe7eb8ffebf5c7ffef2e37fef971bfd7cb8dffee5c6ffef2e3ffd7971bfe9cb8d7fbe5c7ff9f2e37faf971fffdab8dffdd5c77faeae3bfd3571ef, 0xe7afcfbf3d7e7ffafaf2ffd3d796fe7ebcbfb3f5e5ff5faf2fffb9797febcbcfff4e5e6bfa72f3dfcf979ffd7cbcfffed5e5ffaeaf3bfd3579efe7abcfff2d5e7eff5af2ffd6d79ffe96bcf7f3b5e7df9daf3ffaed79fff56bcbdeab5e7eff7de27ffbef17ffdd78dffee9c6bfef4e3dff7df17f, 0xebced5ff4e76bbfdf3b5effb5dafffbaed6ff4d76bbf9ebb5effbd5a7bfbead3df5f56befa7ab5d7cfd5af3e7ead7debf56beff6ab5f7f755adbebaad6df4d56bafdeab5f7cf55af3e7aad7dfeebe5fff74f2dfd7a79effdcfc9ffee7e5ffaf3f37fd79f9ffe9cfcf7b3e7e6dff6bf2ffd35f9ef, 0xfdcf55ffee7abffef3d5bfd79ea9febcf56ff4e7abbfdf3d5fecfeeadf67cf55bfee5abefef2d5b7d796adbe9cb555f4e5abafdf2d5f7cf96afbfdf6d3ffeeb6bfff74b5dff7a5aefebd2d77fdf769ffafbb5ffd3ddaeffdced5bfee76bdfef3b5efd79dab7ebced7bf4e76b9ff73b57ffb9daff, 0xfbafd2ff4d7ebbf9ebf5efcf5fafffdf793ffde9cabff74e55ff7a72efebd3957fdf7c9ffafbe5ffd3df2afe9ef977fee7caffef3e5ffd79f2bfe9cf957fbe7cbfff6be5fff75f2dfe9af957f4d7cbbfdebe5ffcf5f2f7fdf752ffeebab7ff74d5dff7a6acfebd3567fdf7a97fafbd5bfd3deaef, 0xfdd39d7fde9cfbfaf4e75ff7df37febef9dff4f7cfbd9fde76ffbeeb5ffdd35f7fde9af3fefbd6bfd3debeffdcf5dbfee7afdfef3d7afd39ebe7fdcf5dffde7af7fdf3d7effbafa7ffdd3d37fde9e9bfaf4f5dffb9fa3ffdcfd3ffde7e9ffaf3f57fd79faffe9cfd77b3fbe9fd9f3f56ffb5fa7f, 0x3f7de8dff7a7b6febd3df7fefbccfff7de6fffbaf3bf]

noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdCodes.getD (i / 32) 0
  flatDecode 3 ((block >>> (29 * (i % 32))) % 536870912)


set_option maxRecDepth 100000 in
def thirdSuccessorsList : List ℕ := [
  0x602ee029c024a022c01c601ba017c010800f800980078000c,
  0x1203d003a2037203380005,
  0x160544053004d404ac0472043203180048,
  0x3606c606920674060e05c605b204380088,
  0x2c081607e0079c07540722034800c7,
  0x12093a08d608940854070605bc0107,
  0x6097a0142,
  0xe0a2409de09860954085c074e05ec04500386018a,
  0x3a0ad80a860a74061404ac01c6,
  0x80b060a5e099608a007860692067004d203ca020a,
  0x180aa409c4051c0244,
  0x140b480b3a0afa08d607f606d6056e0288,
  0x140b4e0a12092c080602c5,
  0x3c1166111410c210a4107c10320ff40f920f440f220ec40ea60e5c0e0c0dc20da40d5a0d140cca0cb00c560c020bf60b98,
  0x22164c163815e6158a1562151814da14b61468140813e8138c1342133012e6128a1240123811ee1194,
  0x2a1cd41c821c6e1c141bd21bac1b6a1b241ae21aac1a5e1a3c19de1994194a193818ee18921848180217f617b6175e170416ee16b60b9b,
  0x3421de218c2178211c20f420aa206c20361fe81fa81f5e1f141ec41eb81e4c1e021dc21da81d4e1d2e16820bd6,
  0x3c280a27f227942760270226ce26b0267c260a25c2258c257c251c24fc24b22468241823ce23b02366232022d62296227c220e1d0416d60c1c,
  0x222e2e2dd82db82d462d262cf22c962c622c2e2be62bb02b622b022ae22a982a4e2a3c29f22996294c290628fa28ba2858,
  0x34329e327a322831dc31a4315a311c30d830b6305830322fe82f8c2f422f3a2ef02eb02e7c22281d5e17300c56,
  0x1a370436e0368e3642360a35c03582357c351c34fc3498344e343033e633a03356331632d2,
  0xc3a3839e6398a3962391a38f638a8384c383037ca37b8375632f02e7a285622421db61752,
  0xc3db83d663d0c3cca3ca43c623c1a3bf43b983b563b0c3af03a8a3a78375633302eba289622821df617ae118a0c97,
  0x2c411640c440b0405640143fee3fac3f643f2e3ee03e803e623e203de0337a2ec628e022cc1e0217f811d40cd6,
  0x1c434a433642da42b24246422641dc4182414a3a4a37a633822f0c292623081800121a0d12,
  0x3c462645d445824564453c44f244804470441043f043b033cc2f5629702352184a12640d52,
  0xe4884485e480247da47924742472c46ce4684464241703ab037ce34282fb2298e23b81e6e18a612820d95,
  0x184be44b8e4b7a4b284acc4aa44a5c4a2649cc49984976491848d834722ffc29d823c41eb818f012cc0dd5,
  0x64dcc4db84d744d2c4cc84c884c684c04465c418c3acc380e2a2824141eca1902131c0e12,
  0x10505650044fc04fb44f764f124ef24e924e724e182a72245e1f14194c13660e50,
  0xa52f252a0524e523051cc518a5142511e50ee50b24e284c1848ce46b043a641e23e203dd83b563b3c349830222abc24a81f5e19a813840eb8001d,
  0x2854d25480546c541053e8539e536e532e50924e484c76492c46d043c642003e743b9c34f630422adc24fc19c813e20ed80059,
  0x3256a05642560e55f0558a5542552e53324e8c49984942473044203ea8387c351830a22b3c25281f9e1a2814040f380098,
  0x28581257ee579c5758571056de50d24ec84ca649c0446e3ef638b02b4c25761fec1a7614520f4800d4,
  0xe59b65952593458d0588e585056c2550251364f2c4cdc4a1247643f1a3bda38c2355c30e62b8225ac20241ae21a9a14b40fbc011a,
  0x345a0259de53744f724480359a312a205814f20ffa014b,
  0xa5bd65b805b605b2c5ada5abc5a4259d0588e5858570a5568538c518a51404fb44d244a5a47bc44f2426e3fac3f643c623c22390a35e431622c2e2bfc260a25f420ac1b6a1b22153c100601a6,
  0x365c945c425c3c5a7458f0559053f051cc4a8247e4451a429640143fcc3cca3c8a3942361c31962c70265c20d41bd21b8a1564106c01db,
  0x1a5d445d305cc25c1a5a92591c5742560e55ec540e52044ff84d684ade4802457642f040663d26398e366831e62cf22c8226ce26b8212e1c261582108a021f,
  0x2c5db05cd45c605b2c5aee57a0564054605256500c4dba4b14458a430440b83d7839e036ba32382d462d142760270c21421c7815d410dc025c,
  0x105dc45d365c805b745a36595257f2569254b2528e4b44486645dc435640cc3d8c3a0436de32582db2279e21941c8c1626112e029a,
  0x105dec5d9a5d4a5bd65b8e59a8582854ca52d050464dd84be44b8e48bc462c411a373432a22e2e2dfc280a27f421ea1ce2167c114602db,
  0x166340632c62da6280627c621861d66190614e612a60dc60ba605c60345fda5fa05f725f225eca5eae5e5a5e360b97,
  0x20678a6776672466c866a06656661865f465a66566650064e464aa646c641663f8639a5e020bd3,
  0x286cf46c9e6c406c0c6bec6bb86b5c6b286af46aac6a4a6a3a69da69ba6954693868d26882686a682867f863ae5e560c18,
  0xe71da71847164713070d2709e7042700e6fda6f926f6e6f206ec06ea06e786e1e6df66da66d506d14,
  0x2075ca75a67554750874d074867448741673f473967354731a72ec729c7246722867ca5eb00c53,
  0x20777a770c76fc769c7650760672106d2a681663ca,
  0xe7c367be47b927b767b347ad07a8e7a467a2279d479b27956791478f678ac7852783477ea7790761c72666d42686c64225ef811ee11940cca0c9d,
  0x1e7f087ef47ea27e467e1e7df27da47d447d247cfc7cac7c7477ea77ac72b66d9268b25f0a124012240d5a0d16,
  0x3480f28084806080307fd27f8e7f5a72ea64605f4a,
  0x3883ae834a832c82c682bc825a820081cc81aa814c810e7f6c7c527814731e6df868e4649a5fb012e6128c0dc20d97,
  0x3085f685a48560851884c684a68446842683fc7cb678ac78786e14690064f45fcc134213260e5c0e14,
  0x887f0879e874c872e86ca86888640862683cc81127fa47cd6791478d673606e7a6966651c602813840e95,
  0x268990897c892a88ce88a6885c8806842a81707fc47d32795c767473806e9a69ba604813e20ed3,
  0x88bb08b5e8b008acc8aae8a488a0089e6844081cc81a47d5479bc769673e06efa69e6655c60a814040f15,
  0x268d508d2c8cda8c968c4c8c0e8bc6849a822080327da279cc76ee6f0a6a3465aa60f614520f53,
  0x388ee28ebc8e608e3a8df88d8e8bc089c0861884fc824480467a0874126f6c6a5865d0614e611a14b40f95,
  0x208f6c8f0c8c1c88067456661814f20fc8,
  0x34910290ea908c905890068fe88fac8f3a8df88d968c488a26884a868886608506829e7dd07a8e7a50748e6fda6fa86af46aa0665861d661a2153c101e,
  0x2291c091ac91688fa08e2e8a4e88ae86ec82f280867e367b347ac874c2701c6b086680627c620a15641055,
  0x692ae925c922c91468ffc8e5a8c808acc8aaa88cc8724854a83227e527b7a77147512709e706c6bb86b6466da62a615821099,
  0x1892dc9200918c9058902c8cde8b3c891e877685b47ea47ba67564713070c06c0c6bf6672c62f815d410d5,
  0x3a932e926291ea90a08f628e908d308b50897087ae837480c87ef67be0774a7584715e6c4a6740630c16261116,
  0x3a931892c692b4910290f88ee68d488ba6898887f085f8839e7f0e7c2075ce71da71a86cf46ca067966362167c1157,
  0xc95f495a2954e950094de94aa9450941693e89398934b,
  0x1c980697f297a09770972296ea96a096789618934a,
  0x2c9a969a449a3099ee99a09940990c98fa98b098789628938c,
  0x1c9ad693c2,
  0x89d149cfc9c989c569c3a9bc89ba69b729b1c9afa98b0986a96a09650940f,
  0x9e869e729e029de29d829d729b0c98ea9449,
  0x229fcc9fb89f669f289ec29d669b40991e9489,
  0x4a0eca0baa048a0289ee29dba9bc89ba0996296c094cb,
  0x22a1cca1a8a156a1029dd69c2e99b0970e9509,
  0x14a2bca250a216a13aa048a0269f329e189c7099e0974b,
  0x28a1789f469e449a3297a29546,
  0xaa2fca24ca1aca08c9fbc9c969a4697f49589,
  0xaa2d4a2a2a1c4a0e29fc09e889d149cec9a9c980c95cb,
  0xea6f6a6a4a652a636a5d0a588a546a510a4c2a4aca452a418a3daa382a366a31a5e2e1692,
  0x32ab5cab0aaaf6aa9caa5aaa34a9f2a9aca96aa934a8e6a8a6a852a836a7fca780a740a712,
  0x16b1a2b14cb12cb0f8b09ab066b00cafcaaf98af64af16aee2ae9cae5aae24add6adb4ad56ad02ace6ac80ac6eac2eabd6aba6a32e5e4416dc,
  0xeb536b4d4b482b476b434b3c0b3b6b370b310b2c2b288b25ab20ab1d6ab82a34a5e9e1712,
  0x32b99cb978b926b8dcb89ab864b822b7dcb79ab756b734b6d6b6a6b66cb600b5eeb5aeb552,
  0x3abde4bd92bd40bd24bce2bcbcbc7abc34bbf2bb90bb42bb1abacaba80ba58ba08b9eeb54ab1eeabc0a71aa39893761758,
  0x3ac192c140c124c0fcc0b4c07cc02ebfcebfb0bf64bf1abec0bea2be58be08b9eeb5aeac00a7625ec217f61796,
  0xcc574c522c4d0c4b4c472c40ec3ccc38ec340c31ec2c0c2aac25ac210c1e2be58be18ba00b5dab200ac6893b25f1218481819,
  0x22c762c720c6f2c6bac64cc62cc5fac5acb608b27ca798a3d693e05f4e,
  0x26cbb2cb5ccb0acaf6ca9cca5aca34c9f2c9acc96ac934c8dac8a6c846c826c7d2c7bac59ac210c1c0be8aba80ba66b642b2a6acb6a7d2a410941a5fb818ee18a0,
  0x1ece64ce12cdd0cd8ecd48cd06cce0cc82cc60cc02cbd2c7aac264bf1abedabac2acd2a82ca46a94745fd4194a1917,
  0x22d078d026cfcccfa4cf5ccf36cec8ce82cbe6c7ecc5c0c2b0bf56b696ad26a85c601e1992,
  0x2d2aad258d206d1ead1a8d144d102d0c8d088cea0cc06c80cc61ec2cebfb4b6d0b2f4ad5e94ba607c19d5,
  0x22d54cd538d4dad4a6d44cd40ad3e4d3a2d35cd31ad2c8d082cc5ac8a6c840c32ebfc2bb16b730b316ada6a882a48094dc609e1a1a,
  0x2d76ad708d6f4d6b2d670d62ad5e8d5b6cee0ccb4c8fac64ec37cc010bb64adf4a8d0a4ce952a60ec1a55,
  0x26d890d86ad810d7e8d7a8d59ad2dccf06cceac934c072bb9ab75aae2aa906a50e61221a92,
  0x28d952d92cd8ead5dcd308cd2cc972c6b4bbdcb7b6b35cae6ca948a55061641ad0,
  0x22daaeda78da32d9d8d9a8d7b0d622d342d0e4cf4ecd72c98cc3bcc0babc22b7d6aee2aeb2a99661aa1b15,
  0x24dc30dbdadbbadb48db34daf2d664d384d110cdb4c9cec3fcbc64b800b398af64af34a9d0a59861ec1b55,
  0x10dcecdc9adc58d990d7cad3e8d14ccf9aca20c6f2c424c0e2bc9ab874b3caaf9aaa3c62121b93,
  0x12ddaedd5cdd0cd42ad19cca62c734c464bcdcb8b6b40cafdcaa76a5c062541bd0,
  0x32de5cde0adddcdd1adc74daf2d9ecd8ead834d69ad4a6d446d1e6cfd2cdf6ca90c480c100bd26b8c2b45ab066b036aa92a610a21a62ae1c1c,
  0x6de8addeedd6cdcbadb48db38da08d6f8d4d8d238d024ce0acae2c4d2c152bd78b914b4acb0f8b08aaae4a662956c62c21c59,
  0x28dedcde12dd90dcdadb92d910d86ad70cd52ad25ccb22c774c524bd9cb976b4ccb11cab36a6b4958063141c96,
  0x28dec6deb2de64dc30dbe2daaeda68d966d882d762d542d2a2d05ece66cbb2cb4cc57ac1babdf2b98eb516b1a2b172ab4ea6cc95d6636a1cdc,
  0x20e3ece396e376e304e2e4e2b0e254e220e1ece1a4e16ee120e0e0e08ce070e038dfe2dfb8df60df26a338638e1d17,
  0x6e892e87ae81ce7e8e78ae756e738e6c6e692e64ae614e5c6e586e570e516e4dee488e45ee413,
  0x18eb02eadeea8cea40ea00e9fae98ce952e914e8e0df02a3681d4d,
  0x6eeaeee5cee0aedeced86ed7aed3cecdaec8cec64ec14ebcaeb92eb54e8dee438df40a71aa3821d94,
  0x2ef058f006eff2efb0ef62ef08eec8e462df9663ca,
  0x6f3aef35cf30af2eef288f27cf208f1f8f1baf16ef124f0caf088eed2eb5ee4b8dfc0a76c640c1e021dd5,
  0x2cf52af4faf486f476f406f3d2e93ca798a3ea644a,
  0x30f87cf826f7d4f782f764f73cf6f4f680f664f630f5f0f59cf546f3caf094ebcaeb8ce956e4f0e036a7d2a42464841eb81e59,
  0x28faaefa5cfa18f9cef990f96af90cf8ccf89cf56ef124f0e4ec30e50ce052a82ca44064de1f141ed4,
  0x2cfc56fc04fbf0fbaefb64fb02faccf8b0f5b6f43af146e560e0a6a86665281f50,
  0x2cfe56fe04fde4fdb0fd54fd2cfce4fc8cf8e4f630f5f8f1a2ef0cec7ae986e5a0e0e6a882a4a665681f95,
  0xd0034ffd2ff80ff7aff30fef2fe82faeaf900f646f448f1f0ef5aec94e5eee134a8d0a4f465b61fd4,
  0x310175011900f300b10072fea4fca4fb10f974f6baf4bcf23cecc0e9cae624e16ca96aa908a546a51865ec2016,
  0x1901e501b0fecef9baed16662a2047,
  0x2d0379032302c50291027d022501b300b1007aff2cfceefb58f9fcf6c8f246ed46e692e660e1ece1b4a9f2a990a5a066742099,
  0x1b043703e5039900d4fd24f72af4eef2aced80ea38e6d4e21caa5aaa36a5c8669c20d1,
  0x3d04e70495046503bd02350100ff64fdb0fd70fb9cfa02f74af2f2ef8aedccea4ae756e724e2b0e276aa92a62466f82118,
  0x110515047703c502910252ff84fdc4fbeefa54f79cf306efdcee1eea9ce7e8e7b6e304e2caaae4a676670c2156,
  0x330567049b042302d901f4ffd6fe16fc26f7ecf52ef358f02eee42eafae816e35cab36a68a675e2194,
  0x330551053d04ed03790331014d002cfe6cfc68fab0f87cf806f3aef046ee98eb06e892e860e3ece3b2ab4ea6e067b421d8,
  0x21081f07ef07b9074b072b06d706950645062d05c5058b,
  0x21091f08ef088d08450585,
  0x39096d05c2,
  0x210a8b0a6d0a2109df09b909450607,
  0x310b6f0b1b0adf09950645,
  0x30bdd0ba109d70684,
  0x330c450c2d0a2b06c4,
  0x270ce50c850c1b0acb0a4b0706,
  0x270d650d330c5d0b8d08790746,
  0xd0da50d030bef08af0785,
  0xd0de50caf0b210a9f08df07c6,
  0xd0dcd0da70d670cf10b6109210807,
  0x2112ad1257122711f311951161111510d1109d105510110fef0f910f610f390ee90e930e690e20df16aba867fc2217,
  0xf171b16c516a51671161315df1583154f151b14d314af1461143913e9139f1377132712e90e05059ee438df6eabfa28562259,
  0x37196d190f18fb18891847183717d7179d17530e6d05c8e462df906d2a680f,
  0xf1f5b1f051ee51eb11e531e1f1dc51d831d511d1d1ccf1c9b1c531c1d1bcf1bad1b511b0f1ac51ab91a5f1a0319f7199d176712e90e85061ee4b8dfeeac266d42684628fa28a022d622a5,
  0x1f236b231522f522832263222f21d3219f216b212d20df20bd205f200b1ff91f8319f719b713390ed50640ac766d926896294c29302366231c,
  0x7263b25dd258b2579250724cb24952479242523c723b91f9f1a29139f13610f16e4f0e026ac9e6df868fc29f2299823ce2399,
  0x31297d293728c528a52871282127ed27a52741272126c126a1264b1fc51ab91a7913d706b0e50ce042acf86e1469182a4e2a322468241b,
  0x352d032ceb2c8d2c592c392bc72ba92b772b052af52a832a792a1729e729a12647239f20111b0f1ad10f6b06c6e560e096ad206e7a69622abc249d,
  0x152fe12f8b2f6b2f372ed92ea52e492e152de12da72d67298126a523fd206d1b5717af0f8b0734ad406e9a69822adc24d8,
  0x3531ab314d313930e930b5307930272d6126f9241f208f1bb717e114110fc6e5a0e0d6ada06efa69e22b3c2516,
  0x15342133cb339b3367330932d532853251320931d729c12715246d20dd1bc7182f14790754e5eee124adee6f0a6a302b4c2559,
  0x393647362f35fd358b356d353b34c934b9344931f930392a25274b24931c131495102f078ae624e15cae5aae126f6c6a662b82259a,
  0x337b73759370736f536893491323530612d852ac32a6d278724eb211d1cdb1c5b14dd1052e66ce1a4af22ae9a6fb46aae2bca25da,
  0x2b382937fb34f9344532552df72b352aa127df21511d0f1c8f15111086e6a0e1d8af56aece6fe86ae22c3c2616,
  0x2f3941390d38ed38b9386937f536ad352930892e292b79251321851d831d43155510df07f8e6d4e20cafcaaf82701c6b162c70265a,
  0x73a3b39dd39b9384736cb355532b930e52e472bb1280b256f21df1dc9185f15a11116e730e266b01e70786b722c8e2698,
  0x2f3a6d38bd358932d92eb92be5286322131e3b189315d5114ae764e29ab05270ac6ba62cc226d3,
  0x193a9d398d38d93727330d31372ed92c05289d258322711e71163311a8e784e2f8b0b070cc6bc62d202715,
  0x1391b336b2f0d2c7728f522a51e8f18e5166711dce7f6e32cb0e471006c382d542751,
  0x3b3b093aef3a7b39ef396b3837376f35cb33ab314b2f6b2cbb25d522c51eed190516971221083ae816e34cb104715e6c582db2279a,
  0x93ad93a873a033787362133f531a12f832cfd2907262b231b1f1b16ed1252e86ce3a2b15a71b46cae2dca27d6,
  0x3b3b39365534152ff52d31295f234f1f77194f17211286e8a0e3d6b18e71e86ce22e3c2812,
  0x73e6f3e0d3df93dad3d753d2b3ced3cbb3c453c393bd33b833b690e14e8eeb54ab1d632f02e53,
  0x2f40193ff53fa33f533f313ef73e930e467209,
  0x7436f430d42f942af426d423741e94189416b413940dd409340773e833b690eaeb59c72603356333a2ef02e96,
  0x174641461d45cb45bd4547453b44f944994479441543cb439d409340533bb90ec0b5dab22c72b033e6338c2f422f17,
  0x2d47eb47ab4747472746f54692e92cb608b25a72ca,
  0x314afd4aa74a454a3149e549ad4965491548e1488148614835469543cb43b940c53c393be10f0ce966b642b2947318344e34322fe82f9b,
  0x2d4c974c734c214bd54b9f4b434b21482746f9442b41110f56b696737c34983010,
  0xd4eb54e534e014df34dbb4d714d034cc34b0148474719444941713eef0fb4b6d0b2f4739c34f63054,
  0x2d5097507350154fe14f954f5d4f154ec34cd548e148b944a941933f3b3c510ffae996b730b31673fc35183096,
  0x3151db51a55159512350d54ee5492b476d3c951000e9dcb79ab776b3487402355c30d1,
  0x19525552314d3b44eb3cc67440359a3108,
  0x2d543953e353b35341532d52e15295522350dd4f3b4d5f4b6d4947453741f53d11109d1064b822b7c0b390748a35e43158,
  0x3754a55461529951154f734d954ba549ab47bd456f426d422d3d5510c0ea1cb89ab876b434b3c874c2361c3196,
  0x3d5567550554e5546d52e551554fe14f814de14bf149cb45b942a33f793d951161110cea66b8c2b454750e366831d7,
  0x11558554f754b35341533350134e334c054a1d45cd42f53f8d3de711f3119eeab8b914b4a6756036ba3215,
  0x2755235399525b519750754e574c674a6d47c1462f43193fef3e171202eadcb976b4ca758436de3254,
  0x1155bd556d543953f151ed508d4ead4cb14afd4a974647436f40073e6112ad1258eb32b98eb52075da37343296,
  0x1d588b5877581d57f557b3576b570956f9569d5643561b55c33b6712d2eb48b9f83751,
  0x2d5a9b5a495a2b59c55999594b591358db55d33bb71318ba38960a378e,
  0x1f5d155cef5c935c6b5c235bc15ba55b715b155ad358c356393bdf134aeb80ba60967037d2,
  0x295ff55f9f5f4d5f395edd5eb55e6d5e0b5def5dbb5d453c291394ebcabaaa9690,
  0x17619d614b610760fd60ab604d60155add567913e4ec1abacc380d,
  0x2d63976345632562f16295626d622561cd602f5dbb5d655b715b0b593956bb3c61140cec42bb2296e83855,
  0xd6575651364c164bb6471643363eb604b5dc15b99594956ef144d085aec90bb7097363892,
  0x1f66c966a36647662165df65b363e561fd60ad5e235beb572d3c9314af08bcecf4bbf2bb9a38d3,
  0x767536731642b3cfaed05,
  0x1b692768d168b1687d682b67cf6793672165df65bb646d620760f55e6b5c0559b557b357753d0f151b14c6ed7cbc7abc223919,
  0x969e56993694f67876615625d5e935c6b59dd57ed3d43155f08eceda4bce2bc8a3951,
  0x2b6a956a436a13696b67e3664164a562f1628b61395eef5c895a3758393d9315df158aedc0bd2097663995,
  0x3d6ac36a2569b1687d681364c5631d614d5f1b5a4b584d3de51671161cee12bd7297b839d2,
  0x216b156a4969d16887674966b56517635f5f555ced5a9d58af3e0516a1092eee64bd8697cc3a13,
  0x216b3d6aeb6a9b692768df66cd656d639761a95ff55f9f5d073e4f171b16c6eebabddc9812,
  0x296c936c416c2b6bdd6bbb6b773e9d17790948eed0760b,
  0xd6db96d676d296cfb6b713ed7179c7648,
  0x2d6e7b6e096de96cdd6b933f3717e2ef3c7689,
  0x236f0d6ed76eab6bc71830ef4c76c7,
  0x3d6fad6f576ebb6e096de76d233f7b18891872efba770b,
  0x396d416c353f8f18c6efc5,
  0xb6ffd6f8d6eed6e4d6d936c593fed1918f020774a,
  0xb6fe36f296caf4037196ef046,
  0x2d72db7289726d722b71c771857157713970f770ad7053701b55d340771998be2a778a3a52,
  0xf763775e575937577753574d1748f7451740373e173857343731d408319df09a2be7477d2,
  0x1f7955792f78d57893786d782b77e37793777d772176df769576537003563940df1a0af080be9278303a95,
  0x177b9d7b4b7b097ac77abd7a597a1979fb7995766d705d56791a64f0dabeec784c3ad1,
  0x217e677e157dd37d917d497d237cc57ca37c477c057bc51aa109eef124bf367890,
  0x1b8071801f7fc57f9d7f557f2f7ec17e857bdf76837337708f1af0bf5478e03dd63b11,
  0x1d81c781b38161813180c380877c3b79a176c5737970eb41111b2d0a3af15679223e183b52,
  0x39842383d183bd8363832182fb82b98241820380817ea37c5979fd77217397713b6b49416d1b4b0a4ebfb279403e743b98,
  0x58671861385df85858543851d84db8493844182057c93774373dd6bb956a9418f1bb8f1aebfd479a03e95,
  0x39882387c187ad876b872986e186b180ef7ee37cd97a11742b6bc956dd1bc8f1fcc02279ee3ed3,
  0x1f8949892388c988a18861869384557f097d3d7a6377ab57131c3cf234c0467a243f1a3bd2,
  0x1b8aa78a718a2b89d189a1886986db84b9825d7f517d477aab77cf74457173574f1c9b1c7cc08e7a6c3f623c16,
  0x1d8c298bd38bb38b418b2d8aeb871d84fb82937d897aed7811748771b557b741d11d1d1cc8f2507aae3fa43c56,
  0x98ce58c938c5189898883852182c57f93787574eb71ed42031d64c0f47ad43fca3c91,
  0xb8da78d558d058563831578b7752d721d57ef42451da10aaef2b67b16400c3cd0,
  0x2b8e558e038dd58d138c6d8aeb89e388ed875385df85bd8361811f7fd57dcb7b2f78d37549726d6f77583942931e1f1dcaf2c0c1127b7040663d1d,
  0x3d8e838de78d658cb38b418b318a0187b1861183b3817180277e1d7b65759b72816c0b584d42e51eb11e5cf312c1647b8440b83d5a,
  0x218ed58e0b8d898cd38b89892387c5866383c78195793775ed72d36c5d58af43051eeef3767bd640cc3d95,
  0x218efd8eab8e5d8c298bdb8aa78a5f89798839841d81db80617e577b9f794f76296c87434f1f5b1f06f3bac18e7c2c4118,
  0x2f906590238fe38f8f8f658f13701358cb4390c1f09842414c,
  0x399347932f92dd928b926d920791c991ad9179911990f9909543f91f9ac23a98ac7c51,
  0x27952d94db94979469942993cb93a58f2d704b1feac24c98fc7c9c418e,
  0x2b9755970396ef9693966d962b95c19591954b93b990857343733970f770b9441f2000c2a47cf043a641d5,
  0xb98cf98b1984b980197d19791956993d990cf8f6173977119447d205b0adec2c099047d1043c64214,
  0x159a439a2399ef9993996b991197ad917991238f8373cb5939449f2080c32099647d704412,
  0xb9bb39b519b3d9af99a8195a9940991917419596d20cec36e99b27d80444f,
  0x179c239bc197fb44f24485,
  0x2b9df79da19d439d0f9cfb9c9f9c639bf99aab990b982d962b95d7944791d1748f7447718571455987451f216b210ec3ccc39e7dfc44f2425c,
  0x199eb59e639e1f9c5399719853966d92238ff7753574ed722b71eb59fd455321af0b34c472c4067e24451a4296,
  0x3b9f659f139ee39e3b9cbd9ae399ef998f98af969b948b9253754972495a0b45a3222f21d0c4b099e27e42457642d7,
  0xf9f939ef59e439d0f9cd19b039a0396ed94dd92a5759b729b5a5d45f522832262c4c49a347e94458a4315,
  0x319fe59f199ea19d579c339b559a55972f92e5903775ed72ed5a81461522f10b74c5169a487ee645dc4355,
  0x319fcf9fbb9f6b9df79d8b9b8b98eb976795399347932f904f7617465f236b230cc56c9a9e7f3c4614,
  0x11a14fa11fa0e9a0b9a05ba0354686f3fac59c9ace7f4b,
  0x3a22da1fda19ba02746f6f42cc5d27f88,
  0x21a29fa27da1b9a047470cc6307fc7,
  0x21a31fa2eda1e9a086f47ac6608007,
  0x7a35fa2dfa0eb477af4b2c6848047,
  0x7a39fa24fa12b47aaf4e2c720c6f28088,
  0x7a387a361a321a283a211a16d47ecf522c77480ca,
  0x3a4b5a451a425a3e58f1576555adcf552c7b29b04464b,
  0x7a6fba697a679a615a5d3a58ba567a537a4dba03990a176df76a1480723b0f5a6c7cc811848ce4694,
  0x25a8dba889a875a819a7f1a7aba777a737a4f9a05990cf8f7d7701486523c6c8269b6a8176492c46d4,
  0x7aabbaa5daa0ba9f9a987a94ba937a739913b5d715b2148b92430f5e6c8489b8c81984952,
  0x2fab6dab3daaeba765a3ed91638f93776f5da55b5548e4f61ac8ba9bc081cc49824711,
  0x25acf1ac9bac65ac21abd9aba7a511a429a089918b5dc15b952440f674c8d69c1a822649d2,
  0xbae57ae01addbadbdad59ad19abbdaacba90ba575a45fa0e377ad5e235be5490b24b4f6acc96ac93c825c4a124757,
  0x13af49af29aec7ae99ad21abc7a971a795a5d3a58791ed782b77f55e6b5c2d494724fcf6f4c9f2c98682a44a5a4797,
  0x1b01dafcbaf87aebdad6dab39a999a7f9a60fa12d92238fd57893785d5e935c6549b92524f71cca5aca2c82cc4a8247d8,
  0x17b08db04baf9bada5ac0ba9f5a817a64b926f78f95eef5cb149cb2542f776ca989c4a83284ade4814,
  0x29b0ddafe9aeddaa09a85d928d5f054a1d2594f78acafa4b0c,
  0xdb159b10db041b009af01addbac6fab7baa5ba8bba691a16f92e59015791f5f555ce74a7b25e6f7dccb3c9cae834e4b444859,
  0x19b129b0d7b093af57ae31ac87aa8793355fbd4a87263cf832cb549ce44b8f,
  0xdb14bae65ace5a8c7a6c3a4b9936f905f79695fdf5d314af0f866cb889d3883984bce4892,
  0x3db345b331b2efb2adb265b213b1d3b18b93877c057bfb79a1264cf882cbe683f24e284c12,
  0x1db4a3b451b40db3d3b393b1a993e37c5979c126a0cc029d4684124e484c4f,
  0x3db605b5e5b5b1b56db525b4d3b3a5a3c57c8d602126ccf8c2cc629da684724e90,
  0x23b751b70db6c3b685b653b1d1a42994237cd97a2b6041271d0baaf920cc829dc684924ec84c93,
  0x3b875b833b7f1b785b665b4e5b235a4497d3d7a7d60a527430bd0f948cd06ccd884f64f2c4cd3,
  0x25b883b68ef9b44f44,
  0x3db9cbb985b951b93db8e5b8b3b7f1b78db6edb50db3efb2adb25794537d917d497ac77a8760e127ed2798f9d0cd8ecd6085004fb44d1b,
  0xfba55ba3db8f5b811b725b5b1b551b431b2db94957dcb7b0b61252871281cfa12cdf29e2485444ff84d55,
  0x21ba95ba05b951b923b745b5e3b445b32d94e77e1d7b5d617728c528aefa64ce069e768596500c4d94,
  0x21ba8fba7db9cbb983b87db61db4bdb343a4a795217e577b9761b1297d2928fa9ece409eb085d050464dd5,
  0x33bc5dbc0bbbf7bb9bbb75bb33bad3b1b7a4fda191954380817e834b2729850c08ceae50b20313,
  0x33be1dbdf9bda7bd65bd23bcdbbc93b1e7a52da1c195b180ef7ed729f30c42faf6cede50e20353,
  0x7bf2fbecbbe89be5bbca5b20ba5557f392a24fb1ccf008602510d,
  0x3c04fc019bfd3bfb7bf49be63bcf3baedb253a5ab95dd7f752a832a64cf48864a5151,
  0x5c1d1c1b9c15bc127c0d5c0a5bd35bb2fb295a5ed961f4b772b052aeefb4a868c51900392,
  0x2fc28dc279c237bf5bbb79a61396457f954ba92b4ccfae86f051cd,
  0x13c37bc329c2f9c215c093bf8bbea7bd77bbb1b2d7a66f96a1811f7fe14bf92bc72bb0fba6cfcc870e521203d6,
  0x25c3a9c2cdc25bc127c0d9bff9bd8bbbc5b30396f3817180334c0d2c592c04fbf8d01e87605253,
  0x9c3fbc32fc2b9c16fbeddbdddbc3ba683a215970781974c6b2c96fc3087b25290,
  0x9c3e5c393c345c1d1c183c04fc007bf33be33bc7db347a6eb975d81db806d4cb52d032cecfc62d04887ca52d6,
  0x33c59dc54bc52bc4f7c49bc473c413b3aba777a711978182296cc34ce72d48d0a89eee53320413,
  0xdc619c5c197f14d1c881e5346,
  0x21c7edc797c777c705c6f1c695c659c5f3c435bb33bacdb3f1a78b983b82b9827b4d552de12d84d102d0e6886853ac0458,
  0xfc8abc859c815c65bc45bbb59a7dfa2719863832182f34d892e250caad1a8d14e889053d40493,
  0x31c95bc909c8d9c831c6abc4f7c4b7bb91b435a80f98bd83676d014dd92ea52e46d1e69f2a88ec543004d5,
  0x5c989c8ebc877c705c6cbc50bbbe3b449a85183b96d534e2b2f372ed8d2389f7c890054440513,
  0x27c9dbc90fc897c74dc61dc55dbc1ba8a1a2a383cd6db54e4b2f670cead24c9f90895254960553,
  0x27c9c5c9b1c961c7edc7b3c5b3bc5db4a5a8cb98f9840d4e952fe12f82d2a29fe689a854d2,
  0x7cb6fcb3dcacbcaadca49ca25b4fdaacba913846561d54ef93024fc9cd31ad2c089c255060593,
  0x3ccb7cc59cc07cbf5cb89ca33c42db507a96b991d84db84ad621d4f35306cfce4d3a2d3488a0a554e05d5,
  0x2fcd8dcd6dcd39ccf5cbadca5bc46dab39a99399458543851562554f693094fd0cd40ad3ee8a7055b40615,
  0x7ce7bce1dcdf9ccc7cbcbcab7c4b1b54ba9ef999f85896df162a14fb930f0fd66d448a00c8a8e55d20655,
  0x2fceadcd3dcaebc4e5b5a399d385fb6e2562d54fe4fd9ad4baa0408ac256060690,
  0x1dcdcdcd59cc0bc505b5ddaa039a3186056333500d3104fdf8d4de8b20564f,
  0x9ceefcebbce2fcdb7cc6fcb1dc56fab7baa559a45866d6e576357506b3156fe0cd52ca0b08b7256b606d5,
  0x9cec7ce43cc87cb73c5bdb607aaad63ad50b531acfe62d544a0c88b8e,
  0x25d00fcfd9cf97cf55cf1bbc85b659ab9fa2e186b363c931e50d32feaad5e8d58e8bd056d40713,
  0xdd089d043b6b16430fecc8c06,
  0x21d22dd1d7d1a7d173d121d0c9d057cf55cf25bd23bccdb6e1abf99aab872986fb64453251323aff32d670d6168c58571c0759,
  0x31d2dbd2b7d261d0d9cfa7bd51b725ac3d9aed87576e81648932d53280ff74d696a11a8c9c57600794,
  0x5d337d267d173d139bda3b7519b01879364db33673312ff88d6e8a16c8cee5790,
  0x1bd297d18dd08fcfddbddbac61a3339b6387cd6ef5650b33a70d74ffead70ca1908d1257d607d3,
  0x5d331d2e1d22dd1e5d033be25acf1ac8b9bb988236f0d6555342133cd0002d762a1e68d68582c0814,
  0x7d3fbd3bbd355cf09be71b7a1885f65b934710068d7b88d8e584d,
  0x9d4d5d4bdd459d417cf49ca33b7d9ad2165e350fb34c934b300ba8dd058940850,
  0x33d57dd53bd36dca7dad4988876619512d351900d0d7e08e3458cd,
  0x17d5c1d5bdd519d419cfbdcacbca8bbeb5b81bada388e36665517d358b3575012cd8ead83c8e5259160895,
  0xdd601d5b3d57dd47bd38fcfefcb2fbec1adc7a3498909669b51af35cd0d92d910d8628eb6597a08d4,
  0xdd617d5c9d4d5d487d3e5d007cb47bf03b84bae57ae1f895f66f151f9364736310168d966d8b88ece59920916,
  0x2fd649d059c5e5b8a39bd36715522501ac8f0259c6094b,
  0x2fd64dd08dc6179c076759525901e08f745a09,
  0x3bd70dd6c7d6bbd375cb95c677bf47ae9f9c51898f67a152a937f53698d9a88fbc5a51,
  0x13d7c9d7a9d747d699d421d0c7cbf1c695c093bfbdb8fb9cad8aeb89eb67ed52c736fd0234daf2d9c68fda5a9e0997,
  0x25d829d773d119cc05c6e7c0d1b929aecf9cc18b3d6801531937110248db18902c5ad1,
  0xdd6e7d177c71bc119bfc5b9439d338b718a316873534502badb78da0c90605b2409d1,
  0x9d895d849d7bbd72fd67dd47bd397d1b7cc57c779c149af219d538b9168a353ab3837376302dadbaa90805b56,
  0x15d865d813d7d5d4add1c3ccadc791c18fc00bb993af779da98be78a6768f953c337b90330dbeeda4290d65b96,
  0x9d889d4c7d3e1d221c7c5c1c3c07db9eb9ddd8c1b8a9b692d542d0364dc22dab4910a5bce0a13,
  0x1d91dd8c7d6bdd52dcd39ccd9c839c20bafa39e158d138c536965546d38b93865039cdd1adc6c91425c060a56,
  0x1dd8cdd6cdcd6bc84dc25daff59e678d658ca569b75481390d38f703eedd6cdc8091945c580a93,
  0x1d93bd733d56fcd8fc8afc281b007a3999e8b8d898cc969ef394d0ddb0412dd90dce291f65cba0ad4,
  0x1dd8e9d777d25dcdc9c8e9c2d5ba139ec38dc36a0554dd3995044adddc92305cd0,
  0x19d941d909d781d59bd2afcebbce1bc93bc30db0659f158e3d6f956a67552f3a7b39e7049cde3ca26e92445d080b17,
  0x19d953d7d7d5f1d2c7ce71c953c34fba57b0bb9f6b8e6b6abd55473a3d04f2de54a286929a5d53,
  0x25d805d305c9a5c3a1baa9b0cf9fbd8ebd6ad155993a910506de9892ec5d8f,
  0x19d949d895d84dd609cee7c9c9c3cdb159b1319fe18ecb6fe16b3b3b093af30568decaa2fa93105dd40b55]

def thirdSuccessors (i : ℕ) : List ℕ :=
  successorCodes (thirdSuccessorsList.getD i 0)


noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 12 1 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1 z v))

lemma afterSecond_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 11)
    (mixed : mixedFromSecond state = false)
    (pure : pureAt 11 state (fun z v => afterThird (z,v)) = false) :
    afterSecond state = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 12 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 12 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [afterSecond, frc_eq, st_eq, show (13 : ℕ) = Nat.succ 12 from rfl, look1C_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureAt 11 state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeCheck_append (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all



def taggedMissing (codes : List ℕ) (atState : ℕ → SearchState) (z : ℕ) (v : List W) : Bool :=
  st (z % 31) fun tag => !(codes.any fun code =>
    (code / 2048 == tag) && !frontierMissing [atState (code % 2048)] z v)

lemma taggedMissing_found {codes : List ℕ} {atState : ℕ → SearchState} {z : ℕ} {v : List W}
    (h : taggedMissing codes atState z v = false) :
    ∃ code ∈ codes, (z,v) = atState (code % 2048) := by
  simp only [taggedMissing, st_eq, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨code, hc, _, hit⟩ := h
  have captured := frontierMissing_false (boolOfNeg hit)
  exact ⟨code, hc, List.mem_singleton.mp captured⟩

noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  let ids := thirdSuccessors i
  (!pureAt 11 state (taggedMissing ids thirdAt)) &&
    ((ids.all fun j => decide (j % 2048 < thirdCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 11)))

noncomputable def thirdTest (j : ℕ) : Bool := !afterThird (thirdAt j)
noncomputable def secondMixedTest (j : ℕ) : Bool := !mixedFromSecond (secondAt j)

lemma checkedAfterSecond (i : ℕ) (hi : i < secondCount)
    (ready : rangeCheck readyForThird 0 secondCount = true)
    (mixed : rangeCheck secondMixedTest 0 secondCount = true)
    (third : rangeCheck thirdTest 0 thirdCount = true) :
    afterSecond (secondAt i) = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForThird, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterSecond_false (secondAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 11 (secondAt i) afterThird (taggedMissing (thirdSuccessors i) thirdAt) (boolOfNeg hc) ?_
  intro z v found
  obtain ⟨j, hj, eq⟩ := taggedMissing_found found
  rw [eq]
  have hj' : j % 2048 < thirdCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact boolOfNeg (rangeCheck_at third hj')


noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  let ids := secondSuccessors i
  (!pureSecond state (taggedMissing ids secondAt)) &&
    ((ids.all fun j => decide (j % 2048 < secondCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def mixedSecondPicked (state : SearchState) (b : Fin 8) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvPicked I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0 b))

lemma mixedSecondPicked_all (state : SearchState)
    (checked : ∀ b, mixedSecondPicked state b = false) : mixedSecond state = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  simp only [mixedSecond, frc_eq, st_eq] at h
  obtain ⟨b,hb⟩ := mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hc := checked b
  simp only [mixedSecondPicked, frc_eq, st_eq] at hc
  exact Bool.noConfusion (hc.symm.trans hb)

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 12 (firstAt i) afterSecond (taggedMissing (secondSuccessors i) secondAt) (boolOfNeg hc) ?_
  intro z v found
  obtain ⟨j, hj, eq⟩ := taggedMissing_found found
  rw [eq]
  have hj' : j % 2048 < secondCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact next _ hj'


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk3 : rangeCheck readyForSecond 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk4 : rangeCheck readyForSecond 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk5 : rangeCheck readyForSecond 20 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk6 : rangeCheck readyForSecond 24 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 firstCount = true := by
  exact (@rangeCheck_append readyForSecond 0 12 16
    (@rangeCheck_append readyForSecond 0 4 8
    firstCoverageChunk0 (@rangeCheck_append readyForSecond 4 4 4
    firstCoverageChunk1 firstCoverageChunk2)) (@rangeCheck_append readyForSecond 12 8 8
    (@rangeCheck_append readyForSecond 12 4 4
    firstCoverageChunk3 firstCoverageChunk4) (@rangeCheck_append readyForSecond 20 4 4
    firstCoverageChunk5 firstCoverageChunk6)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 1 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk2 : rangeCheck firstMixedTest 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk3 : rangeCheck firstMixedTest 3 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk4 : rangeCheck firstMixedTest 4 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk5 : rangeCheck firstMixedTest 5 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk6 : rangeCheck firstMixedTest 6 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk7 : rangeCheck firstMixedTest 7 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk8 : rangeCheck firstMixedTest 8 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk9 : rangeCheck firstMixedTest 9 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk10 : rangeCheck firstMixedTest 11 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk11 : rangeCheck firstMixedTest 12 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk12 : rangeCheck firstMixedTest 13 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk13 : rangeCheck firstMixedTest 14 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk14 : rangeCheck firstMixedTest 16 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk15 : rangeCheck firstMixedTest 17 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk16 : rangeCheck firstMixedTest 18 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk17 : rangeCheck firstMixedTest 19 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18 : rangeCheck firstMixedTest 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk19 : rangeCheck firstMixedTest 22 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk20 : rangeCheck firstMixedTest 23 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk21 : rangeCheck firstMixedTest 24 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk22 : rangeCheck firstMixedTest 25 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part0 : mixedSecondPicked (firstAt 26) 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part1 : mixedSecondPicked (firstAt 26) 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part2 : mixedSecondPicked (firstAt 26) 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part3 : mixedSecondPicked (firstAt 26) 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part4 : mixedSecondPicked (firstAt 26) 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part5 : mixedSecondPicked (firstAt 26) 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part6 : mixedSecondPicked (firstAt 26) 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23Part7 : mixedSecondPicked (firstAt 26) 7 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk23 : rangeCheck firstMixedTest 26 1 = true := by
  have result : mixedSecond (firstAt 26) = false := by
    apply mixedSecondPicked_all
    intro b
    fin_cases b
    · exact firstMixedChunk23Part0
    · exact firstMixedChunk23Part1
    · exact firstMixedChunk23Part2
    · exact firstMixedChunk23Part3
    · exact firstMixedChunk23Part4
    · exact firstMixedChunk23Part5
    · exact firstMixedChunk23Part6
    · exact firstMixedChunk23Part7
  simp [rangeCheck, firstMixedTest, result]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part0 : mixedSecondPicked (firstAt 27) 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part1 : mixedSecondPicked (firstAt 27) 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part2 : mixedSecondPicked (firstAt 27) 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part3 : mixedSecondPicked (firstAt 27) 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part4 : mixedSecondPicked (firstAt 27) 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part5 : mixedSecondPicked (firstAt 27) 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part6 : mixedSecondPicked (firstAt 27) 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24Part7 : mixedSecondPicked (firstAt 27) 7 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk24 : rangeCheck firstMixedTest 27 1 = true := by
  have result : mixedSecond (firstAt 27) = false := by
    apply mixedSecondPicked_all
    intro b
    fin_cases b
    · exact firstMixedChunk24Part0
    · exact firstMixedChunk24Part1
    · exact firstMixedChunk24Part2
    · exact firstMixedChunk24Part3
    · exact firstMixedChunk24Part4
    · exact firstMixedChunk24Part5
    · exact firstMixedChunk24Part6
    · exact firstMixedChunk24Part7
  simp [rangeCheck, firstMixedTest, result]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 firstCount = true := by
  exact (@rangeCheck_append firstMixedTest 0 13 15
    (@rangeCheck_append firstMixedTest 0 6 7
    (@rangeCheck_append firstMixedTest 0 3 3
    (@rangeCheck_append firstMixedTest 0 1 2
    firstMixedChunk0 (@rangeCheck_append firstMixedTest 1 1 1
    firstMixedChunk1 firstMixedChunk2)) (@rangeCheck_append firstMixedTest 3 1 2
    firstMixedChunk3 (@rangeCheck_append firstMixedTest 4 1 1
    firstMixedChunk4 firstMixedChunk5))) (@rangeCheck_append firstMixedTest 6 3 4
    (@rangeCheck_append firstMixedTest 6 1 2
    firstMixedChunk6 (@rangeCheck_append firstMixedTest 7 1 1
    firstMixedChunk7 firstMixedChunk8)) (@rangeCheck_append firstMixedTest 9 2 2
    firstMixedChunk9 (@rangeCheck_append firstMixedTest 11 1 1
    firstMixedChunk10 firstMixedChunk11)))) (@rangeCheck_append firstMixedTest 13 7 8
    (@rangeCheck_append firstMixedTest 13 4 3
    (@rangeCheck_append firstMixedTest 13 1 3
    firstMixedChunk12 (@rangeCheck_append firstMixedTest 14 2 1
    firstMixedChunk13 firstMixedChunk14)) (@rangeCheck_append firstMixedTest 17 1 2
    firstMixedChunk15 (@rangeCheck_append firstMixedTest 18 1 1
    firstMixedChunk16 firstMixedChunk17))) (@rangeCheck_append firstMixedTest 20 4 4
    (@rangeCheck_append firstMixedTest 20 2 2
    firstMixedChunk18 (@rangeCheck_append firstMixedTest 22 1 1
    firstMixedChunk19 firstMixedChunk20)) (@rangeCheck_append firstMixedTest 24 2 2
    (@rangeCheck_append firstMixedTest 24 1 1
    firstMixedChunk21 firstMixedChunk22) (@rangeCheck_append firstMixedTest 26 1 1
    firstMixedChunk23 firstMixedChunk24)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 12 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 24 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 36 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 48 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 60 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 72 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 84 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 96 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 108 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 120 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 132 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk12 : rangeCheck readyForThird 144 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk13 : rangeCheck readyForThird 156 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk14 : rangeCheck readyForThird 168 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk15 : rangeCheck readyForThird 180 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk16 : rangeCheck readyForThird 192 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk17 : rangeCheck readyForThird 204 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk18 : rangeCheck readyForThird 216 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk19 : rangeCheck readyForThird 228 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk20 : rangeCheck readyForThird 240 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk21 : rangeCheck readyForThird 252 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk22 : rangeCheck readyForThird 264 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk23 : rangeCheck readyForThird 276 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk24 : rangeCheck readyForThird 288 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk25 : rangeCheck readyForThird 300 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk26 : rangeCheck readyForThird 312 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 secondCount = true := by
  exact (@rangeCheck_append readyForThird 0 156 161
    (@rangeCheck_append readyForThird 0 72 84
    (@rangeCheck_append readyForThird 0 36 36
    (@rangeCheck_append readyForThird 0 12 24
    secondCoverageChunk0 (@rangeCheck_append readyForThird 12 12 12
    secondCoverageChunk1 secondCoverageChunk2)) (@rangeCheck_append readyForThird 36 12 24
    secondCoverageChunk3 (@rangeCheck_append readyForThird 48 12 12
    secondCoverageChunk4 secondCoverageChunk5))) (@rangeCheck_append readyForThird 72 36 48
    (@rangeCheck_append readyForThird 72 12 24
    secondCoverageChunk6 (@rangeCheck_append readyForThird 84 12 12
    secondCoverageChunk7 secondCoverageChunk8)) (@rangeCheck_append readyForThird 108 24 24
    (@rangeCheck_append readyForThird 108 12 12
    secondCoverageChunk9 secondCoverageChunk10) (@rangeCheck_append readyForThird 132 12 12
    secondCoverageChunk11 secondCoverageChunk12)))) (@rangeCheck_append readyForThird 156 84 77
    (@rangeCheck_append readyForThird 156 36 48
    (@rangeCheck_append readyForThird 156 12 24
    secondCoverageChunk13 (@rangeCheck_append readyForThird 168 12 12
    secondCoverageChunk14 secondCoverageChunk15)) (@rangeCheck_append readyForThird 192 24 24
    (@rangeCheck_append readyForThird 192 12 12
    secondCoverageChunk16 secondCoverageChunk17) (@rangeCheck_append readyForThird 216 12 12
    secondCoverageChunk18 secondCoverageChunk19))) (@rangeCheck_append readyForThird 240 36 41
    (@rangeCheck_append readyForThird 240 12 24
    secondCoverageChunk20 (@rangeCheck_append readyForThird 252 12 12
    secondCoverageChunk21 secondCoverageChunk22)) (@rangeCheck_append readyForThird 276 24 17
    (@rangeCheck_append readyForThird 276 12 12
    secondCoverageChunk23 secondCoverageChunk24) (@rangeCheck_append readyForThird 300 12 5
    secondCoverageChunk25 secondCoverageChunk26)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 12 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 18 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 30 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 38 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 45 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 57 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 68 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk8 : rangeCheck secondMixedTest 77 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk9 : rangeCheck secondMixedTest 86 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk10 : rangeCheck secondMixedTest 98 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk11 : rangeCheck secondMixedTest 104 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk12 : rangeCheck secondMixedTest 115 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk13 : rangeCheck secondMixedTest 121 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk14 : rangeCheck secondMixedTest 133 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk15 : rangeCheck secondMixedTest 143 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk16 : rangeCheck secondMixedTest 150 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk17 : rangeCheck secondMixedTest 151 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk18 : rangeCheck secondMixedTest 153 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk19 : rangeCheck secondMixedTest 160 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk20 : rangeCheck secondMixedTest 170 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk21 : rangeCheck secondMixedTest 173 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk22 : rangeCheck secondMixedTest 185 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk23 : rangeCheck secondMixedTest 197 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk24 : rangeCheck secondMixedTest 209 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk25 : rangeCheck secondMixedTest 221 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk26 : rangeCheck secondMixedTest 233 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk27 : rangeCheck secondMixedTest 245 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk28 : rangeCheck secondMixedTest 257 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk29 : rangeCheck secondMixedTest 269 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk30 : rangeCheck secondMixedTest 280 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk31 : rangeCheck secondMixedTest 290 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk32 : rangeCheck secondMixedTest 299 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk33 : rangeCheck secondMixedTest 310 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk34 : rangeCheck secondMixedTest 316 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 secondCount = true := by
  exact (@rangeCheck_append secondMixedTest 0 151 166
    (@rangeCheck_append secondMixedTest 0 77 74
    (@rangeCheck_append secondMixedTest 0 38 39
    (@rangeCheck_append secondMixedTest 0 18 20
    (@rangeCheck_append secondMixedTest 0 12 6
    secondMixedChunk0 secondMixedChunk1) (@rangeCheck_append secondMixedTest 18 12 8
    secondMixedChunk2 secondMixedChunk3)) (@rangeCheck_append secondMixedTest 38 19 20
    (@rangeCheck_append secondMixedTest 38 7 12
    secondMixedChunk4 secondMixedChunk5) (@rangeCheck_append secondMixedTest 57 11 9
    secondMixedChunk6 secondMixedChunk7))) (@rangeCheck_append secondMixedTest 77 38 36
    (@rangeCheck_append secondMixedTest 77 21 17
    (@rangeCheck_append secondMixedTest 77 9 12
    secondMixedChunk8 secondMixedChunk9) (@rangeCheck_append secondMixedTest 98 6 11
    secondMixedChunk10 secondMixedChunk11)) (@rangeCheck_append secondMixedTest 115 18 18
    (@rangeCheck_append secondMixedTest 115 6 12
    secondMixedChunk12 secondMixedChunk13) (@rangeCheck_append secondMixedTest 133 10 8
    secondMixedChunk14 (@rangeCheck_append secondMixedTest 143 7 1
    secondMixedChunk15 secondMixedChunk16))))) (@rangeCheck_append secondMixedTest 151 82 84
    (@rangeCheck_append secondMixedTest 151 22 60
    (@rangeCheck_append secondMixedTest 151 9 13
    (@rangeCheck_append secondMixedTest 151 2 7
    secondMixedChunk17 secondMixedChunk18) (@rangeCheck_append secondMixedTest 160 10 3
    secondMixedChunk19 secondMixedChunk20)) (@rangeCheck_append secondMixedTest 173 24 36
    (@rangeCheck_append secondMixedTest 173 12 12
    secondMixedChunk21 secondMixedChunk22) (@rangeCheck_append secondMixedTest 197 12 24
    secondMixedChunk23 (@rangeCheck_append secondMixedTest 209 12 12
    secondMixedChunk24 secondMixedChunk25)))) (@rangeCheck_append secondMixedTest 233 47 37
    (@rangeCheck_append secondMixedTest 233 24 23
    (@rangeCheck_append secondMixedTest 233 12 12
    secondMixedChunk26 secondMixedChunk27) (@rangeCheck_append secondMixedTest 257 12 11
    secondMixedChunk28 secondMixedChunk29)) (@rangeCheck_append secondMixedTest 280 19 18
    (@rangeCheck_append secondMixedTest 280 10 9
    secondMixedChunk30 secondMixedChunk31) (@rangeCheck_append secondMixedTest 299 11 7
    secondMixedChunk32 (@rangeCheck_append secondMixedTest 310 6 1
    secondMixedChunk33 secondMixedChunk34))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 48 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 96 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 144 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 192 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 240 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 288 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 336 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 384 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 432 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 480 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 528 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 576 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 624 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 672 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 697 41 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 738 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk17 : rangeCheck thirdTest 751 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk18 : rangeCheck thirdTest 799 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk19 : rangeCheck thirdTest 847 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk20 : rangeCheck thirdTest 879 37 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk21 : rangeCheck thirdTest 916 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk22 : rangeCheck thirdTest 927 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk23 : rangeCheck thirdTest 947 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk24 : rangeCheck thirdTest 995 34 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk25 : rangeCheck thirdTest 1029 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk26 : rangeCheck thirdTest 1077 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk27 : rangeCheck thirdTest 1125 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk28 : rangeCheck thirdTest 1173 46 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk29 : rangeCheck thirdTest 1219 27 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk30 : rangeCheck thirdTest 1246 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk31 : rangeCheck thirdTest 1268 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk32 : rangeCheck thirdTest 1316 44 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk33 : rangeCheck thirdTest 1360 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk34 : rangeCheck thirdTest 1408 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk35 : rangeCheck thirdTest 1456 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk36 : rangeCheck thirdTest 1504 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk37 : rangeCheck thirdTest 1552 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk38 : rangeCheck thirdTest 1600 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk39 : rangeCheck thirdTest 1648 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk40 : rangeCheck thirdTest 1696 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk41 : rangeCheck thirdTest 1744 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk42 : rangeCheck thirdTest 1792 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk43 : rangeCheck thirdTest 1840 38 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk44 : rangeCheck thirdTest 1878 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 thirdCount = true := by
  exact (@rangeCheck_append thirdTest 0 927 967
    (@rangeCheck_append thirdTest 0 528 399
    (@rangeCheck_append thirdTest 0 240 288
    (@rangeCheck_append thirdTest 0 96 144
    (@rangeCheck_append thirdTest 0 48 48
    thirdTailChunk0 thirdTailChunk1) (@rangeCheck_append thirdTest 96 48 96
    thirdTailChunk2 (@rangeCheck_append thirdTest 144 48 48
    thirdTailChunk3 thirdTailChunk4))) (@rangeCheck_append thirdTest 240 144 144
    (@rangeCheck_append thirdTest 240 48 96
    thirdTailChunk5 (@rangeCheck_append thirdTest 288 48 48
    thirdTailChunk6 thirdTailChunk7)) (@rangeCheck_append thirdTest 384 48 96
    thirdTailChunk8 (@rangeCheck_append thirdTest 432 48 48
    thirdTailChunk9 thirdTailChunk10)))) (@rangeCheck_append thirdTest 528 210 189
    (@rangeCheck_append thirdTest 528 96 114
    (@rangeCheck_append thirdTest 528 48 48
    thirdTailChunk11 thirdTailChunk12) (@rangeCheck_append thirdTest 624 48 66
    thirdTailChunk13 (@rangeCheck_append thirdTest 672 25 41
    thirdTailChunk14 thirdTailChunk15))) (@rangeCheck_append thirdTest 738 109 80
    (@rangeCheck_append thirdTest 738 13 96
    thirdTailChunk16 (@rangeCheck_append thirdTest 751 48 48
    thirdTailChunk17 thirdTailChunk18)) (@rangeCheck_append thirdTest 847 32 48
    thirdTailChunk19 (@rangeCheck_append thirdTest 879 37 11
    thirdTailChunk20 thirdTailChunk21))))) (@rangeCheck_append thirdTest 927 433 534
    (@rangeCheck_append thirdTest 927 198 235
    (@rangeCheck_append thirdTest 927 68 130
    (@rangeCheck_append thirdTest 927 20 48
    thirdTailChunk22 thirdTailChunk23) (@rangeCheck_append thirdTest 995 34 96
    thirdTailChunk24 (@rangeCheck_append thirdTest 1029 48 48
    thirdTailChunk25 thirdTailChunk26))) (@rangeCheck_append thirdTest 1125 121 114
    (@rangeCheck_append thirdTest 1125 48 73
    thirdTailChunk27 (@rangeCheck_append thirdTest 1173 46 27
    thirdTailChunk28 thirdTailChunk29)) (@rangeCheck_append thirdTest 1246 22 92
    thirdTailChunk30 (@rangeCheck_append thirdTest 1268 48 44
    thirdTailChunk31 thirdTailChunk32)))) (@rangeCheck_append thirdTest 1360 288 246
    (@rangeCheck_append thirdTest 1360 144 144
    (@rangeCheck_append thirdTest 1360 48 96
    thirdTailChunk33 (@rangeCheck_append thirdTest 1408 48 48
    thirdTailChunk34 thirdTailChunk35)) (@rangeCheck_append thirdTest 1504 48 96
    thirdTailChunk36 (@rangeCheck_append thirdTest 1552 48 48
    thirdTailChunk37 thirdTailChunk38))) (@rangeCheck_append thirdTest 1648 144 102
    (@rangeCheck_append thirdTest 1648 48 96
    thirdTailChunk39 (@rangeCheck_append thirdTest 1696 48 48
    thirdTailChunk40 thirdTailChunk41)) (@rangeCheck_append thirdTest 1792 48 54
    thirdTailChunk42 (@rangeCheck_append thirdTest 1840 38 16
    thirdTailChunk43 thirdTailChunk44))))))

def initialIndices (kind : Bool) : List ℕ := if kind then [1, 2, 4, 5, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27] else [0, 3, 6, 10, 13, 21]

noncomputable def initialStates (kind : Bool) : List SearchState := (initialIndices kind).map firstAt

lemma allInitialIndices (kind : Bool) : (initialIndices kind).all (fun i => decide (i < firstCount)) = true := by
  cases kind <;> decide +kernel

lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) : chkPairPicked [] rootBounds 0 14 1 FF 0 kind = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : chk [] rootBounds 0 14 1 FF 0 = false :=
  chkPair_picked [] rootBounds 0 14 1 FF 0 binaryCertificate


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked0 : chkPicked [] rootBounds 0 14 1 0 1 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked1 : chkPicked [] rootBounds 0 14 1 0 1 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked2 : chkPicked [] rootBounds 0 14 1 0 1 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked3 : chkPicked [] rootBounds 0 14 1 0 1 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked4 : chkPicked [] rootBounds 0 14 1 0 1 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked5 : chkPicked [] rootBounds 0 14 1 0 1 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked6 : chkPicked [] rootBounds 0 14 1 0 1 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked7 : chkPicked [] rootBounds 0 14 1 0 1 7 = false := by decide +kernel

lemma unaryChecked : chk [] rootBounds 0 14 1 0 1 = false := by
  apply chk_picked
  intro b
  fin_cases b
  · exact unaryChecked0
  · exact unaryChecked1
  · exact unaryChecked2
  · exact unaryChecked3
  · exact unaryChecked4
  · exact unaryChecked5
  · exact unaryChecked6
  · exact unaryChecked7


def rootCases : List (ℕ × ℕ) := [(FF, 0), (0, 1)]

lemma rootCases_full : mFull rootCases = true := by decide +kernel

lemma certify_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rootBounds 0 14 1 p.1 p.2 = false := by
  refine ⟨rootCases, rootCases_full, ?_⟩
  intro p hp
  simp only [rootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3Pair : Lg I.NN (mz 0) (tz 0) 65 := by
  unfold Lg
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3Region : mz 8 &&& mz 0 = mz 8 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3Target : tz 8 ≠ 0 ∧ tz 8 ≠ mz 8 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3SeparatorsKilled : (rawL []).all (fun w =>
    !(sepb I.NN true (w &&& mz 0) 65) || Nat.beq ((w &&& mz 0) &&& mz 8) 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3SeparatorConstant {x : ℕ} (hin : x ∈ C (mz 0) (WZ [] 0))
    (hsep : sepb I.NN true x 65 = true) : Cst (mz 8) x := by
  rcases hin with h | h
  · obtain ⟨w, hw, rfl⟩ := h
    have hz := List.all_eq_true.mp x3SeparatorsKilled w hw
    simp only [hsep, Bool.not_true, Bool.false_or] at hz
    exact Or.inl (Nat.eq_of_beq_eq_true hz)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by rw [Nat.and_comm, x3Region])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3ProjectedInputs {S : Finset ℕ} (hs : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) :
    C (mz 8) (Im (mz 8) S) ⊆ C (mz 8) (WZ [] 8) := by
  rintro x (⟨word, hw, rfl⟩ | hx)
  · rcases hs hw with h | h
    · obtain ⟨w, input, rfl⟩ := h
      exact Or.inl ⟨w, input, by
        change (w &&& mz 0) &&& mz 8 = w &&& mz 8
        rw [Nat.and_assoc, Nat.and_comm (mz 0), x3Region]⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact Or.inr (by simp)
      · apply Or.inr
        change mz 0 &&& mz 8 ∈ ({0, mz 8} : Set ℕ)
        rw [Nat.and_comm, x3Region]
        exact Set.mem_insert_of_mem _ rfl
  · exact Or.inr hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lower14 : Imp [] 0 14 := by
  intro q hq solution
  classical
  let existsSol : ∃ n, Sol Z0 (mz 0) (tz 0) n (C (mz 0) (WZ [] 0)) := ⟨q, solution⟩
  obtain ⟨k, hk, t, S, hS, live⟩ := (Nat.find_spec existsSol).live
  have leSize := le_trans hk (Nat.find_min' existsSol solution)
  have ambient : C (mz 0) (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have minimal : Min Z0 (mz 0) (tz 0) k t S :=
    ⟨live, fun n hn smaller => Nat.find_min existsSol (lt_of_lt_of_le hn hk) (smaller.mono le_rfl ambient)⟩
  obtain ⟨wire, hwire, separated⟩ := live.cov x3Pair.1 x3Pair.2.1 x3Pair.2.2.1 x3Pair.2.2.2
  have constant := x3SeparatorConstant (hS hwire) (sepb_weak (pos' t) separated)
  have killed : 0 < (S.filter (Cst (mz 8))).card :=
    Finset.card_pos.mpr ⟨wire, Finset.mem_filter.mpr ⟨hwire, constant⟩⟩
  obtain ⟨n, leaner, solved⟩ := minimal.const x3Region
    (by rw [tz_sub x3Region]; exact x3Target.1) (by rw [tz_sub x3Region]; exact x3Target.2)
  rw [tz_sub x3Region] at solved
  exact strongRow8 n (by omega) (solved.mono le_rfl (x3ProjectedInputs hS))

lemma needs15 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 14 1 S) : False := by
  have hmin : ∀ q < 14, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => lower14 q hq
  exact imp_of_live (L := 15) (Or.inl rfl) root_p (by norm_num) rootBounds_sound
    (by norm_num) hS hl hmin (Or.inr certify_1)

lemma onFinal : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfit hone hev
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 15 ≤ gates.length := by
      by_contra! hlt
      have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y :=
        fun y => (hev y).trans (f_graph y).symm
      by_cases hsmall : gates.length < 14
      · exact lower14 gates.length hsmall (bridge ⟨gates, o⟩ (fanInTwo_of hfit) hf)
      · have hsize : gates.length = 14 := by omega
        rcases bridge_not gates o (fanInTwo_of hfit) hone hnot hf with hsol | ⟨S, hS, hl⟩
        · exact lower14 (gates.length - 1) (by omega) hsol
        · rw [hsize] at hl
          exact needs15 hS hl
    exact ⟨witness.gates, witness.output, witness_basis, by rw [witness_size]; omega, witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    rcases hfit g hg with ⟨h | h | h, hl⟩
    · exact ⟨Or.inl h, hl⟩
    · exact ⟨Or.inr h, hl⟩
    · exact (hnot ⟨g, hg, h⟩).elim

end inst_data
end PEqualNP.Outside.L_meta_51640_aux

theorem PEqualNP.Outside.L_meta_51640 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_51640_aux.onFinal
