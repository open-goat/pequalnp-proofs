import PEqualNP.Defs
-- Adapted from PEqualNP.Outside.L_meta_52894 and PEqualNP.Outside.L_meta_52902 (Apache 2.0).

namespace PEqualNP.Outside.L_meta_52898
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
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 923
def AA : Nat := 0x3fffffdfbfffffdfffffefbfffffdf7fffffbfffffddfffffeffffff7bfffffdeffffff7beffffd57ffdbffed6abffebffebffefffb5aaafffb5fff6afffbffed6abffebffebffefffb6dbffedfff6dbffedfff0000000000000000000000000000000000000000000000000000000000000000
def HX : Nat := 0x2a800240012954001400140010004a5550004a0009500040012954001400140010004924001200092400120000000000000000000000000000000000000000000000000000000000000000000
def HY : Nat := 0x400000204000002000001040000020800000400000220000010000008400000210000008410000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
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
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
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
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
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
def segsX : List (ℕ × ℕ) := [(255, 269), (269, 272), (272, 286), (286, 289), (289, 292), (292, 295), (295, 309), (309, 312), (312, 326), (326, 329), (329, 332), (332, 335), (335, 338), (338, 352), (352, 366), (366, 368), (368, 382), (382, 384), (384, 398), (398, 400), (400, 402), (402, 404), (404, 407), (407, 409), (409, 412), (412, 426), (426, 440), (440, 442), (442, 444), (444, 447), (447, 461), (461, 463), (463, 466), (466, 480), (480, 482), (482, 484), (484, 486), (486, 488), (488, 490), (490, 493), (493, 495), (495, 498), (498, 512), (512, 526), (526, 528), (528, 542), (542, 544), (544, 558), (558, 560), (560, 562), (562, 564), (564, 567), (567, 569), (569, 572), (572, 586), (586, 589), (589, 603), (603, 605), (605, 607), (607, 609)]
def segsY : List (ℕ × ℕ) := [(609, 628), (628, 634), (634, 639), (639, 664), (664, 669), (669, 694), (694, 699), (699, 724), (724, 749), (749, 753), (753, 778), (778, 803), (803, 809), (809, 834), (834, 840), (840, 865), (865, 890), (890, 897), (897, 922)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
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
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
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
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
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
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
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
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
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
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
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
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
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
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
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
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
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
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
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
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
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
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
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
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
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
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
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
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : L_meta_52898.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
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
    {go : (L_meta_52898.X → L_meta_52898.X → Bool) → List L_meta_52898.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_52898.X.s e
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
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_52898.X → L_meta_52898.X → Bool) → List L_meta_52898.X → Bool,
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
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52898.X.s e))
end sound
def rawP : List ℕ := [0x7fffff8000000007fffff81f0000000014000a00040120012401400580000002820090100500160004012001240140058020012200b02c02420130000000000000000000000000000000000000000000000000000000000000000004445408084454040a2a08084454101084a8084234404212a2298dd0008424c20a52bb03e04454000000000008800000008000fff80080000040000a0003ffe008800000008000fff80c0000dfff0d8000dfffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x1fffffe000000000000001fffffe07fffffbc0000000004c00260100046404a404e013000010118002311013804c0100046404a404e013010c08a604610408e604a0000000000000000000000000000000000000000000000000000000000000000008888810108888081444101088882021091094a5a800842140421060851953800c632e7800888800000000006000008000bffe000002020000000062fff800006000008000bffe0000618000c00061bffec000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xffffff00000000000000000000000ffffff00000001fffffef000000000000000842802140010224422c022808a00404105182123410a04280010424442c042810a080442c0214340448422c000000000000000000000000000000000000000000000000000000000000000001101242021012513589200201124404012482008c485114da080229006119ade100443002101241000000001020000bffe000000001808000300006800000001020000bffe0000000301bffe00006c0000dffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x3fffffc0000000ffffff7fffffbc000000000000000000000000b0005820140b800b000b002c000100260a05c0002c00b020140b800b000b002c1a60130009826817000b0000000000000000000000000000000000000000000000000000000000000000002212084042120820610420412208818a6390411108061989c30cc4e78822030020880c08021208000000000c02bffe000000000000402000035fff000000000c02bffe0000000000036c000000006dbffe0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0x1fffffe0000000000000001fffffe03fffffdfffffee00000000000000000000000000000000000221c0d1606b411c011c011c047008011478008e00047011c06b412c012c012c04b013493c049e000138009c000000000000000000000000000000000000000000000000000000000000000002bc20300004203001801841063c30010c43e08621f1c0200e0010070000401c0401007000402030400018000d680000000000000003002afff80000000000000d6800000000000000036dbffedfff0000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0x1fffffe00000001fffffef80000000000000000000000000000000000000000000000008090045800000500050005001401a940240004800024009004a40b000b000b002c00000a000500000a00050000000000000000000000000000000000000000000000000000000000000000000c003c08287c3c04201e001843fc1f2007c01003e000801f00400f8011003e008400f80108403c100001bffe00000000000000000035a8000000000000000000d6abffebffebffefff800000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0x1fffffeffffff7c0000000000000000000000000000000000000000000000000000000088e00060000006000600060018012d4438010700243800e000000c000c000c003000000c000600000c00060000000000000000000000000000000000000000000000000000000000000000003003c010307fc0183fe00fa07c000040f800207c001103e00081f0002207c000081f00021083c0157ffc000000000000000000000035aaafffb5fff6afffbffe000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0x1fffffefc00000000000000000000000000000000000000000000000000000000000000000000002300098004a4180018001800600000004000080000400100000010001000100040000010000800001000080000000000000000000000000000000000000000000000000000000000000000003ffc001fbf80001fc000083f8000107f00003f800001fc0000fe000043f800010fe0000420fc00157ffdbffed6abffebffebffefff8000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 256 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x3fffffdfbfffffdfffffefbfffffdf7fffffbfffffddfffffeffffff7bfffffdeffffff7beffffd57ffdbffed6abffebffebffefffb5aaafffb5fff6afffbffed6abffebffebffefffb6dbffedfff6dbffedffffffffffffffffffffffffffffffefffefffffffeffffffeefffefffefefaeca0
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
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
  have h := List.all_eq_true.1 raw_good w hw
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
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
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
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
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
    have : Std.Symm (fun a b : L_meta_52898.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52898.X.s e)) hpb
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
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
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
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
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
lemma apI {A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp [] e.1 e.2) (hb : ∀ e ∈ B, Imp [] e.1 e.2) : ∀ e ∈ A ++ B, Imp [] e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
noncomputable def okS (T : List (ℕ × ℕ)) (Z K : ℕ) (p : ℕ × ℕ × ℕ) : Bool := !chk [] (pr T Z) Z K p.1 p.2.1 p.2.2
def selT (M : List (ℕ × ℕ × ℕ)) (t : ℕ) : List (ℕ × ℕ) := (M.filter (fun p => Nat.beq p.1 t)).map Prod.snd
def okP (T : List (ℕ × ℕ)) (Z L : ℕ) (M : List (ℕ × ℕ × ℕ)) : Bool := pOk Z (pr T Z) && Nat.ble L 15 && (List.range L).all (fun t => mFull (selT M t))
lemma imp_run {T : List (ℕ × ℕ)} {Z L : ℕ} (M : List (ℕ × ℕ × ℕ)) (hT : ∀ e ∈ T, Imp [] e.1 e.2) (hp : okP T Z L M = true) (h : M.all (okS T Z (L - 1)) = true) : Imp [] Z L := by
  simp only [okP, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp
  refine imp_of (Or.inl rfl) hp.1.1 (Nat.le_of_ble_eq_true hp.1.2) (fun e he => hT e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ⟨selT M t, hp.2 t ht, fun p hq => ?_⟩)
  simp only [selT, List.mem_map, List.mem_filter] at hq
  obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hq
  have h1 := List.all_eq_true.1 h q hq1
  have h2 : q.1 = t := Nat.eq_of_beq_eq_true hq2
  simp only [okS, Bool.not_eq_true'] at h1
  rw [← h2]; exact h1
lemma appS {T : List (ℕ × ℕ)} {Z K : ℕ} {A B : List (ℕ × ℕ × ℕ)} (ha : A.all (okS T Z K) = true) (hb : B.all (okS T Z K) = true) : (A ++ B).all (okS T Z K) = true := by
  rw [List.all_append, ha, hb]; rfl
lemma one1 {Z L : ℕ} (h : Imp [] Z L) : ∀ e ∈ [(Z, L)], Imp [] e.1 e.2 := fun e he => by
  simp only [List.mem_singleton] at he; subst he; exact h
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
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 2 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 2 0 &&& rawP.getD 5 0) ||| (rawP.getD 3 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 6 0) ||| (rawP.getD 1 0 &&& rawP.getD 6 0) ||| (rawP.getD 3 0 &&& rawP.getD 6 0) ||| (rawP.getD 4 0 &&& rawP.getD 6 0) ||| (rawP.getD 0 0 &&& rawP.getD 7 0) ||| (rawP.getD 1 0 &&& rawP.getD 7 0) ||| (rawP.getD 2 0 &&& rawP.getD 7 0) ||| (rawP.getD 3 0 &&& rawP.getD 7 0) ||| (rawP.getD 5 0 &&& rawP.getD 7 0) ||| (rawP.getD 6 0 &&& rawP.getD 7 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
def CC : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [11, 9]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [21, 22]⟩]
set_option maxRecDepth 100000 in
lemma dec_f : ∀ x : Fin 8 → Bool, decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = f x := by decide +kernel
set_option maxRecDepth 100000 in
lemma CC_f : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨CC, 23⟩ (List.ofFn x) = f x := by decide +kernel
open PEqualNP.CircuitLowerBounds

def rowIndex (x : Fin 8 → Bool) : ℕ := 1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat + 16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat

abbrev ordered (positive a b : Bool) : Prop := (bif positive then a && !b else b && !a) = false

lemma inputOrder : ∀ (x : Fin 8 → Bool) (i : Fin 8), ordered (f x)
    (((rawP.getD i.val 0) &&& mz 0).testBit (rowIndex x)) (x i) := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel

lemma targetRow : ∀ x : Fin 8 → Bool, (tz 0).testBit (rowIndex x) = f x := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel

lemma orderOp : ∀ p d a b c e : Bool, ordered p a c → ordered p b e →
    ordered p (bif d then a || b else a && b) (bif d then c || e else c && e) := by decide

lemma orderTarget (a b : Bool) (h : ordered a a b) : b = a := by
  cases a <;> cases b <;> simp_all [ordered]

def monoGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def wires (gs : List Gate) (x : Fin 8 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

lemma wires_add (gs : List Gate) (g : Gate) (x : Fin 8 → Bool) :
    wires (gs ++ [g]) x = wires gs x ++ [g.op.eval (g.inputs.map fun i => (wires gs x).getD i false)] := by
  simp [wires, List.foldl_append]

lemma wires_len (gs : List Gate) (x : Fin 8 → Bool) : (wires gs x).length = 8 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => simp [wires_add, ih, Nat.add_assoc]

def realizes (gs : List Gate) (w : ℕ) : Prop :=
  ∃ i < 8 + gs.length, ∀ x : Fin 8 → Bool,
    ordered (f x) (w.testBit (rowIndex x)) ((wires gs x).getD i false)

lemma realizes_keep {gs : List Gate} {w : ℕ} (h : realizes gs w) (g : Gate) :
    realizes (gs ++ [g]) w := by
  obtain ⟨i, hi, hr⟩ := h
  refine ⟨i, by simp; omega, fun x => ?_⟩
  rw [wires_add, List.getD_append _ _ _ _ (by rw [wires_len]; exact hi)]
  exact hr x

def binaryGate (d : Bool) (i j : ℕ) : Gate := ⟨bif d then GateOp.or else GateOp.and, [i,j]⟩

lemma realizes_op {gs : List Gate} {a b : ℕ} (ha : realizes gs a) (hb : realizes gs b) (d : Bool) :
    ∃ g : Gate, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      realizes (gs ++ [g]) (op d a b) := by
  obtain ⟨i, _, hi⟩ := ha
  obtain ⟨j, _, hj⟩ := hb
  refine ⟨binaryGate d i j, by cases d <;> simp [binaryGate], 8 + gs.length, by simp, fun x => ?_⟩
  rw [wires_add, List.getD_append_right _ _ _ _ (by rw [wires_len]), wires_len, Nat.sub_self, op_bit]
  have h := orderOp (f x) d _ _ _ _ (hi x) (hj x)
  cases d <;> simpa [binaryGate, GateOp.eval] using h

def monoResult (q : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), monoGates gs ∧ gs.length ≤ q ∧
    ∀ x : Fin 8 → Bool, (wires gs x).getD o false = f x

lemma liveMono {k t : ℕ} {S : Finset ℕ} (h : Live Z0 (mz 0) (tz 0) k t S) :
    t = 0 → ∀ gs : List Gate, monoGates gs → (∀ a ∈ S, realizes gs a) → monoResult (gs.length + k) := by
  induction h with
  | stop =>
    intro _ gs hg hr
    obtain ⟨i, _, hi⟩ := hr (tz 0) (by simp)
    refine ⟨gs, i, hg, by omega, fun x => ?_⟩
    exact orderTarget _ _ (targetRow x ▸ hi x)
  | un _ ih => intro h; omega
  | @bi k t d a b U _ _ _ ih =>
    intro ht gs hg hr
    obtain ⟨g, hg', hw⟩ := realizes_op (hr a (by simp)) (hr b (by simp)) d
    have hnext : monoGates (gs ++ [g]) := by
      intro y hy
      rcases List.mem_append.1 hy with h | h
      · exact hg y h
      · obtain rfl := List.mem_singleton.1 h
        exact hg'
    have finish := ih ht (gs ++ [g]) hnext (by
      intro w hw'
      rcases Finset.mem_insert.1 hw' with e | e
      · exact e ▸ hw
      · exact realizes_keep (hr w (by simp [e])) g)
    convert finish using 1
    simp
    omega

lemma initialMono {k : ℕ} {S : Finset ℕ} (hs : (S : Set ℕ) ⊆ WZ [] 0)
    (hl : Live Z0 (mz 0) (tz 0) k 0 S) : monoResult k := by
  have h := liveMono hl rfl [] (by simp [monoGates]) (by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := hs ha
    simp only [rawL, List.map_nil, List.append_nil] at hw
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hw
    let j : Fin 8 := ⟨i, by simpa only [rawP_len] using hi⟩
    refine ⟨i, by simpa only [List.length_nil, Nat.add_zero] using j.isLt, fun x => ?_⟩
    have hget : rawP.getD i 0 = w := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact he
    have ht := inputOrder x j
    change ordered (f x) (((rawP.getD i 0) &&& mz 0).testBit (rowIndex x)) (x j) at ht
    rw [hget] at ht
    change ordered _ _ ((List.ofFn x).getD i false)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (List.ofFn x).length by simpa only [List.length_ofFn] using j.isLt)]
    simpa only [Option.getD_some, List.getElem_ofFn] using ht)
  simpa using h

inductive Steps (m T : ℕ) : ℕ → ℕ → Set ℕ → Prop
  | done {S} : T ∈ S → Steps m T 0 0 S
  | un {q u S a} : a ∈ S → Steps m T q u (insert (a ^^^ m) S) → Steps m T (q+1) (u+1) S
  | bi {q u S d a b} : a ∈ S → b ∈ S → Steps m T q u (insert (op d a b) S) → Steps m T (q+1) u S

lemma Steps.widen {m T q u S} (h : Steps m T q u S) :
    ∀ {S'}, S ⊆ S' → Steps m T q u S' := by
  induction h with
  | done h => intro _ hs; exact .done (hs h)
  | un ha _ ih => intro _ hs; exact .un (hs ha) (ih (Set.insert_subset_insert hs))
  | bi ha hb _ ih => intro _ hs; exact .bi (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

lemma Steps.liveCount {m T q u S} (h : Steps m T q u S) :
    ∃ k t, ∃ S0 : Finset ℕ, k ≤ q ∧ t ≤ u ∧ u + k ≤ q + t ∧
      (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  induction h with
  | @done S h => exact ⟨0, 0, {T}, le_rfl, le_rfl, le_rfl, by simpa using h, .stop⟩
  | @un q u S a ha _ ih =>
    obtain ⟨k,t,S1,hk,ht,hc,hs,hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k+1, t+1, insert a (S1.erase (a ^^^ m)), by omega, by omega, by omega, ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1,h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩
  | @bi q u S d a b ha hb _ ih =>
    obtain ⟨k,t,S1,hk,ht,hc,hs,hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).elim (fun e => e ▸ ha) id,hl⟩
      refine ⟨k+1,t,insert a (insert b (S1.erase (op d a b))),by omega,by omega,by omega,?_,.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩

section countProjection
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.stepIm {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S')
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) (q+1) (u+1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.widen (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.stepIm {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S')
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) (q+1) u (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.widen (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.stepKill {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a)
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) q u (C n (Im n S)) :=
  hs.widen (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.stepKill {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) q u (C n (Im n S)) :=
  hs.widen (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)

lemma Min.projectCount (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q u, u ≤ t ∧ q + (S.filter (Cst n)).card + t ≤ k + u ∧ Steps n (T &&& n) q u (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, 0, le_rfl, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q,u,hu',hq,hs⟩ := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q,u,by omega,?_,hu.stepKill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left ((Cst_neg hn).2 hc), Finset.card_insert_of_notMem (by simp [hf])] at hq
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q+1,u+1,by omega,?_,hu.stepIm hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q,u,hu',hq,hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q,u,hu',?_,hu.stepKill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q,u,hu',?_,hu.stepKill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q+1,u,hu',?_,hu.stepIm hs⟩
        rw [ite_eq_right hcb]; omega
end countProjection
lemma minimumInputLive {Z q : ℕ}
    (h0 : tz Z ≠ 0) (h1 : tz Z ≠ mz Z)
    (hs : Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ [] Z))) :
    ∃ k ≤ q, ∃ t, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] Z ∧
      Live Z0 (mz Z) (tz Z) k t S ∧
      ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) := by
  classical
  have hex : ∃ j, Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) := ⟨q,hs⟩
  obtain ⟨k,hk,t,S,hS,hl⟩ := (Nat.find_spec hex).live
  have heq := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have lower : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) :=
    fun j hj => Nat.find_min hex (by omega)
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl,fun j hj h => lower j hj (h.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w,_,rfl⟩ | h
    · rw [Nat.and_assoc,Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  obtain ⟨hz,ho⟩ := hm.proper hT h0 h1 hbd
  refine ⟨k, hk.trans (Nat.find_min' hex hs),t,S,?_,hl,lower⟩
  intro x hx
  rcases hS hx with h | h
  · exact h
  · simp at h; rcases h with rfl | rfl
    · exact absurd hx hz
    · exact absurd hx ho
namespace BinarySearch
noncomputable section core
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st z (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
def Cl (P : List ℕ) (T k t : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ j < P.length, ∀ q u, u ≤ t → q + b j + t < k + u →
    ¬ Steps (P.getD j 0) (T &&& P.getD j 0) q u (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k t z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k t b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k t b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q,u,hu,hq,hs⟩ := hm.projectCount p1 p2 p3
  have hqb : ¬ q + b j + t < k + u := fun h => hc j hj q u hu h hs
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
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k t z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k t z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have hcl' : Cl P T k t b' S' := by
    intro j hj q u hu hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q u hu ?_ (hb.stepKill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q+1) u hu ?_ (hb.stepIm hsol)
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
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k t z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
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
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
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
lemma hit_ht {k t z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k t z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
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
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
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
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
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
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k t z v S) (hl : Live R m T k' t S)
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
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
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
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
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
      r.length = S'.card ∧ StOk P T l k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) (t + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k t (z - (bif ka then a.c else 0)) r S' := by
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
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := b
  have hcl' : Cl P T k t b' S' := by
    intro j hj q u hu hq hsol
    by_cases hkill : a.c.testBit (5*j) = true
    · exact hcl j hj q u (by omega) (by dsimp [b'] at hq; omega)
        (hb.stepKill (X.hP j hj).1 (wa.cst hj hkill) hsol)
    · exact hcl j hj (q+1) (u+1) (by omega) (by dsimp [b'] at hq; omega)
        (hb.stepIm (X.hP j hj).1 hsol)
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    rw [pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st z (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) (t + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
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
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c) <;> simp
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
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) z = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) z <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_52898.X → L_meta_52898.X → Bool) → List L_meta_52898.X → Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k t z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
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
        have : a.s = c.s := congrArg L_meta_52898.X.s e
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
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k t z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_52898.X → L_meta_52898.X → Bool) → List L_meta_52898.X → Bool,
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
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52898.X.s e))
end sound
noncomputable section
end
noncomputable section
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
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
    have : Std.Symm (fun a b : L_meta_52898.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52898.X.s e)) hpb
end sound
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - t - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma rejectMinimum {Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hp : pOk Z Q = true) (hL : L - 1 - t ≤ 15) (hk : k < L)
    (hI : ∀ e ∈ Q, ∀ q u, u ≤ t → q < e.2 + u → ¬ Steps (mz e.1) (tz e.1) q u (C (mz e.1) (WZ [] e.1))) (hSW : (S : Set ℕ) ⊆ WZ [] Z)
    (hl : Live Z0 (mz Z) (tz Z) k t S)
    (lower : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)))
    (M : List (ℕ × ℕ)) (hMf : mFull M = true)
    (hchk : ∀ p ∈ M, chk [] Q Z (L-1) t p.1 p.2 = false) : False := by
  classical
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0,hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  have hE6 : ∀ e ∈ ([] : List (ℕ × ℕ)), e ∈ six := by simp
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl,fun j hj hs => lower j hj (hs.mono le_rfl (C_mono hSW))⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := hSW hx
    rw [Nat.and_assoc,Nat.and_self]
  obtain ⟨h0,h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q u, u ≤ t → q < e.2 + u →
      ¬ Steps (mz e.1) (tz Z &&& mz e.1) q u (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q u hu hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q u hu hq (hs.widen (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  have hpw : pwr [] Z = 0 ∨ pwr [] Z ∈ S := Or.inl rfl
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL [])
  set v := (avl (PZ Q) (mz Z) (rawL [])).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL [])) := List.filter_sublist
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
  have hcod : ∀ w ∈ v, w.r = RZ [] Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ [] Z := ⟨x, hx, rfl⟩
    change 3 = RZ [] Z (x &&& mz Z)
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
  have hcl : Cl (PZ Q) (tz Z) (L - 1) t (fun j => L - 1 - t - (Q.getD j (0, L - 1 - t)).2) S := by
    intro j hj q u hu hq
    obtain ⟨e1,e2⟩ := hPget j hj
    have memj : j < Q.length := by simpa [PZ] using hj
    have eqj : Q.getD j (0,L-1-t) = Q.getD j (0,L-1) := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem memj]
    change q + (L-1-t-(Q.getD j (0,L-1-t)).2) + t < L-1+u at hq
    rw [eqj] at hq
    rw [e1]
    exact hno _ e2 q u hu (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - t - e.2)) - sumc v) v S := by
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
  have hhas : hasP (pwr [] Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - t - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R [] Z) (RZ_R2 [] Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine lower q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

end BinarySearch
lemma Steps.signCount {m T q u S} (h : Steps m T q u S) : u ≤ q := by
  induction h <;> omega

def gradedRow (t : ℕ) (e : ℕ × ℕ) : ℕ × ℕ := (e.1,e.2+1-t)
def HasGrade (t : ℕ) (g : ℕ × ℕ) : Prop :=
  ∀ q u, u ≤ t → q < g.2 + u → ¬ Steps (mz g.1) (tz g.1) q u (C (mz g.1) (WZ [] g.1))

lemma gradeFromFloor {z h t : ℕ} (floor : Imp [] z h) (h0 : tz z ≠ 0) (h1 : tz z ≠ mz z)
    (no : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] z → Live Z0 (mz z) (tz z) h t S → False) :
    HasGrade t (gradedRow t (z,h)) := by
  intro q u hu hq steps
  change q < h+1-t+u at hq
  change Steps (mz z) (tz z) q u (C (mz z) (WZ [] z)) at steps
  have huq := steps.signCount
  by_cases cap : t ≤ h+1
  · obtain ⟨k,v,S,hk,hv,count,hS,hl⟩ := steps.liveCount
    have hlow : h ≤ k := by
      by_contra short
      exact floor k (by omega) (hl.sol.mono le_rfl hS)
    have ek : k = h := by omega
    have ev : v = t := by omega
    subst k v
    have hm : Min Z0 (mz z) (tz z) h t S := by
      refine ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl ?_)⟩
      rintro x (hx | hx)
      · exact hS hx
      · exact Or.inr hx
    have hbd : ∀ x ∈ S, x &&& mz z = x := by
      intro x hx
      rcases hS hx with ⟨w,_,rfl⟩ | c
      · rw [Nat.and_assoc,Nat.and_self]
      · simp at c; rcases c with rfl | rfl <;> simp
    obtain ⟨ha,hb⟩ := hm.proper (by simp only [tz,nl,Nat.and_assoc,Nat.and_self]) h0 h1 hbd
    apply no S _ hl
    intro x hx
    rcases hS hx with h | c
    · exact h
    · simp at c; rcases c with rfl | rfl
      · exact absurd hx ha
      · exact absurd hx hb
  · omega

noncomputable def gradeTest (t : ℕ) (before : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  let Q := pr (before.map (gradedRow t)) e.1
  pOk e.1 Q && (e.2+1 ≤ 15) &&
    (e.2 < t || !BinarySearch.chk [] Q e.1 e.2 t FF 1)

lemma checkedGrade {t : ℕ} {before : List (ℕ × ℕ)} {e : ℕ × ℕ}
    (floor : Imp [] e.1 e.2)
    (prior : ∀ x ∈ before, HasGrade t (gradedRow t x))
    (tested : gradeTest t before e = true) : HasGrade t (gradedRow t e) := by
  rcases e with ⟨z,h⟩
  let Q := pr (before.map (gradedRow t)) z
  change pOk z Q && decide (h+1 ≤ 15) && (decide (h < t) || !BinarySearch.chk [] Q z h t FF 1) = true at tested
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true'] at tested
  obtain ⟨⟨hp,hlim⟩,branch⟩ := tested
  have pn := hp
  simp only [pOk,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at pn
  obtain ⟨⟨p0,p1⟩,_⟩ := pn
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e,Nat.beq_refl] at h; simp at h
  apply gradeFromFloor floor (nb p0) (nb p1)
  intro S sw hl
  have hm : Min Z0 (mz z) (tz z) h t S :=
    ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl (C_mono sw))⟩
  rcases branch with lt | chk
  · have := hm.size.2; omega
  · refine BinarySearch.rejectMinimum (Q := Q) (L := h+1) hp (by omega) (by omega) ?_ sw hl floor [(FF,1)] ffull ?_
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hx)
      exact prior y hy
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      simpa using chk

lemma addGrades {t : ℕ} {before group : List (ℕ × ℕ)}
    (lower : ∀ e ∈ group, Imp [] e.1 e.2)
    (prior : ∀ e ∈ before, HasGrade t (gradedRow t e))
    (checks : group.all (gradeTest t before) = true) :
    ∀ e ∈ group, HasGrade t (gradedRow t e) :=
  fun e he => checkedGrade (lower e he) prior (List.all_eq_true.1 checks e he)

lemma joinGrades {t : ℕ} {a b : List (ℕ × ℕ)}
    (h1 : ∀ e ∈ a, HasGrade t (gradedRow t e))
    (h2 : ∀ e ∈ b, HasGrade t (gradedRow t e)) :
    ∀ e ∈ a ++ b, HasGrade t (gradedRow t e) :=
  fun e he => (List.mem_append.1 he).elim (h1 e) (h2 e)

lemma gradeWeak {z h t : ℕ} (floor : Imp [] z h) : HasGrade t (z,h-t) := by
  intro q u hu hq st
  change Steps (mz z) (tz z) q u (C (mz z) (WZ [] z)) at st
  change q < h-t+u at hq
  have huq := st.signCount
  obtain ⟨k,v,S,hk,_,_,hS,hl⟩ := st.liveCount
  exact floor k (by omega) (hl.sol.mono le_rfl hS)
open PEqualNP.CircuitLowerBounds
open scoped Classical in
noncomputable def countNot : List Gate → ℕ
  | [] => 0
  | g :: gs => (if g.op = GateOp.not then 1 else 0) + countNot gs

lemma countNotZero (gs : List Gate) (h : ∀ i : Fin gs.length, (gs.get i).op ≠ GateOp.not) : countNot gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hn : g.op ≠ GateOp.not := h ⟨0,by simp⟩
    have tail : ∀ i : Fin gs.length, (gs.get i).op ≠ GateOp.not := fun i => h i.succ
    simp [countNot,hn,ih tail]
lemma countNotAtMostOne (gs : List Gate)
    (h : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    countNot gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases hg : g.op = GateOp.not
    · have tail : ∀ i : Fin gs.length, (gs.get i).op ≠ GateOp.not := by
        intro i hi
        have he := h ⟨0,by simp⟩ i.succ hg hi
        have hv := congrArg Fin.val he
        simp at hv
      simp [countNot,hg,countNotZero gs tail]
    · have tail : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j := by
        intro i j hi hj
        exact Fin.succ_inj.mp (h i.succ j.succ hi hj)
      simpa [countNot,hg] using ih tail

lemma exSteps (m T : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k u, k ≤ gs.length ∧ u ≤ countNot gs ∧ Steps m T k u S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i,rfl⟩
    exact ⟨0,0,le_rfl,le_rfl,.done (getD_mem hw h0 i)⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → ∃ k u, k ≤ (g::gs).length ∧ u ≤ countNot (g::gs) ∧ Steps m T k u S := by
      intro h
      obtain ⟨k,u,hk,hu,st⟩ := ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append,List.mem_singleton] at hx
        exact hx.elim (hw x) (fun e => e ▸ h)) h0 hm hgs hT
      exact ⟨k,u,by simp; omega,by simp only [countNot]; omega,st⟩
    obtain ⟨k,u,hk,hu,go⟩ := ih (w ++ [gv m w g]) (insert (gv m w g) S) (fun x hx => by
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inr (hw x hx)
      · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop,_⟩ := hg g List.mem_cons_self
    obtain ⟨o,l⟩ := g
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact ⟨k+1,u,by simpa using hk,by simpa [countNot] using hu,.bi (d := false) (rd i) (rd j) go⟩
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact ⟨k+1,u,by simpa using hk,by simpa [countNot] using hu,.bi (d := true) (rd i) (rd j) go⟩
    · match l with
      | [] => exact stay hm
      | i :: _ => exact ⟨k+1,u+1,by simpa using hk,by simp [countNot]; omega,.un (rd i) go⟩

theorem stepsBridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f y) :
    ∃ k u, k ≤ D.size ∧ u ≤ countNot D.gates ∧ Steps (mz 0) (tz 0) k u (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact exSteps (mz 0) (tz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma compareShort {q u budget : ℕ} (hbudget : budget < 16) (hq : q ≤ budget) (hu : u ≤ 1)
    (st : Steps (mz 0) (tz 0) q u (C (mz 0) (WZ [] 0))) (floor : Imp [] 0 15)
    (no : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] 0 → Live Z0 (mz 0) (tz 0) 15 1 S → False) : monoResult budget := by
  obtain ⟨k,t,S,hk,ht,_,hS,hl⟩ := st.liveCount
  have hlow : 15 ≤ k := by
    by_contra bad
    exact floor k (by omega) (hl.sol.mono le_rfl hS)
  have he : k = 15 := by omega
  subst k
  have hm : Min Z0 (mz 0) (tz 0) 15 t S := by
    refine ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl ?_)⟩
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hT : tz 0 &&& mz 0 = tz 0 := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  have hbd : ∀ x ∈ S, x &&& mz 0 = x := by
    intro x hx
    rcases hS hx with ⟨w,_,rfl⟩ | c
    · rw [Nat.and_assoc,Nat.and_self]
    · simp at c; rcases c with rfl | rfl <;> simp
  obtain ⟨h0,h1⟩ := hm.proper hT (by decide +kernel) (by decide +kernel) hbd
  have sw : (S : Set ℕ) ⊆ WZ [] 0 := by
    intro x hx
    rcases hS hx with h | c
    · exact h
    · simp at c; rcases c with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  by_cases hz : t = 0
  · subst t
    obtain ⟨gs,out,hg,hlen,valid⟩ := initialMono sw hl
    exact ⟨gs,out,hg,by omega,valid⟩
  · have he : t = 1 := by omega
    exact False.elim (no S sw (he ▸ hl))

lemma consFloor {z l} {R : List (ℕ × ℕ)} (h : Imp [] z l) (tail : ∀ e ∈ R, Imp [] e.1 e.2) :
    ∀ e ∈ (z,l)::R, Imp [] e.1 e.2 := by
  intro e he
  rcases List.mem_cons.mp he with rfl | ht
  · exact h
  · exact tail _ ht
lemma consGrade {z l} {R : List (ℕ × ℕ)} (h : HasGrade 1 (z,l)) (tail : ∀ e ∈ R, HasGrade 1 e) :
    ∀ e ∈ (z,l)::R, HasGrade 1 e := by
  intro e he
  rcases List.mem_cons.mp he with rfl | ht
  · exact h
  · exact tail _ ht
def P5 : List (ℕ × ℕ) := []
def G5 : List (ℕ × ℕ) := []
lemma P5ok : ∀ e ∈ P5, Imp [] e.1 e.2 := by simp [P5]
lemma G5ok : ∀ e ∈ G5, HasGrade 1 e := by simp [G5]

noncomputable section
def fcEqW (a b : W) : Bool := Nat.beq a.s b.s && Nat.beq a.a b.a && Nat.beq a.b b.b && Nat.beq a.c b.c && Nat.beq a.r b.r
lemma fcEqW_sound {a b : W} (h : fcEqW a b = true) : a = b := by
  cases a; cases b
  simp only [fcEqW, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5]
def fcEqV (u : List W) : List W → Bool :=
  List.rec (motive := fun _ => List W → Bool)
    (fun v => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v)
    (fun a _ ih v => List.rec (motive := fun _ => Bool) false (fun b r _ => Bool.rec (motive := fun _ => Bool) false (ih r) (fcEqW a b)) v) u
lemma fcEqV_sound : ∀ (u v : List W), fcEqV u v = true → u = v := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v => exact Bool.noConfusion h
  | cons a u ih =>
    intro v h
    cases v with
    | nil => exact Bool.noConfusion h
    | cons b v =>
      have h' : Bool.rec (motive := fun _ => Bool) false (fcEqV u v) (fcEqW a b) = true := h
      cases hab : fcEqW a b with
      | false => rw [hab] at h'; exact Bool.noConfusion h'
      | true => rw [hab] at h'; rw [fcEqW_sound hab, ih v h']
def fcEqE (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) (a n k t z : ℕ) (v : List W) : Bool :=
  Nat.beq e.2.2.2.2.1 z && Nat.beq e.2.2.1 k && Nat.beq e.2.1 n && Nat.beq e.1 a && Nat.beq e.2.2.2.1 t && fcEqV e.2.2.2.2.2 v
lemma fcEqE_sound {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} {a n k t z : ℕ} {v : List W} (h : fcEqE e a n k t z v = true) : e = (a, n, k, t, z, v) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := e
  simp only [fcEqE, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h5, h3⟩, h2⟩, h1⟩, h4⟩, h6⟩ := h
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, fcEqV_sound _ _ h6]
def fcHit (T : List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) (a n k t z : ℕ) (v : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcEqE e a n k t z v)) T
lemma fcHit_sound {T : List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)} {a n k t z : ℕ} {v : List W} (h : fcHit T a n k t z v = true) : (a, n, k, t, z, v) ∈ T := by
  induction T with
  | nil => exact Bool.noConfusion h
  | cons e T ih =>
    have h' : Bool.rec (motive := fun _ => Bool) (fcHit T a n k t z v) true (fcEqE e a n k t z v) = true := h
    cases he : fcEqE e a n k t z v with
    | false => rw [he] at h'; exact List.mem_cons_of_mem _ (ih h')
    | true => rw [fcEqE_sound he]; exact List.mem_cons_self
def fcGet (L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (i : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ × List W) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) (fun _ => []) (fun b _ ih i => Nat.rec (motive := fun _ => List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) b (fun j _ => ih j) i) L i
lemma fcGet_mem : ∀ (L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (i : ℕ) (x : ℕ × ℕ × ℕ × ℕ × ℕ × List W), x ∈ fcGet L i → ∃ B ∈ L, x ∈ B := by
  intro L
  induction L with
  | nil => intro i x hx; exact absurd hx List.not_mem_nil
  | cons b L ih =>
    intro i x hx
    cases i with
    | zero => exact ⟨b, List.mem_cons_self, hx⟩
    | succ j =>
      obtain ⟨B, hB, hxB⟩ := ih j x hx
      exact ⟨B, List.mem_cons_of_mem _ hB, hxB⟩
def fcGetT (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (i : ℕ) : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) :=
  List.rec (motive := fun _ => ℕ → List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (fun _ => []) (fun b _ ih i => Nat.rec (motive := fun _ => List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) b (fun j _ => ih j) i) L i
lemma fcGetT_mem : ∀ (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (i : ℕ) (x : List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)), x ∈ fcGetT L i → ∃ B ∈ L, x ∈ B := by
  intro L
  induction L with
  | nil => intro i x hx; exact absurd hx List.not_mem_nil
  | cons b L ih =>
    intro i x hx
    cases i with
    | zero => exact ⟨b, List.mem_cons_self, hx⟩
    | succ j =>
      obtain ⟨B, hB, hxB⟩ := ih j x hx
      exact ⟨B, List.mem_cons_of_mem _ hB, hxB⟩
def fcKey (k z : ℕ) : ℕ := Nat.mod (Nat.add z k) 251
def fcW (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (a n : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool) (k t z : ℕ) (v : List W) : Bool :=
  st k fun k => st t fun t => st (fcKey k z) fun key =>
    Bool.rec (motive := fun _ => Bool) (F k t z v) false (fcHit (fcGet (fcGetT L (Nat.div key 16)) (Nat.mod key 16)) a n k t z v)
def fcOrig (l m g K : ℕ) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (look l m g e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2)
    (look1 l m g K e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2) (Nat.beq e.1 1)
def fcTV1 (l m g K : ℕ) (T : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : Prop := ∀ B ∈ T, ∀ e ∈ B, fcOrig l m g K e = false
def fcTV (l m g K : ℕ) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) : Prop := ∀ T ∈ L, fcTV1 l m g K T
lemma fcW_look {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (n : ℕ) :
    fcW L 0 n (look l m g n) = look l m g n := by
  funext k t z v
  simp only [fcW, st_eq]
  cases h : fcHit (fcGet (fcGetT L (Nat.div (fcKey k z) 16)) (Nat.mod (fcKey k z) 16)) 0 n k t z v with
  | false => rfl
  | true =>
    obtain ⟨B, hB, hx⟩ := fcGet_mem _ _ _ (fcHit_sound h)
    obtain ⟨T, hT', hBT⟩ := fcGetT_mem _ _ _ hB
    exact (hT T hT' B hBT _ hx).symm
lemma fcW_look1 {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (n : ℕ) :
    fcW L 1 n (look1 l m g K n) = look1 l m g K n := by
  funext k t z v
  simp only [fcW, st_eq]
  cases h : fcHit (fcGet (fcGetT L (Nat.div (fcKey k z) 16)) (Nat.mod (fcKey k z) 16)) 1 n k t z v with
  | false => rfl
  | true =>
    obtain ⟨B, hB, hx⟩ := fcGet_mem _ _ _ (fcHit_sound h)
    obtain ⟨T, hT', hBT⟩ := fcGetT_mem _ _ _ hB
    exact (hT T hT' B hBT _ hx).symm
def fcStepL (F : ℕ → ℕ → ℕ → List W → Bool) (l m g : ℕ) (k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv F l m g k t z v y)) true (Nat.ble v.length 1)
def fcStepL1 (F1 F : ℕ → ℕ → ℕ → List W → Bool) (l m g : ℕ) (k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv F l m g k t z v y) true
        (node (F1 (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)
def fcLook (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g : ℕ) (fuel : ℕ) : ℕ → ℕ → ℕ → List W → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → List W → Bool) (fun _ _ _ _ => true) (fun n ih => fcStepL (fcW L 0 n ih) l m g) fuel
def fcLook1 (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K : ℕ) (fuel : ℕ) : ℕ → ℕ → ℕ → List W → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → List W → Bool) (fun _ _ _ _ => true)
    (fun n ih => fcStepL1 (fcW L 1 n ih) (fcW L 0 K (fcLook L l m g K)) l m g) fuel
lemma fcLook_step (l m g n : ℕ) : look l m g (n + 1) = fcStepL (look l m g n) l m g := rfl
lemma fcLook1_step (l m g K n : ℕ) : look1 l m g K (n + 1) = fcStepL1 (look1 l m g K n) (look l m g K) l m g := rfl
lemma fcLook_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) :
    ∀ n, fcLook L l m g n = look l m g n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show fcStepL (fcW L 0 n (fcLook L l m g n)) l m g = look l m g (n + 1)
    rw [ih, fcW_look hT n, fcLook_step]
lemma fcLook1_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) :
    ∀ n, fcLook1 L l m g K n = look1 l m g K n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show fcStepL1 (fcW L 1 n (fcLook1 L l m g K n)) (fcW L 0 K (fcLook L l m g K)) l m g = look1 l m g K (n + 1)
    rw [ih, fcW_look1 hT n, fcLook_eq hT K, fcW_look hT K, fcLook1_step]
def fcTop (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (fcW L 0 K (fcLook L l m g K)) l m g k t z v y) (Nat.beq ph 1)) true
      (node (fcW L 1 K (fcLook1 L l m g K K) (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
lemma fcTop_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (H ph k t z : ℕ) (v : List W) :
    fcTop L l m g K H ph k t z v = topC l m g K H ph k t z v := by
  unfold fcTop topC
  rw [fcLook_eq hT K, fcW_look hT K, fcLook1_eq hT K, fcW_look1 hT K]
def fcStart (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => fcTop L l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def fcChk (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => fcStart L l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma fcChk_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {E Q : List (ℕ × ℕ)} {Z K : ℕ}
    (hT : fcTV (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K L) (t H ph : ℕ) :
    fcChk L E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [fcChk, chk, frc_eq, st_eq, fcStart, startv, fcTop_eq hT]
def fcFrcL {α : Type} (v : List α) : (List α → Bool) → Bool :=
  List.rec (motive := fun _ => (List α → Bool) → Bool) (fun h => h []) (fun e _ ih h => ih fun r => h (e :: r)) v
lemma fcFrcL_eq {α : Type} (v : List α) : ∀ h, fcFrcL v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons e v ih => intro h; exact ih (fun r => h (e :: r))
def fcFrcR (R : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) → Bool) → Bool) (fun h => h [])
    (fun b _ ih h => fcFrcL b fun b' => ih fun r => h (b' :: r)) R
lemma fcFrcR_eq (R : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : ∀ h, fcFrcR R h = h R := by
  induction R with
  | nil => intro h; rfl
  | cons b R ih =>
    intro h
    change fcFrcL b (fun b' => fcFrcR R (fun r => h (b' :: r))) = h (b :: R)
    rw [fcFrcL_eq, ih]
def fcFrcT (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) : (List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) → Bool) (fun h => h [])
    (fun T _ ih h => fcFrcR T fun T' => ih fun r => h (T' :: r)) L
lemma fcFrcT_eq (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) : ∀ h, fcFrcT L h = h L := by
  induction L with
  | nil => intro h; rfl
  | cons T L ih =>
    intro h
    change fcFrcR T (fun T' => fcFrcT L (fun r => h (T' :: r))) = h (T :: L)
    rw [fcFrcR_eq, ih]
def fcOne (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K : ℕ) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (fcLook L l m g e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2)
    (fcLook1 L l m g K e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2) (Nat.beq e.1 1)
lemma fcOne_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : fcOne L l m g K e = fcOrig l m g K e := by
  simp only [fcOne, fcOrig, fcLook_eq hT, fcLook1_eq hT]
def fcPut (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) (L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (i : ℕ) : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) :=
  List.rec (motive := fun _ => ℕ → List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (fun _ => [])
    (fun b t ih i => Nat.rec (motive := fun _ => List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) ((e :: b) :: t) (fun j _ => b :: ih j) i) L i
lemma fcPut_tv {l m g K : ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} (he : fcOrig l m g K e = false) :
    ∀ (L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (i : ℕ), fcTV1 l m g K L → fcTV1 l m g K (fcPut e L i) := by
  intro L
  induction L with
  | nil => intro i h; exact h
  | cons b L ih =>
    intro i h
    cases i with
    | zero =>
      intro B hB x hx
      have hB1 : B ∈ (e :: b) :: L := hB
      rcases List.mem_cons.1 hB1 with rfl | hB'
      · rcases List.mem_cons.1 hx with rfl | hx'
        · exact he
        · exact h b List.mem_cons_self x hx'
      · exact h B (List.mem_cons_of_mem _ hB') x hx
    | succ j =>
      intro B hB x hx
      have hB1 : B ∈ b :: fcPut e L j := hB
      rcases List.mem_cons.1 hB1 with rfl | hB'
      · exact h B List.mem_cons_self x hx
      · exact ih j (fun B' hB'' => h B' (List.mem_cons_of_mem _ hB'')) B hB' x hx
def fcPut2 (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (key : ℕ) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => ℕ → List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fun _ => [])
    (fun T t ih i => Nat.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fcPut e T (Nat.mod key 16) :: t) (fun j _ => T :: ih j) i) L (Nat.div key 16)
lemma fcPut2_aux {l m g K : ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} (he : fcOrig l m g K e = false) (r : ℕ) :
    ∀ (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (i : ℕ), fcTV l m g K L → fcTV l m g K (List.rec (motive := fun _ => ℕ → List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fun _ => [])
      (fun T t ih i => Nat.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fcPut e T r :: t) (fun j _ => T :: ih j) i) L i) := by
  intro L
  induction L with
  | nil => intro i h; exact h
  | cons T L ih =>
    intro i h
    cases i with
    | zero =>
      intro T' hT'
      have h1 : T' ∈ fcPut e T r :: L := hT'
      rcases List.mem_cons.1 h1 with rfl | h2
      · exact fcPut_tv he T r (h T List.mem_cons_self)
      · exact h T' (List.mem_cons_of_mem _ h2)
    | succ j =>
      intro T' hT'
      have h1 : T' ∈ T :: (List.rec (motive := fun _ => ℕ → List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fun _ => [])
        (fun T t ih i => Nat.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fcPut e T r :: t) (fun j _ => T :: ih j) i) L j) := hT'
      rcases List.mem_cons.1 h1 with rfl | h2
      · exact h T' List.mem_cons_self
      · exact ih j (fun T'' hT'' => h T'' (List.mem_cons_of_mem _ hT'')) T' h2
lemma fcPut2_tv {l m g K : ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} (he : fcOrig l m g K e = false) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (key : ℕ) (h : fcTV l m g K L) :
    fcTV l m g K (fcPut2 e L key) := fcPut2_aux he (Nat.mod key 16) L (Nat.div key 16) h
def fcAdd (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (E : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fun L => L) (fun e _ ih L => ih (fcPut2 e.2 L e.1)) E L
lemma fcAdd_tv {l m g K : ℕ} : ∀ (E : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))), fcTV l m g K L →
    (∀ e ∈ E, fcOrig l m g K e.2 = false) → fcTV l m g K (fcAdd L E) := by
  intro E
  induction E with
  | nil => intro L h _; exact h
  | cons e E ih =>
    intro L h hE
    exact ih (fcPut2 e.2 L e.1) (fcPut2_tv (hE e List.mem_cons_self) L e.1 h) (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))
def fcE0 : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) := List.replicate 16 (List.replicate 16 [])
lemma fcE0_tv {l m g K : ℕ} : fcTV l m g K fcE0 := by
  intro T hT B hB x hx
  rw [List.eq_of_mem_replicate hT] at hB
  rw [List.eq_of_mem_replicate hB] at hx
  exact absurd hx List.not_mem_nil
def fcD : W := ⟨0, 0, 0, 0, 0⟩
def fcNth (v : List W) (i : ℕ) : W :=
  List.rec (motive := fun _ => ℕ → W) (fun _ => fcD) (fun w _ ih i => Nat.rec (motive := fun _ => W) w (fun j _ => ih j) i) v i
def fcInsV (o : W) (v : List W) : List W :=
  List.rec (motive := fun _ => List W) [o] (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (o :: w :: t) (Nat.ble w.s o.s)) v
def fcRmV (x : ℕ) (v : List W) : List W :=
  List.rec (motive := fun _ => List W) [] (fun w _ ih => Bool.rec (motive := fun _ => List W) (w :: ih) ih (Nat.beq w.s x)) v
def fcSel (v : List W) (mask : ℕ) : List W :=
  List.rec (motive := fun _ => ℕ → List W) (fun _ => [])
    (fun w _ ih mk => Bool.rec (motive := fun _ => List W) (ih (Nat.div mk 2)) (w :: ih (Nat.div mk 2)) (Nat.beq (Nat.mod mk 2) 1)) v mask
def fcNotM (m : ℕ) (s : ℕ × List W) (a : W) (var : ℕ) : ℕ × List W :=
  Bool.rec (motive := fun _ => ℕ × List W)
    (Nat.sub (Nat.sub s.1 a.c) a.c, fcInsV ⟨Nat.xor a.s m, a.b, a.a, a.c, 0⟩ s.2)
    (Nat.sub s.1 a.c, fcRmV a.s (fcInsV ⟨Nat.xor a.s m, a.b, a.a, a.c, 0⟩ s.2)) (Nat.beq var 0)
def fcNotMF (m : ℕ) (s : ℕ × List W) (a : W) (var : ℕ) (cont : ℕ × List W → Bool) : Bool :=
  st (Nat.xor a.s m) fun os =>
  fcFrcL (fcInsV ⟨os, a.b, a.a, a.c, 0⟩ s.2) fun v1 =>
    Bool.rec (motive := fun _ => Bool)
      (st (Nat.sub (Nat.sub s.1 a.c) a.c) fun z2 => cont (z2, v1))
      (st (Nat.sub s.1 a.c) fun z2 => fcFrcL (fcRmV a.s v1) fun v2 => cont (z2, v2)) (Nat.beq var 0)
lemma fcNotMF_eq (m : ℕ) (s : ℕ × List W) (a : W) (var : ℕ) (cont : ℕ × List W → Bool) :
    fcNotMF m s a var cont = cont (fcNotM m s a var) := by
  simp only [fcNotMF, fcNotM, st_eq, fcFrcL_eq]
  cases Nat.beq var 0 <;> rfl
def fcGateM (s : ℕ × List W) (a b o : W) (var : ℕ) : ℕ × List W :=
  (fun z1 => (fun v1 =>
    Bool.rec (motive := fun _ => ℕ × List W)
      (Bool.rec (motive := fun _ => ℕ × List W)
        (Bool.rec (motive := fun _ => ℕ × List W) (Nat.sub (Nat.sub z1 a.c) b.c, v1) (Nat.sub z1 b.c, fcRmV a.s v1) (Nat.beq var 2))
        (Nat.sub z1 a.c, fcRmV b.s v1) (Nat.beq var 1))
      (z1, fcRmV b.s (fcRmV a.s v1)) (Nat.beq var 0))
    (fcInsV o s.2)) (Nat.sub (Nat.add s.1 (Nat.land a.c b.c)) o.c)
def fcGateMF (s : ℕ × List W) (a b : W) (os oa ob oc var : ℕ) (cont : ℕ × List W → Bool) : Bool :=
  st os fun os => st oc fun oc =>
  st (Nat.sub (Nat.add s.1 (Nat.land a.c b.c)) oc) fun z1 =>
  fcFrcL (fcInsV ⟨os, oa, ob, oc, 0⟩ s.2) fun v1 =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (st (Nat.sub (Nat.sub z1 a.c) b.c) fun z2 => cont (z2, v1))
          (st (Nat.sub z1 b.c) fun z2 => fcFrcL (fcRmV a.s v1) fun v2 => cont (z2, v2)) (Nat.beq var 2))
        (st (Nat.sub z1 a.c) fun z2 => fcFrcL (fcRmV b.s v1) fun v2 => cont (z2, v2)) (Nat.beq var 1))
      (fcFrcL (fcRmV b.s (fcRmV a.s v1)) fun v2 => cont (z1, v2)) (Nat.beq var 0)
lemma fcGateMF_eq (s : ℕ × List W) (a b : W) (os oa ob oc var : ℕ) (cont : ℕ × List W → Bool) :
    fcGateMF s a b os oa ob oc var cont = cont (fcGateM s a b ⟨os, oa, ob, oc, 0⟩ var) := by
  simp only [fcGateMF, fcGateM, st_eq, fcFrcL_eq]
  cases Nat.beq var 0 <;> cases Nat.beq var 1 <;> cases Nat.beq var 2 <;> rfl
def fcMove (m : ℕ) (s : ℕ × List W) (c : ℕ) : ℕ × List W :=
  (fun a => (fun b => (fun op => (fun var =>
    Bool.rec (motive := fun _ => ℕ × List W)
      (Bool.rec (motive := fun _ => ℕ × List W)
        (fcGateM s a b ⟨Nat.lor a.s b.s, Nat.land a.a b.a, Nat.lor a.b b.b, Nat.lor (Nat.land a.a b.a) (Nat.lor a.b b.b), 0⟩ var)
        (fcGateM s a b ⟨Nat.land a.s b.s, Nat.lor a.a b.a, Nat.land a.b b.b, Nat.lor (Nat.lor a.a b.a) (Nat.land a.b b.b), 0⟩ var)
        (Nat.beq op 0))
      (fcNotM m s a var) (Nat.beq op 2))
    (Nat.mod (Nat.div c 1024) 4)) (Nat.mod (Nat.div c 256) 4)) (fcNth s.2 (Nat.mod (Nat.div c 16) 16))) (fcNth s.2 (Nat.mod c 16))
def fcMoveF (m : ℕ) (s : ℕ × List W) (c : ℕ) (cont : ℕ × List W → Bool) : Bool :=
  (fun a b op var =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (st (Nat.land a.a b.a) fun oa => st (Nat.lor a.b b.b) fun ob =>
          fcGateMF s a b (Nat.lor a.s b.s) oa ob (Nat.lor oa ob) var cont)
        (st (Nat.lor a.a b.a) fun oa => st (Nat.land a.b b.b) fun ob =>
          fcGateMF s a b (Nat.land a.s b.s) oa ob (Nat.lor oa ob) var cont)
        (Nat.beq op 0))
      (fcNotMF m s a var cont) (Nat.beq op 2))
  (fcNth s.2 (Nat.mod c 16)) (fcNth s.2 (Nat.mod (Nat.div c 16) 16)) (Nat.mod (Nat.div c 256) 4) (Nat.mod (Nat.div c 1024) 4)
lemma fcMoveF_eq (m : ℕ) (s : ℕ × List W) (c : ℕ) (cont : ℕ × List W → Bool) :
    fcMoveF m s c cont = cont (fcMove m s c) := by
  simp only [fcMoveF, fcMove, st_eq, fcGateMF_eq, fcNotMF_eq]
  cases Nat.beq (Nat.mod (Nat.div c 256) 4) 2 <;> cases Nat.beq (Nat.mod (Nat.div c 256) 4) 0 <;> rfl
def fcRun (m : ℕ) (s : ℕ × List W) (cs : List ℕ) : ℕ × List W :=
  List.rec (motive := fun _ => ℕ × List W → ℕ × List W) (fun s => s) (fun c _ ih s => ih (fcMove m s c)) cs s
def fcRunF (m : ℕ) (s : ℕ × List W) (cs : List ℕ) (cont : ℕ × List W → Bool) : Bool :=
  List.rec (motive := fun _ => ℕ × List W → Bool) cont (fun c _ ih s => fcMoveF m s c ih) cs s
lemma fcRunF_eq (m : ℕ) (cs : List ℕ) : ∀ s cont, fcRunF m s cs cont = cont (fcRun m s cs) := by
  induction cs with
  | nil => intro s cont; rfl
  | cons c cs ih =>
    intro s cont
    change fcMoveF m s c (fun s' => fcRunF m s' cs cont) = _
    rw [fcMoveF_eq, ih]; rfl
def fcSt' (av : List W) (m B : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  (fun r => (fun s => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, s.1, s.2))
      (fcRun m (Nat.sub B (sumc r), r) p.2.2.2.2.2))
    (fcSel av p.2.2.2.2.1)
def fcStF (av : List W) (m B : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) (cont : ℕ × ℕ × ℕ × ℕ × ℕ × List W → Bool) : Bool :=
  st p.1 fun a => st p.2.1 fun n => st p.2.2.1 fun k => st p.2.2.2.1 fun t =>
  fcFrcL (fcSel av p.2.2.2.2.1) fun r =>
  st (Nat.sub B (sumc r)) fun z0 =>
    fcRunF m (z0, r) p.2.2.2.2.2 fun s => cont (a, n, k, t, s.1, s.2)
lemma fcStF_eq (av : List W) (m B : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) (cont) :
    fcStF av m B p cont = cont (fcSt' av m B p) := by
  simp only [fcStF, fcSt', st_eq, fcFrcL_eq, fcRunF_eq]
def fcSt (Q : List (ℕ × ℕ)) (Z K : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  fcSt' (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) p
def fcMv (n w : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => []) (fun _ ih w => Nat.mod w 4096 :: ih (Nat.div w 4096)) n w
def fcHd (mask w : ℕ) (more : List ℕ) : ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) :=
  (fun r => (Nat.mod w 256, Nat.mod r 2, Nat.mod (Nat.div r 2) 16, Nat.mod (Nat.div r 32) 16, Nat.mod (Nat.div r 512) 16, mask,
      List.append (fcMv (Nat.min 3 (Nat.mod (Nat.div r 8192) 8)) (Nat.div r 65536)) more)) (Nat.div w 256)
def fcDecS (mask : ℕ) (ws : List ℕ) : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)) :=
  List.rec (motive := fun _ => List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) [] (fun w _ ih => fcHd mask w [] :: ih) ws
def fcDecL (mask : ℕ) (ws : List ℕ) : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) (fun _ => [])
    (fun w _ ih hd => Nat.rec (motive := fun _ => List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) (ih (Nat.succ w))
      (fun h _ => fcHd mask h (fcMv (Nat.sub (Nat.mod (Nat.div h 2097152) 8) 3) w) :: ih 0) hd) ws 0
def fcBin (b : ℕ × List ℕ × List ℕ) : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)) := List.append (fcDecS b.1 b.2.1) (fcDecL b.1 b.2.2)
def fcAddF (av : List W) (m B : ℕ) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))))
    (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)))
    (cont : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) : Bool :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) cont
    (fun p _ ih L => st p.1 fun key => fcStF av m B p.2 fun e => ih (fcPut2 e L key)) P L
lemma fcAddF_eq (av : List W) (m B : ℕ) (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) :
    ∀ L cont, fcAddF av m B L P cont = cont (fcAdd L (P.map fun p => (p.1, fcSt' av m B p.2))) := by
  induction P with
  | nil => intro L cont; rfl
  | cons p P ih =>
    intro L cont
    change st p.1 (fun key => fcStF av m B p.2 (fun e => fcAddF av m B (fcPut2 e L key) P cont)) = _
    simp only [st_eq, fcStF_eq]
    exact ih _ _
def fcTab (Q : List (ℕ × ℕ)) (Z K : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) fcE0 (fun b _ ih => fcAdd ih ((fcBin b).map (fun p => (p.1, fcSt Q Z K p.2)))) bs
def fcTabF_go (av : List W) (m B : ℕ) (bs : List (ℕ × List ℕ × List ℕ))
    (c : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) : Bool :=
  List.rec (motive := fun _ => (List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) → Bool)
    (fun c => c fcE0)
    (fun b _ ih c => ih fun L => fcAddF av m B L (fcBin b) c) bs c
def fcTabF (av : List W) (m B : ℕ) (bs : List (ℕ × List ℕ × List ℕ))
    (cont : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) : Bool :=
  fcTabF_go av m B bs (fun L => fcFrcT L cont)
lemma fcTabF_aux (Q : List (ℕ × ℕ)) (Z K : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) :
    ∀ c, fcTabF_go (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) bs c = c (fcTab Q Z K bs) := by
  induction bs with
  | nil => intro c; rfl
  | cons b bs ih =>
    intro c
    exact (ih _).trans (fcAddF_eq _ _ _ _ _ _)
lemma fcTabF_eq (Q : List (ℕ × ℕ)) (Z K : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) (cont) :
    fcTabF (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) bs cont = cont (fcTab Q Z K bs) := by
  unfold fcTabF
  rw [fcTabF_aux, fcFrcT_eq]
def fcAnyP (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (av : List W) (m B l g K : ℕ) (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcStF av m B p.2 fun e => fcOne L l m g K e)) P
lemma fcAnyP_val {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {Q : List (ℕ × ℕ)} {Z K l g : ℕ}
    (hT : fcTV l (mz Z) g K L) :
    ∀ P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)),
      fcAnyP L (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) l g K P = false →
      ∀ e ∈ P.map (fun p => (p.1, fcSt Q Z K p.2)), fcOrig l (mz Z) g K e.2 = false := by
  intro P
  induction P with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a P ih =>
    intro h e he
    have h' : Bool.rec (motive := fun _ => Bool) (fcAnyP L (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) l g K P) true (fcStF (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) a.2 fun x => fcOne L l (mz Z) g K x) = false := h
    rw [fcStF_eq] at h'
    have h'' : Bool.rec (motive := fun _ => Bool) (fcAnyP L (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - e.2))) l g K P) true (fcOne L l (mz Z) g K (fcSt Q Z K a.2)) = false := h'
    have he1 : e ∈ (a.1, fcSt Q Z K a.2) :: P.map (fun p => (p.1, fcSt Q Z K p.2)) := he
    cases ha : fcOne L l (mz Z) g K (fcSt Q Z K a.2) with
    | true => rw [ha] at h''; exact Bool.noConfusion h''
    | false =>
      rw [ha] at h''
      rcases List.mem_cons.1 he1 with rfl | he'
      · rw [← fcOne_eq hT]; exact ha
      · exact ih h'' e he'
def fcBV (Q : List (ℕ × ℕ)) (Z K : ℕ) (b : ℕ × List ℕ × List ℕ) : Prop :=
  ∀ e ∈ (fcBin b).map (fun p => (p.1, fcSt Q Z K p.2)), fcOrig (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K e.2 = false
lemma fcTab_tv {Q : List (ℕ × ℕ)} {Z K : ℕ} : ∀ bs : List (ℕ × List ℕ × List ℕ), (∀ b ∈ bs, fcBV Q Z K b) →
    fcTV (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K (fcTab Q Z K bs) := by
  intro bs
  induction bs with
  | nil => intro _; exact fcE0_tv
  | cons b bs ih =>
    intro h
    exact fcAdd_tv _ _ (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) (h b List.mem_cons_self)
def fcAllB (bs : List (ℕ × List ℕ × List ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (b : ℕ × List ℕ × List ℕ) : Bool :=
  st (lz Z) fun l => st (mz Z) fun m => st (pL (Q.map fun _ => 16)) fun g =>
  st (pL (Q.map fun e => 16 + (K - e.2))) fun B =>
  frc (avl (PZ Q) m (rawL [])) fun av =>
    fcTabF av m B bs fun L => fcAnyP L av m B l g K (fcBin b)
lemma fcAllB_val {bs : List (ℕ × List ℕ × List ℕ)} {Q : List (ℕ × ℕ)} {Z K : ℕ} {b : ℕ × List ℕ × List ℕ}
    (hT : ∀ b' ∈ bs, fcBV Q Z K b') (h : fcAllB bs Q Z K b = false) : fcBV Q Z K b := by
  simp only [fcAllB, st_eq, frc_eq, fcTabF_eq] at h
  exact fcAnyP_val (fcTab_tv bs hT) _ h
def fcChkB (bs : List (ℕ × List ℕ × List ℕ)) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  st (lz Z) fun l => st (mz Z) fun m => st (pL (Q.map fun _ => 16)) fun g =>
  st (pL (Q.map fun e => 16 + (K - e.2))) fun B =>
  frc (avl (PZ Q) m (rawL E)) fun av =>
    fcTabF av m B bs fun L =>
      st (pwr E Z) fun p =>
        anySub (pos t) l av 0 (fun r => fcStart L l m g B K t p H ph r)
lemma fcChkB_eq {bs : List (ℕ × List ℕ × List ℕ)} {Q : List (ℕ × ℕ)} {Z K : ℕ} (hT : ∀ b ∈ bs, fcBV Q Z K b) (t H ph : ℕ) :
    fcChkB bs [] Q Z K t H ph = chk [] Q Z K t H ph := by
  simp only [fcChkB, st_eq, frc_eq, fcTabF_eq]
  have := fcChk_eq (E := []) (fcTab_tv bs hT) t H ph
  simpa only [fcChk, frc_eq, st_eq] using this
lemma fcBn {Q : List (ℕ × ℕ)} {Z K : ℕ} : ∀ b ∈ ([] : List (ℕ × List ℕ × List ℕ)), fcBV Q Z K b := fun _ hb => absurd hb List.not_mem_nil
lemma fcBc {Q : List (ℕ × ℕ)} {Z K : ℕ} {b : ℕ × List ℕ × List ℕ} {bs : List (ℕ × List ℕ × List ℕ)} (h : fcBV Q Z K b) (hs : ∀ b' ∈ bs, fcBV Q Z K b') :
    ∀ b' ∈ b :: bs, fcBV Q Z K b' := fun b' hb' => (List.mem_cons.1 hb').elim (fun e => e ▸ h) (hs b')
lemma gradeAll {G U : List (ℕ × ℕ)} (h : U.all (fun e => gradeTest 1 G e) = true)
    (hF : ∀ e ∈ U, Imp [] e.1 e.2) (hG : ∀ e ∈ G, HasGrade 1 e) : ∀ e ∈ U, HasGrade 1 e := fun e he =>
  checkedGrade (before := G) (hF e he) (fun x hx => by simpa [gradedRow] using hG x hx) (List.all_eq_true.1 h e he)
lemma apG {A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, HasGrade 1 e) (hb : ∀ e ∈ B, HasGrade 1 e) : ∀ e ∈ A ++ B, HasGrade 1 e := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
end

namespace BinarySearch
noncomputable section
def fcOrig (l m g K : ℕ) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (look l m g e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2)
    (look1 l m g K e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2) (Nat.beq e.1 1)
def fcTV1 (l m g K : ℕ) (T : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : Prop := ∀ B ∈ T, ∀ e ∈ B, fcOrig l m g K e = false
def fcTV (l m g K : ℕ) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) : Prop := ∀ T ∈ L, fcTV1 l m g K T
lemma fcW_look {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (n : ℕ) :
    fcW L 0 n (look l m g n) = look l m g n := by
  funext k t z v
  simp only [fcW, st_eq]
  cases h : fcHit (fcGet (fcGetT L (Nat.div (fcKey k z) 16)) (Nat.mod (fcKey k z) 16)) 0 n k t z v with
  | false => rfl
  | true =>
    obtain ⟨B, hB, hx⟩ := fcGet_mem _ _ _ (fcHit_sound h)
    obtain ⟨T, hT', hBT⟩ := fcGetT_mem _ _ _ hB
    exact (hT T hT' B hBT _ hx).symm
lemma fcW_look1 {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (n : ℕ) :
    fcW L 1 n (look1 l m g K n) = look1 l m g K n := by
  funext k t z v
  simp only [fcW, st_eq]
  cases h : fcHit (fcGet (fcGetT L (Nat.div (fcKey k z) 16)) (Nat.mod (fcKey k z) 16)) 1 n k t z v with
  | false => rfl
  | true =>
    obtain ⟨B, hB, hx⟩ := fcGet_mem _ _ _ (fcHit_sound h)
    obtain ⟨T, hT', hBT⟩ := fcGetT_mem _ _ _ hB
    exact (hT T hT' B hBT _ hx).symm
def fcStepL (F : ℕ → ℕ → ℕ → List W → Bool) (l m g : ℕ) (k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv F l m g k t z v y)) true (Nat.ble v.length 1)
def fcStepL1 (F1 F : ℕ → ℕ → ℕ → List W → Bool) (l m g : ℕ) (k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv F l m g k t z v y) true
        (node (F1 (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)
def fcLook (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g : ℕ) (fuel : ℕ) : ℕ → ℕ → ℕ → List W → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → List W → Bool) (fun _ _ _ _ => true) (fun n ih => fcStepL (fcW L 0 n ih) l m g) fuel
def fcLook1 (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K : ℕ) (fuel : ℕ) : ℕ → ℕ → ℕ → List W → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → List W → Bool) (fun _ _ _ _ => true)
    (fun n ih => fcStepL1 (fcW L 1 n ih) (fcW L 0 K (fcLook L l m g K)) l m g) fuel
lemma fcLook_step (l m g n : ℕ) : look l m g (n + 1) = fcStepL (look l m g n) l m g := rfl
lemma fcLook1_step (l m g K n : ℕ) : look1 l m g K (n + 1) = fcStepL1 (look1 l m g K n) (look l m g K) l m g := rfl
lemma fcLook_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) :
    ∀ n, fcLook L l m g n = look l m g n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show fcStepL (fcW L 0 n (fcLook L l m g n)) l m g = look l m g (n + 1)
    rw [ih, fcW_look hT n, fcLook_step]
lemma fcLook1_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) :
    ∀ n, fcLook1 L l m g K n = look1 l m g K n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show fcStepL1 (fcW L 1 n (fcLook1 L l m g K n)) (fcW L 0 K (fcLook L l m g K)) l m g = look1 l m g K (n + 1)
    rw [ih, fcW_look1 hT n, fcLook_eq hT K, fcW_look hT K, fcLook1_step]
def fcTop (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (fcW L 0 K (fcLook L l m g K)) l m g k t z v y) (Nat.beq ph 1)) true
      (node (fcW L 1 K (fcLook1 L l m g K K) (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
lemma fcTop_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (H ph k t z : ℕ) (v : List W) :
    fcTop L l m g K H ph k t z v = topC l m g K H ph k t z v := by
  unfold fcTop topC
  rw [fcLook_eq hT K, fcW_look hT K, fcLook1_eq hT K, fcW_look1 hT K]
def fcStart (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => fcTop L l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def fcChk (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => fcStart L l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - t - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma fcChk_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {E Q : List (ℕ × ℕ)} {Z K : ℕ}
    (hT : fcTV (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K L) (t H ph : ℕ) :
    fcChk L E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [fcChk, chk, frc_eq, st_eq, fcStart, startv, fcTop_eq hT]
def fcOne (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K : ℕ) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (fcLook L l m g e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2)
    (fcLook1 L l m g K e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2) (Nat.beq e.1 1)
lemma fcOne_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : fcOne L l m g K e = fcOrig l m g K e := by
  simp only [fcOne, fcOrig, fcLook_eq hT, fcLook1_eq hT]
lemma fcPut_tv {l m g K : ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} (he : fcOrig l m g K e = false) :
    ∀ (L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (i : ℕ), fcTV1 l m g K L → fcTV1 l m g K (fcPut e L i) := by
  intro L
  induction L with
  | nil => intro i h; exact h
  | cons b L ih =>
    intro i h
    cases i with
    | zero =>
      intro B hB x hx
      have hB1 : B ∈ (e :: b) :: L := hB
      rcases List.mem_cons.1 hB1 with rfl | hB'
      · rcases List.mem_cons.1 hx with rfl | hx'
        · exact he
        · exact h b List.mem_cons_self x hx'
      · exact h B (List.mem_cons_of_mem _ hB') x hx
    | succ j =>
      intro B hB x hx
      have hB1 : B ∈ b :: fcPut e L j := hB
      rcases List.mem_cons.1 hB1 with rfl | hB'
      · exact h B List.mem_cons_self x hx
      · exact ih j (fun B' hB'' => h B' (List.mem_cons_of_mem _ hB'')) B hB' x hx
lemma fcPut2_aux {l m g K : ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} (he : fcOrig l m g K e = false) (r : ℕ) :
    ∀ (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (i : ℕ), fcTV l m g K L → fcTV l m g K (List.rec (motive := fun _ => ℕ → List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fun _ => [])
      (fun T t ih i => Nat.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fcPut e T r :: t) (fun j _ => T :: ih j) i) L i) := by
  intro L
  induction L with
  | nil => intro i h; exact h
  | cons T L ih =>
    intro i h
    cases i with
    | zero =>
      intro T' hT'
      have h1 : T' ∈ fcPut e T r :: L := hT'
      rcases List.mem_cons.1 h1 with rfl | h2
      · exact fcPut_tv he T r (h T List.mem_cons_self)
      · exact h T' (List.mem_cons_of_mem _ h2)
    | succ j =>
      intro T' hT'
      have h1 : T' ∈ T :: (List.rec (motive := fun _ => ℕ → List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fun _ => [])
        (fun T t ih i => Nat.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (fcPut e T r :: t) (fun j _ => T :: ih j) i) L j) := hT'
      rcases List.mem_cons.1 h1 with rfl | h2
      · exact h T' List.mem_cons_self
      · exact ih j (fun T'' hT'' => h T'' (List.mem_cons_of_mem _ hT'')) T' h2
lemma fcPut2_tv {l m g K : ℕ} {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} (he : fcOrig l m g K e = false) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (key : ℕ) (h : fcTV l m g K L) :
    fcTV l m g K (fcPut2 e L key) := fcPut2_aux he (Nat.mod key 16) L (Nat.div key 16) h
lemma fcAdd_tv {l m g K : ℕ} : ∀ (E : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))), fcTV l m g K L →
    (∀ e ∈ E, fcOrig l m g K e.2 = false) → fcTV l m g K (fcAdd L E) := by
  intro E
  induction E with
  | nil => intro L h _; exact h
  | cons e E ih =>
    intro L h hE
    exact ih (fcPut2 e.2 L e.1) (fcPut2_tv (hE e List.mem_cons_self) L e.1 h) (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))
lemma fcE0_tv {l m g K : ℕ} : fcTV l m g K fcE0 := by
  intro T hT B hB x hx
  rw [List.eq_of_mem_replicate hT] at hB
  rw [List.eq_of_mem_replicate hB] at hx
  exact absurd hx List.not_mem_nil
def fcNotM (m : ℕ) (s : ℕ × List W) (a : W) (var : ℕ) : ℕ × List W :=
  Bool.rec (motive := fun _ => ℕ × List W)
    (Nat.sub s.1 a.c, fcInsV ⟨Nat.xor a.s m, a.b, a.a, a.c, 0⟩ s.2)
    (s.1, fcRmV a.s (fcInsV ⟨Nat.xor a.s m, a.b, a.a, a.c, 0⟩ s.2)) (Nat.beq var 0)
def fcNotMF (m : ℕ) (s : ℕ × List W) (a : W) (var : ℕ) (cont : ℕ × List W → Bool) : Bool :=
  st (Nat.xor a.s m) fun os =>
  fcFrcL (fcInsV ⟨os, a.b, a.a, a.c, 0⟩ s.2) fun v1 =>
    Bool.rec (motive := fun _ => Bool)
      (st (Nat.sub s.1 a.c) fun z2 => cont (z2, v1))
      (fcFrcL (fcRmV a.s v1) fun v2 => cont (s.1, v2)) (Nat.beq var 0)
lemma fcNotMF_eq (m : ℕ) (s : ℕ × List W) (a : W) (var : ℕ) (cont : ℕ × List W → Bool) :
    fcNotMF m s a var cont = cont (fcNotM m s a var) := by
  simp only [fcNotMF, fcNotM, st_eq, fcFrcL_eq]
  cases Nat.beq var 0 <;> rfl
def fcMove (m : ℕ) (s : ℕ × List W) (c : ℕ) : ℕ × List W :=
  (fun a => (fun b => (fun op => (fun var =>
    Bool.rec (motive := fun _ => ℕ × List W)
      (Bool.rec (motive := fun _ => ℕ × List W)
        (fcGateM s a b ⟨Nat.lor a.s b.s, Nat.land a.a b.a, Nat.lor a.b b.b, Nat.lor (Nat.land a.a b.a) (Nat.lor a.b b.b), 0⟩ var)
        (fcGateM s a b ⟨Nat.land a.s b.s, Nat.lor a.a b.a, Nat.land a.b b.b, Nat.lor (Nat.lor a.a b.a) (Nat.land a.b b.b), 0⟩ var)
        (Nat.beq op 0))
      (fcNotM m s a var) (Nat.beq op 2))
    (Nat.mod (Nat.div c 1024) 4)) (Nat.mod (Nat.div c 256) 4)) (fcNth s.2 (Nat.mod (Nat.div c 16) 16))) (fcNth s.2 (Nat.mod c 16))
def fcMoveF (m : ℕ) (s : ℕ × List W) (c : ℕ) (cont : ℕ × List W → Bool) : Bool :=
  (fun a b op var =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (st (Nat.land a.a b.a) fun oa => st (Nat.lor a.b b.b) fun ob =>
          fcGateMF s a b (Nat.lor a.s b.s) oa ob (Nat.lor oa ob) var cont)
        (st (Nat.lor a.a b.a) fun oa => st (Nat.land a.b b.b) fun ob =>
          fcGateMF s a b (Nat.land a.s b.s) oa ob (Nat.lor oa ob) var cont)
        (Nat.beq op 0))
      (fcNotMF m s a var cont) (Nat.beq op 2))
  (fcNth s.2 (Nat.mod c 16)) (fcNth s.2 (Nat.mod (Nat.div c 16) 16)) (Nat.mod (Nat.div c 256) 4) (Nat.mod (Nat.div c 1024) 4)
lemma fcMoveF_eq (m : ℕ) (s : ℕ × List W) (c : ℕ) (cont : ℕ × List W → Bool) :
    fcMoveF m s c cont = cont (fcMove m s c) := by
  simp only [fcMoveF, fcMove, st_eq, fcGateMF_eq, fcNotMF_eq]
  cases Nat.beq (Nat.mod (Nat.div c 256) 4) 2 <;> cases Nat.beq (Nat.mod (Nat.div c 256) 4) 0 <;> rfl
def fcRun (m : ℕ) (s : ℕ × List W) (cs : List ℕ) : ℕ × List W :=
  List.rec (motive := fun _ => ℕ × List W → ℕ × List W) (fun s => s) (fun c _ ih s => ih (fcMove m s c)) cs s
def fcRunF (m : ℕ) (s : ℕ × List W) (cs : List ℕ) (cont : ℕ × List W → Bool) : Bool :=
  List.rec (motive := fun _ => ℕ × List W → Bool) cont (fun c _ ih s => fcMoveF m s c ih) cs s
lemma fcRunF_eq (m : ℕ) (cs : List ℕ) : ∀ s cont, fcRunF m s cs cont = cont (fcRun m s cs) := by
  induction cs with
  | nil => intro s cont; rfl
  | cons c cs ih =>
    intro s cont
    change fcMoveF m s c (fun s' => fcRunF m s' cs cont) = _
    rw [fcMoveF_eq, ih]; rfl
def fcSt' (av : List W) (m B : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  (fun r => (fun s => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, s.1, s.2))
      (fcRun m (Nat.sub B (sumc r), r) p.2.2.2.2.2))
    (fcSel av p.2.2.2.2.1)
def fcStF (av : List W) (m B : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) (cont : ℕ × ℕ × ℕ × ℕ × ℕ × List W → Bool) : Bool :=
  st p.1 fun a => st p.2.1 fun n => st p.2.2.1 fun k => st p.2.2.2.1 fun t =>
  fcFrcL (fcSel av p.2.2.2.2.1) fun r =>
  st (Nat.sub B (sumc r)) fun z0 =>
    fcRunF m (z0, r) p.2.2.2.2.2 fun s => cont (a, n, k, t, s.1, s.2)
lemma fcStF_eq (av : List W) (m B : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) (cont) :
    fcStF av m B p cont = cont (fcSt' av m B p) := by
  simp only [fcStF, fcSt', st_eq, fcFrcL_eq, fcRunF_eq]
def fcSt (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  fcSt' (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) p
def fcAddF (av : List W) (m B : ℕ) (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))))
    (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)))
    (cont : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) : Bool :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) cont
    (fun p _ ih L => st p.1 fun key => fcStF av m B p.2 fun e => ih (fcPut2 e L key)) P L
lemma fcAddF_eq (av : List W) (m B : ℕ) (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) :
    ∀ L cont, fcAddF av m B L P cont = cont (fcAdd L (P.map fun p => (p.1, fcSt' av m B p.2))) := by
  induction P with
  | nil => intro L cont; rfl
  | cons p P ih =>
    intro L cont
    change st p.1 (fun key => fcStF av m B p.2 (fun e => fcAddF av m B (fcPut2 e L key) P cont)) = _
    simp only [st_eq, fcStF_eq]
    exact ih _ _
def fcTab (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) fcE0 (fun b _ ih => fcAdd ih ((fcBin b).map (fun p => (p.1, fcSt Q Z K t0 p.2)))) bs
def fcTabF_go (av : List W) (m B : ℕ) (bs : List (ℕ × List ℕ × List ℕ))
    (c : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) : Bool :=
  List.rec (motive := fun _ => (List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) → Bool)
    (fun c => c fcE0)
    (fun b _ ih c => ih fun L => fcAddF av m B L (fcBin b) c) bs c
def fcTabF (av : List W) (m B : ℕ) (bs : List (ℕ × List ℕ × List ℕ))
    (cont : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) : Bool :=
  fcTabF_go av m B bs (fun L => fcFrcT L cont)
lemma fcTabF_aux (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) :
    ∀ c, fcTabF_go (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) bs c = c (fcTab Q Z K t0 bs) := by
  induction bs with
  | nil => intro c; rfl
  | cons b bs ih =>
    intro c
    exact (ih _).trans (fcAddF_eq _ _ _ _ _ _)
lemma fcTabF_eq (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) (cont) :
    fcTabF (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) bs cont = cont (fcTab Q Z K t0 bs) := by
  unfold fcTabF
  rw [fcTabF_aux, fcFrcT_eq]
def fcAnyP (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (av : List W) (m B l g K : ℕ) (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcStF av m B p.2 fun e => fcOne L l m g K e)) P
lemma fcAnyP_val {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {Q : List (ℕ × ℕ)} {Z K t0 l g : ℕ}
    (hT : fcTV l (mz Z) g K L) :
    ∀ P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)),
      fcAnyP L (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) l g K P = false →
      ∀ e ∈ P.map (fun p => (p.1, fcSt Q Z K t0 p.2)), fcOrig l (mz Z) g K e.2 = false := by
  intro P
  induction P with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a P ih =>
    intro h e he
    have h' : Bool.rec (motive := fun _ => Bool) (fcAnyP L (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) l g K P) true (fcStF (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) a.2 fun x => fcOne L l (mz Z) g K x) = false := h
    rw [fcStF_eq] at h'
    have h'' : Bool.rec (motive := fun _ => Bool) (fcAnyP L (avl (PZ Q) (mz Z) (rawL [])) (mz Z) (pL (Q.map fun e => 16 + (K - t0 - e.2))) l g K P) true (fcOne L l (mz Z) g K (fcSt Q Z K t0 a.2)) = false := h'
    have he1 : e ∈ (a.1, fcSt Q Z K t0 a.2) :: P.map (fun p => (p.1, fcSt Q Z K t0 p.2)) := he
    cases ha : fcOne L l (mz Z) g K (fcSt Q Z K t0 a.2) with
    | true => rw [ha] at h''; exact Bool.noConfusion h''
    | false =>
      rw [ha] at h''
      rcases List.mem_cons.1 he1 with rfl | he'
      · rw [← fcOne_eq hT]; exact ha
      · exact ih h'' e he'
def fcBV (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (b : ℕ × List ℕ × List ℕ) : Prop :=
  ∀ e ∈ (fcBin b).map (fun p => (p.1, fcSt Q Z K t0 p.2)), fcOrig (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K e.2 = false
lemma fcTab_tv {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} : ∀ bs : List (ℕ × List ℕ × List ℕ), (∀ b ∈ bs, fcBV Q Z K t0 b) →
    fcTV (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K (fcTab Q Z K t0 bs) := by
  intro bs
  induction bs with
  | nil => intro _; exact fcE0_tv
  | cons b bs ih =>
    intro h
    exact fcAdd_tv _ _ (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) (h b List.mem_cons_self)
def fcAllB (bs : List (ℕ × List ℕ × List ℕ)) (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (b : ℕ × List ℕ × List ℕ) : Bool :=
  st (lz Z) fun l => st (mz Z) fun m => st (pL (Q.map fun _ => 16)) fun g =>
  st (pL (Q.map fun e => 16 + (K - t0 - e.2))) fun B =>
  frc (avl (PZ Q) m (rawL [])) fun av =>
    fcTabF av m B bs fun L => fcAnyP L av m B l g K (fcBin b)
lemma fcAllB_val {bs : List (ℕ × List ℕ × List ℕ)} {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} {b : ℕ × List ℕ × List ℕ}
    (hT : ∀ b' ∈ bs, fcBV Q Z K t0 b') (h : fcAllB bs Q Z K t0 b = false) : fcBV Q Z K t0 b := by
  simp only [fcAllB, st_eq, frc_eq, fcTabF_eq] at h
  exact fcAnyP_val (fcTab_tv bs hT) _ h
def fcChkB (bs : List (ℕ × List ℕ × List ℕ)) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  st (lz Z) fun l => st (mz Z) fun m => st (pL (Q.map fun _ => 16)) fun g =>
  st (pL (Q.map fun e => 16 + (K - t - e.2))) fun B =>
  frc (avl (PZ Q) m (rawL E)) fun av =>
    fcTabF av m B bs fun L =>
      st (pwr E Z) fun p =>
        anySub (pos t) l av 0 (fun r => fcStart L l m g B K t p H ph r)
lemma fcChkB_eq {bs : List (ℕ × List ℕ × List ℕ)} {Q : List (ℕ × ℕ)} {Z K t : ℕ} (hT : ∀ b ∈ bs, fcBV Q Z K t b) (H ph : ℕ) :
    fcChkB bs [] Q Z K t H ph = chk [] Q Z K t H ph := by
  simp only [fcChkB, st_eq, frc_eq, fcTabF_eq]
  have := fcChk_eq (E := []) (fcTab_tv bs hT) t H ph
  simpa only [fcChk, frc_eq, st_eq] using this
lemma fcBn {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} : ∀ b ∈ ([] : List (ℕ × List ℕ × List ℕ)), fcBV Q Z K t0 b := fun _ hb => absurd hb List.not_mem_nil
lemma fcBc {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} {b : ℕ × List ℕ × List ℕ} {bs : List (ℕ × List ℕ × List ℕ)} (h : fcBV Q Z K t0 b) (hs : ∀ b' ∈ bs, fcBV Q Z K t0 b') :
    ∀ b' ∈ b :: bs, fcBV Q Z K t0 b' := fun b' hb' => (List.mem_cons.1 hb').elim (fun e => e ▸ h) (hs b')
end
end BinarySearch

def P3r : List (ℕ × ℕ) := [(7,7),(11,6),(13,7),(14,7),(19,7),(21,8),(22,6),(25,7),(26,8),(28,6),(35,6),(37,8),(38,7),(41,6),(42,6),(44,7),(49,8),(50,7),(52,8),(56,7),(67,7),(69,7),(70,7),(73,7),(74,8),(76,7),(81,8),(82,8),(84,8),(88,8),(97,7),(98,7),(100,7),(104,7),(112,8),(131,7),(133,7),(134,6),(137,7),(138,7),(140,6),(145,7),(146,6),(148,6),(152,6),(161,7),(162,7),(164,8),(168,7),(176,7),(193,7),(194,7),(196,7),(200,7),(208,8),(224,6)]
def P3 : List (ℕ × ℕ) := P3r ++ P5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P3r_ok : ∀ e ∈ P3r, Imp [] e.1 e.2 := okAll (by decide +kernel) P5ok
lemma P3ok : ∀ e ∈ P3, Imp [] e.1 e.2 := apI P3r_ok P5ok
def G3 : List (ℕ × ℕ) := P3r ++ G5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G3r_ok : ∀ e ∈ P3r, HasGrade 1 e := gradeAll (by decide +kernel) P3r_ok G5ok
lemma G3ok : ∀ e ∈ G3, HasGrade 1 e := apG G3r_ok G5ok

def P2a : List (ℕ × ℕ) := [(3,10),(5,10),(6,9),(9,10),(10,10),(12,9),(17,10),(18,10),(20,9),(24,10),(33,9),(34,9),(36,10),(40,9),(48,10),(65,10),(66,10),(68,10),(72,10)]
def P2b : List (ℕ × ℕ) := [(96,10),(129,10),(130,10),(132,9),(136,10),(144,9),(160,10),(192,10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P2a_ok : ∀ e ∈ P2a, Imp [] e.1 e.2 := okAll (by decide +kernel) P3ok
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P2b_ok : ∀ e ∈ P2b, Imp [] e.1 e.2 := okAll (by decide +kernel) P3ok
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G2a_ok : ∀ e ∈ P2a, HasGrade 1 e := gradeAll (by decide +kernel) P2a_ok G3ok
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G2b_ok : ∀ e ∈ P2b, HasGrade 1 e := gradeAll (by decide +kernel) P2b_ok G3ok
set_option maxHeartbeats 0 in
def fba_p80_0_0 : ℕ × List ℕ × List ℕ := (63,[667257447842378177,671761047469748692,662754947726635457,676265746608746800,662756047238263252,676266846120374595,667260746377261360,671764346004631875,676899202745299392,681684277349380513,681966851837718964,393737643917111599,162783828186193,165121129256014,165120860820539,164021349192794,
165189865510084,164982851441733,163883339813988,161684316558550,676548458821252275,100156976270472282,681122426907587764,681121327395959969,676617727768589504,676547359309624480,672043759682254015,104943219390870574,672043759665476698,676547359292847163,104661675694683315,676548458804474958,
104660576183055520,104943219374093508,104661675677905998,104660576166278203,671973391206511807,676476990833882272,676830002785874990,676759634293355716,676759634310132782,671973391189734490,676476990817104955,676478090613945523,100156976287249599,676830002769097924,676478090597168206,681403970603775023,
163952344503508,163952612938831,165052124566576,164983388312774,163883876685029,164983656748249,165052393002051,164983119877200,163883608249455,162784096621660,165051856131253,162852832875713,681121328201266234,676617728842331194,681403970872210490,676617728859108511,
681121328218043551,681122427444458554,681122427461235871,681403970888987807],[676829934085263160,357,964778697787756345,357,383814345856962361,2405,379310746229591865,2405,667542290360749982,1381,964778766524010398,357,672045889988120478,1380,100088737312067486,3412,
383814414593216414,2405,100088668575813433,3412,672045821251866425,1380,379310814965845918,2405,667542221624495929,1381,676899203821129529,374,681685377416744862,374,672254866185310110,2405,
676899203821129529,373,681684278156775225,374,100438451249270585,2405,100438451266047902,2405,681684278173552542,374,667542290362839709,1456467,676828834288422814,1381,681685377399967545,374,
672254866168532793,2405,379310746231681592,9777491,676899203837906846,373,676899203837906846,374,379310814967935645,9777491,965060309951762334,374,965060309934985017,374,676828834271645497,1381,
667542221626585656,1456467,99807193330667310,3412,95302494191669171,3411,90797795052670880,3411,86293095913672639,3395])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p80_0_0 : fcAllB [] (pr P3 80) 80 10 fba_p80_0_0 = false := by decide +kernel
lemma fva_p80_0_0 : fcBV (pr P3 80) 80 10 fba_p80_0_0 := fcAllB_val (fcBn) fka_p80_0_0
set_option maxHeartbeats 0 in
def fba_p80_0_1 : ℕ × List ℕ × List ℕ := (63,[233358730793922,235695193002820,235626473526065,234458242421717,86293095911584213,90797795050582352,95302494189580643,99807193328578884,234528069194554,676829934083174713,105507268604260665,388882201139278137,677111409059885369,105507268570706372,388882201122500910,105506100624814515,
105223526119698747,676828834286334368,677111408774672819,676828834269557051,105223526136476064,105507268587483438,677111408757895502,100438451263959487,100438451247182170,388882201105723844,672254866183221695,672254866166444378,105506100608037198,964778697785667898,964778766521921951,960557672378200378,
960557741114454431,964778697248797108,964777666456646049,964778765968273844,960557740829241647,960554373574881728,960554442294358464,960557672109764911,964777597737169313,965270316922237242,681965753131397434,681684278154686778,681966852374589754,681685377397879098,965270316939014559,681685377414656415,
681966852391367071,393737644202324383,393737644185547066,681684278171464095,681965753148174751,965271416719077791,965060309932896570,676899203835818399,965340685397979450,393735377264898463,393455001799815583,965271416702300474,965060309949673887,965340685414756767,676899203819041082,393735377248121146,
393455001783038266],[95865444681962691,2388,95865513418216493,2388,379310746229593177,339,379310814965847230,339,672045821251867725,355,667542221624497210,355,672045889988121778,355,667542290360751263,355])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p80_0_1 : fcAllB [fba_p80_0_0] (pr P3 80) 80 10 fba_p80_0_1 = false := by decide +kernel
lemma fva_p80_0_1 : fcBV (pr P3 80) 80 10 fba_p80_0_1 := fcAllB_val (fcBc fva_p80_0_0 (fcBn)) fka_p80_0_1
set_option maxHeartbeats 0 in
def fba_p80_0_2 : ℕ × List ℕ × List ℕ := (63,[162852547662673,163952059290468,165051570918213,161821755511766,162921267139409,164020778767204,165120290394949,161753036035030,100088668573725007,95865513416126798,100088737309979060,95865444679872996,93652839895908,94752619959109,91453279769558,92553059832657,
234528052417327,234527230333787,235558576133044,235558307697569,235557754049462,234527247111104,234526961898320,235558290920252,234528035640261,235558559355727,94958828721092,164090068669274,165258299773755,165327287685966,667542221622407483,667542290358661536,
672045889986032051,677111271587377604,388600588438401440,388882063415112115,676829796610666948,379310814963757503,383814414591127999,672045821249777998,676829865346920750,677111340323631406,383814345854873946,379310746227503450,388881994678858062,388600519702147387,235695763428154,235627312386874],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p80_0_2 : fcAllB [fba_p80_0_0,fba_p80_0_1] (pr P3 80) 80 10 fba_p80_0_2 = false := by decide +kernel
lemma fva_p80_0_2 : fcBV (pr P3 80) 80 10 fba_p80_0_2 := fcAllB_val (fcBc fva_p80_0_0 (fcBc fva_p80_0_1 (fcBn))) fka_p80_0_2
set_option maxHeartbeats 0 in
def fba_p80_0_3 : ℕ × List ℕ × List ℕ := (63,[164089783456724,162990255051612,164089766679407,165189278307152,94890075689776,94821356213173,165327270908739,92621779309404,93790295626575,164158754591717,165258266219462,93721576149972,165258282996528,93721559372655,93790278849509,164158771368783,
165327254131673,92621796086721,165189295084469,94821339435856,94890058912710,94958778389465,94958795166531,162990271828929,165120575607733,164021332415311,163952596161509,165051839353680,234459316163407,235626758738849,235695478215604,233359804535612,
234458796069824,235627278832581,233359536100187,235695746650927,233359552877504,235695729873861,234458779292507,235627295609647,233359821312929,234459332940724,235695461438287,235626741961532],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p80_0_3 : fcAllB [fba_p80_0_0,fba_p80_0_1,fba_p80_0_2] (pr P3 80) 80 10 fba_p80_0_3 = false := by decide +kernel
lemma fva_p80_0_3 : fcBV (pr P3 80) 80 10 fba_p80_0_3 := fcAllB_val (fcBc fva_p80_0_0 (fcBc fva_p80_0_1 (fcBc fva_p80_0_2 (fcBn)))) fka_p80_0_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p80_0 : fcChkB [fba_p80_0_0,fba_p80_0_1,fba_p80_0_2,fba_p80_0_3] [] (pr P3 80) 80 10 0 FF 1 = false := by decide +kernel
lemma chk_p80_0 : chk [] (pr P3 80) 80 10 0 FF 1 = false := (fcChkB_eq (fcBc fva_p80_0_0 (fcBc fva_p80_0_1 (fcBc fva_p80_0_2 (fcBc fva_p80_0_3 (fcBn))))) 0 FF 1).symm.trans fkr_p80_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_1 : chk [] (pr P3 80) 80 10 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_2 : chk [] (pr P3 80) 80 10 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_3 : chk [] (pr P3 80) 80 10 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_4 : chk [] (pr P3 80) 80 10 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_5 : chk [] (pr P3 80) 80 10 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_6 : chk [] (pr P3 80) 80 10 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_7 : chk [] (pr P3 80) 80 10 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_8 : chk [] (pr P3 80) 80 10 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_9 : chk [] (pr P3 80) 80 10 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80T_10 : chk [] (pr P3 80) 80 10 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_80 : Imp [] 80 11 := by
  refine imp_of (E := []) (Q := pr P3 80) (Z := 80) (L := 11) (Or.inl rfl) (by decide +kernel) (by decide)
    (fun e he => P3ok e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ?_)
  interval_cases t
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p80_0⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_1⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_2⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_3⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_4⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_5⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_6⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_7⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_8⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_9⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p80T_10⟩
set_option maxHeartbeats 0 in
def fba_g80_0 : ℕ × List ℕ × List ℕ := (63,[676265746608886577,667257447842517954,671761047469888469,662754947726775234,671764346004771652,667260746377401137,676266846120514372,662756047238403029,161684316698327,162783828325970,163883339953765,164982851581510,165121129395791,165120860960316,164021349332571,165189865649861,
681966851837858741,681684277349520290,676899202745439169,393737643917251376,163883608389232,164983120016977,165051856271030,162784096761437,163952344643285,163883876824806,164983388452551,163952613078608,165052124706353,162852833015490,165052393141828,164983656888026,
676759634293495493,104943219391010351,104661675694823092,100156976270612059,104660576183195297,676759634310272559,104660576166417980,676478090614085300,100156976287389376,104661675678045775,676830002786014767,104943219374233285,676476990834022049,672043759665616475,676547359292986940,671973391206651584,
676548458804614735,681403970603914800,676617727768729281,681121327396099746,676830002769237701,681122426907727541,676548458821392052,676547359309764257,672043759682393792,671973391189874267,676476990817244732,676478090597307983,676617728842470971,681122427444598331,681403970889127584,681121328201406011,
681403970872350267,681122427461375648,681121328218183328,676617728859248288],[676829934085402937,357,672045889988260275,357,667542290360889760,356,667542221624635707,356,676829865349148974,357,379310814965985727,340,676829796612895172,357,379310746229731674,340,
672045821252006222,357,662757146752119221,355,667259646867861839,340,671762146983604559,340,676264647099347381,355,86293095913812404,3412,99807193330807201,3395,95302494191808960,3395,
95302494191808815,3412,86293095913812385,3411,90797795052810543,3412,99807193330807220,3411,90797795052810688,3395,672045889988260255,1380,676264647099347380,2387,667259646867861952,1363,
676264647099347361,1380,667542221624635706,1381,672045821252006202,1380,662757146752119220,1381,100088668575953210,3412,676264647099347380,1381,667259646867861952,1347,662757146752119201,1380,
662757146752119220,2387,662757146752119201,2371,964778766524150175,357,383814414593356191,2405,667259646867861807,2404,379310814965985695,2405,676264647099347361,2371,671762146983604672,1347,
667259646867861807,2405,671762146983604672,1363,379310746229731642,2405,671762146983604527,2404,383814345857102138,2405,964778697787896122,357,667542290360889759,1381,100088737312207263,3412,
671762146983604527,2405,681120159703953825,372,964497222811185455,357,379029271253021007,339,681120159972389300,372,950986423929074112,357,676617659319775680,357,374526770868842933,355,
676617660125081903,357,959994722427007412,372,955491122799636897,372,95302494191808948,3411,90797795052810657,3411,86293095913812416,3395,99807193330807087,3412,681120159972389300,356,
955491122799636897,340,104659407937401249,2388,104659407937401268,2404,681684278156915002,374,676617660125081903,373,676617660125081903,374,676899203821269306,373,676899203821269306,374,
100438451249410362,2405,100156907553222959,2405,100156907553223104,1364,681120159972389300,374,383532870880391471,2405,681685377400107322,374,672254866168672570,2405,671973322472485167,2405,
676828834288562591,1381,671973322472485312,1364,681120159703953825,373,965060309951902111,374,681120159703953825,340,964497222811185455,373,964497222811185455,374,383532870880391616,1364,
379029271253020975,2405,379029271253021120,1364,950986423929074112,356,950986423929074112,340,672254866185449887,2405,965060309935124794,374,676828834271785274,1381,681685377416884639,374,
676617659319775680,356,676617659319775680,340,676475822319792564,1381,100438451266187679,2405,681684278173692319,374,676475822319792545,1380,374526770868842932,1381,388037569750954420,2404,
388037569750954401,2388,676899203838046623,373,676899203838046623,374,959994722427007412,374,959994722427007412,356,955491122799636897,373,374526770868842913,1380,667542221626725433,1456467,
379310746231821369,9777491,667542290362979486,1456467,379310814968075422,9777491])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g80_0 : BinarySearch.fcAllB [] (pr G3 80) 80 11 1 fba_g80_0 = false := by decide +kernel
lemma fva_g80_0 : BinarySearch.fcBV (pr G3 80) 80 11 1 fba_g80_0 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_g80_0
set_option maxHeartbeats 0 in
def fba_g80_1 : ℕ × List ℕ × List ℕ := (63,[99807193328718661,90797795050722129,95302494189720420,86293095911723990,234528069334331,672325096934937424,384095889014330192,388319113176617910,676546190793446326,676546122073969590,388319044457141174,384095820294853456,672325165654414160,676828765281784625,388600588153328433,383814414037619669,
379309714898621378,677111339770123076,379309646179144642,383814345318142933,667538922819228610,672042522446599125,672042591166075861,677111271050646340,667538991538705346,388881994410562372,388600519433851697,388882063130039108,676828696562307889,104940882912023478,104944180641600438,100719857504555856,
100720956747748176,105223457400361777,95934782363603906,100439481502602197,105507131131892548,100437283016217557,105506031888700228,105225655886746417,95933683120411586,388882201139417914,105507268604400442,676829934083314490,677111409060025146,671762146981516112,676264647097258934,667259646865773392,
662757146750030774,965339448179102645,672394435960705954,374526770866754486,100438451247321947,676475822317704118,960276197133194165,105507268570846149,955772597505823650,105506100624954292,105223526136615841,105507268587623215,100438451264099264,388882201122640687,681965684412060464,672254866183361472,
681684209435349808,965340616410207024,672397733690282914,676901333317653429,965060172225647408,393456031770022818,393737506746733493,676828834269696828,960276265852670901,677111408774812596,677111408758035279,676828834286474145,379029271250932560,383532870878303056,955772666225300386,388668758679557057,
965058041921868706,384165159052186561,100156907551134544,965060240945124144,965339516898579381,955771497994195905,104659407935312822,960274066829415361,105506100608176975,384166258295378881,388669857922749377,965340547690730288,681685308678542128,681966783655252784,105223526119838524,955771566713672641,
671973322470396752,960273998109938625,393734209017156533,672254866166584155,393452734040445858,965057973202391970,676898035588076469,388882201105863621,388037569748865974,964777597737309090,964777666456785826,960554373575021505,964778765968413621,964778697248936885,960554442294498241,960557740829381424,
960557672109904688,960557741114594208,964778697785807675,964778766522061728,960557672378340155,681401634947011509,393174557330183093,388952432679523120,393456032306893616,388670957702812597,681683109655286690,676899134294397889,681402733921768354,677180609271108545,681684208898479010,681964584900432821,
672394435692270529,672396634178655169,681403833433396149,388951332631024577,393737507015168816,384165159320621986,393172358575362978,677180610076414768,677182808562799408,393735308528784176,388669858459620277,393173458086990773,388951333436330800,393454933063701296,393174557061747618,681966783386817461,
676898035051205569,681401634678576034,384167357807006626,677179510027916225,388949134144639937,393455001783178043,393735377248260923,676899203819180859,964990972786316213,393737644185686843,965340685414896544,965060309949813664,965060309933036347,393737644202464160,965340685398119227,960487373158945698,
965270316922377019,681685377398018875,965270316939154336,681685377414796192,681966852391506848,681966852374729531,960486273378882497,681684278171603872,681965753148314528,965271416719217568,965271416702440251,676899203835958176,681965753131537211,393735377265038240,393455001799955360,681684278154826555,
965269148422837173,964987673446126498,960485173598819265,965271347982963504,965270248202900272],[667542221624636987,355,667542290360891040,355,672045889988261555,355,95865444682102468,2388,379310746229732954,339,379310814965987007,339,95865513418356270,2388,672045821252007502,355])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g80_1 : BinarySearch.fcAllB [fba_g80_0] (pr G3 80) 80 11 1 fba_g80_1 = false := by decide +kernel
lemma fva_g80_1 : BinarySearch.fcBV (pr G3 80) 80 11 1 fba_g80_1 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g80_0 (BinarySearch.fcBn)) fka_g80_1
set_option maxHeartbeats 0 in
def fba_g80_2 : ℕ × List ℕ × List ℕ := (63,[233358730933699,234458242561494,235626473665842,235695193142597,95865444680012773,95865513416266575,100088737310118837,100088668573864784,162852547802450,163952059430245,165051571057990,161821755651543,162921267279186,164020778906981,165120290534726,94752620098886,
93652840035685,161753036174807,92553059972434,91453279909335,235489571583282,232191036700099,234389791520214,234390596826437,233291085198642,235489840018757,233290279892419,232191305135574,94958828860869,165327287825743,165258299913532,164090068809051,
234526962038097,234390059955537,235558291060029,233290816763217,234528052557104,235558576272821,235558559495504,232191573570999,235558307837346,234527230473564,235489303147959,234528035780038,235557754189239,234527247250881,677111271587517381,388600588438541217,
388882063415251892,672045889986171828,379310814963897280,383814414591267776,667542290358801313,676829865347060527,677111340323771183,379310746227643227,383814345855013723,672045821249917775,676829796610806725,388600519702287164,388881994678997839,667542221622547260,235695763567931,235627312526651],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g80_2 : BinarySearch.fcAllB [fba_g80_0,fba_g80_1] (pr G3 80) 80 11 1 fba_g80_2 = false := by decide +kernel
lemma fva_g80_2 : BinarySearch.fcBV (pr G3 80) 80 11 1 fba_g80_2 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g80_0 (BinarySearch.fcBc fva_g80_1 (BinarySearch.fcBn))) fka_g80_2
set_option maxHeartbeats 0 in
def fba_g80_3 : ℕ × List ℕ × List ℕ := (63,[165327254271450,162990255191389,164089766819184,94890075829553,165327271048516,93721576289749,165258283136305,92621779449181,92621796226498,164089783596501,165258266359239,162990271968706,94958795306308,93721559512432,94958778529242,94890059052487,
165120575747510,164021332555088,163952596301286,165051839493457,165189278446929,94821339575633,94821356352950,93790278989286,93790295766352,164158754731494,165189295224246,164158771508560,234458796209601,234458779432284,235695478355381,235626758878626,
235695730013638,235695746790704,233359553017281,235695461578064,233359536239964,235627295749424,235626742101309,233359821452706,234459333080501,235627278972358,234459316303184,233359804675389],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g80_3 : BinarySearch.fcAllB [fba_g80_0,fba_g80_1,fba_g80_2] (pr G3 80) 80 11 1 fba_g80_3 = false := by decide +kernel
lemma fva_g80_3 : BinarySearch.fcBV (pr G3 80) 80 11 1 fba_g80_3 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g80_0 (BinarySearch.fcBc fva_g80_1 (BinarySearch.fcBc fva_g80_2 (BinarySearch.fcBn)))) fka_g80_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g80 : BinarySearch.fcChkB [fba_g80_0,fba_g80_1,fba_g80_2,fba_g80_3] [] (pr G3 80) 80 11 1 FF 1 = false := by decide +kernel
lemma chk_g80 : BinarySearch.chk [] (pr G3 80) 80 11 1 FF 1 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g80_0 (BinarySearch.fcBc fva_g80_1 (BinarySearch.fcBc fva_g80_2 (BinarySearch.fcBc fva_g80_3 (BinarySearch.fcBn))))) FF 1).symm.trans fkr_g80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strong80 (floor : Imp [] 80 11) (prior : ∀ e ∈ G3, HasGrade 1 e) : HasGrade 1 (80,11) := by
  apply gradeFromFloor (t := 1) floor (by decide +kernel) (by decide +kernel)
  intro S sw hl
  refine BinarySearch.rejectMinimum (Q := pr G3 80) (L := 12) (by decide +kernel) (by decide) (by decide) ?_ sw hl floor [(FF, 1)] ffull ?_
  · intro e he
    exact prior e (List.mem_of_mem_filter he)
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact chk_g80
lemma g_80 : HasGrade 1 (80,11) := strong80 p_80 G3ok
def P2 : List (ℕ × ℕ) := P2a ++ (80,11) :: (P2b ++ P3)
lemma P2ok : ∀ e ∈ P2, Imp [] e.1 e.2 := apI P2a_ok (consFloor p_80 (apI P2b_ok P3ok))
def G2 : List (ℕ × ℕ) := P2a ++ (80,11) :: (P2b ++ G3)
lemma G2ok : ∀ e ∈ G2, HasGrade 1 e := apG G2a_ok (consGrade g_80 (apG G2b_ok G3ok))

def P1r : List (ℕ × ℕ) := [(1,12),(2,12),(4,12),(8,12),(16,12),(32,12),(64,12)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P1r_ok : ∀ e ∈ P1r, Imp [] e.1 e.2 := okAll (by decide +kernel) P2ok
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G1r_ok : ∀ e ∈ P1r, HasGrade 1 e := gradeAll (by decide +kernel) P1r_ok G2ok
set_option maxHeartbeats 0 in
def fba_p128_0_0 : ℕ × List ℕ × List ℕ := (127,[235558592927676,235627043968814,235558324492227,236726840809419,234527515564005,235558022502269,233359284459398,965343914944967969,965343846225491233,681263233954297956,969283396387812797,969563840572372400,969564940084000040,680701383780939991,104099824716036337,103818418173589730,
675704102862272582,94811218650413078,680419840067975328,974699728105190829,671483008752105706,90306450791938104,90307550303565995,94810119138785438,680490070282680512,675985371143682063,676265815328241686,676266914839869455,671762215700871326,99315986508888141,393105356582106475,680771613978867904,
671483077740017749,675704033874360539,680206533990103077,104101130386094091,104382605379582167,103819655124170897,681263233920743556,681264333700806903,974701996133135716,99597461770811437,681545877396994288,686190213707413741,94812318162040916,681616245872736496,680982790021396640,681052058431862814,
974982303130400085,681616245889513476,974701927665317205,681334701924890635,666768440045942898,676547359292864738,109447918781544695,109446819269916804,672043759665494127,666980508636362804,666698895935486036,104943219374110790,662192066492708927,676759634293372998,680980590461270068,109165275590506541,
108323185763629133,676478090613962986,108604730281900036,680487940264114228,103818486624630799,965057973202269459,100160481014134843,95093793423964212,960558771621410224,960274066829292955,99314886997260303,666698964654962772,675703964886448143,671201464770705423,686190213975849048,99316055496800401,
680207427074864717,99597531027159044,95093862143440941,94812387149953054,85802851164567608,85805050187823337,90307619023042582,680488971324700307,99597530758723595,99316056033671408,680207427343300126,99316055228364992,680208527123363575,666694429169497663,675701628424238763,675703827984365126,
94811287906760774,680206327563236948,99316055765235959,680488971056264749,680490071104763396,686751927532336385,681333602396485764,90308718803105829,681334701908113655,90590193796593716,680770515037664868,686470383014065482,681053157960267936,671480672289896062,680487871544636980,681052058448640045,
964780896272070077,95374237893736486,686469284039308720,970056560025875800,398520452137432328,680206327831672357,970057591103239425,965062439968257320,970057659805939032,94811287638325467,398238977143944577,398520452120655348,90307619291478242,95092762900248661,681685377414673746,686751996268590392,
969846553053312359,686470452001977729,686471620535072056,965060309932913987,970126859513705965,960557809817171267,677182877298931026,686471551782041069,686751996251813223,393457132086834472,397959701190489588,666769608277047336,969777215906592008,970055391543112968,397679256469058890,969846553036535128,
970126859530482945,969846484065400065,680487871527860261,970126928501618008,388669858727933258,393174557866931645,397959632471012648,662265939930200138],[681616177205678906,374,667259646867739549,340,676264647099225002,355,667261845890995027,372,384097058086261541,357,681615970996917231,374,676832064372282122,374,676550520390882192,374,
672328464744911762,373,680771545261478847,374,671765445518365516,373,671764346006737678,357,667543321136141092,372,393105218574817363,336,379313013989118771,372,676547221855998945,356,
672043622228628334,340,672043690964882301,340,676831995636028406,374,676550589127136159,374,681332433899034660,368,681262065440069683,369,676264647099224850,2371,667260746379367186,1347,
671761047471854490,2371,681332296460081188,369,676550589127137439,371,672046989499766828,371,681050890219624499,370,676831995636029686,372,672328396008659075,372,969564871366611843,1398,
969844147588502356,1415,667257447846572397,13975875,965340616412174446,2352,100651619068212837,9781264,959995821940601116,1534323,100651687804466827,9781281,955491123338473858,1534341,667261845890994983,1398,
680768246726595401,1397,681050821483369300,3429])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_0_0 : fcAllB [] (pr P2 128) 128 12 fba_p128_0_0 = false := by decide +kernel
lemma fva_p128_0_0 : fcBV (pr P2 128) 128 12 fba_p128_0_0 := fcAllB_val (fcBn) fka_p128_0_0
set_option maxHeartbeats 0 in
def fba_p128_0_1 : ℕ × List ℕ × List ℕ := (127,[235627329181581,234527532341174,234458812864336,236658372990834,236727109244739,236658104555514,235627027191645,234458510874378,233358999246609,680486771747797225,680769414955612244,969282296876184906,680700284000876644,681264333734361303,99595125577037950,99313719034591343,
680137334013900932,680138433793964279,974981203081901349,680418740287911981,671201602746529862,675985508867848426,103819654855735488,671479572493056056,680488970771052621,675983172120426667,109730423778653445,680770514467240013,675985577855760469,671201533758617819,680417640507848756,99878937032734820,
99597462039246995,99315986777323550,681545877413771268,103819655392606455,974982371598218596,99315987045759108,104101130117658784,681333602413262995,109729462477732080,676830002785892437,90308649815193833,676548458804492507,109729462494509060,680981690241333293,681053157943490705,686190213992626279,
104661675694700778,681050958920235045,666694497888974911,94812318430476325,108323186837371120,666980439916886068,666698896203921445,680206396551149605,108323255288412400,671973391206529150,676476990833899761,109166375102134432,108323254483105984,108604661830858756,662195365027592425,662264840418572300,
681053158530692667,964780964991546813,960554373574899099,960277365364176202,680205296771086569,680771614817728208,108604523855034420,99879006020647120,108323117312587813,965062371248780584,662195296308115689,964777666456663315,680206465002190932,666699033642874917,393737640192587158,671201396051228687,
675703896166971407,686190213724190721,95092762631813354,94812387418388612,680208527391799024,85801751652939839,85803950676195499,90306519511414942,680490070836327947,90308718534670420,95093862411876499,99597530490288288,94812386881517645,680208526854928017,680207427611735684,671198028796868152,
680205228051609321,671199128308496030,675702727935866390,680208526586492608,680490070567892640,675985371428894442,686471620501517656,686471551798818049,686751996235035992,676830002769115206,90589094284966129,680771614549292759,676266915410294310,960277296644699466,686752957502404029,675984271917266673,
99879005752211671,676548458821269738,95375337405364324,675703827447494159,681403966879250582,675703827715929819,398238977160721808,686750759284454696,960558840340886960,675702728204302050,671199128576931439,970056491323176193,675985371697329749,90306519779850351,94811287369889807,90587994773338238,
686753094958134536,686470521291879736,686753026490316276,686753095511782712,686470520469796240,398523887322740024,970126928518395239,969846484048623085,397958601678861697,680769415240824884,686751927515559405,686471620518294887,965273616279221648,970125760002078196,662266008649676989,388953532191028656,
969773916566402448,398242206154044848,398237808912840010,969844285025367425,398519283889550781,970199427281139178,970199496285828554,398523681130755368,397958532959385008,666769539557570736,397679256737494461],[681616108469425103,374,671761047471854391,339,667260746379367189,356,680768246726595560,371,681616039733170947,374,672046920763511581,373,680770445749850956,373,383815514373297129,356,
676269045145736127,374,384096920613753669,357,676266846122480398,357,392823812317583592,320,388881994412529678,352,677111271052613646,352,677111339772090382,352,388882063132006414,352,
676547290592252912,356,393105356298983475,337,393105356282206244,336,672328396008657795,373,672046989499765548,373,681050890219623219,372,685906402002146128,389,681050821483369252,372,
393105218843252772,336,104593436451084339,2369,384096920613754949,356,383815514373298409,355,667259646867739546,1347,969563771854984067,2422,969282365597750045,2422,969844216324756323,1415,
969283465109377821,1398,965339448181069934,2368,955491123338473858,1534339,667261845890995119,1397,680768246726595516,1398,681122358460739868,1534340,681332365196333923,3429])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_0_1 : fcAllB [] (pr P2 128) 128 12 fba_p128_0_1 = false := by decide +kernel
lemma fva_p128_0_1 : fcBV (pr P2 128) 128 12 fba_p128_0_1 := fcAllB_val (fcBn) fka_p128_0_1
set_option maxHeartbeats 0 in
def fba_p128_0_2 : ℕ × List ℕ × List ℕ := (127,[236727092467672,235627849275352,236658071000863,236863994550232,235627295627094,234528052434774,681897583444047312,681897652180301115,393105356280116517,109448879780476393,677041109303637286,388600657711543590,388600519433729302,667260746377278742,393668444242916816,105506031888577807,
384095820294731166,667259646865651102,388319113176495531,232191305013049,235691468478267,393668168794584465,393668237799273739,235489571460887,392823812315493865,393105218572727636,104944180641478059,100439481502479672,110292343728452875,110009769240114579,672325165654291870,676828765281662230,
676546122073847211,393105218841163045,676269045143647680,100721025483879806,680771545259390400,384095958002120047,236726555596652,681897445166233024,681897513885709760,393668168526149056,681614870677894477,676759565590672874,667261845888906580,680768246724507113,681614939397371213,393668237245625792,
671764346004649231,676266846120391951,110009769223337348,672046920761423134,110009700520637741,672328464742823315,393668444209362416,398523887020750317,388600657157895665,676547290590164465,100721025467102575,110293511691121924,383815514371208682,384096920611665222,393668444226139396,236726538819483,
969564871364523304,969282365595661642,236657534130107,677111271050523919,110293305515914688,969283465107289533,110009631784383821,681262065437979956,681050890217534772,667543321134052645,104874980430394632,970125622563124724,969844216322667920,393105356296893748,676831995633939959,676547221853910498,
393386694086309252,681897582890399136,672325165939504510,955772597505701139,681615077373195652,672046989497677101,681615008402060589,393668237530838432,398523887037527297,398523887289185624,970199495732180356,104593436448994764,965340616695297362,104874842957886760,166289645590747,166220909336693,
163883339831356,166151636211768,166358381844692,165121129273535,166151367776461,165189865527338,166082899957801,166151904647217,166152173082788,164983388330214,970199427549574485,166083436828821,163952344520732,398238908424467888,398242205885609290,166220372465673,
164021349210195,162783828203587,164983119894656,163952612956290],[667257447844483902,323,100651687802378243,2405,969283465931461376,374,969001922218496800,374,681122359532393248,374,379309714900587374,3429,667538922821194606,3429,959995821938512669,2419,
964499421565883165,1398,681122358458651421,2436,685908532574360349,1398,686187809064686467,2422,686187809333121923,1398,685624859111265155,2422])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_0_2 : fcAllB [fba_p128_0_0,fba_p128_0_1] (pr P2 128) 128 12 fba_p128_0_2 = false := by decide +kernel
lemma fva_p128_0_2 : fcBV (pr P2 128) 128 12 fba_p128_0_2 := fcAllB_val (fcBc fva_p128_0_0 (fcBc fva_p128_0_1 (fcBn))) fka_p128_0_2
set_option maxHeartbeats 0 in
def fba_p128_0_3 : ℕ × List ℕ × List ℕ := (127,[234528337647461,236726824032101,236658339436434,236727075690252,236726807254932,236795275073381,234459316180956,235558559373276,681616108467336656,681616177203590459,109730423761876276,109727057296045396,105224694384375078,384097058084173094,105507131131770127,110293511724676411,
671761047469765944,110293511707899344,676264647097136555,393668444259693883,383814414037497144,393386762822563219,235622749001667,393386693817873694,234390059833247,232191573448620,234523237373829,110009700503860510,110292274992199057,100719857504433566,105223457400239382,392823812869141812,
672042522446476600,681332364909032788,681049721701217769,680770445747762509,671765445516277069,105225724622878193,388600657141118434,236657836119814,393386693549438285,393386762268915021,105224694350820678,681897651878311179,681615077389972883,677041109270082886,681615008385283358,681897582873621905,
104943150671410666,109727126015522085,109445651055588660,676832064370193675,110292343711675895,676550520388793745,110292275008976288,672325097203250543,105225724606100962,676828696830621154,384095958018897278,672043690962793854,398523887305962855,110293511674344944,388319113998579178,388600520239035718,
232191841884138,388881994410439951,110011830270768461,677111339770000655,236589083088725,969563771852895664,110292206272722368,388882063129916687,681332296457991461,681332433896944933,232191036577600,379313013987030324,969844147586413953,970125691299378440,397960799359939921,681897651861534199,
672328396006569348,672043622226539887,955772666225177875,109730423745099045,676828765566875121,955771566713550235,393668169063020023,676550589125047712,393386762554127661,955771497994073499,686187876976768337,685906402000057681,970199427012703518,965340547959043395,681332365194245428,681050821481280805,
166220640901122,166289377155176,166082631522494,164982851459247,970125691014165800,969844216037455280,969843047806350666,970124522783061437,165052393019630,164983656765663,163883876702323,166083168393250,970199496017392996,165051856148623,398523680862320061,398520383401178408,
163883608266765,166082363087085,165120860838086,161684316575960,162784096638996,165052124584181,162852832892963],[100651619066124527,2405,969564872171918167,374,681122358458651403,374,955491123336385393,374,955491123336385411,2435,667257447844483950,3429,95934782365569902,3429,959995821938512669,2422,
685907433062732573,2422,955491123336385411,2437,685624859379700611,1398])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_0_3 : fcAllB [fba_p128_0_0,fba_p128_0_1] (pr P2 128) 128 12 fba_p128_0_3 = false := by decide +kernel
lemma fva_p128_0_3 : fcBV (pr P2 128) 128 12 fba_p128_0_3 := fcAllB_val (fcBc fva_p128_0_0 (fcBc fva_p128_0_1 (fcBn))) fka_p128_0_3
set_option maxHeartbeats 0 in
def fba_p128_0_4 : ℕ × List ℕ × List ℕ := (127,[236657265694698,166151082563565,166219802040301,236725985171285,235627312404263,234528069211943,233359804553187,233359552894847,233359821330418,233359536117616,93790312421203,94890092484550,236726253606694,236657819342645,236794704648014,236863424124865,
235557754066860,235626473543447,234526961915807,234458242438969,165120290412463,164020778784572,165051570935727,163952059307836,667257447842395455,235559096244114,235627832497932,234528320870292,234459584616223,236795811944401,236864279762748,236864262985681,
236795828721468,165258585003818,165189848750015,234458796087167,235558307715058,234527230351216,235626741979107,235558290937827,235626758756338,234527247128447,234458779309936,234459601393454,233360089765685,233360072988454,95934782363481407,234528304093061,
235627815720952,235559113021345,234459332958187,235558576150507,234528035657543,235627278849863,667538922819106111,379309714898498879,166357811418889,166289091942153,95989872547593,236588814653418,233291353511765,236794973083423,235489839896336,236795258296212,
236863977772812,236863692560274,234390596704016,681615970994828784,681897445971539440,681616039731082500,681897514707793156,94890058930150,93790278866803,94821356230543,93721576167196,166426799331074,166495787243381,166495804020699,166426816108392,100651687800288749,
100651619064034782,965339448178980108,965340616410084722,236657802565414,236726270383925,164089766696717,165189278324608,165258283014133,164158771386242,235695478233067,166151619434281,166357777864489,235695729891143,166220087252941,166288806729677,965343846493926893,
965343915498616167,236795241518981,236863709337505,236794989860654,236863960995832,686187809331033384,685907433060644170,685908532572272061,96127294724004,686187809062598064,96058575247153,96058558469922,96127277946773,164158754609011,164089783473948,965270316939031890,
165258266236902,165189295101839,965340685397996867,969283465929372929,969564872169829720,970196128477820271,964499421563794877,965343983932880365,685624859377612072,965344052937569639,685624859109176752,959995821936424266,393738675799799041,681969120385774936,681965684411938162,393738744502498648,
95989838993193,681969051683075329,393737506746610956,162852816115476,681966783386694924,162921552369443,393735308528661874,95921136293837,393738607063545121,681122358456562956,955491123334296946,969001922216408353,681968982946821409,393737507820352801,681966784460436769,681122359530304801,
96127345055700,970196060026778991],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_0_4 : fcAllB [fba_p128_0_0,fba_p128_0_1,fba_p128_0_2,fba_p128_0_3] (pr P2 128) 128 12 fba_p128_0_4 = false := by decide +kernel
lemma fva_p128_0_4 : fcBV (pr P2 128) 128 12 fba_p128_0_4 := fcAllB_val (fcBc fva_p128_0_0 (fcBc fva_p128_0_1 (fcBc fva_p128_0_2 (fcBc fva_p128_0_3 (fcBn))))) fka_p128_0_4
set_option maxHeartbeats 0 in
def fba_p128_0_5 : ℕ × List ℕ × List ℕ := (127,[161753036052440,162921267156803,235695763445543,233358730811200,235696585529148,235696568752081,235695193020176,236726790477701,236658356213665,236658087778094,236727058913272,236795778390001,233290279769920,236795795166981,236864229431281,236864246208261,
234389791397689,235489303025580,233291085076247,233290816640927,235696551974661,235696535197681,234390865139534,235490376767425,235695461455836,235695746668374,236589619959745,236589351524174,162990255068948,92621796103971,94958778406879,165121112496110,
165327270926318,94958795184110,165327254149087,165052376242143,166495753688981,166426782553905,166426765776674,166495770466212,166151350998974,166220355688248,166357794641720,166288789952446],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_0_5 : fcAllB [fba_p128_0_0,fba_p128_0_1,fba_p128_0_2,fba_p128_0_3,fba_p128_0_4] (pr P2 128) 128 12 fba_p128_0_5 = false := by decide +kernel
lemma fva_p128_0_5 : fcBV (pr P2 128) 128 12 fba_p128_0_5 := fcAllB_val (fcBc fva_p128_0_0 (fcBc fva_p128_0_1 (fcBc fva_p128_0_2 (fcBc fva_p128_0_3 (fcBc fva_p128_0_4 (fcBn)))))) fka_p128_0_5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p128_0 : fcChkB [fba_p128_0_0,fba_p128_0_1,fba_p128_0_2,fba_p128_0_3,fba_p128_0_4,fba_p128_0_5] [] (pr P2 128) 128 12 0 FF 1 = false := by decide +kernel
lemma chk_p128_0 : chk [] (pr P2 128) 128 12 0 FF 1 = false := (fcChkB_eq (fcBc fva_p128_0_0 (fcBc fva_p128_0_1 (fcBc fva_p128_0_2 (fcBc fva_p128_0_3 (fcBc fva_p128_0_4 (fcBc fva_p128_0_5 (fcBn))))))) 0 FF 1).symm.trans fkr_p128_0
set_option maxHeartbeats 0 in
def fba_p128_1_0 : ℕ × List ℕ × List ℕ := (127,[94890092615622,93790312552275,166495804151771,166426816239464,166495787374453,166426799462146,165258585134890,165189848881087,162921267287875,161753036183512,233358730942272,96127278077845,96127294855076,96058575378225,96058558600994,165189278455680,
164089766827789,165258283145205,164158771517314,166288790083518,166357794772792,93790278997875,166151636342840,93721576298268,94821356361615,94890059061222,166082631653566,92621796235043,162990255200020,166426782684977,166495770597284,166495753820053,
166426765907746,166358381975764,104593436449125836,104874842958017832,163883339962428,164982851590319,233359804684259,166289645721819,166289377286248,165189865658410,166220909467765,166220641032194,165121129404607,233359821461490,233359553025919,233359536248688,
162921552500515,162852816246548,234390059964319,235489571591959,232191573579692,232191305144121,165120860969158,164021349341267,166220372596745,166152173213860,164983388461286,166082900088873,166083168524322,164983656896735,166151904778289,165052393150702,
163952344651804,165051856279695,166151367907533,166083436959893,163883876833395,164089783605020,165189295232911,164158754740083,165258266367974,163952613087362,165052124715253,164983120025728,162852833024035,163883608397837,21080542762837,162784096770068,
162783828334659,161684316707032,392823812315624937,166082363218157,236589083219797,393105218572858708,232191842015210,232191036708672,680771545259521472,680770445747893581,671765445516408141,676269045143778752,398523887322871096,397679256737625533,969282365595792714,969564871364654376,
969283465107420605,397679256469189962,969563771853026736,965343915498747239,965343846494057965,397959632471143720,397958532959516080,969563840572503472,969283396387943869,969282296876315978,969564940084131112],[104874980432614199,3429,969283397195338732,374,969564940908303206,374])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_1_0 : fcAllB [] (pr P2 128) 128 12 fba_p128_1_0 = false := by decide +kernel
lemma fva_p128_1_0 : fcBV (pr P2 128) 128 12 fba_p128_1_0 := fcAllB_val (fcBn) fka_p128_1_0
set_option maxHeartbeats 0 in
def fba_p128_1_1 : ℕ × List ℕ × List ℕ := (127,[104874980430525704,100651619064165854,100651687800419821,166151351130046,166220355819320,235696585660220,235696568883153,165051571066799,164020778915644,165120290543535,163952059438908,96127345186772,235695763576615,236863994681304,236795275204453,166151619565353,
166220087384013,166151082694637,166219802171373,235695461586908,236658071131935,236658339567506,236727075821324,236726807386004,235695746799446,166357777995561,166288806860749,95989839124265,95921136424909,234390865270606,236589620090817,236589351655246,
235490376898497,236725985302357,236658087909166,235696535328753,236658356344737,235696552105733,236657265825770,236727059044344,236726790608773],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_1_1 : fcAllB [fba_p128_1_0] (pr P2 128) 128 12 fba_p128_1_1 = false := by decide +kernel
lemma fva_p128_1_1 : fcBV (pr P2 128) 128 12 fba_p128_1_1 := fcAllB_val (fcBc fva_p128_1_0 (fcBn)) fka_p128_1_1
set_option maxHeartbeats 0 in
def fba_p128_1_2 : ℕ × List ℕ × List ℕ := (127,[95989872678665,166289092073225,166357811549961,165052376373215,165121112627182,165327254280159,94958778537951,165327271057390,94958795315182],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p128_1_2 : fcAllB [fba_p128_1_0,fba_p128_1_1] (pr P2 128) 128 12 fba_p128_1_2 = false := by decide +kernel
lemma fva_p128_1_2 : fcBV (pr P2 128) 128 12 fba_p128_1_2 := fcAllB_val (fcBc fva_p128_1_0 (fcBc fva_p128_1_1 (fcBn))) fka_p128_1_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p128_1 : fcChkB [fba_p128_1_0,fba_p128_1_1,fba_p128_1_2] [] (pr P2 128) 128 12 1 FF 1 = false := by decide +kernel
lemma chk_p128_1 : chk [] (pr P2 128) 128 12 1 FF 1 = false := (fcChkB_eq (fcBc fva_p128_1_0 (fcBc fva_p128_1_1 (fcBc fva_p128_1_2 (fcBn)))) 1 FF 1).symm.trans fkr_p128_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_2 : chk [] (pr P2 128) 128 12 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_3 : chk [] (pr P2 128) 128 12 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_4 : chk [] (pr P2 128) 128 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_5 : chk [] (pr P2 128) 128 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_6 : chk [] (pr P2 128) 128 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_7 : chk [] (pr P2 128) 128 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_8 : chk [] (pr P2 128) 128 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_9 : chk [] (pr P2 128) 128 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_10 : chk [] (pr P2 128) 128 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_11 : chk [] (pr P2 128) 128 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p128T_12 : chk [] (pr P2 128) 128 12 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_128 : Imp [] 128 13 := by
  refine imp_of (E := []) (Q := pr P2 128) (Z := 128) (L := 13) (Or.inl rfl) (by decide +kernel) (by decide)
    (fun e he => P2ok e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ?_)
  interval_cases t
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p128_0⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p128_1⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_2⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_3⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_4⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_5⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_6⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_7⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_8⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_9⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_10⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_11⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p128T_12⟩
set_option maxHeartbeats 0 in
def fba_g128_0 : ℕ × List ℕ × List ℕ := (127,[235558593067453,235627044108591,235558324632004,234458511014155,235627027331422,233358999386386,680771614817867985,681263233954437733,680701383781079768,94811287370029584,680488971324840084,680486771747937002,680487871544776757,680206327831812134,686471620518434664,686751927515699182,
686751996251953000,675702727936006167,675701628424378540,99595125577177727,99313719034731120,666694429169637440,680207427075004494,675704102862412359,680137334014040709,675985508867988203,680418740288051758,94811218650552855,90307550303705772,680488971056404526,680770514467379790,675703827984504903,
680770515037804645,680490071104903173,680208527391938801,671762215701011103,676266915410434087,95092762631953131,675985371429034219,680771613979007681,675985577855900246,671483077740157526,671201533758757596,675702728204441827,671199128577071216,675985371697469526,675984271917406450,99878937032874597,
680487940264254005,104101130386233868,104382605379721944,681616245889653253,681052058432002591,680982790021536417,681545877413911045,681264333700946680,99315987045898885,676830002786032214,685061770911635561,90308649815333610,681334701925030412,104101130117798561,676759634293512775,964777666456803092,
666980508636502581,108323186837510897,109166375102274209,662195365027732202,104943219374250567,108604661830998533,671973391206668927,680980590461409845,108323255288552177,94812318430616102,666698895935625813,108604730282039813,964780964991686590,960554373575038876,108323185763768910,960558771621550001,
666980439917025845,662195296308255466,666699033643014694,969917952858216293,666698964655102549,680205296771226346,680206465002330709,686751996235175769,686471620501657433,686190213975988825,686190213724330498,970199427583268662,970057591103379202,970194961589032735,686470452002117506,686753026490456053,
970199358830237573,681052058448779822,681403966879390359,398521620351899481,398521551649199874,686751996268730169,676830002769254983,686471620535211833,960277296644839243,960558840341026737,970126859530622722,969846484048762862,974138977980471275,960557809817311044,970126928518535016,677182877299070803,
974420521693435851,970199427281278955,974137878737278955,970056560059569977,680769415240964661,388669858728073035,680487871528000038],[681616177205818683,374,384097058086401318,357,671761047471994168,339,680768246726735337,371,667261845891134804,372,383815514373436906,356,672328464745051539,373,672046920763651358,373,
680770445749990733,373,671765445518505293,373,681262065440209460,369,681332433899174437,368,104593436451224116,2369,672043690965022078,340,672043622228768111,340,677111271052753423,352,
383815514373438186,355,677111339772230159,352,393105356299123252,337,676831995636168183,374,676550589127275936,374,681050821483509029,372,681050890219762996,372,676269045145875752,1396,
671765445518505392,1396,680770445749990730,1395,145759290089617587,368,104593436451222928,3412,667543321136280961,1397,145476646596589673,368,145194003640432877,353,667543321136281076,1398,
676831995636169463,372,676550589127277216,371,379313013989258640,1397,145470049526823090,289,145189605325486318,306,145477746376652971,384,145196202395252948,385,145196202663688355,385,
145477746108217511,384,681332296460220965,369,145188505545422869,274,950988622952346961,389,685623759331341649,388,145192904128805108,337,145192903860369450,337,145188506082293934,274,
145472248818514070,320,144633114164017177,389,145188505813858527,274,955773697019557201,389,144629815629133930,325,950843551875545265,359,680771545261618465,1381,965343846496156397,389,
671765445518505249,2405,676269045145875745,1381,965343915500845671,389,964499421566023101,391,392823812317721886,3446,685624859379840296,391,393386693551667786,2352,379313013989258596,3429,
393668237247855144,2368,667257447846712174,13975875,969564871366751620,1398,964499421834458408,391,432511922613598340,2083,432793260117800968,66,432511853877344319,83,680771545261618469,3395,
955773697019557293,1414,955773765739034029,1414,969283465109517598,1398,955773765739033893,1415,685623759868212669,391,955773697019557157,1415,955491123338613635,1534339,969563771855123844,2422,
433074872567019674,2113,955772667053666658,6276274564,676269045145875749,3395,432792160337737810,66,955491123338613635,1534341,109727057298273668,3446,960627011406214573,406,960628110917842213,406,
681332296460219733,3429,969844147588642133,1415,676266846122620292,3444,685623759331341605,1415,960132226106996118,1381,950988622952347053,1414,681050890219763044,3429,681122358460879645,1534340,
393105218843391317,3446,955772597510017828,1595780,658796675569104425,2402,432511785141090344,52,100651687804606604,9781281,965339448181209711,2368,432509585580963846,52,432793328854055054,82,
432510685092591737,52,965062440255698276,1414,432793259580930231,82,109727126017750357,3446,974419284996601220,391,432793328585619483,82,974420384239793540,391,432510685361027186,52,
432792229073991896,82,955491123338613614,1533268,950987523711243118,1534291,658796675569104487,2418,964780896811169109,1414,959995822211264898,6276274547,685905234308052305,389,974138908994647333,406,
109730423747327317,3446,955772667051578211,1603974,680768246726735178,1397,680768246726735293,1398,681332365196473700,3429,667261845891134760,1398,393105356299122020,3446,676264647101453166,5658947,
667260746381595502,5657923,94811287640553709,2416,95092762902476903,2417,85801751655168155,2384,85802851166795850,2416,90306519513643184,2416,95374237895964728,2418])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_0 : BinarySearch.fcAllB [] (pr G2 128) 128 13 1 fba_g128_0 = false := by decide +kernel
lemma fva_g128_0 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_0 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_g128_0
set_option maxHeartbeats 0 in
def fba_g128_1 : ℕ × List ℕ × List ℕ := (127,[235627329321358,234527532480951,234458813004113,234527515703782,235558022642046,233359284599175,681053158530832444,680700284001016421,681264333734501080,675703827447633936,680769414955752021,680490070836467724,680207427343439903,680208526855067794,109730423778793222,90308718803245606,
90590193796733493,393105356582246252,686471551782180846,671199128308635807,680205228051749098,680206327563376725,671198028797007929,103818418173729507,104099824716176114,680208526586632385,90306450792077881,671201602746669639,680138433794104056,671483008752245483,680419840068115105,94810119138925215,
680208527123503352,680488970771192398,676266914840009232,675985371143821840,94811287906900551,680207427611875461,676265815328381463,675983172120566444,99315986509027918,103819654855875265,680771614549432536,680490070282820289,680490070568032417,671479572493195833,675704033874500316,671480672290035839,
675703827716069596,680417640507988533,680206533990242854,680206396551289382,99597462039386772,103819655124310674,99315986777463327,671549872517896276,676548458804632284,681263233920883333,680981690241473070,681053157943630482,681333602413402772,94812318162180693,103819655392746232,109729462494648837,
681545877397134065,109729462477871857,685060671400007683,99597461770951214,681616245872876273,960274066829432732,666698896204061222,662192066492848704,109447918781684472,109446819270056581,672043759665633904,109165275590646318,676547359293004515,681050958920374822,666694497889114688,676476990834039538,
662264840418712077,104661675694840555,965062371248920361,666768440046082675,960277365364315979,965057973202409236,108323254483245761,676478090614102763,974419353713989462,103818486624770576,974420452957181782,95093793424103989,99314886997400080,965414353499281253,108323117312727590,108604523855174197,
675703896167111184,671201464770845200,686471551798957826,675703964886587920,686751927532476162,671201396051368464,970199496302745500,970056560026015577,686753094958274313,686470520469936017,970057659806078809,970056491323315970,676548458821409515,681053157960407713,398241176184116994,398241244886816601,
681333602396625541,681334701908253432,686753095511922489,686470521292019513,964780896272209854,965062439968397097,970199496285968331,969846553053452136,970126859513845742,965060309933053764,681685377414813523,969846553036674905,974419422450243531,970126928501757785,970057659839633209,970194960783726448,
969846484065539842,393174557867071422,393457132086974249,388953532191168433],[681616108469564880,374,676264647099364779,355,667260746379506966,356,667259646867879326,340,384096920613893446,357,676550520391021969,374,676832064372421899,374,676269045145875904,374,
680771545261618624,374,667543321136280869,372,379313013989258548,372,393105218843392549,336,676547290592392689,356,676547221856138722,356,388881994412669455,352,384096920613894726,356,
388882063132146191,352,672328396008797572,373,393105356282346021,336,672046989499905325,373,680771545261618621,1395,964780896811169268,389,145759290089617587,352,104593436451222792,3428,
960277297183798657,389,145189605593921725,306,145470049795258550,289,672328396008798852,372,379313013989258504,1398,672046989499906605,371,145475547353397493,352,145195102883625110,369,
144630915140761699,357,681050890219764276,370,144632014652389590,373,145196202126817290,385,145189605057050660,306,145195102615189703,369,145194003103561812,353,145471149306886341,304,
144628716117506052,309,145471149038450881,304,955773765739033937,388,145472248550078610,320,680770445749990689,2405,432793397590308964,2098,432511922613598363,2115,955347151502915625,359,
959995821938652490,390,393105218574955908,3446,685624859111404976,390,393668168528378557,2352,393386762271144624,2368,667543321136280917,3429,432511853608908999,83,432510754097281161,83,
959995822207088048,390,680768246726735134,3429,680770445749990829,3395,959995821940740893,1534323,960628110917842213,408,667261845891134852,3429,960627011406214573,407,969282365597889822,2422,
960629210161034533,408,671765445518505389,3395,432793397590309098,2114,432793259849365648,66,955772598317412691,6276274564,433356347543730228,2096,685623759599777098,390,960629209892599213,407,
960629209892599213,405,955771566717866924,1595780,671764346006877470,3443,671764346006877572,3444,960629210161034533,405,955772666229494564,1595780,392823812871370084,3446,109448879782704414,3446,
955628626479626902,2403,685623759331341741,1414,676266846122620190,3443,950988622952346917,1415,969844216324896100,1415,955771497998390188,1595780,109445651057816932,3446,100651619068352614,9781264,
969773916568630628,1415,432791060557674502,82,965343915232410113,389,432792160069302393,82,432511784604219575,52,960558840628327780,1415,965340616412314223,2352,974137810019890462,391,
974138909263082782,391,658796675569104561,2386,432511784872655024,52,950987523713331484,6276270467,959992523405857646,1534323,681122358460879726,1534292,965343846764591704,389,960277297183798613,1415,
969844285027595605,1415,974137809483019693,406,681050821483509077,3429,685905234576487853,1413,955772598315324244,1603974,685905234844923173,1413,392823812319811723,1179698,393105218577045680,1245249,
667261845891134896,1397,667259646869967726,9852227,671761047474082670,9853251,671764346008965998,1535299,676266846124708718,1535299,85801751655168019,2400,85803950678423741,2416,90307619025270824,2416])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_1 : BinarySearch.fcAllB [] (pr G2 128) 128 13 1 fba_g128_1 = false := by decide +kernel
lemma fva_g128_1 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_1 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_g128_1
set_option maxHeartbeats 0 in
def fba_g128_2 : ℕ × List ℕ × List ℕ := (127,[166358381984469,166220909476470,166220641040899,165120860977863,164983656905440,165052393159407,166083168533027,164983388469991,166151367916238,162852833032740,164983120034433,236658104695040,236658373130611,393668168794724242,676269045143787457,105224694384514855,
388600657711683367,383814414037636921,681897583444187089,681616177203730236,393386693549578062,680768246724646890,109445651055728437,393668444259833660,672042522446616377,672325165654431647,110292274992338834,110292343728592652,109730423762016053,393105218841302822,100721025484019583,105225724623017970,
388600657141258211,384095958002259824,236726538959260,236657534269884,681615008385423135,955628626477537157,110292275009116065,672328464742963092,110292343711815672,676828696830760931,672043690962933631,110009631784523598,100721025467242352,676831995634079736,681332296458131238,388600657158035442,
105225724606240739,398238977144084354,398523887306102632,99316055496940178,970125760002217973,99597530758863372,970125622563264501,965343846225631010,681897582890538913,676547221854050275,965340616695437139,393386762554267438,393668237530978209,398241176167340014,398523887037667074,398521551632422894,
94812386881657422,90306519511554719,90307619023182359,960132226104907715,974981203082041126,974699728105330606,99316055765375736,95093862143580718,970199495732320133,95374237893876263,686188977025406850,686749659772966846,109730423745238822,686190076537034741,970199427566491493,94811287638465244,
965062440253609737,90589094285105906,90306519779990128,970196129836914533,974701927665456982,974982303130539862,970199358561802015,970196061100660613,960627011404126126,960629209890510766,974138909260994335,974419284994512773,393737640192726935,950988622950258514,974417085702821806,974138908992558886,
398242205885749067],[667257447844623679,323,681615970997057008,374,100651619066264304,2405,667259646867879323,1347,955491123336525170,374,667260746379507058,1381,955491123336525188,2435,955772598313235797,2438,
955772667049489764,2439,667538922821334383,3429,955772598315324244,1534341,969283465933689699,1602949,969282365597889965,1413,955772598315324244,1534340,685907433062872350,2422,955491123336525188,2437,
686187809064826244,2422,969283465109517605,1413,959995821938652446,2422,685906403078116180,5726597,685906402809680724,9920901,969283396390040869,1413,969282296878413229,1413,671764346006877551,3395,
955771497996301741,2437,960628110380971375,391,955772666227406117,2436,959992523403769199,2419,685623759601865501,9920900,964499421836546947,5726597])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_2 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1] (pr G2 128) 128 13 1 fba_g128_2 = false := by decide +kernel
lemma fva_g128_2 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_2 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBn))) fka_g128_2
set_option maxHeartbeats 0 in
def fba_g128_3 : ℕ × List ℕ × List ℕ := (127,[166151636351545,165189865667115,166289645730524,166220372605450,163883339971133,166151904786994,163883876842100,165051856288400,162784096778773,163952613096067,161684316715737,162783828343364,236726840949196,393386693818013471,393668237799413516,680771545259530177,
677041109303777063,236726555736429,681897652180440892,388319113176635308,388600519433869079,393668237245765569,393668168526288833,393668444243056593,110293511724816188,676828765281802007,110009769240254356,681897513885849537,681897445166372801,393105356280256294,388600520239175495,681049721701357546,
681332364909172565,384096920611804999,388319113998718955,105224694350960455,104943150671550443,681897582873761682,681897651878450956,110009700520777518,676550520388933522,681332433897084710,672325097203390320,110011830270908238,110292206272862145,672328396006709125,672046989497816878,384095958019037055,
100160481014274620,379313013987170101,398523887020890094,398238977160861585,94812387150092831,95093862412016276,969773916566542225,970125691299518217,681615077373335429,681615008402200366,672043622226679664,965343914945107746,965273616279361425,398241244903593832,393386694086449029,397959701190629365,
397958601679001474,85805050187963114,85802851164707385,960413701081618235,955773765736945490,681332365194385205,94812387418528389,681050821481420582,95375337405504101,99597530490428065,398519283889690558,686468184527820619,686470383282640817,398523681130895145,398242206154184625,960558840626239377,
397956333936269138,90587994773478015,686190213992766056,680276902465985044,686190213707553518,675773302838614684,970124522783201214,685905234305963858,974420384237705093,969843047806490443,969844216037595057,974980035387807526,398238908424607665,974417085971257126,970199427549714262,970199496017532773,
686470383014205259,686750759284594473],[671764346006877455,357,100651687802518020,2405,667260746379506963,1347,671761047471994267,2371,676264647099364627,2371,667259646867879282,2405,671761047471994124,2405,959995821938652446,2419,
955772667051578211,1534340,379309714900727151,3429,974699729197938020,408,955771566715778477,2437,955772598315324244,1595780,969001922220725021,1602948,950987523711243037,1534339,681122358458791198,2436,
681122359534621571,1602949,685906402826457955,9920901,686469352777790820,1415,95934782365709679,3429,955771497996301741,2436,686187809333261700,1398,955772597507929381,2437,960627011137779055,391,
950987523711243037,1534340,955771566715778477,2436,959995822209176451,1595763])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_3 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1] (pr G2 128) 128 13 1 fba_g128_3 = false := by decide +kernel
lemma fva_g128_3 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_3 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBn))) fka_g128_3
set_option maxHeartbeats 0 in
def fba_g128_4 : ℕ × List ℕ × List ℕ := (127,[166082631662271,165121129413312,166289377294953,164021349349972,164982851599024,166152173222565,166083436968598,163952344660509,166082900097578,163883608406542,165052124723958,166082363226862,236727109384516,393386762822702996,680770445747902286,671765445516416846,
384097058084312871,236657836259591,384095820294870943,681616108467476433,393386762269054798,667261845889046357,109727126015661862,110293511708039121,676546122073986988,110009700504000287,681614939397510990,681614870678034254,392823812869281589,105223457400379159,100719857504573343,100439481502619449,
104944180641617836,383815514371348459,677041109270222663,676759565590812651,681615077390112660,110009769223477125,676832064370333452,672046920761562911,681262065438119733,676547290590304242,110293305516054465,681050890217674549,676550589125187489,99879006020786897,667543321134192422,398520452137572105,
398520452120795125,970055391543252745,969844147586553730,969844216322807697,969844285025507202,965340547959183172,681897651861673976,672325165939644287,676828765567014898,969777215906731785,398521620368676712,393668169063159800,398523887289325401,955773697017468754,85801751653079616,85803950676335276,
90308718534810197,99316055228504769,99879005752351448,970199427012843295,99597531027298821,99316056033811185,393105356297033525,398237808912979787,686752957770979113,960558909345716113,965062508973086473,397679256200763218,964780896809080821,960277297181710210,970199496000755542,90307619291618019,
95092762900388438,970196129820137302,686190214009543225,974701996133275493,974982371598358373,686186709282674514,960628110915753766,974698560411097006,970125691014305577,974137810017802015,960629210158946086,974137809480931246,685623759329253202,398520383401318185,398523680862459838,686752957502543806,
686469284039448497],[681616039733310724,374,676266846122620175,357,393105218574957140,336,392823812317723369,320,685906402002285905,389,681122358458791180,374,676264647099364620,1381,667257447844623727,3429,
955772598313235797,2439,955772667049489764,2438,969283397197435732,1602949,685624859379840388,1398,955772667051578211,1534341,685906403094893411,5726597,955772667051578211,1595780,685624859111404932,2422,
964499421566022942,1398,959995822209176451,1534323,974699729181160789,408,955772666227406117,2437,686469352761013589,1415,955772597507929381,2436,685908532574500126,1398,676266846122620271,3395,
950987523709154671,2387,681122358729315203,1534341,685623759870300957,5726596,950987523711243037,1591683,959995822209176451,9920901])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_4 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1] (pr G2 128) 128 13 1 fba_g128_4 = false := by decide +kernel
lemma fva_g128_4 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_4 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBn))) fka_g128_4
set_option maxHeartbeats 0 in
def fba_g128_5 : ℕ × List ℕ × List ℕ := (127,[93790312560980,166495787383158,165189848889792,236864279902525,96127278086550,96058558609699,234528337787238,93721576306973,235626473683224,235557754206637,165189278464385,236794973223200,235627832637709,236863977912589,234459316320733,236863424264642,
235558307854835,233360073128231,235559113161122,235558576290284,235627278989640,235622749141444,393105218572867413,234458779449713,165189295241616,676264647097276332,667260746377418519,379309714898638656,969283465107429310,95934782363621184,236863961135609,109727057296185173,
109448879780616170,232191842023915,388881994410579728,677111339770140432,110293511674484721,676266846120531728,965343983933020142,398523887322879801,384165159052203932,965340685398136644,969564940084139817,969282296876324683,685907433060783947,955772666225317652,686187809062737841,397960799360079698,
232191036717377,393735308528801651,672112960984012564,686469352775702417,686750828004071413,964499421563934654,685624859109316529,685906402000197458,974699729195849573,960628110378882928],[685906403092804872,389,955772667049489746,374,969564940908311911,374,950987523709154572,374,685623759868212669,388,959995822207088048,389,686187877784302933,2422,397960800452687204,1415,
685906402824369508,2422,955772667049489764,2436,955772598313235797,2437,959995822207088004,2419])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_5 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4] (pr G2 128) 128 13 1 fba_g128_5 = false := by decide +kernel
lemma fva_g128_5 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_5 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBn)))))) fka_g128_5
set_option maxHeartbeats 0 in
def fba_g128_6 : ℕ × List ℕ × List ℕ := (127,[94890092624327,166426799470851,235627312544040,236795828861245,236864263125458,96058575386930,236727092607449,94890059069927,94821356370320,234458242578746,164158771526019,235559096383891,234528321010069,236795258435989,235627295766871,236794704787791,
235626742118884,234527230490993,234528304232838,235627815860729,234528035797320,236726253746471,392823812315633642,235626758896115,164089783613725,165258266376679,667259646865790879,667538922819245888,969564871364663081,969282365595801419,236795241658758,681897514707932933,
681615970994968561,105507131131909904,105506031888717584,236657802705191,388882063130056464,393668444209502193,393668444226279173,970196128477960048,672396634178672540,965270316939171667,965339448179119885,969283396387952574,965343846494066670,955772597505840916,686187809331173161,681965684412077939,
964496123029051156,686469352758925186,959995821936564043,686187876976908114,685624859377751849,974699729179072342,974981203887347542,970196060026918768],[104874980432622904,3429,685906402807592321,389,955772598313235779,374,685906403076027892,389,969564872172057944,374,681122359532533025,374,969283397195347437,374,685623759599777098,388,
685906403092804964,1398,950987523709154590,2435,397679256739722526,1415,686187878052738389,1398,969283397195347285,1413,397958532961613188,2439])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_6 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4] (pr G2 128) 128 13 1 fba_g128_6 = false := by decide +kernel
lemma fva_g128_6 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_6 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBn)))))) fka_g128_6
set_option maxHeartbeats 0 in
def fba_g128_7 : ℕ × List ℕ × List ℕ := (127,[166426816248169,166495804160476,165258585143595,234528069351720,236795812084178,96127294863781,236726824171878,235627849415129,93790279006580,234526962055584,165258283153910,164089766836494,236863692700051,234459584756000,235558559513053,234528052574551,
21080542771542,234458796226944,233360089905462,234459601533231,234459333097964,236657819482422,235691468618044,234527247268224,235558291077604,164158754748788,671761047469905721,234523237513606,667257447842535232,969563771853035441,236794990000431,236863709477282,
681897445971679217,681616039731222277,236589083228502,677111271050663696,236726270523702,671764346004789008,110293511691261701,965344052937709416,384165159320639252,672397733690300180,965340616410224499,969563840572512177,965343915498755944,955771566713690012,685908532572411838,955771497994213276,
393737506746750733,681966783386834701,959992523401680796,672112960715577244,686750828020848393,955491123334436723,681122358456702733,974981203904124773,960627011135690608],[685906402824369552,389,969283465931601153,374,969001922218636577,374,104874842960115032,3429,681122358727226738,374,104593436451222785,3429,964499421834458408,389,397679256471287070,2439,
397960800167474517,2439,397960800184251748,2439,969283465931601252,1413,397960800435909973,1415,397959632473240964,1415])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_7 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4] (pr G2 128) 128 13 1 fba_g128_7 = false := by decide +kernel
lemma fva_g128_7 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_7 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBn)))))) fka_g128_7
set_option maxHeartbeats 0 in
def fba_g128_8 : ℕ × List ℕ × List ℕ := (127,[166151082703342,233358730950977,161753036192217,163952059447613,164020778924349,236863994690009,96127345195477,166151351138751,104874980430534409,162990255208725,92621796243748,100651619064174559,166426782693682,166495753828758,236795795306758,236864229571058,
235489303165357,233290816780704,166288790092223,236588814793195,233291353651542,104874842958026537,162852816255253,162921552509220,965343984235009849,393735377265055571,969564940906223464,969283397193258990,681966783655270259,965343846762501977,393737507015186291,685906403073939445,
686187877798991761,955772598311147332,686187877782214530,393738744519415656,681969051666438126,681969120402691944,685906402822281105,955772667047401299,397959632471152425,965343983949797122,969001922216548130,681122359530444578,397679256737634238,681122358725138291,685623759866124222,950987523707066125,
964499421832369961,393738607063684898,685623759597688651,686190007817557801,970058759586142041,393738675799938818,393738744502638425],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_8 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7] (pr G2 128) 128 13 1 fba_g128_8 = false := by decide +kernel
lemma fva_g128_8 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_8 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBn))))))))) fka_g128_8
set_option maxHeartbeats 0 in
def fba_g128_9 : ℕ × List ℕ × List ℕ := (127,[166219802180078,236657265834475,236725985311062,162921267296580,165051571075504,165120290552240,236795275213158,166220355828025,235695461595613,235695746808151,100651687800428526,166426765916451,166495770605989,235695193159953,236864246348038,236795778529778,
233291085216024,234389791537466,166357794781497,233290279909697,234390596843793,235489840036113,104593436449134541,965344052954486585,970058759619696441,681965753131554628,681965753148331859,393735377248278340,681964584900450061,393734209017173773,965343915230320386,685906402805503874,
686187878067427081,686187878050650101,393738675783161838,397960800165386114,397960800450598665,685906403090716425,397960800182163345,397960800433821685,969283465929512706,965344052920932185,397679256469198667,969564872169969497,397958532959524785,393737507820492578,681966784460576546,685905234842834878,
686188908305930161,959995822204999601,681968982946961186,685905234574399307,681969051683215106,681969120385914713,970058690883442434],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_9 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7] (pr G2 128) 128 13 1 fba_g128_9 = false := by decide +kernel
lemma fva_g128_9 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_9 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBn))))))))) fka_g128_9
set_option maxHeartbeats 0 in
def fba_g128_10 : ℕ × List ℕ × List ℕ := (127,[235696568891858,235696585668925,166357811558666,166289092081930,235695763585320,95989872687370,236726790617478,236658356353442,236727059053049,236658087917871,233359804692964,236658071140640,236658339576211,233359536257393,236727075830029,233359821470195,
233359553034624,236726807394709,236589620099522,234390865279311,235490376907202,236589351663951,165327254288864,94958795323887,94958778546656,165327271066095,95989839132970,95921136433614,235696535337458,235696552114438,165121112635887,165052376381920,
235695478372844,232191573588397,232191305152826,235695730030920,235489571600664,234390059973024,166288806869454,166357778004266,166220087392718,166151619574058],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g128_10 : BinarySearch.fcAllB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7,fba_g128_8,fba_g128_9] (pr G2 128) 128 13 1 fba_g128_10 = false := by decide +kernel
lemma fva_g128_10 : BinarySearch.fcBV (pr G2 128) 128 13 1 fba_g128_10 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBc fva_g128_8 (BinarySearch.fcBc fva_g128_9 (BinarySearch.fcBn))))))))))) fka_g128_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g128_0 : BinarySearch.fcChkB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7,fba_g128_8,fba_g128_9,fba_g128_10] [] (pr G2 128) 128 13 1 (0x7fffffffff) 0 = false := by decide +kernel
lemma chk_g128_0 : BinarySearch.chk [] (pr G2 128) 128 13 1 (0x7fffffffff) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBc fva_g128_8 (BinarySearch.fcBc fva_g128_9 (BinarySearch.fcBc fva_g128_10 (BinarySearch.fcBn)))))))))))) (0x7fffffffff) 0).symm.trans fkr_g128_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g128_1 : BinarySearch.fcChkB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7,fba_g128_8,fba_g128_9,fba_g128_10] [] (pr G2 128) 128 13 1 (0x7fffffff8000000000) 0 = false := by decide +kernel
lemma chk_g128_1 : BinarySearch.chk [] (pr G2 128) 128 13 1 (0x7fffffff8000000000) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBc fva_g128_8 (BinarySearch.fcBc fva_g128_9 (BinarySearch.fcBc fva_g128_10 (BinarySearch.fcBn)))))))))))) (0x7fffffff8000000000) 0).symm.trans fkr_g128_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g128_2 : BinarySearch.fcChkB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7,fba_g128_8,fba_g128_9,fba_g128_10] [] (pr G2 128) 128 13 1 (0x1fffffffffffffff800000000000000000) 0 = false := by decide +kernel
lemma chk_g128_2 : BinarySearch.chk [] (pr G2 128) 128 13 1 (0x1fffffffffffffff800000000000000000) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBc fva_g128_8 (BinarySearch.fcBc fva_g128_9 (BinarySearch.fcBc fva_g128_10 (BinarySearch.fcBn)))))))))))) (0x1fffffffffffffff800000000000000000) 0).symm.trans fkr_g128_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g128_3 : BinarySearch.fcChkB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7,fba_g128_8,fba_g128_9,fba_g128_10] [] (pr G2 128) 128 13 1 (0x7fffffffffffffe000000000000000000000000000000000) 0 = false := by decide +kernel
lemma chk_g128_3 : BinarySearch.chk [] (pr G2 128) 128 13 1 (0x7fffffffffffffe000000000000000000000000000000000) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBc fva_g128_8 (BinarySearch.fcBc fva_g128_9 (BinarySearch.fcBc fva_g128_10 (BinarySearch.fcBn)))))))))))) (0x7fffffffffffffe000000000000000000000000000000000) 0).symm.trans fkr_g128_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g128_4 : BinarySearch.fcChkB [fba_g128_0,fba_g128_1,fba_g128_2,fba_g128_3,fba_g128_4,fba_g128_5,fba_g128_6,fba_g128_7,fba_g128_8,fba_g128_9,fba_g128_10] [] (pr G2 128) 128 13 1 (0x3fffff800000000000000000000000000000000000000000000000) 1 = false := by decide +kernel
lemma chk_g128_4 : BinarySearch.chk [] (pr G2 128) 128 13 1 (0x3fffff800000000000000000000000000000000000000000000000) 1 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g128_0 (BinarySearch.fcBc fva_g128_1 (BinarySearch.fcBc fva_g128_2 (BinarySearch.fcBc fva_g128_3 (BinarySearch.fcBc fva_g128_4 (BinarySearch.fcBc fva_g128_5 (BinarySearch.fcBc fva_g128_6 (BinarySearch.fcBc fva_g128_7 (BinarySearch.fcBc fva_g128_8 (BinarySearch.fcBc fva_g128_9 (BinarySearch.fcBc fva_g128_10 (BinarySearch.fcBn)))))))))))) (0x3fffff800000000000000000000000000000000000000000000000) 1).symm.trans fkr_g128_4
def shards_g128 : List (ℕ × ℕ) := [(0x7fffffffff,0),(0x7fffffff8000000000,0),(0x1fffffffffffffff800000000000000000,0),(0x7fffffffffffffe000000000000000000000000000000000,0),(0x3fffff800000000000000000000000000000000000000000000000,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shardsCover_g128 : mFull shards_g128 = true := by decide +kernel
lemma chkAll_g128 : ∀ p ∈ shards_g128, BinarySearch.chk [] (pr G2 128) 128 13 1 p.1 p.2 = false := by
  intro p hp
  simp only [shards_g128, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact chk_g128_0
  · exact chk_g128_1
  · exact chk_g128_2
  · exact chk_g128_3
  · exact chk_g128_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strong128 (floor : Imp [] 128 13) (prior : ∀ e ∈ G2, HasGrade 1 e) : HasGrade 1 (128,13) := by
  apply gradeFromFloor (t := 1) floor (by decide +kernel) (by decide +kernel)
  intro S sw hl
  refine BinarySearch.rejectMinimum (Q := pr G2 128) (L := 14) (by decide +kernel) (by decide) (by decide) ?_ sw hl floor shards_g128 shardsCover_g128 chkAll_g128
  intro e he
  exact prior e (List.mem_of_mem_filter he)
lemma g_128 : HasGrade 1 (128,13) := strong128 p_128 G2ok
def P1 : List (ℕ × ℕ) := P1r ++ (128,13) :: P2
lemma P1ok : ∀ e ∈ P1, Imp [] e.1 e.2 := apI P1r_ok (consFloor p_128 P2ok)
def G1 : List (ℕ × ℕ) := P1r ++ (128,13) :: G2
lemma G1ok : ∀ e ∈ G1, HasGrade 1 e := apG G1r_ok (consGrade g_128 G2ok)

set_option maxHeartbeats 0 in
def fba_bf0_0 : ℕ × List ℕ × List ℕ := (255,[690412202043210388,690413301286402613,690411102531582524,681403903276841507,685907502635776703,690411102263147016,686186847325485792,690690447221291698,690690446952856105,690693745756175044,681683247966550681,690694844999367184,974351115290245500,690688247929600587,681400604741958387,690407803728263896,
685904204100893332,690406704216636016,686184648302230023,690688248198036180,681681048943295163,681399505230330507,668170250061183657,685903104589265452,690406704485071524,668170249792748064,690407803996699153,685908602684275236,970199497359587649,974701997475330369,685623897372064480,681122428300130851,
686185747813857903,676895905334524666,690127497267870386,676897004846152295,681120298013129369,668171349304375944,685626027659066047,690127496999434793,690689347709663809,690129627286436360,681682148454922792,668171349572811286,690131826309691957,690130727066499732,690689347441228467,690129627554871868,
690413370022656528,690412270779464388,676897005114587803,676895905602959923,676266915393535141,685275214159903771,680770515020905594,685276313671531755,685557857384496216,676548459106499602,681052058733870306,685556757872868483,685555658361240619,104665180153150638,109168848499997827,686118539578407358,
685274114648276158,979205596834265409,681053158245497919,979206696077457729,676269251872521279,680771614532533458,680771751988263999,114233062423887022,114234161935514755,397891461961578942,114516666865514942,113672379944762587,113672448395803867,681334701941685311,104383705159662653,108887373506509842,
104102230166174928,108605898513022117,685839401080683608,113390973402315882,685838301569055875,113390904951274602],[388883301206677353,374,109661223552898905,3446,677114776601581401,1415,681618376228951897,1414,685838232851666818,390,677114707865327420,390,388883301208767576,1530247,681618307492697873,391,
388883301208767064,9916789,685839332363294551,391,676833232620181378,390,681336832247551831,391,681827352426142809,2435,110010937506880601,2435,686471690061961187,407,691539338634288217,403,
672327365233301412,357,681615077392078697,2439,677111477764708244,2438,388882201141402808,2418,110010937508969560,1587591,681618376228951938,391,691256764414385241,403,677114776601581485,390,
672328464744929145,373,393386900280401080,2418,686471690061961187,408,681827352428231768,1587591,974350152699565992,2439,969848683375974353,408,686190146367863853,1601927,393737645294966696,2456,
974351252211193768,1415,685839332363294632,3429,672329564256556948,2405,393668375259200045,9920882,672329564256556905,2421,685837133340039080,3446,965345083748603649,407,681897651899284013,9920882,
110010937473326203,2433,686401320529255513,2419,398242344165529512,2456,681827352392588411,2433,686683895017593945,2403,685838232851666856,3445,397891599419398056,3463,393386900280401105,2437,
965345152468080552,2438,388882201141402625,2437,690692646196303721,390,974632796194683992,1520024,974632796192595033,371,681336832247551912,3429,691256763575523136,1432,979488239238862656,425,
974351184028588003,391,691257863624021883,408,681334633224296254,374,681966922203485953,407,681827352392587131,2439,110010937473324923,2439,686401320531344472,1586567,691256764380829563,408,
681336832247551790,1398,671836158430370472,2454,965345083748603816,2438,676833232620181294,2422,676833232620181416,3445,686190145562557623,1532278,970126859817802920,2454,686118608316749736,3446,
676832133108553534,374,681545877449431641,2437,686470521830856657,408,685837133340038954,389,974842803181935705,373,690692645927868308,374,691538239391095897,389,109729462530169433,2437,
974913171657677913,387,105507268606385336,2418,979205596853131176,408,676829934087388160,9912677,681333533714758864,9912693,681333533714758839,9843061,974842803181935705,403,686753095513889960,2455,
110011967745383608,2418,105507268606385153,2436,686190145562557607,9990535,676829934087388343,9843045,110011967745383633,2436,398523818873805992,2455,686401320514567394,1582471,691256695661352897,408,
686401320512478435,2418,979485972301436736,425,672327365233301328,2421,974632796177906914,1515928,686683895000816867,2402,685838232851666734,1415,685838164115412884,1381,690692645944645377,406,
691257794904545217,408,691255595881289536,1432,979206696096323496,408,672328464744929104,2405,685839263627040617,1397,393386900280401105,2436,685839332363294510,1414,690692646213081041,406,
974843902961998937,403,965344052956454072,389,677111477764708160,3463,681615077392078656,3462,388882201141402808,2421,686471688971443280,385,686471688971443280,369,969848752078673769,408,
388882201141402625,2436,974630528147871552,1432,965345152451303316,407,681333533712669905,2435,676829934087388343,9851237,691256764397608163,402,965345152451303232,1432,969848752078673728,1431,
691256763575524500,369,104099962157095572,2433,691539338063862889,385,108604661296093801,2433,974632589732173761,408,965343915502812239,1511814,388883163734169467,2439,685839263627040746,391,
393386763361539963,2439,686402214117332737,391,690692645927868308,406,690692645927868224,1432,691539338617511139,402,105506169346414400,3463,402747043304527784,2456,686401114068834241,1415,
686470521277208384,2455,388882063687760975,1513846,685838164115412762,390,393739844033009472,1432,686471688988220600,338,686471688988220600,354,686402282853586793,391,690692646196303721,406,
974069709051877166,408,974069709051877166,407,99877837523212984,2418,99877837523212984,2421,99877837523212801,2437,690692646196303680,1431,974632796175817955,370,681966921918273344,2456,
99878937034840760,2402,99878937034840785,2437,974913171640900835,386,110009769242220352,3463,104382605381687854,2438,108886205009058350,2438,689850556939852334,406,403310130445245529,371,
403310130445245529,403,114516666884380584,3463,398243443928815424,1432,110011967745383633,2438,676829934085299384,2419,965063609042417063,1603973,965063609042417063,1669509,965063609042417063,1673605,
681969120421436600,390,676829934085299201,2435,105507268606385153,2438,105507268606385336,2422,681333533714758839,1530213,681333533714758864,9916789,676829934087388160,9916773,681333533712669880,2403,
402747043572963240,1432,685837064603785108,1414,681615008689380561,2434,685837064603785065,1415,672327365233301396,2437,672327365233301396,2438,685838164115412884,1413,685838164115412929,1415,
388882063685672016,2417,969846415616466000,385,672328464744929129,2437,672328464744929129,2439,685839263627040617,1413,685839263627040705,1414,403310130160032936,2386,965343915500723280,369,
393386762824670288,2417,691539338080640209,402,691539338080640209,354,677111477764709456,2421,686118677019449152,3446,970126928520502336,2454,960558910169765800,2454,970130227055385793,406,
104099962157095572,2437,974069709051877288,1430,108604661296093801,2437,686190145543690048,2455,691256763592301569,402,691256763592301569,354,686190145543690048,2456,690692645944645544,1432,
960558841433511760,374,690974120921356200,2439,691255595898066856,1432,969848752097540816,1593698,965345152470170112,1593698,691539269898034222,402,974704195980580776,424,974632727189994541,1515928,
960558841433511760,390,690692646213081000,1431,690692645927868224,2438,690692645927868308,407,690974121189791656,1415,979485972318214056,425,686401251526655021,1582471,105506169346415764,2433,
691256695678131246,402,970200596621645736,425,969848683375975633,354,965345083748604929,354,105506169346415696,2420,686470521277208384,2456,690692646196303680,2422,393737645563402152,2439,
686753096319196206,407,970199497378453416,407,398523819679112238,407,690692646196303721,408,965343984236976040,2456,685839332363294510,1398,681966921918273344,2455,110009769242221673,2433,
676832133108554798,2435,110009769242221648,2420,676832133108553640,3461,676829934087386535,14115173,681333533714757031,14115189,969846484352718760,2455,681053158532798553,2435,685838232851666734,2422,
677111409062009857,2434,681334633224297518,2435,100160481016240729,2435,681334633224296360,3461,685837064603785024,3446,690692645944645377,407,685838232851666689,1413,681616245925173849,2437,
685837133342127568,1603957,685837133342127527,5794165,685837133342127527,5798245,105437999661136617,9850947,685837133342127360,1599845,672329564256556864,3446,974350083980089256,2439,681333533714757031,9992549,
960558910169765800,2455,676829934087386535,9988469,681897583179807277,9920882,114513369138026304,3463,970200596604868416,424,393737645278189376,2456,960558910169765800,2456,677114776603671128,1595765,
685839332363294673,1413,974351183491717032,1415,393668306539723309,9920882,974704195963803456,425,398242344148752192,2456,690692645944645544,2438,691256695124481856,1432,970130158354774695,1665362,
681966921935050664,2456,690692646213081041,408,974069640315623361,408,974069640315623361,407,690692646213081000,2422,686470521293985704,2455,979488170787821376,425,970130227074251431,1665362,
681334633226384685,1603974,686190145562555815,9990534,680490071106869371,2433,681336832249640359,5797237,676833232622269863,5797221,95374237895842488,2418,686190145562555815,1603990,680490070838433985,2433,
680488971326806121,2433,675985371699435668,2433,675985371699435600,2417,99597530760829633,2433,95374237895842305,2434,95093862413982313,2433,676832133110641965,1603974,95092762902354580,2433,
95092762902354512,2417,676829934087386535,5798278,960558910171854247,1603989,680771614819834083,2434,99879006022752995,2434,681333533714757031,1674630,95375337407470289,2434,99879005754317358,2434,
676266915412400312,2418,676266915412400129,2434,680770515039770833,2434,680771614551398446,2434,965063609042417063,1534341,965063609042417063,1599877,965063609042417063,5796214,965063609042417063,1669510,
969567208669787559,1673590,969567208669787559,5796230,686190145562555815,9990518,99597531029265019,2433,965063540308251454,6561556869])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_0 : fcAllB [] (pr P1 0) 0 14 fba_bf0_0 = false := by decide +kernel
lemma fva_bf0_0 : fcBV (pr P1 0) 0 14 fba_bf0_0 := fcAllB_val (fcBn) fka_bf0_0
set_option maxHeartbeats 0 in
def fba_bf0_1 : ℕ × List ℕ × List ℕ := (255,[165052393037025,166151904664758,167251684727895,166220640918563,167320152546407,167319884111021,166220372483177,165120860855444,166151636229121,165052124601388,167320420981951,164021349227580,167320689417364,167251953163308,165121129290830,970130158350596399,
690694913702067290,690693814458874970,677111477762619813,681615077389990266,690130864505453658,974985739121031489,690131963748645978,691256763573434773,403310130409601404,974985739137808809,403025220281137410,403306695257848274,691539338061773162,965345152449214869,686332120550964443,686402489026706651,
969848752076585322,109661223550810583,685486527121292462,965345015010261397,393737645544536469,398242344683534698,397891599400532414,691539269879167426,691257794902456770,969848614637631850,685487626901355651,691538170635975106,691256695659264450,686471690043095420,114515705631702235,979206696094235049,
114798142127438211,974911865683540330,979205596851042729,115079617372584280,680843288963546297,685345789079289017,397891599417309483,686118677017360830,974632589730085314,974630390706829717,974351114753374570,974912965195168194,974350015241746837,686683689091954946,686190215099939930,686402214115244290,
403309993255860527,685838232849578371,970126791079459153,685839332361206104,680561745519017041,690976456844606511,685064245634759761,974704195978492329,970200596619557289,403028518547585327,974982372957190569,403310130141166018,970130296074762586,979488239236774209,115079754794760450,979768614701857089,
398454687329777922,689849320792489007,689569013761670268,403309992970647914,166152173100051,672327365231212965,685838164113324315,686401114066745627,403028517993937301,672328464742840698,685839263624952299,686683688555084267,114798142110660891,689567845799001282,970130089614342594,970200596602779969,
115079617355807211,689849388706659330,167251416292602,689567914518477948,689850488218287314,685064314085801041,685345720628247737,974704195961715009,689849320255618050,680843220512505017,680561813970058321,689850419767246034,114516666882292011,689850420035681327,167251147856965,686471690059872740,
689568945042193602,689850488755158244,166220909354107,689849389511965924,163952612973775,690976456827829442,681966922201397506,686470521828768210,690694913131641962,393739844030921109,979767447024400809,686683757828209002,686402282851498346,681053295969664106,676550795853921386,690693813620014229,
686470521811990890,681966922184620437,686190213992643665,690694913148419282,974843902926354812,681545877447343210,690693813636791298,686049477074713774,686190214009420985,974912003122493802,974630528145783189,398243443926727018,974842803146291580,974985670669990209,672329564254468542,109729462528081002,
686050576854776963,974845002739972442,685837064601696702,979485972316125609,691539269610731882,690976457113042148,979767447007623489,690976457129819226,685629532083944538,979485972299348289,676622401548680282,691256695122393493,979768546250815809,676340926286756911,685348056822021167,970130227053296066,
979488170785732929,685629463632903258,99877837521124370,974351183489628626,99878937032752354,691537071124347242,681897583175629119,691256764378741116,393668306535545151,671837257939909634,398173074377242907,398454549353953771,676269320860433652,680771820976176372,691255595879201173,671837326659386578,
104099962155007141,684924676914379941,974982372940413249,108604661294005370,115078586848868626,114796012360530237,684923577134316752,974350083978000642,691539338598644092,691257863621933436,681966921932962233,690974120902490517,690974121170925930,402747043285662101,691538239355451772,402747043554097514,
970126928518412625,681616245906308340,686119845533678653,960558841431423313,686120945045306386,686470521291897273,974069640313534914,690693814425320572,680562845030644885,676340926555192548,685348057090456804,690694913668512892,689850557206199524,691255595895978242,685347919651503314,689848221012425730,
685907571338476729,685066444658015338,680844320024132610,686470521275119953,690413369989102639,690976457096264828,690413369720667346,681966921916184913,690694913685290212,689566746018938005,685066582096968828,690412270209039362,691537071141124562,689848221280861394,681403971979541689,108605898244586731,
685908670581669049,105506169344326053,690412270745910319,676059451293269186,671555851665898602,685066581828533442,110009769240131962,690693814442097892,104102229897739291,685907571321699409,671555782946421909,686190215066385532,685066513109056618,681403972247976962,685907571875347666,680562913481686165,
690413369703890026,689566746287373418,689568944773758058,685908671386975279,685908671370198210,686190215083162852,681403971962764369,690413369972325570,685907571858570346,681403972231199893,689569013224799338,690132032199687258,690412270729133250,676059451561704572,680844388475173890,685347988102544594,
689567845262130325,114513369135937982,685908670564891729,689567913713171605,113390972865444952,108887373238074456,113390904145968259,104383704891227267,690412270192262293,689850556937763887,685557857669708419,685556758158080686,681053158530710122,685557857938143963,685839401651108501],[974351252764841817,391,691256764414383961,408,691257863657576281,408,686190145543690064,391,393386900834047833,2439,388883301206677337,2439,681827352426141529,2439,685837133340039121,1415,
110010937506879321,2439,685837133340038913,1414,686190146348996545,391,388883301206678633,373,969848752095451089,408,965345152468080385,407,388882201141401512,3463,393386900280399784,3463,
686471690078738265,407,686471690078738265,408,105437999659048154,2422,681334633224296238,2439,676832133108553518,2438,681970219933062913,407,676829934085298088,3463,681333533712668584,3462,
686190146365773614,391,388883301206678617,2437,393386900834049113,2437,681334633224296238,2438,676832133108553518,2439,686473819560433617,408,388882201141401528,2422,965344052956452792,390,
681333533712668600,2405,676829934085298104,2421,686402351589840858,391,686402420326094740,391,686190145560467384,391,686683826012904494,2402,681336832247551953,1397,676833232620181249,1381,
965345152468080552,1432,969848752095451048,1431,676832133108553656,1381,681334633224296376,1397,974632796192593753,408,686401320529254233,1415,686190146365773614,408,686190146365773614,407,
686401251524566062,2418,681897651897195582,370,685837133340038913,2405,685837133340039121,2421,677111409062008577,2438,681615008689379281,2439,974630459445172136,1432,686190145560467384,390,
686190145560467384,374,393668375257111614,370,974913102652988462,386,393738744521381712,391,974701997494196136,424,970199497378453416,425,974632727187905582,370,974632658468427566,408,
686401182805088046,1415,393737645278189392,391,974069709051877166,391,686401251524564782,1415,974632796175816675,408,686401320512477155,1415,691257794921322286,408,676833232620181294,1415,
681333533712668600,1398,681336832247551790,1414,974632727187904302,408,686473819560433576,1431,681970219933063080,1432,691257863640799203,408,691256695678129966,408,676829934085298104,2422,
691256764397606883,408,686190145560467368,2456,686190145560467368,2455,969567139931445097,406,393737645563402152,1432,388882063685670736,2422,676829934085297937,357,676829934085297921,2437,
398242344702400424,1432,677114776601582681,2421,388883163734169483,374,686190146348996416,1430,110292343747337262,2439,681333533712668641,373,965344052956452776,2456,681333533712668625,2437,
681615008689379240,3462,677111409062008744,3463,965063540304074560,2437,965063540304074644,406,393668375257111598,2438,686190145543690048,2454,965345152468081665,354,110293442990529582,2439,
969848752095452369,354,965343915500722000,390,969846553072195496,2455,681897651897195566,2438,109661086080391035,3446,681333533712668625,2439,960558910169765816,391,974985670688857256,423,
979488170804598696,425,110011967745382312,3463,681969120421435304,2456,676829934085297921,2438,691256695141259176,1432,686471620537178024,2455,105507268606384040,3463,686190146365773736,1398,
686190146365773736,1414,960558910169765800,2453,969567208667699153,408,969567208667699112,1431,969567208667699112,1415,969567208667699153,390,970130227072162862,406,970130227357375577,406,
965063609040328616,1432,965063609040328449,407,965063609040328616,2439,965063609040328449,374,677114707865327587,1415,690976319659398976,1415,965063609040328616,2438,402744844801365824,2456,
969567208667699112,2422,681618307492698083,1414,402745944312993600,1432,686190145560467368,2454,965345083748603816,1432,969848683375974312,1431,690975220164548520,2439,690692646213081000,1415,
690976319676176296,1415,690975220147771200,2439,965063540304074560,2439,690692645944645544,2439,969567139931445056,1415])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_1 : fcAllB [fba_bf0_0] (pr P1 0) 0 14 fba_bf0_1 = false := by decide +kernel
lemma fva_bf0_1 : fcBV (pr P1 0) 0 14 fba_bf0_1 := fcAllB_val (fcBc fva_bf0_0 (fcBn)) fka_bf0_1
set_option maxHeartbeats 0 in
def fba_bf0_2 : ℕ × List ℕ × List ℕ := (255,[105437999656958443,166289645608172,167389425671178,167526898179100,167389157235765,166289377172628,167458161925311,167457893489898,166358381862054,165189865544895,393386900831959402,388883301204588906,686402351587752411,686683826564463067,979488239253551529,979768614718634409,
691257863655487834,237895592024851,691538239389006170,237895323589438,691256764412295514,691539338632198490,403310130157943087,234528337664995,234528069229331,686471688986130873,974913033931421999,167526327753688,686471690076649818,969848752093362642,965345152465991938,974630459443083522,
974911934419794386,974351252762753370,974632658466339119,685837133337950507,970126859815713209,677114776599493038,681618376226863491,974913171655588186,974632796190505306,403028518010714370,403309992987425234,167320135769082,237826855771116,965344052954364345,969846553070107065,237826587335452,
686190146346908098,974842803179845978,974701997492107689,970130158619032036,974843902959909210,393738744519293265,681969120419346873,398241244903471441,677111409059920146,970199497376364969,681615008687290850,686471620535089593,686471688969353553,236796332055462,969846484350630329,235696820427729,
970130227070073135,234528320887675,403310130426378724,234528052452262,691256763590211842,237895306812369,237895575247782,691539338078550482,398454687380109717,965343984234887609,115079754845092245,110010937504790890,691257794919233839,681827352424053098,691538170652752175,974632796173728228,
974913171638811108,974351252209105362,393386900278311394,974350152697477378,979768546267593129,388882201139312914,979488170802510249,388882063683582373,393737645292878265,686473819558345170,965343915498633553,393386762822580602,115078586865645955,403027488040647002,686190145558378937,398454480919689490,
403307863505729882,398173005942978877,114796012377307566,398242344146663761,398242344163441081,393737645276100945,676829934083209490,681333533710580194,969846415614376273,686190146363685167,115079754811537770,398173074394020227,398454687346555242,398454549370730840,681970219930974466,974913102650898735,
691256695676041519,236863977790419,686683895300716949,686402420324006293,105437930920704378,115079754828315099,110293442988439871,398454687363332571,691539269895944495,974632727185815855,110292343745247551,398454549655943555,398173074679232942,398173005674543491,691256764395518436,398242344700312018,
393737645561313538,974985670686767529,686401182802999683,686683757291338072,398454480651254104,686190145541601617,691539338615421412,970130296057985508,969848683373885906,965345083746515202,970130227355285850,388883163732081036,393386763359451532,403307794769475887,691256695139170562,398524987656468826,
970130296041208188,403027488023869924,167388888800472,403307863488952804,686118608314661163,403027419304393007,677114707863238973,681618307490609426,691539269627509202,686755363539745114,676832133106465087,114795943641053571,691257863638710756,110011967743293922,681827352390498700,974845002706418044,
681334633222207807,115078518129391960,676833232618092931,681336832245463384,686755294803491119,398523818854938961,686753095495022929,691538239372229092,398524918920214831,105507268604295442,110010937471236492,686401320527165870,686683895015504259,969567208665610706,965063609038240002,686753096317106479,
686753096300329410,398523819677022511,398523819660245442],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_2 : fcAllB [fba_bf0_0,fba_bf0_1] (pr P1 0) 0 14 fba_bf0_2 = false := by decide +kernel
lemma fva_bf0_2 : fcBV (pr P1 0) 0 14 fba_bf0_2 := fcAllB_val (fcBc fva_bf0_0 (fcBc fva_bf0_1 (fcBn))) fka_bf0_2
set_option maxHeartbeats 0 in
def fba_bf0_3 : ℕ × List ℕ × List ℕ := (255,[166358365084652,96058608819092,94958828755903,166427101338534,236795828738923,235696585546603,166495804038124,96127328295916,237895340366767,237895608802180,166426816125844,165327304498111,167664303577866,167595315665717,167664320355263,167595332443114,
237964328279004,238032779320284,166357811436393,165258299808660,236864279780203,235627312421651,236726824049635,237826604112772,237826872548185,165327287720782,166426799348515,238032796097430,237964345056150,96058575264694,235696853982127,94958795201505,
236796365609860,236727612578796,235628100950812,236865101863830,236795258313595,236865085086684,235695746685862,236863994567488,236727092484928,235627295644582,236726807272315,236727075707859,235627832515539,235627849292608,236795275090915,235695763462931,
235628117728132,236727629355865,235696837204798,236796348832531,236864263003125,167457608276952,166289628830587,236864246225805,236865051532035,238032510884740,235696551992205,236795795184525,166495787260795,236795811961845,237963791408047,96127311518587,
235696568769525,167457323064237,97227108358965,97295827835658,167526310976359,97158355327994,167526294199290,237826335677228],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_3 : fcAllB [fba_bf0_0,fba_bf0_1,fba_bf0_2] (pr P1 0) 0 14 fba_bf0_3 = false := by decide +kernel
lemma fva_bf0_3 : fcBV (pr P1 0) 0 14 fba_bf0_3 := fcAllB_val (fcBc fva_bf0_0 (fcBc fva_bf0_1 (fcBc fva_bf0_2 (fcBn)))) fka_bf0_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_bf0 : fcChkB [fba_bf0_0,fba_bf0_1,fba_bf0_2,fba_bf0_3] [] (pr P1 0) 0 14 0 FF 1 = false := by decide +kernel
lemma chk_bf0 : chk [] (pr P1 0) 0 14 0 FF 1 = false := (fcChkB_eq (fcBc fva_bf0_0 (fcBc fva_bf0_1 (fcBc fva_bf0_2 (fcBc fva_bf0_3 (fcBn))))) 0 FF 1).symm.trans fkr_bf0
set_option maxHeartbeats 0 in
def fba_bf1_0 : ℕ × List ℕ × List ℕ := (255,[685275214445247037,100160481014283370,685276313956874770,685274114665183787,104665249141193947,685557857669839491,685839401651239573,685556758158211758,681053158530841194,685557857938275035,686332120551095515,686402489026837723,685487626901486723,686050576854908035,685486527121423534,686049477074844846,
99877837521255442,676550795854052458,681053295969795178,99878937032883426,114515705631833307,681545877447474282,109729462528212074,680771614817876724,95093862412024954,684994769975474923,397891599400663486,99879005752359999,99597531027307660,680490070836476626,403310130409732476,99598630538935504,
104102298885782693,680490071104912012,684993670732282576,684994770243910309,684992570952219326,104102299154217986,684994770512345602,676266915410442770,684993670463846939,680770515037813474,680488971324848762,675985371697478309,680771614549441087,685275214176811651,104102298617347307,685276314225310314,
99598630270499867,685276313688439384,95092762900397221,99597530758872274,104099962155138213,95094961923652798,108604661294136442,686118677017491902,684923577134447824,680771820976307444,974842803179977050,974843902960040282,970130227053427138,691257863655618906,691538239389137242,676269320860564724,
684924676914511013,672329564254599614,685837064601827774,680771751988395071,974982372957321641,676269251872652351,965345152466123010,969848752093493714,970130089614473666,965345083746646274,686119845550587054,974913171655719258,969848683374016978,403307863505860954,974632796190636378,686120945062214787,
691256695139301634,691539269627640274,104665180153281710,109168848500128899,114513369136069054,114516666865646014,403027488040778074,681616245923216490,686118539578538430,681052058734001378,680770515021036666,99880036544511019,104383704891358339,686120945045437458,114234161935645827,974632796173859300,
686119845533809725,681616245906439412,114233062424018094,974913171638942180,685275214160034843,393737645561444610,398242344700443090,113672379944893659,685276313671662827,113390972865576024,108887373238205528,113390904146099331,676266915393666213,397891461961710014,403310130141297090,104102229897870363,
108605898244717803,685557857384627288,690976457096395900,403310130443286874,113672448395934939,685556757872999555,685555658361371691,676548459106630674,403310130426509796],[388883301206809705,373,388883301206808425,374,686402420326225812,391,686402351589971930,391,681333533712799713,373,676829934085429009,357,109661223553029977,3446,393668375257242686,370,
681897651897326654,370,974351184028719075,391,686190146349127617,391,388883163734300555,374,681618376229083010,391,677114776601712557,390,397891599419529128,3463,690692645944776449,406,
690692646213212113,406,672327365233432484,357,974351252211324840,1415,672328464745060217,373,681618376229084290,389,974350152699697064,2439,681336832247682903,391,676833232620312450,390,
677114776601713837,389,677114707865458492,390,681618307492828945,391,685839332363425623,391,402747043573094312,1432,685838232851797890,390,685837133340170152,3446,402747043304658856,2456,
109661086080522107,3446,960558910169896872,2454,974069709052008360,1430,105437930922925161,2422,690974120921487272,2439,690974121189922728,1415,397891599419530282,354,676832133108684606,374,
676829934085429176,2422,681334633224427326,374,681333533712799672,1398,105437999661267689,9850947,685837133340170193,1415,685837133340169985,1414,685837133340170026,389,681334633224427432,3461,
685838232851797761,1413,686402214117463809,391,676832133108684712,3461,685839332363425745,1413,676833232620312366,2422,681336832247682862,1398,965063609042548135,1603973,685839263627171818,391,
114516666884511656,3463,979205596853262248,408,685838164115543834,390,979206696096454568,408,686402282853717865,391,686190145562686887,1603990,960558910171985319,1603989,95374237895973377,2434,
95375337407601361,2434,99879006022884067,2434])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_0 : fcAllB [] (pr P1 0) 0 14 fba_bf1_0 = false := by decide +kernel
lemma fva_bf1_0 : fcBV (pr P1 0) 0 14 fba_bf1_0 := fcAllB_val (fcBn) fka_bf1_0
set_option maxHeartbeats 0 in
def fba_bf1_1 : ℕ × List ℕ × List ℕ := (255,[388883301204719978,393386900832090474,110010937504921962,235627832646611,686683895300848021,686402420324137365,236727075838931,681827352424184170,115079754845223317,398454687380240789,166289645739244,388882201139443986,393386900278442466,167389157366837,167389425802250,167526898310172,
115079754828446171,235627295775654,236726807403387,681333533710711266,237894770072511,398454687363463643,114796012377438638,676829934083340562,237895306943441,115078586865777027,237895575378854,110011967743424994,236863977921491,677114776599624110,165052393168097,166151904795830,
105507268604426514,974985739137939881,681618376226994563,236796332186534,235696820558801,110010937471367564,686683895015635331,104946724134681749,686401320527296942,398454549656074627,398173074679364014,100161580525911214,104665248872758403,681827352390629772,970130158619163108,238032477461414,
237963757984721,970130296058116580,681615008687421922,104383773879270418,99880105532423229,677111409060051218,681615077390121338,95376436917140523,677111477762750885,676833232618224003,681336832245594456,970130227070204207,686683826010945880,686401251522607491,115078586848999698,114796012360661309,
686683894998858002,686401320510519613,237826319031231,234528589454271,398454549370861912,974351252209236434,398173074394151299,974350152697608450,388882063683713445,110009769240263034,110293442988570943,110292343745378623,114795943641184643,393386762822711674,115078518129523032,393668306535676223,
974630459443214594,974911934419925458,681334633222338879,685839332361337176,685838232849709443,686190146347039170,388883163732212108,677114707863370045,681618307490740498,676832133106596159,393386763359582604,105506169344457125,681897583175760191,104383774147705962,970130296074893658,398454687329908994,
974985670686898601,115079754794891522,104383773610835032,686118608314792235,99880105263987843,398454549354084843,99879006020795636,95375337405512930,685838164113455387,970126859815844281,398173074377373979,685839263625083371,115079754811668842,115079617372715352,672328464742971770,672327365231344037,
95374237893884946,114798142127569283,398454687346686314,979205596851173801,970130296041339260,979206696094366121,686401114066876699,398173005674674563,970130158350727471,974845002740103514,686683688555215339,686683757291469144,686402214115375362,685837133338081579,974845002706549116,686683689092086018,
398454480919820562,398173005943109949,403309992987556306,403028518010845442,686401182803130755,115079617355938283,114798142110791963,398454480651385176,686753096300460482,970130089882909052,398523819660376514,974351183489759698,974350083978131714,166289377303700,681897651895236927,165189865675967,
109661086078433785,109661223550941655,686402282851629418,686683757828340074,393668375255152959,167458162056383,166358381993126,167457893620970],[105437999659179226,2422,974351252764972889,391,686190146365904686,391,686190145560598456,391,965063609040459688,2437,960558910169896872,2453,960558910169896888,391,974069709052008238,391,
686190145560598440,2454,690692645944776616,2439,690692646213212072,1415])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_1 : fcAllB [fba_bf1_0] (pr P1 0) 0 14 fba_bf1_1 = false := by decide +kernel
lemma fva_bf1_1 : fcBV (pr P1 0) 0 14 fba_bf1_1 := fcAllB_val (fcBc fva_bf1_0 (fcBn)) fka_bf1_1
set_option maxHeartbeats 0 in
def fba_bf1_2 : ℕ × List ℕ × List ℕ := (255,[236795828869995,235696585677675,237964345187222,238032796228502,236863994698560,237963791539119,234528606231340,238032511015812,236796365740932,236796348963603,235696854113199,235696837335870,237895592155923,686683826564594139,237895323720510,686402351587883483,
166427101469606,237964311632747,167664320486335,238032762674027,167595332574186,97295811189652,97227091712959,236795812092917,167457323195309,235696568900597,237964294855427,237963506326404,238032225803097,97158389013464,237826335808300,167664286931860,
167595299019711,238032745896707,236795275221987,235695763594003,235695746816934,236795258444667,236727092616000,235627849423680,237826587466524,235696552123277,236795795315597,166357811567465,237826855902188,165258299939732,237963774761790,238032494238483,
96058608950164,94958828886975,974351252762884442,237963489549084,238032209026028,236727612709868,235628101081884,167664270154540,105437999657089515,167595282242391,686755363539876186,398524987656599898,398523818871847353,686753095511931321,234528052583334,96058575395766,
234528321018747,165327304629183,166426816256916,94958795332577,165120844208940,167526327884760,166220892707603,166220355836673,97295861521180,970130227355416922,686190146363816239,105437930920835450,690976319674218962,690975220162590978,686190145558510009,969567208665741778,
965063609038371074,398523819677153583,686753096317237551,398524918920345903,690692646211123666,686755294803622191,690692645942688002],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_2 : fcAllB [fba_bf1_0,fba_bf1_1] (pr P1 0) 0 14 fba_bf1_2 = false := by decide +kernel
lemma fva_bf1_2 : fcBV (pr P1 0) 0 14 fba_bf1_2 := fcAllB_val (fcBc fva_bf1_0 (fcBc fva_bf1_1 (fcBn))) fka_bf1_2
set_option maxHeartbeats 0 in
def fba_bf1_3 : ℕ × List ℕ × List ℕ := (255,[234528069360403,234528337796067,166289628961659,236864279911275,238032779451356,237964328410076,237826604243844,166495787391867,237826872679257,96127311649659,236865101994902,237895340497839,237895608933252,166358365215724,235627312552723,236726824180707,
235628117859204,236727629486937,166495804169196,167595315796789,96127328426988,167664303708938,236865085217756],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_3 : fcAllB [fba_bf1_0,fba_bf1_1,fba_bf1_2] (pr P1 0) 0 14 fba_bf1_3 = false := by decide +kernel
lemma fva_bf1_3 : fcBV (pr P1 0) 0 14 fba_bf1_3 := fcAllB_val (fcBc fva_bf1_0 (fcBc fva_bf1_1 (fcBc fva_bf1_2 (fcBn)))) fka_bf1_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_bf1 : fcChkB [fba_bf1_0,fba_bf1_1,fba_bf1_2,fba_bf1_3] [] (pr P1 0) 0 14 1 FF 1 = false := by decide +kernel
lemma chk_bf1 : chk [] (pr P1 0) 0 14 1 FF 1 = false := (fcChkB_eq (fcBc fva_bf1_0 (fcBc fva_bf1_1 (fcBc fva_bf1_2 (fcBc fva_bf1_3 (fcBn))))) 1 FF 1).symm.trans fkr_bf1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_2 : chk [] (pr P1 0) 0 14 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_3 : chk [] (pr P1 0) 0 14 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_4 : chk [] (pr P1 0) 0 14 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_5 : chk [] (pr P1 0) 0 14 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_6 : chk [] (pr P1 0) 0 14 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_7 : chk [] (pr P1 0) 0 14 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_8 : chk [] (pr P1 0) 0 14 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_9 : chk [] (pr P1 0) 0 14 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_10 : chk [] (pr P1 0) 0 14 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_11 : chk [] (pr P1 0) 0 14 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_12 : chk [] (pr P1 0) 0 14 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_13 : chk [] (pr P1 0) 0 14 13 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseT_14 : chk [] (pr P1 0) 0 14 14 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseFloor : Imp [] 0 15 := by
  refine imp_of (E := []) (Q := pr P1 0) (Z := 0) (L := 15) (Or.inl rfl) (by decide +kernel) (by decide)
    (fun e he => P1ok e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ?_)
  interval_cases t
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_bf0⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_bf1⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_2⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_3⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_4⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_5⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_6⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_7⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_8⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_9⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_10⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_11⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_12⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_13⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact baseT_14⟩
set_option maxHeartbeats 0 in
def fba_si_0 : ℕ × List ℕ × List ℕ := (255,[690413301286542390,690412270779604165,690131826309831734,685623897372204257,681122428300270628,690127496999574570,685626027659205824,689844922511236276,690411102531722301,676334055161306268,667326924642819095,667326924374383753,680555149036592316,685058748395527176,680770515021045371,685341254147611797,
689562279555079333,685058679659273261,689844854043417618,681403903276981284,676051480672967732,667044350154480810,667044349886045217,690406704216775793,685838301569195652,685839401080823385,690407803996838930,108605898513161894,685904204101033109,690688248198175957,686184648302369800,668170250061323434,
681399505230470284,680837655057112264,685627127707704357,690693745756314821,690690447221431475,690690446952995882,681400605010533576,690689347441368244,690689347709803586,680771751988403776,676897004846292072,685555658361380396,676548459106639379,668171349304515721,668171349572951063,104665180153290415,
974351115290385277,686185747813997680,979206696077597506,979205596834405186,114234161935654532,114233062424026799,104383705159802430,681053158245637696,680771614532673235,675987639440219859,671766751756918316],[105437999661276394,9850947,681618376229091674,1414,677114776601721178,1415,110010937507020378,2435,686190145562697400,1532278,110010937509109337,1587591,393668375259339822,9920882,393386900280540857,2418,
973788234094041817,1573380,388882201141542585,2418,672327365233441189,357,686190145562697384,9990535,960278534991993538,1442308,686471690062100964,408,681618376229091715,391,677111477764848021,2438,
685837133340178857,3446,686190145545920064,9990535,686190146349136193,1414,969848683376114130,408,681336832247691567,1398,681053158532938330,2435,686683895017733722,2403,686401320529395290,2419,
672329564256696725,2405,685837133340178731,389,691539338617650916,402,105507268606525113,2418,965345152468220329,2438,110010937473464700,2439,676829934087528120,9843045,680771614819973860,2434,
979206696096463273,408,979205596853270953,408,691256764397747940,402,686471688971583057,385,979488239239002433,425,676829934085438978,2435,691538239391235674,389,681966922203625730,407,
686401320531484249,1586567,974913171657817690,387,974632796194823769,1520024,691257863624161660,408,676266915412539906,2434,691257794904684994,408,691255595881429313,1432,979485972301576513,425,
974843902962138714,403,965345152451443093,407,974630528148011329,1432,690692645944785154,406,677111477764847937,3463,965343915502952016,1511814,388882201141542585,2421,686683895000956644,2402,
974632796178046691,1515928,686401320512618212,2418,965344052956593849,389,388882063687900752,1513846,110011967745523410,2436,686753095514029737,2455,105507268606524930,2436,691256695661492674,408,
685837064603924842,1415,402747043573103017,1432,685838232851806511,2422,690692646213220777,2422,99877837523352761,2421,681897583179947054,9920882,691539338080779986,402,99878937034980562,2437,
104382605381827631,2438,689850556939992111,406,393386763361679740,2439,690692645928008001,2438,690692645928008085,407,690692645928008001,1432,685838164115552539,390,676832133108693417,3461,
965345152470309889,1593698,105507268606524930,2438,681969120421576377,390,681333533714898616,1530213,398243443928955201,1432,686401114068974018,1415,974913171641040612,386,691256763575664277,369,
676829934087528120,9851237,676829934087527937,9916773,681334633224437295,2435,403310130445385306,403,685839332363434287,1398,690692646196443498,406,690692645944785321,2438,690692646196443457,1431,
969848752078813505,1431,691539269898173999,402,685837064603924885,1414,110009769242360129,3463,681334633224436137,3461,691256695678271023,402,979485972318353833,425,690974121189931433,1415,
970126928520642113,2454,398523819679252015,407,110009769242361450,2433,965345083748744706,354,681966921918413121,2455,965343915500863057,369,969848683376115410,354,681053295973850335,1508869,
974351183491856809,1415,970130227055525570,406,685839263627180482,1414,672328464745068906,2439,672328464745068906,2437,686401251526794798,1582471,676829934087526312,14115173,969846415616605777,385,
95092762902494357,2433,685486527125478440,1508869,681545877451529406,1377795,685838164115552706,1415,104099962157235349,2437,686470521277348161,2456,105506169346555473,2420,685838164115552661,1413,
672327365233441173,2438,970130227074391208,1665362,403310130160172713,2386,95093862414122090,2433,960558841433651537,374,99597531029404796,2433,398523818857168449,2455,108604661296233578,2437,
677111409064238593,1583494,109729462532267042,1377795,685487626905541809,1508869,686332120555150483,1377795,680488971326945898,2433,105437999663234280,1080043894,676829934087526312,9988469,686190145545918272,1673623,
974069640315763138,407,685838232851806466,1413,685837133342267304,5794165,685837133342267345,1603957,974704195963943233,425,684923577138502730,1508869,685839332363434450,1413,99878937036938261,1574405,
681333533714896808,9992549,686190145562695592,1673623,676833232622409640,1670517,681336832249780136,1674597,680771820980362350,1508869,681966921935190441,2456,970130158354914472,1665362,960558910171994024,1603989,
960558910171994024,1673621,676829934087526312,5798278,681333533714896808,1674630,676833232622409640,5797221,689566746289601601,2420,676833232622409640,9921893,685839332365522856,1674597,676832133110781742,1603974,
970126859820031144,1665426,676829934087527592,9980275,965063609044645287,6561425797,970126859820031144,9974115])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_0 : BinarySearch.fcAllB [] (pr G1 0) 0 15 1 fba_si_0 = false := by decide +kernel
lemma fva_si_0 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_0 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_si_0
set_option maxHeartbeats 0 in
def fba_si_1 : ℕ × List ℕ × List ℕ := (255,[690412202043350165,690413370022796305,690130727066639509,681120298013269146,690129627286576137,690127497268010163,690129627555011645,689844922779671618,690411102263286793,676334054892870760,685908602684415013,680837723524930601,689562348291333333,680837654788676852,689562348022897740,676266915393674918,
685341322883865712,680555080300338316,689844853774982361,685907502635916480,689562279286643825,676051480404532224,113672448395943644,113672379944902364,690406704485211301,681334701941825088,690407803728403673,104102230166314705,681681048943434940,681400604742098164,690688247929740364,668170249792887841,
685903104589405229,685341254684482717,690694844999506961,685345514453179616,686186847325625569,681683247966690458,685904204637904029,676269251872661056,676897005114727580,685557857384635993,685556757873008260,681052058734010083,685276313671671532,685275214160043548,109168848500137604,676895905603099700,
676895905334664192,681682148455062569,685064039476468960,108887373506649619,113390973402455659,113390904951414379,397891461961718719,685274114648415935,686118539578547135,676269183153184320,671766683037441580,680490139555962579,680771683268927040,685274183384669740],[388883301208906841,9916789,388883301208907353,1530247,109661223553038682,3446,681827352426282586,2435,681827352428371545,1587591,691539338634427994,403,691256764414525018,403,681897651899423790,9920882,
973788234094041817,1507844,681827352392728188,2433,110010937473465980,2433,672328464745068922,373,686190146368003630,1601927,960278534723558108,1442308,397891599419537833,3463,677114776601721262,390,
974351252211333545,1415,681615077392218474,2439,960277435211930215,1442308,974350152699705769,2439,686471690062100964,407,686190146349136193,1398,965345083748743426,407,676833232620321071,2422,
676832133108693311,374,681334633224436031,374,672329564256696682,2421,686118608316889513,3446,393386900280540882,2437,974632796192734810,371,680770515039910610,2434,681333533712809682,2435,
110011967745523385,2418,691256764380969340,408,388882201141542402,2437,974351184028727780,391,681333533714898616,9843061,686471688971583057,369,691256763575662913,1432,109729462530309210,2437,
690692645928008085,374,686470521830996434,408,681545877449571418,2437,974842803182075482,373,681827352392726908,2439,690692646196443498,390,685839332363434287,1414,974842803182075482,403,
681966921918413121,2456,686470521277348161,2455,685838232851806511,1415,969848752078813546,408,690692646213220818,406,681333533714898641,9912693,681615077392218433,3462,388882201141542402,2436,
685839263627180394,1397,676829934087527937,9912677,672328464745068881,2405,686401320514707171,1582471,114516666884520361,3463,393386900280540882,2436,398523818873945769,2455,685838164115552661,1381,
672327365233441105,2421,686471688988360377,354,691256763592441346,402,99877837523352761,2418,99877837523352578,2437,108604661296233578,2433,99878937034980537,2402,691539338064002666,385,
108886205009198127,2438,388883163734309244,2439,686402214117472514,391,690692645928008085,406,677111409062149634,2434,105506169346554177,3463,104099962157235349,2433,969848752097680593,1593698,
105507268606525113,2422,388882063685811793,2417,970200596605008193,425,110011967745523410,2438,393739844033149249,1432,686471688988360377,338,974704195963943233,424,974632796175957732,370,
681615008689520338,2434,676832133108694575,2435,690692646196443457,2422,403310130445385306,371,393668306539863086,9920882,686402282853726570,391,685839263627180523,391,690692646196443498,408,
965345152451443009,1432,402747043304667561,2456,393386762824810065,2417,974632589732313538,408,681333533714898641,9916789,686118677019588929,3446,675985371699575445,2433,677111477764849233,2421,
675985371699575377,2417,681334633226524584,9991541,686753096319335983,407,110009769242361425,2420,685837064603924801,3446,691255595898206633,1432,690974120921495977,2439,974069709052017065,1430,
397891599402760513,3463,960558910169905577,2454,676550795858107544,1574405,685839263627180394,1413,681334633226526254,1587591,95092762902494289,2417,676832133110783534,1587590,974632727190134318,1515928,
681615008691609297,1583495,686049477078899719,1377795,686402489030892596,1377795,676832133110781864,9991525,681333533714896808,14115189,105506169346555541,2433,965063609044647591,6561495429,680771614551538223,2434,
676266915412540089,2418,672327365233441173,2437,960558841433651537,390,680490071107009148,2433,691539338080779986,354,686753095497252417,2455,99597530760969410,2433,974350083980229033,2439,
691256763592441346,354,686050576858963003,1377795,680490070838573762,2433,108604661298191528,1508869,114516666867743041,3463,974069640315763138,408,104099962159193119,1508869,398242344148891969,2456,
105437999663234253,1348479350,685837133342267137,1599845,99877837525310599,1508869,681616245925313626,2437,677114776603810905,1595765,393737645278329153,2456,970200596605008193,424,684924676918566099,1508869,
114513369138166081,3463,672329564256696641,3446,676269320864619559,1574405,686470521294125481,2455,685837133342267304,5798245,960558910171994024,1669525,681336832249780136,5797237,681336832249780136,1600869,
686190146368001960,1602934,686190145562695592,1603990,681334633226524462,1603974,685838232853895080,1670517,689566746021166145,2436,681333533714898088,9980259,965063609044645287,6561491333,965063540308391231,6561556869,
95374237898070696,9972082])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_1 : BinarySearch.fcAllB [] (pr G1 0) 0 15 1 fba_si_1 = false := by decide +kernel
lemma fva_si_1 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_1 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_si_1
set_option maxHeartbeats 0 in
def fba_si_2 : ℕ × List ℕ × List ℕ := (255,[685839401651248278,685557857669848196,685275214445255742,685276313956883475,686402489026846428,686332120551104220,684992570952228031,104102298885791398,684993670732291281,685276314225319019,99597531027316365,99597530758880979,680770515037822179,685275214176820356,680488971324857467,104102299154226691,
685276313688448089,99598630270508572,684994769975483628,685486527121432239,114515705631842012,685064245634899538,99878937032892131,689567914518617725,686049477074853551,681615077390130043,686050576854916740,680561813970198098,681545877447482987,689568945042333379,685066582097108605,681053295969803883,
108604661294145147,691539269879307203,691256763573574550,676269320860573429,691538170636114883,969848752076725099,965345152449354646,680771820976316149,681616245906448117,680562845030784662,690413369704029803,974985670686907306,965345015010401174,685908671370337987,969848614637771627,690412270192402070,
686471690043235197,686470521828907987,686190213992783442,690693813620154006,970126791079598930,681616245923225195,974350015241886614,979768614701996866,686402214115384067,398242344683674475,974351114753514347,974982372957330346,974632589730225091,970130296074902363,398454687329917699,115079754794900227,
690693814425460349,686190215066525309,108605898244726508,970200596602919746,686401114066885404,685066581828673219,686683688555224044,689567913713311382,974704195961854786,686120945062223492,685838164113464092,689569013224939115,672327365231352742,99880036544519724,689568944773897835,974842803146431357,
114798142110800668,686470521812130667,974630528145922966,393739844031060886,685907571321839186,691256764378880893,979767447007763266,691539338598783869,689566746287513195,691537071124487019,104382605379739200,686049477041299153,974982372940553026,691255595879340950,970130227053435843,402747043285801878,
690974120902630294,105506169344465830,974351183489768403,686470521292037050,110009769240271739,960558841431563090,114516666865654719,681966921916324690,686470521275259730],[974351252764981594,391,686402420326234517,391,388883301206817130,374,393386900834188890,2437,691257863657716058,408,105437930922933866,2422,681333533712808361,3462,388882201141541289,3463,
110010937507019098,2439,685837133340178898,1415,686471690078878042,408,681897651897335359,370,393668375257251391,370,969848752095590866,408,685839332363434328,391,681333533712808377,2405,
686190146365913391,408,686190146365913391,407,676829934085437881,2421,974069709052016943,391,676832133108693295,2439,681334633224436015,2438,686401251524705839,2418,388882201141541305,2422,
685837133340178898,2421,686683826013044271,2402,965063609040468226,407,681334633224436015,2439,969567208667838889,1431,965063609040468393,1432,677114707865467364,1415,681618307492837860,1414,
681333533712808377,1398,974701997494335913,424,398242344165669289,2456,676829934085437881,2422,676832133108693295,2438,393738744521521489,391,676829934085437698,2437,676829934085437698,2438,
393737645563541929,1432,398242344702540201,1432,681333533712808402,2439,681618307492837650,391,974632658468567343,408,677114707865467197,390,685839332363434409,3429,681615008689519017,3462,
691256695678269743,408,691257863640938980,408,691257794921462063,408,970130158621261540,406,676833232620321155,390,677111409062148521,3463,686473819560573353,1431,960558910169905593,391,
676829934085439161,2419,681333533712809657,2403,99879006022892772,2434,691256764397746660,408,109661086080530812,3446,110293442990669359,2439,677114776601722458,2421,388883163734309260,374,
393668375257251375,2438,965345152468221442,354,969848752095592146,354,970126859817942697,2454,690692646213220777,1431,970130227072302639,406,398173005676772866,2386,686190145543829825,2456,
398173074396249602,2386,970130227357515354,406,690692645944785321,1432,690976319676316073,1415,690692645944785321,2439,677111409062148354,2438,960558910169905577,2456,970200596621785513,425,
691256695124621633,1432,969567139931584833,1415,690976319659538753,1415,99879005754457135,2434,965345083748743593,2438,690692645944785154,407,965063540304214337,2439,965063609042556840,1534341,
686190145562695592,9990534,965063609042556840,1599877,680843220514733225,2452,689848221014654121,2436])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_2 : BinarySearch.fcAllB [fba_si_0,fba_si_1] (pr G1 0) 0 15 1 fba_si_2 = false := by decide +kernel
lemma fva_si_2 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_2 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBn))) fka_si_2
set_option maxHeartbeats 0 in
def fba_si_3 : ℕ × List ℕ × List ℕ := (255,[681053158530849899,685556758158220463,685557857938283740,685274114665192492,95094961923661503,680771614549449792,99598630538944209,684994770243919014,680490071104920717,680771614817885429,676266915410451475,680490070836485331,684993670463855644,675985371697487014,104102298617356012,95092762900405926,
684994770512354307,95093862412033659,685487626901495428,680561745519156818,686402489010069099,686332120534326891,689569013761810045,99877837521264147,677111477762759590,114515705615064683,690976456827969219,685064314085940818,109729462528220779,689567845799141059,676059451561844349,690976457096404605,
676550795854061163,104099962155146918,970130158350736176,691256695659404227,691539338061912939,970199497359727426,974701997475470146,684924676914519718,974985739121171266,684923577134456529,691257794902596547,685066444658155115,690412270729273027,685908670565031506,690413369972465347,974985739137948586,
681966922201537283,974630390706969494,690694913131781739,974911865683680107,686118677017500607,686683689092094723,979488239236913986,397891599400672191,974912965195307971,686119845533818430,686120945045446163,403309992970787691,979206696094374826,403028517994077078,979205596851182506,393737645544676246,
403310130141305795,685839263625092076,672328464742980475,104383704891367044,676059451293408963,108887373238214233,113390972865584729,104102229897879068,970130089614482371,113390904146108036,686119845550595759,690694913668652669,672329564254608319,689567845262270102,685837064601836479,680562913481825942,
398243443926866795,115079617355946988,685066513109196395,974843902926494589,974912003122633579,681966922184760214,974985670670129986,685907571858710123,681403972231339670,689566746019077782,681403971962904146,979485972299488066,398173074377382684,974845002740112219,108886205007109696,691257863622073213,
691538239355591549,686050576821362342,398454549354093548,970126928518552402,974350083978140419,402747043554237291,690974121171065707,974069640313674691,681966921933102010,671555782946561686,671555851666038379,114513369136077759],[105437999659187931,2422,388883301206818410,373,388883301206818394,2437,691256764414523738,408,676829934085437865,3463,393386900280539561,3463,681827352426281306,2439,686190146349136322,391,
686190145543829841,391,685837133340178690,1414,681336832247691730,1397,676833232620321026,1381,686471690078878042,407,686402351589980635,391,965345152468220162,407,685838232851806595,390,
681333533712808418,373,676829934085437714,357,681334633224436153,1397,676833232620321193,3445,681336832247691689,3429,676832133108693433,1381,965344052956592553,2456,965344052956592569,390,
969846553072335273,2455,686401320529394010,1415,685837133340178690,2405,969567208667838930,408,974632796192733530,408,974630459445311913,1432,970199497378593193,425,393737645295106473,2456,
969848752095590825,1431,965345152468220329,1432,974632727188045359,370,974913102653128239,386,681333533712808402,2437,677114776601722542,389,681618376229092995,389,686473819560573394,408,
681970219933202690,407,100160481016380506,2435,393737645278329169,391,686401182805227823,1415,685838232851806633,3445,681336832247691608,391,681336832247691567,1414,671836158430510249,2454,
676833232620321071,1415,95374237895982082,2434,681970219933202857,1432,686401320512616932,1415,969567139931584874,406,974632796175956452,408,95375337407610066,2434,965063540304214421,406,
965063540304214337,2437,686190146349136193,1430,965343915500861777,390,686190145560607145,2454,388882063685810513,2422,686190145543829825,2454,681897651897335343,2438,397891599419538987,354,
110292343747477039,2439,681615008689519058,2439,960558910169905577,2455,686190145543829825,2455,690692646213220777,1415,398454480653483730,2386,690975220164688297,2439,398454549372960466,2386,
691256695141398953,1432,393668306537774655,370,681897583177858623,370,974069709052016943,408,974069709052016943,407,979488170804738473,425,979488170787961153,425,402745944313133377,1432,
402744844801505601,2456,690692646213220818,408,95374237895982265,2418,690975220147910977,2439,974704195980720553,424,686190145562695592,9990518,965063609042556840,1603973,685345720630475945,2452,
689849388708887721,2437,689848221283089577,2420])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_3 : BinarySearch.fcAllB [fba_si_0,fba_si_1] (pr G1 0) 0 15 1 fba_si_3 = false := by decide +kernel
lemma fva_si_3 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_3 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBn))) fka_si_3
set_option maxHeartbeats 0 in
def fba_si_4 : ℕ × List ℕ × List ℕ := (255,[167526898318877,166151904804535,165189865684672,167457893629675,166220641058340,166220372622954,167251684867672,166151636368898,100160481014292075,99880105532431934,99879005752368704,99879006020804341,95375337405521635,99880105263996548,110010937504930667,681333533710719971,
680843288963686074,974351252762893147,969848752093502419,115079754845232022,689850419767385811,686683895300856726,689850488755298021,398454687363472348,681615008687430627,689850420035821104,680843220512644794,681618376227003268,686471690076789595,685908670581808826,974913171655727963,167320135908608,
965345083746654979,969846484350770106,965343984235027386,403028518010854147,970126859815852986,403027488024009701,388882063683722150,690412270209179139,398242344146803538,974913033931561776,691256763590351619,974911934419934163,974632727185955632,686471688969493330,388883163732220813,685908671387115056,
691539338078690259,685348056822160944,403310130426518501,970200596619697066,685837133338090284,685629532084084315,398242344163580858,965343915498773330,403028518547725104,114796012360670014,686683757291477849,685839332361345881,671836158428421818,398454687346695019,110010937471376269,115078518129531737,
689850557206339301,115079754811677547,979768546250955586,234528052592039,690975220162599683,690976319674227667,974069709049928496,403027419304532784,110292343745387328,676340926555332325,691539338615561189,681403972248116739,970130296058125285,686190215083302629,689848221281001171,970130227355425627,
691539269610871659,686683826010954585,403310130443295579,970130296041347965,686683757828348779,686751996268747706,690692645942696707,686683895015644036],[686190145560607145,2455,110011967745522089,3463,105507268606523817,3463,969567208667838889,1415])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_4 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3] (pr G1 0) 0 15 1 fba_si_4 = false := by decide +kernel
lemma fva_si_4 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_4 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBn))))) fka_si_4
set_option maxHeartbeats 0 in
def fba_si_5 : ℕ × List ℕ × List ℕ := (255,[166289645747949,165052393176802,166358382001831,167458162065088,165121129430607,167320689557141,164021349367357,167319884250798,104946724134690454,100161580525919919,104383773879279123,104383774147714667,236796332195239,104383773610843737,681827352424192875,690693814459014747,
690976457113181925,685345789079428794,979768614718774186,965345152466131715,403310130158082864,691539338632338267,686402420324146070,686471688986270650,677111409060059923,685629463633043035,393386900278451171,677114776599632815,388882201139452691,690976456844746288,974632796190645083,965344052954504122,
681336832245603161,115078586865785732,686190215100079707,393386762822720379,403309992987565011,398241244903611218,671837326659526355,115079617372724057,970130227070212912,671837257940049411,974351252209245139,691538170652891952,691538239372368869,403307863505869659,690694913148559059,974913102651038512,
686190214009560762,403025220281277187,690412270746050096,393737645293018042,676622401548820059,690413369989242416,115078586849008403,979767447024540586,685838232849718148,686401182803139460,686755363539884891,681827352390638477,114795943641193348,398524987656608603,691539269896084272,676832133106604864,
690693814442237669,686755294803630896,681334633222347584,690694913685429989,686190145541741394,398454549370870617,685348057090596581,397891599417449260,689850556937903664,685907571338616506,689848221012565507,685907571875487443,691537071141264339,685347919920078384,686118608314800940,686402282851638123,
686753096300469187,974845002706557821,690692646211132371,686401320527305647,690132032199827035],[686190146365913391,391,686190145560607161,391,686190146365913513,1398,965063609040468393,2437,965063609040468226,374,969567208667838930,390,965063609040468393,2439])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_5 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3] (pr G1 0) 0 15 1 fba_si_5 = false := by decide +kernel
lemma fva_si_5 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_5 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBn))))) fka_si_5
set_option maxHeartbeats 0 in
def fba_si_6 : ℕ × List ℕ × List ℕ := (255,[167389425810955,167389157375542,166289377312405,167320152686184,167320421121728,165120860995221,167251953303085,165052124741165,104665248872767108,104665249141202652,95376436917149228,235696820567506,95374237893893651,690131963748785755,690130864505593435,690694913702207067,
676829934083349267,690976457129959003,979488239253691306,689849320255757827,398454687380249494,691256764412435291,689849389512105701,115079754828454876,686471690060012517,685345720628387514,689849320792628784,689849388706799107,689850488218427091,969846553070246842,969848683374025683,676833232618232708,
114796012377447343,403310130409741181,403307863489092581,393738744519433042,690413369720807123,114798142127577988,974632658466478896,393737645276240722,691257794919373616,974630459443223299,691257863638850533,676340926286896688,393386763359591309,403027488040786779,974350152697617155,690693813636931075,
403306695257988051,237826587475229,237826855910893,685347988102684371,974704195978632106,680844388475313667,403309993256000304,969846415614516050,979485972316265386,681970219931114243,167526327893465,686190146347047875,686473819558484947,691256695676181296,979488170785872706,234528321027452,
398524918920354608,691256764395658213,398173074394160004,398454480651393881,110293442988579648,398173005674683268,403307794769615664,685347919651643091,680844320024272387,681403971979681466,691255595896118019,691256695122533270,114516666882431788,686401251522616196,398523819660385219,960558910167817146,
398521620385471418],[393386900834187610,2439,388883301206817114,2439,686190146365913513,1414,686190145560607161,390,686190145560607161,374,686190145560607145,2456,681969120421575081,2456,686471620537317801,2455,
969567208667838889,2422,965063609040468393,2438])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_6 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3] (pr G1 0) 0 15 1 fba_si_6 = false := by decide +kernel
lemma fva_si_6 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_6 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBn))))) fka_si_6
set_option maxHeartbeats 0 in
def fba_si_7 : ℕ × List ℕ × List ℕ := (255,[105437999657098220,237895608941957,237895340506544,236796365749637,235696854121904,166427101478311,235695763602708,236795275230692,236795258453372,235695746825639,235628101090589,236727612718573,235627295784359,236726807412092,236727092624705,235627849432385,
236727075847636,235627832655316,236795812101622,235696568909302,235696552131982,236795795324302,167664320495040,167595332582891,165327304637888,236865085226461,393386900832099179,388883301204728683,166426816265621,237826872687962,237826604252549,166357811576170,
165258299948437,236864246365582,686683826564602844,686402351587892188,691257863655627611,167457323204014,691538239389145947,97227108498742,97295827975435,94958795341282,96058575404471,974701997492247466,970199497376504746,974842803179985755,974843902960048987,237895323729215,
237895592164628,167457608416729,393737645561453315,398242344700451795,681969120419486650,686471620535229370,236865102003607,110011967743433699,105507268604435219,974632796173868005,974913171638950885,236863994707265,686190146363824944,686190145558518714,97158355467520,979488170802650026,
167526294338816,979768546267732906,677114707863378750,681618307490749203,97158389022169,236865051671812,970130158619171813,234528337804772,234528069369108,236864279919980,691256695139310339,691539269627648979,969567208665750483,965063609038379779,398523819677162288,686753096317246256,
686753095511940026,398523818871856058],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_7 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3,fba_si_4,fba_si_5,fba_si_6] (pr G1 0) 0 15 1 fba_si_7 = false := by decide +kernel
lemma fva_si_7 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_7 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBc fva_si_4 (BinarySearch.fcBc fva_si_5 (BinarySearch.fcBc fva_si_6 (BinarySearch.fcBn)))))))) fka_si_7
set_option maxHeartbeats 0 in
def fba_si_8 : ℕ × List ℕ × List ℕ := (255,[236795828878700,235696585686380,166358365224429,238032779460061,237964328418781,94958828895680,96058608958869,238032796237207,237964345195927,235627312561428,236726824189412,235628117867909,236727629495642,235696837344575,236796348972308,167595315805494,
167664303717643,166495804177901,96127328435693,165327287860559,166426799488292],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_8 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3,fba_si_4,fba_si_5,fba_si_6,fba_si_7] (pr G1 0) 0 15 1 fba_si_8 = false := by decide +kernel
lemma fva_si_8 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_8 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBc fva_si_4 (BinarySearch.fcBc fva_si_5 (BinarySearch.fcBc fva_si_6 (BinarySearch.fcBc fva_si_7 (BinarySearch.fcBn))))))))) fka_si_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_si : BinarySearch.fcChkB [fba_si_0,fba_si_1,fba_si_2,fba_si_3,fba_si_4,fba_si_5,fba_si_6,fba_si_7,fba_si_8] [] (pr G1 0) 0 15 1 FF 1 = false := by decide +kernel
lemma chk_si : BinarySearch.chk [] (pr G1 0) 0 15 1 FF 1 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBc fva_si_4 (BinarySearch.fcBc fva_si_5 (BinarySearch.fcBc fva_si_6 (BinarySearch.fcBc fva_si_7 (BinarySearch.fcBc fva_si_8 (BinarySearch.fcBn)))))))))) FF 1).symm.trans fkr_si
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma signedImpossible (S : Finset ℕ) (sw : (S : Set ℕ) ⊆ WZ [] 0) (hl : Live Z0 (mz 0) (tz 0) 15 1 S) : False := by
  refine BinarySearch.rejectMinimum (Q := pr G1 0) (L := 16) (by decide +kernel) (by decide) (by decide) ?_ sw hl baseFloor [(FF, 1)] ffull ?_
  · intro e he
    exact G1ok e (List.mem_of_mem_filter he)
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact chk_si

end PEqualNP.Outside.L_meta_52898

open PEqualNP.Outside.L_meta_52898 in
theorem PEqualNP.Outside.L_meta_52898 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg one hf
  by_cases size : 16 ≤ gates.length
  · exact ⟨CC, 23, by simp [CC], size, fun x => (CC_f x).trans (dec_f x).symm⟩
  · have hD : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
      intro g h
      refine ⟨?_, (hg g h).2⟩
      rcases (hg g h).1 with e | e | e <;> simp [e]
    obtain ⟨q, u, hq, hu, st⟩ := stepsBridge ⟨gates, o⟩ hD (fun x => (hf x).trans (dec_f x))
    change q ≤ gates.length at hq
    change u ≤ countNot gates at hu
    obtain ⟨gs, out, hm, hlen, eval⟩ := compareShort (by omega) hq (hu.trans (countNotAtMostOne gates one)) st baseFloor signedImpossible
    exact ⟨gs, out, hm, hlen, fun x => (eval x).trans (dec_f x).symm⟩
