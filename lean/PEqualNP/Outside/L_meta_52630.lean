import PEqualNP.Defs
-- Adapted from lean/PEqualNP/Outside/L_meta_52894.lean and lean/PEqualNP/Outside/L_meta_52902.lean (Apache-2.0).

namespace PEqualNP.Outside.L_meta_52630
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
def NN : Nat := 945
def AA : Nat := 0xfffffefdfffffdfffffdf7fffff7fffff7bfffffbfffffbbfffffbfffffbdfffffdefffffef7bfffeabfff6bfff6b55fffafffd7ffefffdad6abfff5bfff57ffedfffb6d6bfff6afffdfffb6dbfff6fffdb6fffdbfff0000000000000000000000000000000000000000000000000000000000000000
def HX : Nat := 0x1540009400094aa000500028001000252954000a4000a800120004929400095000200049240009000249000240000000000000000000000000000000000000000000000000000000000000000000
def HY : Nat := 0x100000102000002000002080000080000084000004000004400000400000420000021000001084000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
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
def segsX : List (ℕ × ℕ) := [(255, 270), (270, 273), (273, 288), (288, 291), (291, 294), (294, 297), (297, 312), (312, 315), (315, 330), (330, 333), (333, 336), (336, 339), (339, 342), (342, 357), (357, 372), (372, 374), (374, 376), (376, 379), (379, 394), (394, 396), (396, 399), (399, 401), (401, 404), (404, 407), (407, 410), (410, 425), (425, 428), (428, 443), (443, 445), (445, 447), (447, 462), (462, 465), (465, 467), (467, 482), (482, 484), (484, 486), (486, 488), (488, 491), (491, 493), (493, 496), (496, 498), (498, 501), (501, 516), (516, 531), (531, 533), (533, 548), (548, 550), (550, 565), (565, 567), (567, 569), (569, 571), (571, 574), (574, 576), (576, 579), (579, 594), (594, 596), (596, 599), (599, 614), (614, 616), (616, 618), (618, 620)]
def segsY : List (ℕ × ℕ) := [(620, 638), (638, 643), (643, 648), (648, 672), (672, 677), (677, 701), (701, 706), (706, 730), (730, 754), (754, 758), (758, 782), (782, 806), (806, 811), (811, 835), (835, 859), (859, 865), (865, 889), (889, 913), (913, 920), (920, 944)]
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
  have : Std.Symm (fun a c : L_meta_52630.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
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
    {go : (L_meta_52630.X → L_meta_52630.X → Bool) → List L_meta_52630.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_52630.X.s e
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_52630.X → L_meta_52630.X → Bool) → List L_meta_52630.X → Bool,
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52630.X.s e))
end sound
def rawP : List ℕ := [0x3fffff80000000000000000000000000000000007fffff000000001fffffc0f000001081400814000841202092105020b00041101431024220498814000110240440a08160081024440b02c4121104c000000000000000000000000000000000000000000000000000000000000000001102a040420550754540010095010055080804a808046880804a88a26e8004024c20a2576078102a08000000000044000000010000fffc006080001800010000c000001080000a0001fff80c00006fffc360001bfffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x7fffff000000000000003fffff81fffffde0000000004c0004c020004640252013802600004008c0008c80128804e0080008c44027004c0430114c0461040473012800000000000000000000000000000000000000000000000000000000000000000221440808428808068810209220208a210104910946b500104850104830428ad3800c365cf00214400000000000300000200017ffe0000010200000000040000dfff80c0000062fffc00006180006000186fffd8000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xfffffe000000000000007fffff00000003fffffbc0000000000000001281022800201244096004a009400800022880248804b00128040c0448d0114022820104580114340124204b000000000000000000000000000000000000000000000000000000000000000000442121010842410182420412092496c9002082482081890a2a368208148030c9ade1040860084212000000800008100002fffc000000000c0000004000057ffe000006060000680000000301bfff00001b00001bffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x7fffff00000007fffff7fffff7800000000000000000000000b0000b040280b80058002c005800010013090170002c000b0200501700005800b0698026000982680b8002c0000000000000000000000000000000000000000000000000000000000000000008848420210908206108408244208230220c533904112100c33270c33273c4110300208818100848400000000006015fff8000000000000200800005bfff0000000003006bfff00000000036c000000001b6fffc0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0x1fffffc000000000000000fffffe00000007fffff7fffff70000000000000000000000000000000000442c0c44c0d6822c0116008b011601001445c00458008b0022c069a049800126024c04d24b8092e00012c004b000000000000000000000000000000000000000000000000000000000000000000af081800021030018030820c78c00440c008623e08623e3804038004038000201c040100e0010081820000600006b400000000000000001800abfff0000000000000036d0000000000000036dbfff6fffc0000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0x3fffff80000000fffffefffffef0000000000000000000000000000000000000000000000101300517000000b00058002c0058035a8026000260004c0013004d282e0090b8017000002c000b00000b0002c0000000000000000000000000000000000000000000000000000000000000000003000e04143e1c04201c003087f03087f079003c01003c001003c01003c008801e000400f0022100e0800006bfff00000000000000000001ad6000000000000000000036d6bfff6afffdfff8000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0x3fffffbfffffbe00000000000000000000000000000000000000000000000000000000000111c00018000000c00060003000600252c1380023800270011c000000300000c00180000030000c00000c00030000000000000000000000000000000000000000000000000000000000000000000c00f008183fe0183fe01f40f80040f8000207c00207c002207c00207c001103e000881f0004020f00abfff0000000000000000000000001ad6abfff5bfff57ffedfff800000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0x1fffffdf800000000000000000000000000000000000000000000000000000000000000000000000004600086000948300018000c001800000004000040000800020000000400001000200000040001000001000040000000000000000000000000000000000000000000000000000000000000000000fff000fdfc0001fc000107f00007f000043f80003f800003f80003f800021fc00010fe0000843f000abfff6bfff6b55fffafffd7ffefffc0000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 256 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0xfffffefdfffffdfffffdf7fffff7fffff7bfffffbfffffbbfffffbfffffbdfffffdefffffef7bfffeabfff6bfff6b55fffafffd7ffefffdad6abfff5bfff57ffedfffb6d6bfff6afffdfffb6dbfff6fffdb6fffdbffffffffffffffffffffffffffffffefffefffffffefffffffcfffeffeefefaeca0
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
    have : Std.Symm (fun a b : L_meta_52630.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52630.X.s e)) hpb
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
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 2 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 3 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 6 0) ||| (rawP.getD 2 0 &&& rawP.getD 6 0) ||| (rawP.getD 3 0 &&& rawP.getD 6 0) ||| (rawP.getD 4 0 &&& rawP.getD 6 0) ||| (rawP.getD 0 0 &&& rawP.getD 7 0) ||| (rawP.getD 1 0 &&& rawP.getD 7 0) ||| (rawP.getD 2 0 &&& rawP.getD 7 0) ||| (rawP.getD 3 0 &&& rawP.getD 7 0) ||| (rawP.getD 5 0 &&& rawP.getD 7 0) ||| (rawP.getD 6 0 &&& rawP.getD 7 0)
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
def CC : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [5, 6]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [3, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [14, 2]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [5, 13]⟩, ⟨.and, [15, 11]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [22, 18]⟩]
set_option maxRecDepth 100000 in
lemma dec_f : ∀ x : Fin 8 → Bool, decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = f x := by decide +kernel
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
    {go : (L_meta_52630.X → L_meta_52630.X → Bool) → List L_meta_52630.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_52630.X.s e
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_52630.X → L_meta_52630.X → Bool) → List L_meta_52630.X → Bool,
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52630.X.s e))
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
    have : Std.Symm (fun a b : L_meta_52630.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_52630.X.s e)) hpb
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
-- NEW PART (not in the recorded file): tables of search states that are already known to fail.
-- A state is (kind, fuel, k, t, z, live wires): kind 1 stands for `look1 l m g K fuel k t z v`, any other kind for
-- `look l m g fuel k t z v`.  A table is 16 rows of 16 buckets of states (bucket number = (z + k) mod 251).
-- `fcLook` / `fcLook1` / `fcTop` / `fcChk` are the searches of the recorded text with one change: before a
-- continuation is run, the table is consulted, and a state found there counts as failed.  `fcChk_eq`, `fcOne_eq`:
-- when every state of the table is one where the ORIGINAL search fails (`fcTV`), the searches with the table
-- return what the original searches return.  In the file a state is written as the moves that lead to it
-- (`fcSt`), packed into one or two numbers (`fcBin`); a theorem `fcAllB bins Q Z K b = false` runs the states of
-- the list b with the states of earlier lists as table (`fcTab`), and `fcAllB_val` makes b usable as a table.
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
  Nat.beq e.2.2.1 k && Nat.beq e.2.1 n && Nat.beq e.1 a && Nat.beq e.2.2.2.1 t && Nat.beq e.2.2.2.2.1 z && fcEqV e.2.2.2.2.2 v
lemma fcEqE_sound {e : ℕ × ℕ × ℕ × ℕ × ℕ × List W} {a n k t z : ℕ} {v : List W} (h : fcEqE e a n k t z v = true) : e = (a, n, k, t, z, v) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := e
  simp only [fcEqE, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h3, h2⟩, h1⟩, h4⟩, h5⟩, h6⟩ := h
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
def fcFrc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => st w.r fun r => ih fun rest => h (⟨s, a, b, c, r⟩ :: rest)) v
lemma fcFrc_eq (v : List W) : ∀ h, fcFrc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => st w.r fun r => fcFrc v fun rest => h (⟨s, a, b, c, r⟩ :: rest)) = _
    simp only [st_eq]; rw [ih]
def fcOne (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (l m g K : ℕ) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : Bool :=
  st e.2.1 fun n => st e.2.2.1 fun k => st e.2.2.2.1 fun t => st e.2.2.2.2.1 fun z => fcFrc e.2.2.2.2.2 fun v =>
    Bool.rec (motive := fun _ => Bool) (fcLook L l m g n k t z v) (fcLook1 L l m g K n k t z v) (Nat.beq e.1 1)
lemma fcOne_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : fcOne L l m g K e = fcOrig l m g K e := by
  simp only [fcOne, fcOrig, st_eq, fcFrc_eq, fcLook_eq hT, fcLook1_eq hT]
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
-- a state by the moves that lead to it: (kind, fuel, k, t, the inputs in use as a bit mask, the moves);
-- a move is  first wire + 16 * second wire + 256 * operation (0 and, 1 or, 2 not) + 1024 * which wires stay
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
def fcGateM (s : ℕ × List W) (a b o : W) (var : ℕ) : ℕ × List W :=
  (fun z1 => (fun v1 =>
    Bool.rec (motive := fun _ => ℕ × List W)
      (Bool.rec (motive := fun _ => ℕ × List W)
        (Bool.rec (motive := fun _ => ℕ × List W) (Nat.sub (Nat.sub z1 a.c) b.c, v1) (Nat.sub z1 b.c, fcRmV a.s v1) (Nat.beq var 2))
        (Nat.sub z1 a.c, fcRmV b.s v1) (Nat.beq var 1))
      (z1, fcRmV b.s (fcRmV a.s v1)) (Nat.beq var 0))
    (fcInsV o s.2)) (Nat.sub (Nat.add s.1 (Nat.land a.c b.c)) o.c)
def fcMove (m : ℕ) (s : ℕ × List W) (c : ℕ) : ℕ × List W :=
  (fun a => (fun b => (fun op => (fun var =>
    Bool.rec (motive := fun _ => ℕ × List W)
      (Bool.rec (motive := fun _ => ℕ × List W)
        (fcGateM s a b ⟨Nat.lor a.s b.s, Nat.land a.a b.a, Nat.lor a.b b.b, Nat.lor (Nat.land a.a b.a) (Nat.lor a.b b.b), 0⟩ var)
        (fcGateM s a b ⟨Nat.land a.s b.s, Nat.lor a.a b.a, Nat.land a.b b.b, Nat.lor (Nat.lor a.a b.a) (Nat.land a.b b.b), 0⟩ var)
        (Nat.beq op 0))
      (fcNotM m s a var) (Nat.beq op 2))
    (Nat.mod (Nat.div c 1024) 4)) (Nat.mod (Nat.div c 256) 4)) (fcNth s.2 (Nat.mod (Nat.div c 16) 16))) (fcNth s.2 (Nat.mod c 16))
def fcRun (m : ℕ) (s : ℕ × List W) (cs : List ℕ) : ℕ × List W :=
  List.rec (motive := fun _ => ℕ × List W → ℕ × List W) (fun s => s) (fun c _ ih s => ih (fcMove m s c)) cs s
def fcSt (Q : List (ℕ × ℕ)) (Z K : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  (fun r => (fun s => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, s.1, s.2))
      (fcRun (mz Z) (Nat.sub (pL (Q.map fun e => 16 + (K - e.2))) (sumc r), r) p.2.2.2.2.2))
    (fcSel (avl (PZ Q) (mz Z) (rawL [])) p.2.2.2.2.1)
-- the packed form.  First number of a state: key + 256 * (kind + 2 * (fuel + 16 * (k + 16 * (t + 16 * (n + 8 * moves)))))
-- with n the number of moves and 12 bits per move; a state with more than three moves has a second number with
-- the moves after the third.  A list b = (mask, states of one number, states of two numbers).
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
def fcAnyP (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (Q : List (ℕ × ℕ)) (Z K l m g : ℕ) (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcOne L l m g K (fcSt Q Z K p.2))) P
lemma fcAnyP_val {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {Q : List (ℕ × ℕ)} {Z K l m g : ℕ} (hT : fcTV l m g K L) :
    ∀ P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)), fcAnyP L Q Z K l m g P = false → ∀ e ∈ P.map (fun p => (p.1, fcSt Q Z K p.2)), fcOrig l m g K e.2 = false := by
  intro P
  induction P with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a P ih =>
    intro h e he
    have h' : Bool.rec (motive := fun _ => Bool) (fcAnyP L Q Z K l m g P) true (fcOne L l m g K (fcSt Q Z K a.2)) = false := h
    have he1 : e ∈ (a.1, fcSt Q Z K a.2) :: P.map (fun p => (p.1, fcSt Q Z K p.2)) := he
    cases ha : fcOne L l m g K (fcSt Q Z K a.2) with
    | true => rw [ha] at h'; exact Bool.noConfusion h'
    | false =>
      rw [ha] at h'
      rcases List.mem_cons.1 he1 with rfl | he'
      · rw [← fcOne_eq hT]; exact ha
      · exact ih h' e he'
def fcBV (Q : List (ℕ × ℕ)) (Z K : ℕ) (b : ℕ × List ℕ × List ℕ) : Prop :=
  ∀ e ∈ (fcBin b).map (fun p => (p.1, fcSt Q Z K p.2)), fcOrig (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K e.2 = false
def fcTab (Q : List (ℕ × ℕ)) (Z K : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) fcE0 (fun b _ ih => fcAdd ih ((fcBin b).map (fun p => (p.1, fcSt Q Z K p.2)))) bs
lemma fcTab_tv {Q : List (ℕ × ℕ)} {Z K : ℕ} : ∀ bs : List (ℕ × List ℕ × List ℕ), (∀ b ∈ bs, fcBV Q Z K b) →
    fcTV (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K (fcTab Q Z K bs) := by
  intro bs
  induction bs with
  | nil => intro _; exact fcE0_tv
  | cons b bs ih =>
    intro h
    exact fcAdd_tv _ _ (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) (h b List.mem_cons_self)

def fcFrcE (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) (h : (ℕ × ℕ × ℕ × ℕ × ℕ × List W) → Bool) : Bool :=
  st e.1 fun a => st e.2.1 fun n => st e.2.2.1 fun k => st e.2.2.2.1 fun t => st e.2.2.2.2.1 fun z =>
    fcFrc e.2.2.2.2.2 fun v => h (a, n, k, t, z, v)
lemma fcFrcE_eq (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) (h : (ℕ × ℕ × ℕ × ℕ × ℕ × List W) → Bool) : fcFrcE e h = h e := by
  obtain ⟨a, n, k, t, z, v⟩ := e
  simp only [fcFrcE, st_eq, fcFrc_eq]
def fcFrcB (B : List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) : (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W) → Bool) → Bool) (fun h => h [])
    (fun e _ ih h => fcFrcE e fun e => ih fun r => h (e :: r)) B
lemma fcFrcB_eq (B : List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) : ∀ h, fcFrcB B h = h B := by
  induction B with
  | nil => intro h; rfl
  | cons e B ih => intro h; change fcFrcE e (fun e => fcFrcB B fun r => h (e :: r)) = _; rw [fcFrcE_eq, ih]
def fcFrcR (R : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)) → Bool) → Bool) (fun h => h [])
    (fun B _ ih h => fcFrcB B fun B => ih fun r => h (B :: r)) R
lemma fcFrcR_eq (R : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) : ∀ h, fcFrcR R h = h R := by
  induction R with
  | nil => intro h; rfl
  | cons B R ih => intro h; change fcFrcB B (fun B => fcFrcR R fun r => h (B :: r)) = _; rw [fcFrcB_eq, ih]
def fcFrcT (T : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) : (List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) → Bool) → Bool) (fun h => h [])
    (fun R _ ih h => fcFrcR R fun R => ih fun r => h (R :: r)) T
lemma fcFrcT_eq (T : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) : ∀ h, fcFrcT T h = h T := by
  induction T with
  | nil => intro h; rfl
  | cons R T ih => intro h; change fcFrcR R (fun R => fcFrcT T fun r => h (R :: r)) = _; rw [fcFrcR_eq, ih]
def fcStF (m B0 : ℕ) (v0 : List W) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  (fun r => (fun s => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, s.1, s.2))
      (fcRun m (Nat.sub B0 (sumc r), r) p.2.2.2.2.2))
    (fcSel v0 p.2.2.2.2.1)
def fcTabF (m B0 : ℕ) (v0 : List W) (bs : List (ℕ × List ℕ × List ℕ)) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) fcE0
    (fun b _ ih => fcAdd ih ((fcBin b).map (fun p => (p.1, fcStF m B0 v0 p.2)))) bs
def fcAnyPF (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (m B0 : ℕ) (v0 : List W) (l g K : ℕ)
    (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcOne L l m g K (fcStF m B0 v0 p.2))) P
def fcAllB (bs : List (ℕ × List ℕ × List ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (b : ℕ × List ℕ × List ℕ) : Bool :=
  st (lz Z) fun l => st (mz Z) fun m => st (pL (Q.map fun _ => 16)) fun g =>
    st (pL (Q.map fun e => 16 + (K - e.2))) fun B0 =>
      frc (avl (PZ Q) m (rawL [])) fun v0 =>
        fcFrcT (fcTabF m B0 v0 bs) fun T => fcAnyPF T m B0 v0 l g K (fcBin b)
lemma fcAllB_val {bs : List (ℕ × List ℕ × List ℕ)} {Q : List (ℕ × ℕ)} {Z K : ℕ} {b : ℕ × List ℕ × List ℕ}
    (hT : ∀ b' ∈ bs, fcBV Q Z K b') (h : fcAllB bs Q Z K b = false) : fcBV Q Z K b := by
  simp only [fcAllB, st_eq, frc_eq, fcFrcT_eq] at h
  exact fcAnyP_val (fcTab_tv bs hT) _ h
def fcChkB (bs : List (ℕ × List ℕ × List ℕ)) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  st (mz Z) fun m => st (pL (Q.map fun e => 16 + (K - e.2))) fun B0 =>
    frc (avl (PZ Q) m (rawL [])) fun v0 =>
      fcFrcT (fcTabF m B0 v0 bs) fun T => fcChk T E Q Z K t H ph
lemma fcChkB_eq {bs : List (ℕ × List ℕ × List ℕ)} {E Q : List (ℕ × ℕ)} {Z K : ℕ} (hT : ∀ b ∈ bs, fcBV Q Z K b) (t H ph : ℕ) :
    fcChkB bs E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [fcChkB, st_eq, frc_eq, fcFrcT_eq]
  exact fcChk_eq (fcTab_tv bs hT) t H ph
lemma fcBn {Q : List (ℕ × ℕ)} {Z K : ℕ} : ∀ b ∈ ([] : List (ℕ × List ℕ × List ℕ)), fcBV Q Z K b := fun _ hb => absurd hb List.not_mem_nil
lemma fcBc {Q : List (ℕ × ℕ)} {Z K : ℕ} {b : ℕ × List ℕ × List ℕ} {bs : List (ℕ × List ℕ × List ℕ)} (h : fcBV Q Z K b) (hs : ∀ b' ∈ bs, fcBV Q Z K b') :
    ∀ b' ∈ b :: bs, fcBV Q Z K b' := fun b' hb' => (List.mem_cons.1 hb').elim (fun e => e ▸ h) (hs b')
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
  st e.2.1 fun n => st e.2.2.1 fun k => st e.2.2.2.1 fun t => st e.2.2.2.2.1 fun z => fcFrc e.2.2.2.2.2 fun v =>
    Bool.rec (motive := fun _ => Bool) (fcLook L l m g n k t z v) (fcLook1 L l m g K n k t z v) (Nat.beq e.1 1)
lemma fcOne_eq {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {l m g K : ℕ} (hT : fcTV l m g K L) (e : ℕ × ℕ × ℕ × ℕ × ℕ × List W) : fcOne L l m g K e = fcOrig l m g K e := by
  simp only [fcOne, fcOrig, st_eq, fcFrc_eq, fcLook_eq hT, fcLook1_eq hT]
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
def fcMove (m : ℕ) (s : ℕ × List W) (c : ℕ) : ℕ × List W :=
  (fun a => (fun b => (fun op => (fun var =>
    Bool.rec (motive := fun _ => ℕ × List W)
      (Bool.rec (motive := fun _ => ℕ × List W)
        (fcGateM s a b ⟨Nat.lor a.s b.s, Nat.land a.a b.a, Nat.lor a.b b.b, Nat.lor (Nat.land a.a b.a) (Nat.lor a.b b.b), 0⟩ var)
        (fcGateM s a b ⟨Nat.land a.s b.s, Nat.lor a.a b.a, Nat.land a.b b.b, Nat.lor (Nat.lor a.a b.a) (Nat.land a.b b.b), 0⟩ var)
        (Nat.beq op 0))
      (fcNotM m s a var) (Nat.beq op 2))
    (Nat.mod (Nat.div c 1024) 4)) (Nat.mod (Nat.div c 256) 4)) (fcNth s.2 (Nat.mod (Nat.div c 16) 16))) (fcNth s.2 (Nat.mod c 16))
def fcRun (m : ℕ) (s : ℕ × List W) (cs : List ℕ) : ℕ × List W :=
  List.rec (motive := fun _ => ℕ × List W → ℕ × List W) (fun s => s) (fun c _ ih s => ih (fcMove m s c)) cs s
def fcSt (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  (fun r => (fun s => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, s.1, s.2))
      (fcRun (mz Z) (Nat.sub (pL (Q.map fun e => 16 + (K - t0 - e.2))) (sumc r), r) p.2.2.2.2.2))
    (fcSel (avl (PZ Q) (mz Z) (rawL [])) p.2.2.2.2.1)
def fcAnyP (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (Q : List (ℕ × ℕ)) (Z K t0 l m g : ℕ) (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcOne L l m g K (fcSt Q Z K t0 p.2))) P
lemma fcAnyP_val {L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))} {Q : List (ℕ × ℕ)} {Z K t0 l m g : ℕ} (hT : fcTV l m g K L) :
    ∀ P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ)), fcAnyP L Q Z K t0 l m g P = false → ∀ e ∈ P.map (fun p => (p.1, fcSt Q Z K t0 p.2)), fcOrig l m g K e.2 = false := by
  intro P
  induction P with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a P ih =>
    intro h e he
    have h' : Bool.rec (motive := fun _ => Bool) (fcAnyP L Q Z K t0 l m g P) true (fcOne L l m g K (fcSt Q Z K t0 a.2)) = false := h
    have he1 : e ∈ (a.1, fcSt Q Z K t0 a.2) :: P.map (fun p => (p.1, fcSt Q Z K t0 p.2)) := he
    cases ha : fcOne L l m g K (fcSt Q Z K t0 a.2) with
    | true => rw [ha] at h'; exact Bool.noConfusion h'
    | false =>
      rw [ha] at h'
      rcases List.mem_cons.1 he1 with rfl | he'
      · rw [← fcOne_eq hT]; exact ha
      · exact ih h' e he'
def fcBV (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (b : ℕ × List ℕ × List ℕ) : Prop :=
  ∀ e ∈ (fcBin b).map (fun p => (p.1, fcSt Q Z K t0 p.2)), fcOrig (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K e.2 = false
def fcTab (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (bs : List (ℕ × List ℕ × List ℕ)) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) fcE0 (fun b _ ih => fcAdd ih ((fcBin b).map (fun p => (p.1, fcSt Q Z K t0 p.2)))) bs
lemma fcTab_tv {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} : ∀ bs : List (ℕ × List ℕ × List ℕ), (∀ b ∈ bs, fcBV Q Z K t0 b) →
    fcTV (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K (fcTab Q Z K t0 bs) := by
  intro bs
  induction bs with
  | nil => intro _; exact fcE0_tv
  | cons b bs ih =>
    intro h
    exact fcAdd_tv _ _ (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) (h b List.mem_cons_self)
def fcStF (m B0 : ℕ) (v0 : List W) (p : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × List W :=
  (fun r => (fun s => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, s.1, s.2))
      (fcRun m (Nat.sub B0 (sumc r), r) p.2.2.2.2.2))
    (fcSel v0 p.2.2.2.2.1)
def fcTabF (m B0 : ℕ) (v0 : List W) (bs : List (ℕ × List ℕ × List ℕ)) : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W))) :=
  List.rec (motive := fun _ => List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) fcE0
    (fun b _ ih => fcAdd ih ((fcBin b).map (fun p => (p.1, fcStF m B0 v0 p.2)))) bs
def fcAnyPF (L : List (List (List (ℕ × ℕ × ℕ × ℕ × ℕ × List W)))) (m B0 : ℕ) (v0 : List W) (l g K : ℕ)
    (P : List (ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (fcOne L l m g K (fcStF m B0 v0 p.2))) P
def fcAllB (bs : List (ℕ × List ℕ × List ℕ)) (Q : List (ℕ × ℕ)) (Z K t0 : ℕ) (b : ℕ × List ℕ × List ℕ) : Bool :=
  st (lz Z) fun l => st (mz Z) fun m => st (pL (Q.map fun _ => 16)) fun g =>
    st (pL (Q.map fun e => 16 + (K - t0 - e.2))) fun B0 =>
      frc (avl (PZ Q) m (rawL [])) fun v0 =>
        fcFrcT (fcTabF m B0 v0 bs) fun T => fcAnyPF T m B0 v0 l g K (fcBin b)
lemma fcAllB_val {bs : List (ℕ × List ℕ × List ℕ)} {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} {b : ℕ × List ℕ × List ℕ}
    (hT : ∀ b' ∈ bs, fcBV Q Z K t0 b') (h : fcAllB bs Q Z K t0 b = false) : fcBV Q Z K t0 b := by
  simp only [fcAllB, st_eq, frc_eq, fcFrcT_eq] at h
  exact fcAnyP_val (fcTab_tv bs hT) _ h
def fcChkB (bs : List (ℕ × List ℕ × List ℕ)) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  st (mz Z) fun m => st (pL (Q.map fun e => 16 + (K - t - e.2))) fun B0 =>
    frc (avl (PZ Q) m (rawL [])) fun v0 =>
      fcFrcT (fcTabF m B0 v0 bs) fun T => fcChk T E Q Z K t H ph
lemma fcChkB_eq {bs : List (ℕ × List ℕ × List ℕ)} {E Q : List (ℕ × ℕ)} {Z K t : ℕ} (hT : ∀ b ∈ bs, fcBV Q Z K t b) (H ph : ℕ) :
    fcChkB bs E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [fcChkB, st_eq, frc_eq, fcFrcT_eq]
  exact fcChk_eq (fcTab_tv bs hT) t H ph
lemma fcBn {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} : ∀ b ∈ ([] : List (ℕ × List ℕ × List ℕ)), fcBV Q Z K t0 b := fun _ hb => absurd hb List.not_mem_nil
lemma fcBc {Q : List (ℕ × ℕ)} {Z K t0 : ℕ} {b : ℕ × List ℕ × List ℕ} {bs : List (ℕ × List ℕ × List ℕ)} (h : fcBV Q Z K t0 b) (hs : ∀ b' ∈ bs, fcBV Q Z K t0 b') :
    ∀ b' ∈ b :: bs, fcBV Q Z K t0 b' := fun b' hb' => (List.mem_cons.1 hb').elim (fun e => e ▸ h) (hs b')
end
end BinarySearch

def P3_only : List (ℕ × ℕ) := [(7,7),(11,7),(13,7),(14,6),(19,7),(21,8),(22,7),(25,7),(26,7),(28,7),(35,7),(37,8),(38,6),(41,7),(42,6),(44,6),(49,8),(50,7),(52,8),(56,7),(67,7),(69,7),(70,7),(73,7),(74,7),(76,7),(81,8),(82,7),(84,8),(88,7),(97,7),(98,7),(100,7),(104,7),(112,8),(131,7),(133,7),(134,7),(137,7),(138,7),(140,7),(145,7),(146,7),(148,7),(152,7),(161,8),(162,7),(164,7),(168,7),(176,7),(193,6),(194,7),(196,7),(200,7),(208,7),(224,6)]
def P3 : List (ℕ × ℕ) := P3_only ++ P5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P3_only_ok : P3_only.all (fun e => okE [] (pr P5 e.1) e) = true := by decide +kernel
lemma P3ok : ∀ e ∈ P3, Imp [] e.1 e.2 := apI (okAll P3_only_ok P5ok) P5ok
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_7 : HasGrade 1 (7,7) := checkedGrade (before := G5) (e := (7,7)) (P3ok (7,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_11 : HasGrade 1 (11,7) := checkedGrade (before := G5) (e := (11,7)) (P3ok (11,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_13 : HasGrade 1 (13,7) := checkedGrade (before := G5) (e := (13,7)) (P3ok (13,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_14 : HasGrade 1 (14,6) := checkedGrade (before := G5) (e := (14,6)) (P3ok (14,6) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_19 : HasGrade 1 (19,7) := checkedGrade (before := G5) (e := (19,7)) (P3ok (19,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_21 : HasGrade 1 (21,8) := checkedGrade (before := G5) (e := (21,8)) (P3ok (21,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_22 : HasGrade 1 (22,7) := checkedGrade (before := G5) (e := (22,7)) (P3ok (22,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_25 : HasGrade 1 (25,7) := checkedGrade (before := G5) (e := (25,7)) (P3ok (25,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_26 : HasGrade 1 (26,7) := checkedGrade (before := G5) (e := (26,7)) (P3ok (26,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_28 : HasGrade 1 (28,7) := checkedGrade (before := G5) (e := (28,7)) (P3ok (28,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_35 : HasGrade 1 (35,7) := checkedGrade (before := G5) (e := (35,7)) (P3ok (35,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_37 : HasGrade 1 (37,8) := checkedGrade (before := G5) (e := (37,8)) (P3ok (37,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_38 : HasGrade 1 (38,6) := checkedGrade (before := G5) (e := (38,6)) (P3ok (38,6) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_41 : HasGrade 1 (41,7) := checkedGrade (before := G5) (e := (41,7)) (P3ok (41,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_42 : HasGrade 1 (42,6) := checkedGrade (before := G5) (e := (42,6)) (P3ok (42,6) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_44 : HasGrade 1 (44,6) := checkedGrade (before := G5) (e := (44,6)) (P3ok (44,6) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_49 : HasGrade 1 (49,8) := checkedGrade (before := G5) (e := (49,8)) (P3ok (49,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_50 : HasGrade 1 (50,7) := checkedGrade (before := G5) (e := (50,7)) (P3ok (50,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_52 : HasGrade 1 (52,8) := checkedGrade (before := G5) (e := (52,8)) (P3ok (52,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_56 : HasGrade 1 (56,7) := checkedGrade (before := G5) (e := (56,7)) (P3ok (56,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_67 : HasGrade 1 (67,7) := checkedGrade (before := G5) (e := (67,7)) (P3ok (67,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_69 : HasGrade 1 (69,7) := checkedGrade (before := G5) (e := (69,7)) (P3ok (69,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_70 : HasGrade 1 (70,7) := checkedGrade (before := G5) (e := (70,7)) (P3ok (70,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_73 : HasGrade 1 (73,7) := checkedGrade (before := G5) (e := (73,7)) (P3ok (73,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_74 : HasGrade 1 (74,7) := checkedGrade (before := G5) (e := (74,7)) (P3ok (74,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_76 : HasGrade 1 (76,7) := checkedGrade (before := G5) (e := (76,7)) (P3ok (76,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_81 : HasGrade 1 (81,8) := checkedGrade (before := G5) (e := (81,8)) (P3ok (81,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_82 : HasGrade 1 (82,7) := checkedGrade (before := G5) (e := (82,7)) (P3ok (82,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_84 : HasGrade 1 (84,8) := checkedGrade (before := G5) (e := (84,8)) (P3ok (84,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_88 : HasGrade 1 (88,7) := checkedGrade (before := G5) (e := (88,7)) (P3ok (88,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_97 : HasGrade 1 (97,7) := checkedGrade (before := G5) (e := (97,7)) (P3ok (97,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_98 : HasGrade 1 (98,7) := checkedGrade (before := G5) (e := (98,7)) (P3ok (98,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_100 : HasGrade 1 (100,7) := checkedGrade (before := G5) (e := (100,7)) (P3ok (100,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_104 : HasGrade 1 (104,7) := checkedGrade (before := G5) (e := (104,7)) (P3ok (104,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_112 : HasGrade 1 (112,8) := checkedGrade (before := G5) (e := (112,8)) (P3ok (112,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_131 : HasGrade 1 (131,7) := checkedGrade (before := G5) (e := (131,7)) (P3ok (131,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_133 : HasGrade 1 (133,7) := checkedGrade (before := G5) (e := (133,7)) (P3ok (133,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_134 : HasGrade 1 (134,7) := checkedGrade (before := G5) (e := (134,7)) (P3ok (134,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_137 : HasGrade 1 (137,7) := checkedGrade (before := G5) (e := (137,7)) (P3ok (137,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_138 : HasGrade 1 (138,7) := checkedGrade (before := G5) (e := (138,7)) (P3ok (138,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_140 : HasGrade 1 (140,7) := checkedGrade (before := G5) (e := (140,7)) (P3ok (140,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_145 : HasGrade 1 (145,7) := checkedGrade (before := G5) (e := (145,7)) (P3ok (145,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_146 : HasGrade 1 (146,7) := checkedGrade (before := G5) (e := (146,7)) (P3ok (146,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_148 : HasGrade 1 (148,7) := checkedGrade (before := G5) (e := (148,7)) (P3ok (148,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_152 : HasGrade 1 (152,7) := checkedGrade (before := G5) (e := (152,7)) (P3ok (152,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_161 : HasGrade 1 (161,8) := checkedGrade (before := G5) (e := (161,8)) (P3ok (161,8) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_162 : HasGrade 1 (162,7) := checkedGrade (before := G5) (e := (162,7)) (P3ok (162,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_164 : HasGrade 1 (164,7) := checkedGrade (before := G5) (e := (164,7)) (P3ok (164,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_168 : HasGrade 1 (168,7) := checkedGrade (before := G5) (e := (168,7)) (P3ok (168,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_176 : HasGrade 1 (176,7) := checkedGrade (before := G5) (e := (176,7)) (P3ok (176,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_193 : HasGrade 1 (193,6) := checkedGrade (before := G5) (e := (193,6)) (P3ok (193,6) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_194 : HasGrade 1 (194,7) := checkedGrade (before := G5) (e := (194,7)) (P3ok (194,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_196 : HasGrade 1 (196,7) := checkedGrade (before := G5) (e := (196,7)) (P3ok (196,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_200 : HasGrade 1 (200,7) := checkedGrade (before := G5) (e := (200,7)) (P3ok (200,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_208 : HasGrade 1 (208,7) := checkedGrade (before := G5) (e := (208,7)) (P3ok (208,7) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_224 : HasGrade 1 (224,6) := checkedGrade (before := G5) (e := (224,6)) (P3ok (224,6) (by decide)) (fun e he => by simpa [gradedRow] using G5ok e he) (by decide +kernel)
def G3 : List (ℕ × ℕ) := [(7,7),(11,7),(13,7),(14,6),(19,7),(21,8),(22,7),(25,7),(26,7),(28,7),(35,7),(37,8),(38,6),(41,7),(42,6),(44,6),(49,8),(50,7),(52,8),(56,7),(67,7),(69,7),(70,7),(73,7),(74,7),(76,7),(81,8),(82,7),(84,8),(88,7),(97,7),(98,7),(100,7),(104,7),(112,8),(131,7),(133,7),(134,7),(137,7),(138,7),(140,7),(145,7),(146,7),(148,7),(152,7),(161,8),(162,7),(164,7),(168,7),(176,7),(193,6),(194,7),(196,7),(200,7),(208,7),(224,6)] ++ G5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G3ok : ∀ e ∈ G3, HasGrade 1 e := consGrade g_7 (consGrade g_11 (consGrade g_13 (consGrade g_14 (consGrade g_19 (consGrade g_21 (consGrade g_22 (consGrade g_25 (consGrade g_26 (consGrade g_28 (consGrade g_35 (consGrade g_37 (consGrade g_38 (consGrade g_41 (consGrade g_42 (consGrade g_44 (consGrade g_49 (consGrade g_50 (consGrade g_52 (consGrade g_56 (consGrade g_67 (consGrade g_69 (consGrade g_70 (consGrade g_73 (consGrade g_74 (consGrade g_76 (consGrade g_81 (consGrade g_82 (consGrade g_84 (consGrade g_88 (consGrade g_97 (consGrade g_98 (consGrade g_100 (consGrade g_104 (consGrade g_112 (consGrade g_131 (consGrade g_133 (consGrade g_134 (consGrade g_137 (consGrade g_138 (consGrade g_140 (consGrade g_145 (consGrade g_146 (consGrade g_148 (consGrade g_152 (consGrade g_161 (consGrade g_162 (consGrade g_164 (consGrade g_168 (consGrade g_176 (consGrade g_193 (consGrade g_194 (consGrade g_196 (consGrade g_200 (consGrade g_208 (consGrade g_224 (G5ok))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def P2_only : List (ℕ × ℕ) := [(3,10),(5,10),(6,10),(9,10),(10,9),(12,10),(17,10),(18,10),(20,10),(24,10),(33,10),(34,9),(36,9),(40,9),(48,10),(65,10),(66,10),(68,10),(72,10),(80,10),(96,10),(129,10),(130,10),(132,10),(136,10),(144,10),(160,10),(192,10)]
def P2 : List (ℕ × ℕ) := P2_only ++ P3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P2_only_ok : P2_only.all (fun e => okE [] (pr P3 e.1) e) = true := by decide +kernel
lemma P2ok : ∀ e ∈ P2, Imp [] e.1 e.2 := apI (okAll P2_only_ok P3ok) P3ok
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_3 : HasGrade 1 (3,10) := checkedGrade (before := G3) (e := (3,10)) (P2ok (3,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_5 : HasGrade 1 (5,10) := checkedGrade (before := G3) (e := (5,10)) (P2ok (5,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_6 : HasGrade 1 (6,10) := checkedGrade (before := G3) (e := (6,10)) (P2ok (6,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_9 : HasGrade 1 (9,10) := checkedGrade (before := G3) (e := (9,10)) (P2ok (9,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_10 : HasGrade 1 (10,9) := checkedGrade (before := G3) (e := (10,9)) (P2ok (10,9) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_12 : HasGrade 1 (12,10) := checkedGrade (before := G3) (e := (12,10)) (P2ok (12,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_17 : HasGrade 1 (17,10) := checkedGrade (before := G3) (e := (17,10)) (P2ok (17,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_18 : HasGrade 1 (18,10) := checkedGrade (before := G3) (e := (18,10)) (P2ok (18,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_20 : HasGrade 1 (20,10) := checkedGrade (before := G3) (e := (20,10)) (P2ok (20,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_24 : HasGrade 1 (24,10) := checkedGrade (before := G3) (e := (24,10)) (P2ok (24,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_33 : HasGrade 1 (33,10) := checkedGrade (before := G3) (e := (33,10)) (P2ok (33,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_34 : HasGrade 1 (34,9) := checkedGrade (before := G3) (e := (34,9)) (P2ok (34,9) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_36 : HasGrade 1 (36,9) := checkedGrade (before := G3) (e := (36,9)) (P2ok (36,9) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_40 : HasGrade 1 (40,9) := checkedGrade (before := G3) (e := (40,9)) (P2ok (40,9) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_48 : HasGrade 1 (48,10) := checkedGrade (before := G3) (e := (48,10)) (P2ok (48,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_65 : HasGrade 1 (65,10) := checkedGrade (before := G3) (e := (65,10)) (P2ok (65,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_66 : HasGrade 1 (66,10) := checkedGrade (before := G3) (e := (66,10)) (P2ok (66,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_68 : HasGrade 1 (68,10) := checkedGrade (before := G3) (e := (68,10)) (P2ok (68,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_72 : HasGrade 1 (72,10) := checkedGrade (before := G3) (e := (72,10)) (P2ok (72,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_80 : HasGrade 1 (80,10) := checkedGrade (before := G3) (e := (80,10)) (P2ok (80,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_96 : HasGrade 1 (96,10) := checkedGrade (before := G3) (e := (96,10)) (P2ok (96,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_129 : HasGrade 1 (129,10) := checkedGrade (before := G3) (e := (129,10)) (P2ok (129,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_130 : HasGrade 1 (130,10) := checkedGrade (before := G3) (e := (130,10)) (P2ok (130,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_132 : HasGrade 1 (132,10) := checkedGrade (before := G3) (e := (132,10)) (P2ok (132,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_136 : HasGrade 1 (136,10) := checkedGrade (before := G3) (e := (136,10)) (P2ok (136,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_144 : HasGrade 1 (144,10) := checkedGrade (before := G3) (e := (144,10)) (P2ok (144,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_160 : HasGrade 1 (160,10) := checkedGrade (before := G3) (e := (160,10)) (P2ok (160,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_192 : HasGrade 1 (192,10) := checkedGrade (before := G3) (e := (192,10)) (P2ok (192,10) (by decide)) (fun e he => by simpa [gradedRow] using G3ok e he) (by decide +kernel)
def G2 : List (ℕ × ℕ) := [(3,10),(5,10),(6,10),(9,10),(10,9),(12,10),(17,10),(18,10),(20,10),(24,10),(33,10),(34,9),(36,9),(40,9),(48,10),(65,10),(66,10),(68,10),(72,10),(80,10),(96,10),(129,10),(130,10),(132,10),(136,10),(144,10),(160,10),(192,10)] ++ G3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G2ok : ∀ e ∈ G2, HasGrade 1 e := consGrade g_3 (consGrade g_5 (consGrade g_6 (consGrade g_9 (consGrade g_10 (consGrade g_12 (consGrade g_17 (consGrade g_18 (consGrade g_20 (consGrade g_24 (consGrade g_33 (consGrade g_34 (consGrade g_36 (consGrade g_40 (consGrade g_48 (consGrade g_65 (consGrade g_66 (consGrade g_68 (consGrade g_72 (consGrade g_80 (consGrade g_96 (consGrade g_129 (consGrade g_130 (consGrade g_132 (consGrade g_136 (consGrade g_144 (consGrade g_160 (consGrade g_192 (G3ok))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_1 : Imp [] 1 12 := imp_okE (e := (1,12)) (Q := pr P2 1) (Or.inl rfl) (by decide +kernel) (fun e he => P2ok e (List.mem_of_mem_filter he))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_1 : HasGrade 1 (1,12) := checkedGrade (before := G2) (e := (1,12)) p_1 (fun e he => by simpa [gradedRow] using G2ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_2 : Imp [] 2 12 := imp_okE (e := (2,12)) (Q := pr P2 2) (Or.inl rfl) (by decide +kernel) (fun e he => P2ok e (List.mem_of_mem_filter he))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_2 : HasGrade 1 (2,12) := checkedGrade (before := G2) (e := (2,12)) p_2 (fun e he => by simpa [gradedRow] using G2ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_4 : Imp [] 4 12 := imp_okE (e := (4,12)) (Q := pr P2 4) (Or.inl rfl) (by decide +kernel) (fun e he => P2ok e (List.mem_of_mem_filter he))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_4 : HasGrade 1 (4,12) := checkedGrade (before := G2) (e := (4,12)) p_4 (fun e he => by simpa [gradedRow] using G2ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_8 : Imp [] 8 12 := imp_okE (e := (8,12)) (Q := pr P2 8) (Or.inl rfl) (by decide +kernel) (fun e he => P2ok e (List.mem_of_mem_filter he))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_8 : HasGrade 1 (8,12) := checkedGrade (before := G2) (e := (8,12)) p_8 (fun e he => by simpa [gradedRow] using G2ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_32 : Imp [] 32 12 := imp_okE (e := (32,12)) (Q := pr P2 32) (Or.inl rfl) (by decide +kernel) (fun e he => P2ok e (List.mem_of_mem_filter he))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_32 : HasGrade 1 (32,12) := checkedGrade (before := G2) (e := (32,12)) p_32 (fun e he => by simpa [gradedRow] using G2ok e he) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_128 : Imp [] 128 12 := imp_okE (e := (128,12)) (Q := pr P2 128) (Or.inl rfl) (by decide +kernel) (fun e he => P2ok e (List.mem_of_mem_filter he))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g_128 : HasGrade 1 (128,12) := checkedGrade (before := G2) (e := (128,12)) p_128 (fun e he => by simpa [gradedRow] using G2ok e he) (by decide +kernel)
set_option maxHeartbeats 0 in
def fba_p16_0_0 : ℕ × List ℕ × List ℕ := (127,[104311892467594742,104593367712740658,100088668573742522,99807193328596355,95302494189597988,91079270295745904,95865444679890186,235489571461014,236589083088654,235558559373240,236658071000880,234389791397768,233358730811293,233360089765716,233359821330396,236658087778111,
235558576150471,384095820294731062,672325097203250541,379310746227520877,383532870878180662,234528337647397,234528069212077,234528320870377,234528052434806,667259646865650998,672043622226539885,379029271250810166,383814345854891373,162783828203578,163883608266844,970124591502538170,
970054223026795962,970126859513705867,970125691014165865,969565009088689583,965058041921746424,969561641549116784,681401634678453752,685905234305824112,965343915230180762,969772748050085211,965269148422714851,969846415345923482,685623759597548891,681120159970178531,965062508972946863,161684316575883,
397960799359939952,398242205885609307,393737506746611171,393456100220941816,681683109655164408,686186709282534768,686468184527680859,681964584900310499,969846484065400218,969564940369212847,166082899957981,970125691299378607,965062440253470127,166083436828716,166082631522355,164983119894715,
164982851459204,970126859530483098,166082363087095,166083168393416,965343983949657498,164983656765525,164983388330090,393737644202341848,964988773226067448,398242343341339984,969492372853437808,970126791079441737,388672057214317915,388670957702690275,100719857504433462,970126859815695744,
100721025467102573,100156907551012150,686190076536894880,166289645590561,162852832893056,681968982946821460,163952344520811,686471483062564180,165051856148682,166220640901139,165121129273499,166358381844492,166151367776322,165052124584057,166151636211948,681687576421152160,
672254866166461805,163883339831333,162784096639089,672043690962793852,970055322806859113,970056491306399115,164021349210193,163883876702219,166152173082683,969917952035993036,974420452151735756,166151904647383,165052393019492,165120860838064,163952612956186,166220372465704,
974701858677405111,970199358561662391,166220909336690,165189865527370,166289377155261,676899203819058633,676617660122871186,676899204087493953,676617660391306506,393738675799799194,393456101579896239,398241176183977370,397960800450459055,384095958018897276,974980035656103351,970058759619556736,
970057659839493504,974980035387667916,672325165939504508,398241244903454025,393738744519275849,393737645292860800,398242344163423616,393737645276083529,398242344146646345,384095958002120045,672325165654291766,671973322470274358,100438451247199597,965060309949691352,969844216322667856,965340616695297496,
969563909577061712,974982371598218668,974982303147177388,970199496017393068,100721025483879804,974701996133135788,970056560059430272,970126928518395209,960557672109782418,960557672378217929,960558771889845569,960558771621410058],[388883301206659868,374,681333396240143320,373,676829796612772709,357,388883094997898023,374,388601620021187388,373,388883163734151990,374,388601757493695362,373,681050821483369283,372,
681053020506624909,374,680771545261478742,374,676547221855998923,356,676269045145736022,374,676266846122480511,357,676550520390882189,374,685627057597649849,391,680770445749851122,373,
685908601025401785,391,388038670067766102,371,388320145044476813,372,667261845890994956,372,955492223116448616,391,672045821251883958,357,393668306252404892,369,667260746379367316,356,
672046920763511598,373,681897582892488860,369,960277297720529802,391,393668237532928156,369,681897514173012124,369,374526770868720613,355,681897582875711629,368,681897445436758157,368,
374527870380348253,371,960277366456783769,391,685908601579049902,391,681897513887799382,368,393668168796674189,368,662757146751996901,355,681897445168322646,368,662758246263624541,371,
393668168528238678,368,393668306235627661,368,393668237247715414,368,685908601562272671,391,685627058134520659,391,681053089242878876,374,676550589127136156,374,955773698093159327,391,
959995822743819091,391,672045889988137925,357,672046989499765565,373,671764346006737791,357,667543321136141123,372,667542221624513483,356,671765445518365682,373,681050890219623250,372,
676547290592252890,356,662756047240369030,339,374524571845464987,323,676829934085280683,357,676829865349026676,357,681333464976397287,373,681333533712651043,373,667261845890995055,1395,
388037569750832098,2404,667260746379367415,1379,392542268889830234,2404])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p16_0_0 : fcAllB [] (pr P2 16) 16 12 fba_p16_0_0 = false := by decide +kernel
lemma fva_p16_0_0 : fcBV (pr P2 16) 16 12 fba_p16_0_0 := fcAllB_val (fcBn) fka_p16_0_0
set_option maxHeartbeats 0 in
def fba_p16_0_1 : ℕ × List ℕ × List ℕ := (127,[105437793448178987,236795811944303,235696568751983,235627832497997,236727075690317,234527247128445,233359536117614,234390059833143,93652839913253,92621779326833,234528304093146,234528035657575,164090068686673,164021332432666,164158754608907,93790278866699,
234526961915703,234527230351214,105437862184432954,393386763359434039,388883163732063543,105437930920686961,393105357118977411,388601757491606915,676269045143647575,392823743596016990,234458779309934,233290816640823,388319044457018854,680771545259390295,676266846120392064,680770445747762675,
676550520388793742,392542268887741790,681053020504536462,388037569748743654,681050821481280836,676547221853910476,236864279762718,109447850062067086,680982721285141847,109166306365879639,392823744669758862,388320145042388366,681264264981329294,388038670065677655,392542269693048151,393105218572727565,
393386693817873711,388600519433729429,388881994678875575,388882063415129542,393386762554127678,388600657157895643,393105356296893779,374524571843376540,662756047238280583,393105219646469437,676829796610684262,681333396238054873,677111271587394918,393386694623180072,681614871214765529,388601620019098941,
388883094995809576,676475822317581798,680979421944952158,662757146749908454,374527870378259806,662758246261536094,374526770866632166,681049790420694366,676546190793324006,667543321134052676,671764346004649344,667542221622425036,671765445516277235,686752957502404026,398523680862320058,667260746377278869,
672046920761423151,672045821249795511,667261845888906509,686753025953445306,398523749313361338,379028171470747036,681897445166232919,383814345318020487,393668168794584462,681614870677894643,681897445434668430,393668168526148951,676828696830621132,681332296457991492,677111271050524032,681897513885709655,
393668306233537934,388600519702164940,685908601023313338,388881994410440064,110293374252168605,681897582873621902,393668237245625687,110292275008976285,393105218841163076,393386693549438451,685627057595561402,110293374235391374,393105356280116548,388600657141118412,164158771386138,110293305515914583,
393386762268915187,110292206272722263,388882063129916800,93790312421201,110292274992199054,685908601560184224,104659407935190502,104940882911901158,109444482807706974,109163007830996318,685627058132432212,105507131131770240,105225724606100940,109730423745099076,110011830270768627,681897514170922397,
393668306250315165,393668237530838429,681897582890399133,676901333317531107,969281266084033904,964777666456663544,676902432829158747,955492223114360169,398523749867009455,686753026507093423,398521551649060250,686751927532336538,960277297718441355,960277366454695322,685908601576961455,681827352424035613,
393386900831941917,388883301204571421,110010937504773405,672046989497677118,398523681399190868,686752958039274836,676547290590164443,681050890217534803,398523749850232224,686753026490316192,672045889986049478,676828834269574604,681614939397371379,677111339770000768,681332433896944964,398520383401178473,
681827352373703976,681545808677516605,686751927515559307,110010937454441768,686750759284454761,109729393758254397,398521551632283019,955773698091070880,959995822741730644,110010937471218999,681827352390481207,681545808711071107,109729393791808899,110011967709722073,105507268570723686,388882201105741158,
393386900244739545,681053089240790429,686751858796082516,686750828003931552,398520452120655264,672042591165953415,676550589125047709,667468623062840732,398521482912806228,105225724622878171,105223457400239509,110009700503860527,105506100624831942,105506100608054711,110009700520637758,681615008385283375,
677111408757913015,109730423761876307,109727057296045325,676828765281662357,681332364909032717,393386900261516776,388882201122518389,105507268604278188,110011967743276324,677111408774690246,681332365194245459,676828765566875099,95652208143578524,681615008402060606,100437283016095111,393386900278293796,
388882201139295660,110011967726499304,105507268587500917],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p16_0_1 : fcAllB [fba_p16_0_0] (pr P2 16) 16 12 fba_p16_0_1 = false := by decide +kernel
lemma fva_p16_0_1 : fcBV (pr P2 16) 16 12 fba_p16_0_1 := fcAllB_val (fcBc fva_p16_0_0 (fcBn)) fka_p16_0_1
set_option maxHeartbeats 0 in
def fba_p16_0_2 : ℕ × List ℕ × List ℕ := (127,[94890058930026,94958778406741,95989838993373,96058558470088,236727058913086,235627815720766,235696535197481,236795778389801,166426765776840,166357777864669,165258266236778,165327254148949,91453279786891,232191841883999,161821755529099,232191573448679,
166288789952307,165120290412420,166219802040311,165189278324667,95852400039927,94752619976580,95921119516467,94821339453371,235490376767320,235559096244111,236658339436431,236589619959640,166495753688876,96127277946668,236795275073317,235695763445677,
235627295627126,236726807255017,165327270926180,166357811418920,166426782554071,165258299791280,235695461455800,236794973083440,236725985171214,235626473543574,233359804553165,234390596704129,233360072988485,234390865139700,166358365067041,166427101320972,
166426799331091,166357794641900,165327287703451,165258283014009,236726253606725,235626741979085,236794704648180,235695193020289,234459584616240,233291353511694,233291085076374,234459316180920,233290279770013,234458242439048,235696585529118,236795828721438,
236863692560271,236863424124760,166151082563575,165051570935684,165051839371195,166151350998835,236795795167032,235696551974712,236727092467588,235627849275268,236794989860671,235695478233031,236726270383956,235626758756316,236795258296297,236726824032037,
235627312404397,235695746668406,236863960995646,236864229431081,236658356213662,235559113021342,162921267156794,235489303025639,236588814653279,236657265694559,164089766696796,235557754066919,236863709337502,164020778784549,162990255069041,92553059850042,
93721559390044,235558307715036,236657819342676,234459332958151,234459601393471,94890092484528,95989872547624,94958795183972,96058575247319,235695729891175,236795241519066,235627278849895,236726790477786,166289628813170,166495787243378,166220892559163,
166495770466107,96127311501170,96127294723899,236864246208312,232191036577693,232191305013128,236863994550148,166152156305196,162852816115569,94958828738378,96058608801725,163952059307813,164089783474027,162921552369536,235558290937805,236657802565445,
235489839896449,236589351524340,166288806729538,165189295101898,166220087252802,165120575625162,236863977772877,236864262985583,163952596178699],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p16_0_2 : fcAllB [fba_p16_0_0,fba_p16_0_1] (pr P2 16) 16 12 fba_p16_0_2 = false := by decide +kernel
lemma fva_p16_0_2 : fcBV (pr P2 16) 16 12 fba_p16_0_2 := fcAllB_val (fcBc fva_p16_0_0 (fcBc fva_p16_0_1 (fcBn))) fka_p16_0_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p16_0 : fcChkB [fba_p16_0_0,fba_p16_0_1,fba_p16_0_2] [] (pr P2 16) 16 12 0 FF 1 = false := by decide +kernel
lemma chk_p16_0 : chk [] (pr P2 16) 16 12 0 FF 1 = false := (fcChkB_eq (fcBc fva_p16_0_0 (fcBc fva_p16_0_1 (fcBc fva_p16_0_2 (fcBn)))) 0 FF 1).symm.trans fkr_p16_0
set_option maxHeartbeats 0 in
def fba_p16_1_0 : ℕ × List ℕ × List ℕ := (127,[232191573579751,232191842015071,235557754197991,236657265825631,236588814784351,235489303156711,162921267287866,164089766827868,235696568883055,233291085207446,236795812075375,234459316311992,235627832629069,233291353642766,234459584747312,236727075821389,
165120575756234,166220087383874,166288806860610,165189295232970,236864263116655,236863977903949,105437793448310059,100088668573873594,104593367712871730,99807193328727427,104311892467725814,235489571592086,236589083219726,235558559504312,236658071131952,233359804684237,
233360073119557,234390596835201,234390865270772,234389791528840,233358730942365,105437862184564026,105437930920818033,233359821461468,233360089896788,236863961126718,236658087909183,236864229562153,235558576281543,235489840027521,236589351655412,236657802696517,
235558291068877,236864279893790,95302494189729060,91079270295876976,95865444680021258,162783828334650,680771545259521367,163883608397916,676269045143778647,676550520388924814,681053020504667534,681897445166363991,393668168794715534,681897445434799502,393668168526280023,392823744669889934,
388320145042519438,392542269693179223,388038670065808727,393386694623311144,374524571843507612,388881994679006647,393105218572858637,393386693818004783,388601620019230013,388600519433860501,393105219646600509,388883094995940648,662756047238411655],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p16_1_0 : fcAllB [] (pr P2 16) 16 12 fba_p16_1_0 = false := by decide +kernel
lemma fva_p16_1_0 : fcBV (pr P2 16) 16 12 fba_p16_1_0 := fcAllB_val (fcBn) fka_p16_1_0
set_option maxHeartbeats 0 in
def fba_p16_1_1 : ℕ × List ℕ × List ℕ := (127,[165051571066756,166151082694647,165051839502267,166151351129907,95921119647539,95852400170999,94821339584443,94752620107652,96127278077740,166495753819948,161821755660171,91453279917963,166288790083379,165120290543492,166219802171383,165189278455739,
163952059438885,162852816246641,236589620090712,235559096375183,236863692691343,235490376898392,236863424255832,236658339567503,96127311632242,166495770597179,96127294854971,166495787374450,166220892690235,166289628944242,162990255200113,164020778915621,
166152156436268,236727059044158,236795778520873,236725985302286,236794973214512,235626473674646,235627815851838,235696535328553,235695461586872,232191305144200,232191036708765,94890059061098,94958778537813,95989839124445,96058558601160],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p16_1_1 : fcAllB [fba_p16_1_0] (pr P2 16) 16 12 fba_p16_1_1 = false := by decide +kernel
lemma fva_p16_1_1 : fcBV (pr P2 16) 16 12 fba_p16_1_1 := fcAllB_val (fcBc fva_p16_1_0 (fcBn)) fka_p16_1_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p16_1 : fcChkB [fba_p16_1_0,fba_p16_1_1] [] (pr P2 16) 16 12 1 FF 1 = false := by decide +kernel
lemma chk_p16_1 : chk [] (pr P2 16) 16 12 1 FF 1 = false := (fcChkB_eq (fcBc fva_p16_1_0 (fcBc fva_p16_1_1 (fcBn))) 1 FF 1).symm.trans fkr_p16_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_2 : chk [] (pr P2 16) 16 12 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_3 : chk [] (pr P2 16) 16 12 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_4 : chk [] (pr P2 16) 16 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_5 : chk [] (pr P2 16) 16 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_6 : chk [] (pr P2 16) 16 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_7 : chk [] (pr P2 16) 16 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_8 : chk [] (pr P2 16) 16 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_9 : chk [] (pr P2 16) 16 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_10 : chk [] (pr P2 16) 16 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_11 : chk [] (pr P2 16) 16 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16T_12 : chk [] (pr P2 16) 16 12 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_16 : Imp [] 16 13 := by
  refine imp_of (E := []) (Q := pr P2 16) (Z := 16) (L := 13) (Or.inl rfl) (by decide +kernel) (by decide)
    (fun e he => P2ok e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ?_)
  interval_cases t
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p16_0⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p16_1⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_2⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_3⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_4⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_5⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_6⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_7⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_8⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_9⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_10⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_11⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p16T_12⟩
set_option maxHeartbeats 0 in
def fba_g16_0 : ℕ × List ℕ × List ℕ := (127,[166289377295038,166220909476467,166220372605481,166151904787160,969634210658867128,974137810017802168,965343915230320539,965062508973086640,681401634947028964,685623759329253233,970126859815835521,970126791079581514,970055322806998890,970056491306538892,970199427012843448,974701927128586168,
974420383700834253,686471551798957979,681969051683215259,686187878067427248,960557809834088409,960558840626239313,960557741114611673,960554442294515610,686470383819511637,384095958019037053,974138909260994488,672325165654431543,681966783386834916,686187876976908145,384095958002259822,672325165939644285,
974982234142627768,969561641549256561,965269148422854628,970058759619696513,398241244903593802,393738744519415626,686471551782180748,970057659839633281,965413254239311774,965414353482504094,974980035656243128,100719857504573239,677180610076432275,686190076537034657,388951402424260418,677180610344867595,
393735377248278474,398238977144084290,393737644202481625,398242343341479761,974701996133275565,965409886984951662,393737645276223306,398242344146786122,398242344163563393,677183976810698577,388951402172602329,969917884121962343,974701927665457054,965413184446093302,969282366149449553,964778766522079193,
676899204104410961,676899203835975641,686471688684263308,974699729179072414,974419284994512743,686188908305929995,671973322470414135,100438451247339374,686469352758925122,965340616695437273,969844216322807633,960628110378883062,686470452538988428,974137809480931182,100721025484019581,393456101043165145,
397960800182163281,960627011404126062,681965753148331993,686187877798991697,686469352775702353,970196129836914605,974420452973959085,680206327563376654,675702727936006294,675701628424378599,666694429169637533,680207427343439920,680208527123503166,671199128308635703,671199128577071214],[388883301206799645,374,680771545261618519,374,676269045145875799,374,388038670067905879,371,388320145044616590,372,950988623489217978,391,681050821483509060,372,676266846122620288,357,
680770445749990899,373,960277297720669579,391,960558910169888128,391,960558841433634121,391,685908601579189679,391,662756047240510087,338,104311892469822825,3428,95865444682119782,2388,
100088668575970699,3429,99807193330824553,3428,969282297415284033,357,969000822438573322,357,104311892469822906,3427,964778697787913673,357,95302494191826267,3427,960558772697380154,391,
667261845891136013,370,374527870380489310,370,672045821252025015,355,95302494191827584,2386,91079270297975364,2403,91079270297975500,2387,388319044459248358,320,662758246263764318,371,
662757146752136678,355,104311892469824094,2352,392823743598246494,320,681897513887939159,368,379310746229750381,339,393668306235767438,368,393668237247855191,368,91079270297975405,2371,
667260746379507093,356,681053089243018653,374,667542221624654540,355,671765445518506739,370,672046920763651375,373,388038670067907159,370,680982721287371351,368,676550589127275933,374,
388601757493836419,372,393668237533067933,369,99807193330825815,2401,672045821252023735,357,104311892469824087,2400,100088668575970720,3428,99807193330825815,2400,99807193330824532,3429,
104593367714968992,3428,393668168796813966,368,681897445168462423,368,676547221856139980,353,393668168528378455,368,950986423929091481,357,955773698093299104,391,671765445518505459,373,
681053089243018671,1396,99807193330824696,3395,959994722427024867,372,676550589127275930,1397,676269045145875817,1396,676898035858617783,1415,955491122799654392,372,955492222311282032,388,
681053020506764683,1381,676898035590182327,2439,388953532193256806,1415,388952432681629030,2439,677182877284382109,2439,384168457320740300,1415,672046920763651467,1398,685908601562412445,2405,
964989873008358839,2439,969493472635729335,1415,677182808564905318,2439,384167357809112524,2439,685627057866224998,2405,685627057866225100,1364,676547290592392667,356,950988623489217996,2387,
662758246263764315,1397,374526770868860408,1380,667260746379507049,2422,388320145044616587,1398,388038670067905897,1397,91079270297974217,3412,964499421566023095,1398,680771545261618516,1381,
100088668575970761,3412,964780896274298316,1397,99807193330824594,3412,104593367714968897,3412,676550520391021984,1396,969633111149327820,408,676269045145875796,1397,393175657112352183,1415,
969494572415792588,1414,672112961254536652,2420,681120160509277623,2404,681333464976537064,373,964780896274298298,391,397678157496530359,1415,667261845891134832,1395,392542268889970011,2404,
672112960986101196,2436,388037569750971875,2404,388320145044616608,1397,955491122799654348,2436,680771545261618618,1379,379028171472975216,2420,392542269695276372,1398,388038670067905876,1398,
676266846122620387,1363,680770445749990747,1363,955492222311282124,2420,392542268889970106,2420,662757146752136634,2422,950988623489217975,1414,662758246263764410,1398,950988623489217996,1413,
950988623489217996,1397,685623759868212666,391,685908532574500279,1398,681406032458757559,1414,374526770868860408,2371,950988623489217978,371,955491122799654348,2439,685905234844923340,1413,
685905234308052336,389,662757146752136675,2387,662758246263764315,2387,676547290592392623,2422,681050890219763119,1398,969281266086262220,1415,672045889988277658,2422,374527870380488048,2371,
685623759868212663,1414,959992523403769241,340,964496123033228235,1603971,964778697253131190,1603972,964497222813291365,1603971])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_0 : BinarySearch.fcAllB [] (pr G2 16) 16 13 1 fba_g16_0 = false := by decide +kernel
lemma fva_g16_0 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_0 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_g16_0
set_option maxHeartbeats 0 in
def fba_g16_1 : ℕ × List ℕ × List ℕ := (127,[165189865667147,166152173222460,165052393159269,165120860977841,960629210158946253,960628110915753933,974982371313145703,969846415346063259,969565009088829360,974982371581581214,681120159701882873,685905234574399324,970056560059570049,970126928518534986,970199358561802168,969917883585091533,
969917952036132813,974420452151875533,974701858677544888,681684278708492208,960558909345716049,960484073818773402,681684278691714977,681966784460576597,686187878050650017,969636408876816333,969636409145251768,686470383014205276,681684277349537785,974138908992559053,974981203082041293,969772748050224988,
965058041921886201,681687507701815146,681969051666438028,686190007817557866,965414284763027303,965413185519834983,974982371598358445,974980035387807693,672254866166601582,100156907551151927,100721025467242350,681968982946961237,681687576421291937,686471483062703957,397958532959524619,388951402155825098,
393454933063718803,676617660123010963,676899203819198410,676617660391446283,676899204087633730,965409886716516342,970199496017532845,672043690962933629,393737645293000577,677182877299070937,388951402441037649,965414352408762222,970199427549714334,965413252897134582,965414283957720942,974420384237705063,
686190144719640426,970196129820137374,969915685635577703,681685308678559635,681965753131554762,965060309949831129,969563909577201489,681966853180053388,969634209853560822,681684209972238186,686187809331173226,960629209890510702,974982303130539934,974981135167870823,974982303147317165,960627011135690742,
393735377265055705,398238977160861521,681684278171621337,974699729195849645,974419353730766765,969917952858216365,969915754371831725,970199427566491565,974701927682234285,671198028797008008,680205228051748959,680208527391938601,675703827716069560],[676550520391021966,374,681053020506764686,374,676829796612912486,357,681333396240283097,373,95865444682118458,3429,388601620021327165,373,388883094998037800,374,388883163734291767,374,
388601757493835139,373,676547221856138700,356,955492223116588393,391,388601620021328445,372,388883094998039080,373,960277366456923546,391,95865444682119897,2404,374524571845606044,322,
104593367714968971,3429,95302494191826260,3429,964497222811202962,357,969001921681765818,372,964499421566023098,388,99807193330824634,3427,91079270297974176,3429,964496123031139832,340,
968999722658510192,340,95302494191826403,3411,672046920763652655,371,662757146752137958,354,662758246263765598,370,667260746379508373,354,374526770868861670,354,99807193330825815,2402,
374526770868860390,355,100088668575971982,2403,99807193330825958,2352,676550520391023246,371,676269045145877079,370,95302494191827699,2402,374527870380488030,371,681897582892628637,369,
379029271253039670,338,681897582875851406,368,671764346006878848,354,388883163734293047,373,667261845891134733,372,681264264983558798,368,681897514173151901,369,667543321136282180,371,
667259646867880502,338,388320145044617870,371,681053020506765966,369,680771545261619799,369,100088668575971982,2401,393668306252544669,369,681050821483510340,369,104311892469822804,3429,
104593367714970254,2400,100088668575971982,2400,681897445436897934,368,676266846122621568,353,680770445749992179,369,959995822743958868,391,667543321136280900,372,671764346006877568,357,
667542221624653260,356,681053089243018650,1381,959995821938652507,388,676550589127275951,1380,104311892469822832,3395,680771545261618537,1380,672112961254536652,1415,676550520391021963,1397,
104311892469822811,3411,99807193330824675,3411,672112960986101196,2439,677183976796009885,1415,672045821252023691,2422,677183908076533094,1415,964989873008358839,2437,672046989499905342,373,
685627058134660454,1381,685908601830847901,1381,388952501401105821,2439,672045889988277702,357,388953600912733597,1415,681050890219763027,372,374527870380488048,1396,950988623489217975,2404,
667261845891134825,1398,662757146752136675,1381,392542269695276393,1397,374524571845604764,323,392823744671987083,1398,95302494191826322,3412,91079270297974081,3428,95302494191826186,3428,
662756047240508807,339,974136710508262860,408,965131710545212855,408,104311892469822730,3412,969001921681765815,1414,965132809788405175,408,681053020506764704,1380,969283396390041036,1413,
676550520391021984,1380,676269045145875796,1381,681053020506764704,1396,969283396390041018,391,681333533712790820,373,969495672195855820,1414,676829934085420460,357,969001921681765818,391,
676829865349166453,357,964499421566023098,391,667260746379507192,1379,685623759868212663,2404,680771545261618516,1397,685905234844923322,391,379028171472975352,2404,392823744671987104,1397,
392542269695276474,1396,388038670067905978,1396,676269045145875898,1395,374527870380488122,1398,681120160509277626,391,681401635485988282,391,676269045145875895,3411,950988623489217975,1398,
388037569750971834,2420,680771545261618615,3411,374526770868860346,2422,676901333319759287,2439,685623759599777115,390,676902432831387063,1415,950988623489217978,372,950988623489217978,387,
969283465109517772,1413,964777666458891724,2439,681401634680681976,373,681401635485988300,1397,95302494191826329,3395,955492222311282124,1415,681120159972406755,374,681120160509277623,1398,
964780964993775052,1397,960276197135300023,2439,672046989499905434,1398,960277296646927799,1415,950988623489217978,388,964778697790002076,1603972,964778765972607926,1603972,685627057599878091,1603924])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_1 : BinarySearch.fcAllB [] (pr G2 16) 16 13 1 fba_g16_1 = false := by decide +kernel
lemma fva_g16_1 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_1 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_g16_1
set_option maxHeartbeats 0 in
def fba_g16_2 : ℕ × List ℕ × List ℕ := (127,[105437793448318764,99807193328736132,163883608406621,166358381984269,166289645730338,162852833032833,165051856288459,165052124723834,165121129413276,166083436968493,164983388469867,166083168533193,166082900097758,166082363226872,164983120034492,162784096778866,
388319044457158631,392823743596156767,681897582873761679,681897513885849432,393668168526288728,681897445166372696,393105218572867342,388600519433869206,681264264981469071,109447850062206863,671765445516417012,671764346004789121,91079270295885681,676475822317721575,681049790420834143,392542269693187928,
388320145042528143,384095820294870839,374524571843516317,676266846120531841,681050821481420613,676269045143787352,681053020504676239,964780896272209851,964499421563934651,374526770866771943,383532870878320439,662757146750048231,388601620019238718,388883094995949353,374527870378399583,110292274992338831,
110292206272862040,110293374235531151,959995822741870421,955773697017468785,955772597505841145,110292275009116062,685908601577101232,393105357119117188,393386763359573816,672046920761562928,676829796610824039,681333396238194650,681614871214905306,681053089240930206,676550589125187486,970124591502677947,
969564940369352624,969846484065539995,686751996235175739,964497222809114515,964778697785825226,393386693549578228,393105218841302853,681401635483899835,681120160507189179,388600519702304717,104659407935330279,970126790525933397,393457132086974314,393738675783161740,969846346609809292,965062371248920426,
95865444680029963,974981134631000013,672397733690300409,681401634678593529,960558771621549835,960558771889985346,964778765968431076,393386762554267455,388600657158035420,950986423927003034,681050890217674580,676547290590304220,686751858796222293,686750828004071329,398520452120795041,398521482912946005,
965339516898596836,964987673446143993,969846346341373781,955772666225317881,955773765736945521,969564871633098657,686753026507233200,398521551649200027,676828696830760909,398237808912979804,964992072566396764,970058622147188565,681614870678034420,969777215889954721,393172358575380473,393452734040463353,
397960800450598832,393105356280256325,105506031888717697,388600657141258189,105223526119856077,393386762269054964,965132809786316728,965131710543124408,397959701190629281,970125691014305642,970126859513845644,964780964991686587,398241107447863125,109730423745238853,388949134144657306,105507131131910017,
686751996251952970,686751996268730241,398521620385453953,667259646865790775,672043622226679662,965272447763044243,393456100221081593,960558840341026571,964777666456803321,676902432829298524,677111339770140545,681614939397511156,970125691299518384,398242205885749084,681897514171062174,388883301204711198,
681897582890538910,964988773226207225,393668237530978206,393386900832081694,110010937504913182,969776047390414698,965343983933020044,686186709282674545,969846484048762764,969913486612322253,970194961589032888,974698560947967928,965062439968397162,969844285025507138,379028171470886813,681545808677656382,
969563771853035275,110011967726639081,388882201139435437,965340547959183306,393386900278433573,393737507820492629,969844147586553666,110010937454581545,955771497994213274,959992523401680794,379029271250949943,969495672193767355,681545808711210884,681827352390620984,676898035856529244,676898035588093924,
672112961252448113,388882201105880935,960558841431545674,105507268570863463,960277296644839260,681402733921785849,685906333549156209,960277365364315996,965062508956309409,969846415060850517,969773916549764930,681332364909172494,681615008385423152,388953532191168267,677111408758052792,677183976793921346,
955771566713690010,672042591166093192,109730423762016084,110009700504000304,109727057296185102,105223457400379286,105507268604417965,388882201122658166,388952501399017418,970055391526475681,681332365194385236,95652208143718301,100437283016234888,970056422587062101,686749659772966843],[685627057866225001,391,685908601830847883,391,685908601562412448,391,685627057597789626,391,685908601025541562,391,968999722658510284,1415,964778697251042743,2439,969282296878413239,1415])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_2 : BinarySearch.fcAllB [fba_g16_0,fba_g16_1] (pr G2 16) 16 13 1 fba_g16_2 = false := by decide +kernel
lemma fva_g16_2 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_2 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBn))) fka_g16_2
set_option maxHeartbeats 0 in
def fba_g16_3 : ℕ × List ℕ × List ℕ := (127,[100088668573882299,104593367712880435,104311892467734519,162783828343355,164021349349970,163952613095963,163952344660588,166151367916099,166151636351725,166220641040916,163883876841996,164983656905302,164982851598981,166082631662132,163883339971110,161684316715660,
388037569748883431,392542268887881567,393668237245765464,393668306233677711,393668168794724239,681897445434808207,393386693818013488,388881994679015352,680982721285281624,109166306366019416,667543321134192453,667542221622564813,95302494189737765,680979421945091935,676546190793463783,970126722343327547,
388038670065817432,392823744669898639,672325097203390318,662756047238420360,680770445747902452,676547221854050253,676550520388933519,680771545259530072,969283396387952571,969001921679677371,662758246261675871,379310746227660654,164090068826450,393105219646609214,393386694623319849,164021332572443,
960558772695291707,110293305516054360,955773698091210657,959994722424936420,959995821936564060,110293374252308382,960277366454835099,388601757491746692,388883163732203320,667261845889046286,672045821249935288,677111271587534695,667260746377418646,955492223114499946,960277297718581132,970054223026935739,
965062440253609904,965343983949797275,398521620351899451,969000822436484875,969282297413195586,109163007831136095,970125760002217889,109444482807846751,388881994410579841,104940882912040935,685905234842834875,685623759866124219,397959632471152490,398241176167339916,969564871364663146,965343846494066572,
974982302593669048,681120159970318308,960557672109922195,685905234305963889,969282365595801436,672398833201928049,685623759597688668,960557672378357706,393105356297033556,388882063415269319,672045889986189255,393173458087008228,960487373158963193,672046989497816895,960488472939026289,397677057982814044,
969843116525967196,969491273073514353,685907433060783964,965062371517355937,965343846225631061,681403833433413604,398523749867149232,686751927532476315,677111271050663809,397956333936269169,681332296458131269,969776116109891489,970057522367125333,964990972786333668,393734209017173988,397675958471186289,
388882063130056577,393738675799938971,109727126015661893,393456101580036016,398241176184117147,110009631784523764,969633111147239373,974136710506174413,393738607063684949,969283465107429307,393457200806451105,685908532572411835,681406032456669115,110011830270908404,105225724606240717,677179510027933594,
398521620368676682,234458796226942,965272516482521034,965273616262584130,965273547543107339,676901333317670884,969281266084173681,393737506746750948,960557809817311178,960558909328938818,960557740829398931,681332433897084741,397960799360079729,676828834269714381,970126859530622875,681827352424175390,
969492372853577585,388670957702830052,393668306250454942,388672057214457692,681964584900450276,969777147170477930,681683109655304185,970058690866665356,686468184527820636,969564940084139882,970057591086602124,974417085971257293,965060240945141651,969563840572512011,965340685398136778,383814345318160264,
398520383401318250,686750759284594538,965060172225664915,105507268587640694,681827352373843753,397960800433821601,686751927515699084,398521551632422796,393456101563258785,398242206691055445,109729393758394174,110010937471358776,393175657110263739,397678157494441915,383814345855031150,969494572413704123,
109729393791948676,672112960984012793,960276197133211620,955492222309193585,393386900244879322,110011967709861850,955491122797565945,960558910167799681,960276265852688356,969565009072052129,965343914945107797,965271347982981011,969774947610351371,965270316922394570,388952432679540627,676828765281802134,
672396634178672538,677182877282293706,667468623062980509,105225724623017948,105506100624971719,110009700520777535,105506100608194488,677182808562816915,677183908074444555,110011967743416101,388953600910645058,393386900261656553,676828765567014876,677111408774830023,681615008402200383,384166258295396250,
960486273378899866,398519283889690555],[685627058134660436,391,955773766829553071,391,685908601847625114,391,964496123031139788,2439])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_3 : BinarySearch.fcAllB [fba_g16_0,fba_g16_1] (pr G2 16) 16 13 1 fba_g16_3 = false := by decide +kernel
lemma fva_g16_3 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_3 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBn))) fka_g16_3
set_option maxHeartbeats 0 in
def fba_g16_4 : ℕ × List ℕ × List ℕ := (127,[96127278086445,165189278464444,165120290552197,94890059069803,95989839133150,235490376907097,236589620099417,95921119656244,94752620116357,165258266376555,165327254288726,166152156444973,235696585668895,166427101460749,166358365206818,166151082703352,
91453279926668,161821755668876,236795778529578,235695461595577,236794973223217,235626473683351,232191573588456,236726253746502,165258283153786,165327287843228,93652840053030,235627832637774,236795812084080,236727075830094,94958795323749,94890092624305,
95989872687401,235627278989672,235695730030952,235696552114489,235627849415045,166357811558697,236794990000448,235695478372808,235626758896093,94958828878155,96058608941502,236863709477279,236864279902495,235627312544174,235695746808183,233291353651471,
234459584756017,164158754748684,93790279006476,236726807394794,235627295766903,236795275213094,236863977912654,233359536257391,970125622563264417,232191036717470,234390596843906,233359804692942,234390865279477,166220087392579,233358730951070,233290279909790,
234458242578825,234528035797352,964496123029051385,234528052574583,686753026490455969,234528321010154,686752958039414613,236657819482453,234459601533248,234459333097928,685908601845536667,955773766827464624,685908601560324001,686753025953585083,398523749313501115,398520452137572272,
686750828020848560,685627057864136554,686752957770979178,398523750118807436],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_4 : BinarySearch.fcAllB [fba_g16_0,fba_g16_1,fba_g16_2,fba_g16_3] (pr G2 16) 16 13 1 fba_g16_4 = false := by decide +kernel
lemma fva_g16_4 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_4 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBc fva_g16_2 (BinarySearch.fcBc fva_g16_3 (BinarySearch.fcBn))))) fka_g16_4
set_option maxHeartbeats 0 in
def fba_g16_5 : ℕ × List ℕ × List ℕ := (127,[166495753828653,166288790092084,166219802180088,94958778546518,96058558609865,235559096383888,236658339576208,95852400179704,94821339593148,166357778004446,166426765916617,105437862184572731,105437930920826738,236795828861215,166151351138612,165051571075461,
165051839510972,236727059052863,235696535337258,235627815860543,236725985310991,232191842023776,235695193160066,236794704787957,235626742118862,166426799470868,166357794781677,92621779466610,235696568891760,162921267296571,164089766836573,96058575387096,
236795241658843,236726790617563,236795795306809,236727092607365,166426782693848,165258299931057,165327271065957,236726270523733,236658356353439,235559113161119,93721559529821,92553059989819,685908601023453115,685627057595701179,236795258436074,236726824171814,
233291085216151,234459316320697,162990255208818,164020778924326,235695763585454,233290816780600,234458779449711,236864263125360,970126721806456661,234390059972920,232191305152905,233360073128262,166288806869315,165189295241675,165120575764939,234389791537545,
234528304232923,964778697248954340,969282296876324700,968999722656421745,234528337787174,398523749850372001,398523681399330645,234528069351854,235558307854813,234526962055480,234527230490991,685627058132571989,398523680862459835,686752957502543803,163952596318476,686753026775668635,
398523750135584667,685908601828759436,398523681130895210,686753026758891404],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_5 : BinarySearch.fcAllB [fba_g16_0,fba_g16_1,fba_g16_2,fba_g16_3] (pr G2 16) 16 13 1 fba_g16_5 = false := by decide +kernel
lemma fva_g16_5 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_5 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBc fva_g16_2 (BinarySearch.fcBc fva_g16_3 (BinarySearch.fcBn))))) fka_g16_5
set_option maxHeartbeats 0 in
def fba_g16_6 : ℕ × List ℕ × List ℕ := (127,[236863424264537,236863692700048,236863961135423,236864229570858,235557754206696,236657265834336,235489303165416,236588814793056,235489571600791,236589083228431,236658071140657,235558559513017,96127311640947,166495770605884,96127294863676,166495787383155,
166220892698940,166289628952947,162852816255346,163952059447590,235489840036226,236589351664117,236657802705222,235558291077582,236864246348089,236863994689925,235558576290248,236658087917888,233359821470173,233360089905493],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g16_6 : BinarySearch.fcAllB [fba_g16_0,fba_g16_1,fba_g16_2,fba_g16_3,fba_g16_4,fba_g16_5] (pr G2 16) 16 13 1 fba_g16_6 = false := by decide +kernel
lemma fva_g16_6 : BinarySearch.fcBV (pr G2 16) 16 13 1 fba_g16_6 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBc fva_g16_2 (BinarySearch.fcBc fva_g16_3 (BinarySearch.fcBc fva_g16_4 (BinarySearch.fcBc fva_g16_5 (BinarySearch.fcBn))))))) fka_g16_6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g16_0 : BinarySearch.fcChkB [fba_g16_0,fba_g16_1,fba_g16_2,fba_g16_3,fba_g16_4,fba_g16_5,fba_g16_6] [] (pr G2 16) 16 13 1 (0x1ffffffffffffffffffffff) 0 = false := by decide +kernel
lemma chk_g16_0 : BinarySearch.chk [] (pr G2 16) 16 13 1 (0x1ffffffffffffffffffffff) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBc fva_g16_2 (BinarySearch.fcBc fva_g16_3 (BinarySearch.fcBc fva_g16_4 (BinarySearch.fcBc fva_g16_5 (BinarySearch.fcBc fva_g16_6 (BinarySearch.fcBn)))))))) (0x1ffffffffffffffffffffff) 0).symm.trans fkr_g16_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g16_1 : BinarySearch.fcChkB [fba_g16_0,fba_g16_1,fba_g16_2,fba_g16_3,fba_g16_4,fba_g16_5,fba_g16_6] [] (pr G2 16) 16 13 1 (0x1ffffffe0000000000000000000000) 0 = false := by decide +kernel
lemma chk_g16_1 : BinarySearch.chk [] (pr G2 16) 16 13 1 (0x1ffffffe0000000000000000000000) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBc fva_g16_2 (BinarySearch.fcBc fva_g16_3 (BinarySearch.fcBc fva_g16_4 (BinarySearch.fcBc fva_g16_5 (BinarySearch.fcBc fva_g16_6 (BinarySearch.fcBn)))))))) (0x1ffffffe0000000000000000000000) 0).symm.trans fkr_g16_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g16_2 : BinarySearch.fcChkB [fba_g16_0,fba_g16_1,fba_g16_2,fba_g16_3,fba_g16_4,fba_g16_5,fba_g16_6] [] (pr G2 16) 16 13 1 (0x3fffffffffffffffffffffffe00000000000000000000000000000) 1 = false := by decide +kernel
lemma chk_g16_2 : BinarySearch.chk [] (pr G2 16) 16 13 1 (0x3fffffffffffffffffffffffe00000000000000000000000000000) 1 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g16_0 (BinarySearch.fcBc fva_g16_1 (BinarySearch.fcBc fva_g16_2 (BinarySearch.fcBc fva_g16_3 (BinarySearch.fcBc fva_g16_4 (BinarySearch.fcBc fva_g16_5 (BinarySearch.fcBc fva_g16_6 (BinarySearch.fcBn)))))))) (0x3fffffffffffffffffffffffe00000000000000000000000000000) 1).symm.trans fkr_g16_2
def shards_g16 : List (ℕ × ℕ) := [(0x1ffffffffffffffffffffff,0),(0x1ffffffe0000000000000000000000,0),(0x3fffffffffffffffffffffffe00000000000000000000000000000,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shardsCover_g16 : mFull shards_g16 = true := by decide +kernel
lemma chkAll_g16 : ∀ p ∈ shards_g16, BinarySearch.chk [] (pr G2 16) 16 13 1 p.1 p.2 = false := by
  intro p hp
  simp only [shards_g16, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact chk_g16_0
  · exact chk_g16_1
  · exact chk_g16_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strong16 (floor : Imp [] 16 13) (prior : ∀ e ∈ G2, HasGrade 1 e) : HasGrade 1 (16,13) := by
  apply gradeFromFloor (t := 1) floor (by decide +kernel) (by decide +kernel)
  intro S sw hl
  refine BinarySearch.rejectMinimum (Q := pr G2 16) (L := 14) (by decide +kernel) (by decide) (by decide) ?_ sw hl floor shards_g16 shardsCover_g16 chkAll_g16
  intro e he
  exact prior e (List.mem_of_mem_filter he)
lemma g_16 : HasGrade 1 (16,13) := strong16 p_16 G2ok
set_option maxHeartbeats 0 in
def fba_p64_0_0 : ℕ × List ℕ × List ℕ := (127,[676546087714108877,236795258296181,236863977773032,235695746668343,234528069211904,235627312404224,234389791397807,235489303025447,235696551974732,236588814653285,166082899957966,234458796087183,235558307714823,235489839896407,234390596704087,965344052954346769,
235558576150374,234459332958054,232191305013167,232191573448487,965343846225491304,166220372465885,166289377155090,166289645590661,236727075690472,686187878050510285,236726807254901,686187877782074714,970199496000615726,233290279769936,166082363086905,163883608266828,
164983119894719,236589351524245,233291085076467,233290816640896,236589619959565,235559113021212,234459601393572,965343846493926705,104874911694140696,236657819342661,965340685397996828,166083436828837,161684316575827,162784096639208,964780896808941005,960277297181570394,
166082631522306,166083168393266,109727126032299332,964780896272069944,960277296644699584,166358381844708,165120860838047,970196129819997486,164021349210156,166220640901185,166220909336756,163883876702237,164983388330128,164982851459318,163883339831427,165189865527503,
166151367776328,166152173082859,165051856148490,163952344520850,162852832892979,166151904647288,164983656765679,162783828203556,393105287577417028,165052393019450,165052124584150,165121129273347,166151636211737,163952612956259,681332433913722180,965343984234870033,
675983137760688333,667543389870306628,393737609557390597,393737472118437328,393455997141726557,398523887322739985,680136165514361081,676898000154473915,965340547690607955,672394400527103304,109729462477731845,676899168385578475,965340685414774114],[681616177205679071,374,681616039733171018,374,681616108469424915,374,681615970996916996,374,667543321136142584,371,100651756538632211,2405,393105218843252984,336,100088668575832271,2401,
95583969436833884,2401,681403902423274267,374,667543321136141304,372,676269045145735947,374,671765445518365587,373,672328533481165628,373,676832133108536239,374,667541122112885575,340,
667542221624513466,356,672046920763511644,373,676550520390882255,374,671762146983482238,340,676265746610852849,356,662754947728741198,323,667541190849139597,340,667542290360767237,356,
676548321367626526,357,681053020506624975,374,959994687798711247,374,955491088171340636,373,950987488543970296,372,676831995636028320,374,672045821251883806,357,384096920613753834,357,
672328396008657709,373,681051920994997084,373,384096989350007605,357,667541122112886855,339,667542221624514746,355,379312945252865016,372,374523437705664760,2401,383815445637042974,356,
388881994680965150,352,388882132119918622,352,677111408760002590,352,955772598313095963,374,677111271321049118,352,950987488543970296,371,955772563148051245,373,100651619066124292,2405,
960276162775421856,374,676550520390883535,371,672046920763512924,371,374523437705663480,2403,672042488088826784,2405,969564872171918081,374,667538888461456173,2404,960557637752133636,372,
662758246263624547,371,667261845890994996,372,681403901886403457,374,95583969436832601,3428,100088668575830988,3428,681051989731251106,373,955487789636457243,2403,681053089242878746,374,
104874842959975169,3429,680769346238223156,372,959991389263827739,1381,955487789636457243,2405,388319010099368705,3429,969565009644426000,374,374523437705663259,3412,955491088173429039,1464675])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p64_0_0 : fcAllB [] (pr P2 64) 64 12 fba_p64_0_0 = false := by decide +kernel
lemma fva_p64_0_0 : fcBV (pr P2 64) 64 12 fba_p64_0_0 := fcAllB_val (fcBn) fka_p64_0_0
set_option maxHeartbeats 0 in
def fba_p64_0_1 : ℕ × List ℕ × List ℕ := (127,[388319010097280461,388600485073990961,388881960050701732,374523437703575015,100088668573742526,95583969434744139,104874842957886925,388037535120569601,104593367712740609,667538888459367708,672042488086738319,667543321134052857,235695478232934,681332433896945145,955491088169252189,959994687796622800,
393105218841163257,393386694086309166,393668169063019937,681053020504536528,681051920992908637,392823744132888057,100651619064034798,672045821249795359,676548321365538079,667542221622425019,667541122110797128,960557637750043909,166220087252808,393668168526148876,393386693549438356,950987488541881849,
388319045262325023,383815445634954527,235696568751893,965057938842531118,965339413819241889,965343846762362114,109727126015522297,104943150654633247,676759565573895455,388881994678875423,677111271318959391,393105218572727605,392823743596016996,676831995633939873,672328396006569262,379312945250776569,
964494988889110009,681897445434668496,109727057296045365,960276162773333409,681615008385283421,955772563145962798,233360089765701,681897582873621968,681614870946329949,676550520388793808,236726270383941,672046920761423197,393386831256827229,681616108467336468,393668306233538000,681897583444047124,
393386831558817085,681332296189556021,393668306535527856,677111408757912863,388882132117828895,384096920611665387,388600520239035883,109445651038811641,109730355025622325,955487789634368840,959991389261739451,969564871632958925,969563772121331034,681401599781844473,109444482807706980,379309646179022159,
969563909560284506,969565009071912397,960554339215160811,393386693817873757,393668168794584528,681897445971539205,681615970994828549,105506100608054559,105507199851246879,393738744502498562,681969120385774850,681332364909032757,681897652180301280,681616177203590624,965409851282896156,970058759586002178,
681897513885709580,384095889014207871,388600588153206258,105223526136493318,100719926240687502,681897514707793227,681616039731082571,681614939397371284,955772598311007516,110293511724676576,671765445516277140,393668444259694048,969564872169829634,676269045143647500,965413218537256194,388600519702164923,
681965753131414812,384095820563166536,393735377248138524,676828696562185714,672325096934815103,681897651895088560,393668444242916628,110293511707899156,110009769256891709,676265746608764402,681615077406750013,676832133106447792,672328533479077181,110292343745230256,671762146981393791,110293511691121995,
681262065421202937,393668444226139467,676828834269574587,393668444209362181,110293511674344709,672325234642203976,110009631784383892,110292206272722188,393105287292204341,110011899007022499,110292343711675809,100719926223910216,110011898990245213,681120124805133817,105223526119716283,110292274992199120,
110293374235391440,105224694367597878,110293374252168475,110009769223337262,110009700503860573,677041109286860086,681615077373195566,384096989347919158,388600588975289654,95933683120289103,681403902421185820,965270316922254620,100720956747625855,677041109270083051,681897651861534113,105225655886624242,
662754947726652751,105224694350820843,681966748758521296,681403901884315010,681684174270182749,667538991538582863,681966817477997985,672325234658981262,676828834286351622,384095889299420558,393737575734523164,681684242989659438,681966852374607132,662758246261536100,388600588438418694,393737575197652354,
667542290358678790,393386831273604515,667541190847051150,681966851837736322,393668306250315035],[676617624691479326,357,681403903228580656,374])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p64_0_1 : fcAllB [fba_p64_0_0] (pr P2 64) 64 12 fba_p64_0_1 = false := by decide +kernel
lemma fva_p64_0_1 : fcBV (pr P2 64) 64 12 fba_p64_0_1 := fcAllB_val (fcBc fva_p64_0_0 (fcBn)) fka_p64_0_1
set_option maxHeartbeats 0 in
def fba_p64_0_2 : ℕ × List ℕ × List ℕ := (127,[165017211197393,235523394328526,161718676314044,166151350998786,162990255069160,96058558469938,96127277946789,236795275073342,236863994550193,236863692560337,236794973083486,233360072988666,236727092467633,236726824032062,95921119516418,166288789952258,
166151082563385,236726253606906,166426799331137,166495787243444,166219802040121,161821755529043,166426765776690,166495753688997,95989838993358,236863960995746,236795241518895,236795828721633,236864279762913,92621779326952,232156139968488,162921267156772,
235695461455648,233291353511734,165120290412534,164020778784643,235660833281957,235592113805106,234528304092975,235627815720866,166357777864654,235627849275313,234528337647422,96127311501236,165189278324671,236657802565626,164089766696780,96058592024385,
164158754608925,165258266236816,166357811419101,235695193020247,235454674851586,166288806729544,233324371072797,234423882700688,235626741979068,234527230351177,94890058930064,96127345055716,93790278866717,235696585529313,236657265694565,236725985171254,
93721559390028,94821339453375,165258299791263,164158788163372,165120575624970,164021063997330,235558559373088,234459316180768,236794704648085,236863424124685,233359804553148,233358730811216,233359536117577,165051839371199,163952327743308,235695763445504,
166495770466283,166426782553976,236658071000926,236658339436497,236794989860772,236863709337372,236727058913186,236726790477615,235695729891308,162852547680036,232191841884005,166495804020613,166426816108306,236864229431046,236795778389766,235627278850028,
234528035657708,166289091942365,165258585003983,166151619434446,165121112495930,165327254149103,94958778406895,234458242439087,235557754066727,236658087778212,236658356213532,235558290937788,234458779309897,236795811944213,236864262985493,234526961915776,
235626473543667,236589083088694,234390865139605,235490376767245,236864246208332,236795795167052,94890075707350,93790295644003,233359552894863,233359821330183,232191036577616,234528052434743,235627295627063,681403903226492209,162990271846195,234390059833216,
235489571461107,100651756536542466,166357794641689,393737576539829553,681966853179913521,165052376242159,95989855770393,676617624689390879,388951298002728223,677180574642812191],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p64_0_2 : fcAllB [fba_p64_0_0,fba_p64_0_1] (pr P2 64) 64 12 fba_p64_0_2 = false := by decide +kernel
lemma fva_p64_0_2 : fcBV (pr P2 64) 64 12 fba_p64_0_2 := fcAllB_val (fcBc fva_p64_0_0 (fcBc fva_p64_0_1 (fcBn))) fka_p64_0_2
set_option maxHeartbeats 0 in
def fba_p64_0_3 : ℕ × List ℕ × List ℕ := (127,[234459584616286,235559096244177,234492602177519,233255651596108,234355163223999,235696535197446,165327287703299,94958811961091,165189848749827],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p64_0_3 : fcAllB [fba_p64_0_0,fba_p64_0_1,fba_p64_0_2] (pr P2 64) 64 12 fba_p64_0_3 = false := by decide +kernel
lemma fva_p64_0_3 : fcBV (pr P2 64) 64 12 fba_p64_0_3 := fcAllB_val (fcBc fva_p64_0_0 (fcBc fva_p64_0_1 (fcBc fva_p64_0_2 (fcBn)))) fka_p64_0_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p64_0 : fcChkB [fba_p64_0_0,fba_p64_0_1,fba_p64_0_2,fba_p64_0_3] [] (pr P2 64) 64 12 0 FF 1 = false := by decide +kernel
lemma chk_p64_0 : chk [] (pr P2 64) 64 12 0 FF 1 = false := (fcChkB_eq (fcBc fva_p64_0_0 (fcBc fva_p64_0_1 (fcBc fva_p64_0_2 (fcBc fva_p64_0_3 (fcBn))))) 0 FF 1).symm.trans fkr_p64_0
set_option maxHeartbeats 0 in
def fba_p64_1_0 : ℕ × List ℕ × List ℕ := (127,[236726253737978,236727092598705,236726824163134,235696585660385,235559096375249,234459584747358,236727059044258,236726790608687,104874842958017997,95583969434875211,100088668573873598,104593367712871681,100651619064165870,100651756536673538,166357811550173,166082900089038,
388319010097411533,166220372596957,166289377286162,166289645721733,388881960050832804,388600485074122033,676546087714239949,166082363217977,163883608397900,164983120025791,388037535120700673,166151636342809,374523437703706087,672042488086869391,667538888459498780],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p64_1_0 : fcAllB [] (pr P2 64) 64 12 fba_p64_1_0 = false := by decide +kernel
lemma fva_p64_1_0 : fcBV (pr P2 64) 64 12 fba_p64_1_0 := fcAllB_val (fcBn) fka_p64_1_0
set_option maxHeartbeats 0 in
def fba_p64_1_1 : ℕ × List ℕ × List ℕ := (127,[166151351129858,166151619565518,95989839124430,163952327874380,165051839502271,164089766827852,165189278455743,166288790083330,166357777995726,165017211328465,93721559521100,94821339584447,235523394459598,95921119647490,165052376373231],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_p64_1_1 : fcAllB [fba_p64_1_0] (pr P2 64) 64 12 fba_p64_1_1 = false := by decide +kernel
lemma fva_p64_1_1 : fcBV (pr P2 64) 64 12 fba_p64_1_1 := fcAllB_val (fcBc fva_p64_1_0 (fcBn)) fka_p64_1_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_p64_1 : fcChkB [fba_p64_1_0,fba_p64_1_1] [] (pr P2 64) 64 12 1 FF 1 = false := by decide +kernel
lemma chk_p64_1 : chk [] (pr P2 64) 64 12 1 FF 1 = false := (fcChkB_eq (fcBc fva_p64_1_0 (fcBc fva_p64_1_1 (fcBn))) 1 FF 1).symm.trans fkr_p64_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_2 : chk [] (pr P2 64) 64 12 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_3 : chk [] (pr P2 64) 64 12 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_4 : chk [] (pr P2 64) 64 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_5 : chk [] (pr P2 64) 64 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_6 : chk [] (pr P2 64) 64 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_7 : chk [] (pr P2 64) 64 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_8 : chk [] (pr P2 64) 64 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_9 : chk [] (pr P2 64) 64 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_10 : chk [] (pr P2 64) 64 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_11 : chk [] (pr P2 64) 64 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p64T_12 : chk [] (pr P2 64) 64 12 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p_64 : Imp [] 64 13 := by
  refine imp_of (E := []) (Q := pr P2 64) (Z := 64) (L := 13) (Or.inl rfl) (by decide +kernel) (by decide)
    (fun e he => P2ok e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ?_)
  interval_cases t
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p64_0⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chk_p64_1⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_2⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_3⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_4⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_5⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_6⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_7⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_8⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_9⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_10⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_11⟩
  · exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact p64T_12⟩
set_option maxHeartbeats 0 in
def fba_g64_0 : ℕ × List ℕ × List ℕ := (127,[165052393159227,675983137760828110,235489303165224,234389791537584,234528069351681,235627312544001,236727075830249,236726807394678,965344052954486546,970199496000755503,235489840036184,234459333097831,235558576290151,234390596843864,965343984235009810,235627832637929,
234528321010038,965343846225631081,686187877782214491,686187878050650062,970196129820137263,398523887306102601,109727126032439109,680276661947816018,680277761459443909,680275562436188398,675770863297190111,671267263669819500,666763664042448909,680274462924560418,685905234574399425,685905234842834745,
970199358561802133,965340547690747732,686470452018894753,686753026507233049,970196060026918784,965132809786316693,965129511251433344,969633110610368384,969636409145251733,393105287577556805,680769414955751990,686750759284594442,686469284039448466,964777597737326372,960273998109956012,398242274873661275,
398523749850372046,672394435692287916,965340685414913891,676266914840009303,671761116189383343,676264715816753703,672394435960723236,680771613979007501,680770514467379861,965343983949797240,667257516562012752,970199427549714223,680768315444124261,671762215701011072,676265815328381683,681332433913861957,
676336149712820768,398238908424607634,398520383401318154,681122392548006562,681121293036378671,680838649828563706,109729462477871622,974701927682234229,974699660459595622,974982303147317109,974981135167870822,965129511519868862,969633111147239222,393455997141866334,393737472118577105,667543389870446405,
398242274890438561,398523887289325315,393737609557530374,398523749867149081,965343914945107817,960274066829432748,964777666456803108,974981134630999862,960277365364316097,398523887322879762,974699659654289342,965340616410224468,964780964991686457,680136165514500858,94811287638465056,970055391526475726,
969773916549764955,672394400527243081,398238977144084315,398520452120795086,90308718534810166,676898000154613692,680206327563376694,675703827716069408,965343915230320504,685623759597688769,685623759866124089,100160481014274785,681053158530832609,680771614549432497,680770515037804606,99879005752351409,
95375337405504062,676899168385718252,680208527391938566,675702728204441788,666694429169637456,671198028797008047,675701628424378407,680208527123503266,680207427611875375,680487871544776773,680205228051748965,680207427075004565,680208526586632205,680488971324840053,671199128577071177,680490070836467944,
680208526855067857,680207427343439966,680206327831812346],[667543321136281081,372,681616108469564692,374,681615970997056773,374,681616177205818848,374,681616039733310795,374,672045821252023583,357,676548321367766303,357,100088668575970765,3428,
95583969436972378,3428,676832133108676016,374,383815445637182751,356,672328533481305405,373,676269045145875724,374,671765445518505364,373,969564872172057858,374,672046920763651421,373,
676550520391022032,374,667542221624653243,356,667541122113025352,340,681053020506764752,374,676265746610992626,356,955490023288026539,356,681051920995136861,373,955491122799654179,372,
676831995636168097,374,671762146983622015,340,672328396008797486,373,667543321136282361,371,384096989350147382,357,384096920613893611,357,379312945253004793,372,676550520391023312,371,
672046920763652701,371,955772598313235740,374,681403902440191330,374,969001921681765688,372,969000822170138048,356,955491123336525139,374,392823743598246500,320,950987488544110073,372,
393105218843392761,336,969001922218636648,374,393105218574957109,336,672328396008798766,372,676831995636169377,372,95583969436973661,2401,681051920995138141,369,681403901886543234,374,
667541122113026632,339,667542221624654523,355,681403903245497719,374,681053020506766032,369,379312945253006073,371,100088668575972048,2401,950987523709154690,374,100088668575972048,2403,
95583969436973599,2387,672045821252024863,355,95583969436973661,2403,95583969436973599,2385,685624858574533985,389,104874911696368968,3429,676548321367767583,353,100651619066264069,2405,
104593367714970361,2368,959991389263967693,2420,662754947728880975,323,964780965547423000,389,960277365920052640,389,100651756538771988,2405,685624859111404945,389,955487789636597082,2420,
685624859379840265,389,969283397195347249,374,667541190849279374,340,667542290360907014,356,676546087716336898,3412,960276162775562913,371,955772563148192302,371,950987488544111353,370,
384096920613894891,356,955491088171480413,373,681332296191785525,368,677111408760142367,352,388881994681104927,352,677111271321188895,352,388882132120058399,352,383815445637184031,355,
959994687798851024,374,960557637752273413,372,676759565576124959,352,104593367714968881,3429,95583969436973599,2384,662758246263764324,371,374523437705804537,2402,100088668575971871,2384,
667261845891134773,372,672042488088967841,2403,667538888461597230,2403,955772563148191022,373,681053089243018523,374,950987488544110073,371,374523437705804537,2401,681051989731390883,373,
960276162775561633,374,680769346238362933,372,667538888461595950,2404,672042488088966561,2405,374523437705803257,2403,672046920763651418,1396,955492222311282017,388,676550520391022029,1396,
676548321367766318,3444,969000822170138045,1413,969001921681765685,1413,672045821252023598,3444,681403902425502509,1534341,964780896274298168,391,681402733923874101,2437,960277296646927808,390,
676899134296503741,2437,685624858574534077,2404,969001922218636645,1413,681403902440191348,2437,685624859111404901,2422,686188977044272500,2422,964780965547423092,1398,960277365920052596,2422,
686190076555900276,1398,960277365920052596,2420,676902432831387069,1413,397960731447997797,2439,681406032458757429,1413,955491122799654197,2437,685624859111404989,1380,388672057216546237,1414,
955491122799654197,2435,685624859379840309,1396,686187809064826213,2422,685624859379840357,1398,955490023288026557,2437,955490023288026557,2435,388668758681662909,2438,393172358577468725,2438,
681403903245497716,1413,686187809333261669,1398,397958601697867124,2439,397959701209494900,1415,955491123336525157,2435,955491123336525157,2437,397960731716433253,1415,393175657112352053,1414,
685624858574533941,2420,955487789638685467,1464675,964780896811169229,391,960277297183798618,390,667541122113025308,2405,388037535122797873,3429,667542221624653084,1381,374523437705803036,3412,
955772598313235758,2436,960277297185887021,1534324,964780896813257517,5726597,960277297185887021,9920901,960277297185887021,1595764,955491088175657260,6280399203])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_0 : BinarySearch.fcAllB [] (pr G2 64) 64 13 1 fba_g64_0 = false := by decide +kernel
lemma fva_g64_0 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_0 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_g64_0
set_option maxHeartbeats 0 in
def fba_g64_1 : ℕ × List ℕ × List ℕ := (127,[104593367712880386,166082900097743,100088668573882303,166289645730438,166220372605662,163883608406605,374523437703714792,165189865667280,163952613096036,163952344660627,166151636351514,164021349349933,166220641040962,162852833032756,164983656905456,672042488086878096,
166151904787065,166151367916105,163883876842014,161684316715604,166083436968614,166082631662083,676550520388933585,393105218841303034,393668168794724305,393668306535667633,681053020504676305,233360089905478,393386693549578133,388881994679015200,667542221622564796,393668169063159714,
677111408758052640,236726270523718,965343846494066482,969564871633098702,236863977912809,681969120385914627,105506100608194336,676548321365677856,974419353713989423,383815445635094304,681897445971678982,950987488542021626,681616108467476245,104943150654773024,964780896272209721,969564872169969411,
681403902438102883,110011898990384990,964494988889249786,681897445434808273,965057938842670895,681965753131554589,393386831256967006,379309646179161936,955492222309193570,671765445516416917,109727057296185142,681897582873761745,965340685398136605,969776116109891534,379312945250916346,384095820563306313,
676831995634079650,166220087392585,104874911694280473,676265746608904179,685906403073939406,681401599781984250,969565009072052174,681966851837876099,969563909560424283,393668444243056405,960276162773473186,950987523707066243,681897652180441057,681616177203730401,681402733921785636,676899134294415276,
110293511724816353,393668444259833825,672325096934954880,100719926240827279,109730355025762102,681614939397511061,384095889014347648,681897514707933004,685906333549156194,110293511691261772,681120124805273594,676832133106587569,110292206272861965,681615077406889790,681897651895228337,672325234642343753,
965270316922394397,393737575751440227,110292343711815586,393738607063684969,110293374252308252,681968982946961257,393668306250454812,100719926224049993,681403903243409272,965413149817919282,393737576556746616,969001921679677241,677041109270222828,388600588975429431,681897651861673890,100720956747765632,
676902432829298625,969283397193258802,393735308528801620,388672057214457793,667538991538722640,95933683120428880,662754947726792528,681684174270322526,662758246261675877,681684242989799215,672325234659121039,384095889299560335,667261845889046326,686470452002117467],[959994687798851021,1396,964780896811169229,389,681403902423414044,374,955487789636597020,2403,959991389263967516,1381,681403903230808877,1602949])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_1 : BinarySearch.fcAllB [fba_g64_0] (pr G2 64) 64 13 1 fba_g64_1 = false := by decide +kernel
lemma fva_g64_1 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_1 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBn)) fka_g64_1
set_option maxHeartbeats 0 in
def fba_g64_2 : ℕ × List ℕ × List ℕ := (127,[388600485074130738,388881960050841509,388037535120709378,95583969434883916,166289377294867,166082363226682,164983120034496,165121129413124,165052124723927,165051856288267,166358381984485,165120860977824,166220909476533,162783828343333,164982851599095,163883339971204,
667538888459507485,166152173222636,164983388469905,676546087714248654,162784096778985,166083168533043,667543321134192634,672046920761562974,681332433897084922,100651619064174575,393386831558956862,393386693818013534,681051920993048414,393668168526288653,677111271319099168,667541122110936905,
393386694086448943,388882132117968672,392823744133027834,392823743596156773,969563772121470811,236795258435958,393738744502638339,105507199851386656,672045821249935136,388319045262464800,974420452957181743,109727126015662074,681615970994968326,681897583444186901,676759565574035232,960277296644839361,
681262065421342714,393105218572867382,110293374235531217,393735377248278301,965339413819381666,681614870946469726,109445651038951418,955491123334436692,393668306233677777,681969051666437938,676269045143787277,681615008385423198,393738675783161650,965343983933019954,969775016329828187,388600519702304700,
965409851283035933,681403901884454787,672328396006709039,671762146981533568,685906402805503835,110009700504000350,110292274992338897,393737575197792131,955772598311147293,110293511708038933,970058690866665266,955772563146102575,393668444209501958,110293511674484486,681332296189695798,388600520239175660,
384096920611805164,105223526136633095,955490023285938092,676828696562325491,955491122797565732,681897513885849357,388600588153346035,393734209017173891,681616039731222348,681964584900450179,393668444226279244,110009769257031486,672328533479216958,110009631784523669,110292343745370033,681332364909172534,
676828834269714364,681966852391524195,969001922216548201,110009769223477039,105224694367737655,110011899007162276,393105287292344118,393386831273744292,677041109286999863,105223526119856060,681966853196830584,105224694350960620,384096989348058935,969000822168049601,681615077373335343,105225655886764019,
681406032456668985,681965684412077908,388668758679574444,393172358575380260,109444482807846757,393175657110263609,667542290358818567,667541190847190927,681966748758661073,681966817478137762,676828834286491399,388600588438558471,686753026490456014,681049790420834149],[388319010099508482,3429,955491088171480410,1396,960277297183798618,389,104874842960114946,3429,676617624693707565,1535348,955487789636597020,2405,955491088173568816,1464675])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_2 : BinarySearch.fcAllB [fba_g64_0] (pr G2 64) 64 13 1 fba_g64_2 = false := by decide +kernel
lemma fva_g64_2 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_2 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBn)) fka_g64_2
set_option maxHeartbeats 0 in
def fba_g64_3 : ℕ × List ℕ × List ℕ := (127,[166151351138563,95921119656195,232156140108265,96058558609715,236726253746432,235660833421734,233324371212574,165189278464448,104874842958026702,163952327883085,166495753828774,236794973223263,236795275213119,164020778924420,96058592164162,235695763585281,
166495787383221,236795828861410,235627815860643,235695193160024,235626742118845,164158754748702,165258299931040,233359536257354,236726790617392,234528337787199,94890059069841,92621779466729,236657265834342,235557754206504,233358730950993,166426816248083,
236794704787862,236658071140703,236657802705152,236863961135523,166495770606060,165258585143760,94821339593152,236795778529543,236657819482438,165120575764747,236863709477149,234459316320545,234390865279382,235626473683444,165327254288880,236658087917989,
234528035797485,236795812083990,236588814793062,236589083228471,960557637750183686,235695746808120,235559113160989,236864246348109,233359553034640,235695478372711,233359821469960,232191573588264,93790295783780,94890075847127,233291085216244,95989855910170,
234390059972993,232191036717393,235558307854600,236589620099342,959991389261879228,234527247268240,165052376381936,166220355827994,162921267296549,965344052920932099,964780896809080782,397958601679001435,397959701190629326,393737575734662941],[676617624691619103,357,969565009644565777,374,969634174959039790,1398,955491088171480369,2403])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_3 : BinarySearch.fcAllB [fba_g64_0,fba_g64_1,fba_g64_2] (pr G2 64) 64 13 1 fba_g64_3 = false := by decide +kernel
lemma fva_g64_3 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_3 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBn)))) fka_g64_3
set_option maxHeartbeats 0 in
def fba_g64_4 : ℕ × List ℕ × List ℕ := (127,[162990255208937,166151082703162,166288790092035,96127278086566,388319010097420238,235592113944883,235454674991363,234423882840465,164089766836557,165051839510976,166426765916467,236863692700114,166357811558878,236863994689970,165120290552311,96127311641013,
166426799470914,236864279902690,234528304232752,233360073128192,234527230490954,165258266376593,164158788303149,233359804692925,236727059052963,235627849415090,93790279006494,235695461595425,166289092082142,162852547819813,234458242578864,166495804160390,
236863424264462,236658339576274,236725985311031,236795241658672,166426782693753,96127345195493,93721559529805,232191842023782,236864229570823,164021064137107,165121112635707,235558559512865,235490376907022,236794990000549,234526962055553,94958778546672,
236658356353309,235627278989805,236864263125270,235696568891670,233290279909713,235696552114509,234459601533349,166357794781466,236795795306829,166288806869321,233291353651511,166219802179898,161821755668820,232191305152944,233290816780673,235627295766840,
234528052574520,235489571600884,234458796226960,236589351664022,955487789634508617,970058759586141955,235626758895880,960554339215300588,965343846762501891,162990271985972,686190076537034702,686188977025406811,960277297181710171,681403902421325597,681966852374746909],[681403903228720433,374,969633075447412014,2422,676617624691619118,3444])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_4 : BinarySearch.fcAllB [fba_g64_0,fba_g64_1,fba_g64_2] (pr G2 64) 64 13 1 fba_g64_4 = false := by decide +kernel
lemma fva_g64_4 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_4 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBn)))) fka_g64_4
set_option maxHeartbeats 0 in
def fba_g64_5 : ℕ × List ℕ × List ℕ := (127,[161718676453821,95989839133135,166151619574223,234458779449674,235558291077565,235695730031085,166357778004431,955491088169391966,959994687796762577,100651756536682243,681966853180053298,393737576539969330,681969120419469074,393738744536192786,969565009642477330,681403903226631986,
677180574642951968,388951298002868000,965413218537395971],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_5 : BinarySearch.fcAllB [fba_g64_0,fba_g64_1,fba_g64_2,fba_g64_3,fba_g64_4] (pr G2 64) 64 13 1 fba_g64_5 = false := by decide +kernel
lemma fva_g64_5 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_5 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBc fva_g64_3 (BinarySearch.fcBc fva_g64_4 (BinarySearch.fcBn)))))) fka_g64_5
set_option maxHeartbeats 0 in
def fba_g64_6 : ℕ × List ℕ × List ℕ := (127,[165017211337170,235523394468303,233255651735885,234355163363776,234492602317296,235696535337223,236726824171839,236727092607410,235696585669090,234459584756063,235559096383954,165327287843076,94958812100868,165189848889604],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_g64_6 : BinarySearch.fcAllB [fba_g64_0,fba_g64_1,fba_g64_2,fba_g64_3,fba_g64_4,fba_g64_5] (pr G2 64) 64 13 1 fba_g64_6 = false := by decide +kernel
lemma fva_g64_6 : BinarySearch.fcBV (pr G2 64) 64 13 1 fba_g64_6 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBc fva_g64_3 (BinarySearch.fcBc fva_g64_4 (BinarySearch.fcBc fva_g64_5 (BinarySearch.fcBn))))))) fka_g64_6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g64_0 : BinarySearch.fcChkB [fba_g64_0,fba_g64_1,fba_g64_2,fba_g64_3,fba_g64_4,fba_g64_5,fba_g64_6] [] (pr G2 64) 64 13 1 (0x7fffffffffff) 0 = false := by decide +kernel
lemma chk_g64_0 : BinarySearch.chk [] (pr G2 64) 64 13 1 (0x7fffffffffff) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBc fva_g64_3 (BinarySearch.fcBc fva_g64_4 (BinarySearch.fcBc fva_g64_5 (BinarySearch.fcBc fva_g64_6 (BinarySearch.fcBn)))))))) (0x7fffffffffff) 0).symm.trans fkr_g64_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g64_1 : BinarySearch.fcChkB [fba_g64_0,fba_g64_1,fba_g64_2,fba_g64_3,fba_g64_4,fba_g64_5,fba_g64_6] [] (pr G2 64) 64 13 1 (0x7fffffffffffffff800000000000) 0 = false := by decide +kernel
lemma chk_g64_1 : BinarySearch.chk [] (pr G2 64) 64 13 1 (0x7fffffffffffffff800000000000) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBc fva_g64_3 (BinarySearch.fcBc fva_g64_4 (BinarySearch.fcBc fva_g64_5 (BinarySearch.fcBc fva_g64_6 (BinarySearch.fcBn)))))))) (0x7fffffffffffffff800000000000) 0).symm.trans fkr_g64_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_g64_2 : BinarySearch.fcChkB [fba_g64_0,fba_g64_1,fba_g64_2,fba_g64_3,fba_g64_4,fba_g64_5,fba_g64_6] [] (pr G2 64) 64 13 1 (0x3fffffffffffffffffffffffff8000000000000000000000000000) 1 = false := by decide +kernel
lemma chk_g64_2 : BinarySearch.chk [] (pr G2 64) 64 13 1 (0x3fffffffffffffffffffffffff8000000000000000000000000000) 1 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_g64_0 (BinarySearch.fcBc fva_g64_1 (BinarySearch.fcBc fva_g64_2 (BinarySearch.fcBc fva_g64_3 (BinarySearch.fcBc fva_g64_4 (BinarySearch.fcBc fva_g64_5 (BinarySearch.fcBc fva_g64_6 (BinarySearch.fcBn)))))))) (0x3fffffffffffffffffffffffff8000000000000000000000000000) 1).symm.trans fkr_g64_2
def shards_g64 : List (ℕ × ℕ) := [(0x7fffffffffff,0),(0x7fffffffffffffff800000000000,0),(0x3fffffffffffffffffffffffff8000000000000000000000000000,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shardsCover_g64 : mFull shards_g64 = true := by decide +kernel
lemma chkAll_g64 : ∀ p ∈ shards_g64, BinarySearch.chk [] (pr G2 64) 64 13 1 p.1 p.2 = false := by
  intro p hp
  simp only [shards_g64, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact chk_g64_0
  · exact chk_g64_1
  · exact chk_g64_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strong64 (floor : Imp [] 64 13) (prior : ∀ e ∈ G2, HasGrade 1 e) : HasGrade 1 (64,13) := by
  apply gradeFromFloor (t := 1) floor (by decide +kernel) (by decide +kernel)
  intro S sw hl
  refine BinarySearch.rejectMinimum (Q := pr G2 64) (L := 14) (by decide +kernel) (by decide) (by decide) ?_ sw hl floor shards_g64 shardsCover_g64 chkAll_g64
  intro e he
  exact prior e (List.mem_of_mem_filter he)
lemma g_64 : HasGrade 1 (64,13) := strong64 p_64 G2ok
def P1 : List (ℕ × ℕ) := [(1,12),(2,12),(4,12),(8,12),(16,13),(32,12),(64,13),(128,12)] ++ P2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma P1ok : ∀ e ∈ P1, Imp [] e.1 e.2 := consFloor p_1 (consFloor p_2 (consFloor p_4 (consFloor p_8 (consFloor p_16 (consFloor p_32 (consFloor p_64 (consFloor p_128 (P2ok))))))))
def G1 : List (ℕ × ℕ) := [(1,12),(2,12),(4,12),(8,12),(16,13),(32,12),(64,13),(128,12)] ++ G2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma G1ok : ∀ e ∈ G1, HasGrade 1 e := consGrade g_1 (consGrade g_2 (consGrade g_4 (consGrade g_8 (consGrade g_16 (consGrade g_32 (consGrade g_64 (consGrade g_128 (G2ok))))))))

set_option maxHeartbeats 0 in
def fba_bf0_0 : ℕ × List ℕ × List ℕ := (255,[677111271587412431,686119570622216630,681615970994846177,393669269379971485,398172869007341981,686401045598927286,681897445971556833,681897652180318581,393668444259711349,398173143398709578,686401251807689034,681616177203607925,686119776830978378,960559872475232723,167526898179181,681615077373212972,
686118677000583425,398524987606137229,403028586428201339,403027487990315405,398523887289203110,974912003105716691,167389425671347,167389157235803,166289645608070,691257931787762018,691257932106529057,166358381862065,167182948474055,167457893489798,979768614685079890,164983656782864,
166083436846322,384096920611682767,965343846762379686,965344946274007419,166082899975229,686753096283552098,166289377172727,167388888800460,691256695642487138,979488239219997010,974985739104254290,167182411602962,164983388347616,970130296074762529,974632796190505249,974845002689640845,
686613595477342621,974843902909577613,114797180558080413,965344947079313805,974982372923636050,388600520239053263,979485972282571090,965344052920809894,965345152432437627,686470521795213779,690974121154148819,974704195944937810,979206696060680530,403306695224293843,110009769223354668,691537071107570131,
114513369119160577,403028587233507725,398523888362944909,403307863455398285,402744844782500219,398241244886694310,691538239338674573,685907535871442102,681403936244071649,979767446990846290,388882201105758671,970058759586019750,970059859366082939,970199497342810450,970200596586002770,979488170768955730,
163883876719702,974985670653213010,165189865544863,686402489026706481,681685446922697126,676617693408885967,681685447191132539,685624892663626753,686190179079257245,685627091686882531,681121293036256300,974913102936111393,684642033421352075,680138433793981622,684713226530814483],[393388000614111137,390,965345153290164000,408,964777563381642705,1603972,393669544327075675,391,393388000614112417,389,960273963752183674,2437,960273963752183717,2421,960273963752183758,357,
104874842959992786,3445,109379542098991058,3445,686050508087056338,1414,114234093167794130,1414,384095785937099957,2420,672325062577183968,2404,384095785937100000,2404,672325062577183925,2420,
685839194890786770,1413,681336694775044050,1397,964778662893270368,1603972,672325062577182604,3446,960273963752183717,2422,681332261831923637,1397,969563737495263157,390,960273963752183674,2438,
676828662204553184,1381,969281163006924666,2405,965060137867892704,374,964777563379554213,2405,969848752061896658,406,383814310960387962,3445,383814310960388005,3429,393386900246845394,2438,
965060137867892620,2437,398454549339266274,384,965060137867892620,2438,969563737495263116,2422,686683825979350242,384,379309611821389778,3446,676828662204553100,3445,681332261831923596,3429,
383814310960387937,3446,686190110361868172,1414,965063472104691553,408,964777563381642705,1530244,964777563381642705,1595780,100651619066140556,3446,681336694775044050,1413,685839194890786770,1397,
685836995867531218,2421,686190110361868172,1398,681333396240160722,2437,379309611821389733,3429,955771463636440997,2422,676829796612790181,2421,676829796612790138,2437,379309611821389690,3445,
965340513332975500,2438,681333396240160722,2439,685836995867531218,1415,955771463636440954,2438,681970219899508561,1432,681969120387880785,2456,393456065863309266,2438,969917917678360530,406,
969564872171935653,374,969282262518552442,1413,681336694775043937,1414,676833095147673441,1415,974068471799306106,374,690694844665911121,2422,114515636914312992,1415,685839194890786657,1398,
964778662891181989,1381,676831995636045665,2439,676833095147673482,390,393737609559496588,2439,384095785937098636,3446,970199461374547852,407,676831995636045749,374,964778662891181989,1397,
397609919056009170,1414,685836995867531008,389,393106319428638674,1414,681333396240160555,373,964778662891181921,2438,969282262518552442,1381,969282262518552417,2422,686332051833575200,1415,
690976388630534028,391,690976388630534028,407,955771463636440954,2437,379309611821389774,2388,955771463636440997,2421,955771463636441038,356,398242344668846034,407,398243443912038354,407,
965413218539362129,2456,685908566665680721,3429,970130296026519436,407,393668444211468172,2439,671199162670340731,3377,95865444681996197,3429,95865444681996154,3445,109379542098990945,3446,
676829796612790181,2422,676829796612790138,2438,672328396008675237,1398,690976388680865568,391,690976388680865568,407,104874842959992673,3446,672329495520302970,1414,965414318050989905,1432,
969564872174024016,1673621,378537960817121978,2432,374033192958646882,2416,374033192958646839,2432,99316056035777164,2432,100160481016240672,2435,94812387420494546,2432,99316055767341665,2432,
94811287908866725,2416,94811287908866682,2432])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_0 : fcAllB [] (pr P1 0) 0 14 fba_bf0_0 = false := by decide +kernel
lemma fva_bf0_0 : fcBV (pr P1 0) 0 14 fba_bf0_0 := fcAllB_val (fcBn) fka_bf0_0
set_option maxHeartbeats 0 in
def fba_bf0_1 : ℕ × List ℕ × List ℕ := (255,[383814310958299615,379309611819301205,681614836318173638,677111236690803185,110223967832340771,109379542096902417,104874842957904188,686470417105385867,681966817478015414,685836995865442561,681333396238072108,384095785935010063,960273963750095311,685839194888698339,681336694772955619,676833095145585035,
676831995633957302,672325062575094031,388951366722222543,672328396006586668,672329495518214401,686683619818830307,398454343178746339,397891394030631187,393387794403260691,969848545901378003,974351046017120723,974630321970575739,970126722343205286,393386694086326572,397891393225324801,955771463634352591,
686187842617047297,681684242989676844,671199162668252175,95865444679907669,235695729908688,686050508084967907,114234093165705699,393668169063037366,398172868202035595,690976388091574739,397609919053920739,393106319426550243,110293511724693877,114798210863692106,681614871214782764,686118470842153217,
974632520993831266,397891599383755009,969848752059808211,974351252175550931,393386900244756780,970130020878088546,402747043537320403,398242344666757587,676829796610701775,965060137865804257,969563737493174710,974068471797217659,969564872169847206,676899168385595855,398454549337176547,686683825977260515,
235696535215074,235696803650487,974912896727349645,115079617339029987,115078518095837667,686753095478245798,691256695105616251,969844112958257590,965340513330887137,969915718653016486,974419318280386939,100651619064051983,686471620501535142,690975220128905595,969846553036552614,974350152663923067,
398243443909949907,402745944294128083,974911796947286483,686332051781155091,114515636861892883,970196094118099366,974699693745469819,965063472102603106,167183216909348,974630528129005947,970126928501635494,166083168410728,167182680038461,167458161925342,686190110359779603,686471654055967133,
398173143348378038,393668444209379809,974981168722180563,398242308696406454,393737609557408225,686613595544451420,114797180625189212,677041109270100431,105507268570741199,974843902959909153,681897651861551542,686401251488921995,974845002739972385,974982268233808226,398521620351777190,403025220247583099,
974560159653263739,970056560025893286,398524918886660450,403027419270838626,974701892768725346,114795943607499147,970199392652982626,110292343711693238,970057659805956518,974561259433326971,393669544324987228,974842803129514381,398173143952357724,686470521258342822,690974120885713275,398242344129886630,
402747043268884859,403307863505729825,691538239389006113,686751996235053478,691255595862423931,393738744502516134,393739844014143867,965345153288075553,974982336953285005,686755363489413517,691257863605156237,974841634629974483,965414318048901499,965413218537273766,974632727152261474,970130227036518754,
105224694350838223,110293511674362337,114798210813360566,686755363539745057,691257863655487777,974913102617344354,974844933970164066,974843834190100834,691257932056197517,684784969664527571,689287469780270291,690694913114864851,970199461372459405,974701961488202125,974563458993453523,970130296024430989,
974562359213390291,974632796140173709,686332051831486882,403028587283839265,114515636912224674,398523888413276449,974842734410037602],[690694844665911250,408,685908566665680866,391,685908566665680850,1413,685908566665680850,1397,964777563379554091,373,690694844934346593,408,969281163006924544,389,969281163006924754,1415,
964777563379554258,2439,964777563379554258,2437,969281163006924754,2421,690694844665911250,390,690694844665911250,406,964778662891181921,2436,964777563379554258,2436,964778662891181921,2439,
969282262518552417,1415])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_1 : fcAllB [fba_bf0_0] (pr P1 0) 0 14 fba_bf0_1 = false := by decide +kernel
lemma fva_bf0_1 : fcBV (pr P1 0) 0 14 fba_bf0_1 := fcAllB_val (fcBc fva_bf0_0 (fcBn)) fka_bf0_1
set_option maxHeartbeats 0 in
def fba_bf0_2 : ℕ × List ℕ × List ℕ := (255,[110224174041102770,234423882718176,234492602194704,238032779320114,235660833299442,236760344927175,681332261829835068,676828662202464615,238032192117732,235628084173708,235627815738295,236727595801572,237826838993892,233324371090262,94958828755871,970126687446595997,
964778662889093558,969282262516464011,167595265334215,166495753706482,237895340366667,236795828738934,236865085086514,237964328278834,97089619073810,95989839010621,964777563377465644,969281163004836097,235627278867408,97295777504036,970125587934968083,167664253246244,
165327254166288,237895290035127,236795778407394,238032796097373,167526881401822,236795241536301,237894753164034,236796315278100,237895558470420,237963472640908,236863961013175,235696853982027,235696585546614,397891600239393186,393388000612022690,237964277947294,
236865034754974,690694844663822803,94890058947552,234528304110381,167457289509650,166357777881917,93790278884182,234528572545794,94958778424080,166495804038022,167595315665755,237963741076407,236864229448674,238032510884771,690694844932258146,96058558487400,
97158338550589,167595617655661,97227058027463,96127277964274,969917917676272083,974420417792014803,234528035675088,403309993222306146,691539269862390114,403309992953870803,691539269593954771,397960765000218881,393456065861220652,686473819524790739,690976319640533459,114516666848737537,
110011967709739308,398523714953640419,686752991593724387],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_2 : fcAllB [fba_bf0_0,fba_bf0_1] (pr P1 0) 0 14 fba_bf0_2 = false := by decide +kernel
lemma fva_bf0_2 : fcBV (pr P1 0) 0 14 fba_bf0_2 := fcAllB_val (fcBc fva_bf0_0 (fcBc fva_bf0_1 (fcBn))) fka_bf0_2
set_option maxHeartbeats 0 in
def fba_bf0_3 : ℕ × List ℕ × List ℕ := (255,[163917699586848,162818187959185,235523394345789,236622905973522,236829064403748,235592113822568,236691625450301,167664303578035,97295827835827,236727058930615,237826570558348,167458145147827,236726790495021,237826302122754,238032460552980,238032728988574,
96058608819191,97158388882380,237895608802211,236796365609891,166426765794152,167526277421885],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf0_3 : fcAllB [fba_bf0_0,fba_bf0_1,fba_bf0_2] (pr P1 0) 0 14 fba_bf0_3 = false := by decide +kernel
lemma fva_bf0_3 : fcBV (pr P1 0) 0 14 fba_bf0_3 := fcAllB_val (fcBc fva_bf0_0 (fcBc fva_bf0_1 (fcBc fva_bf0_2 (fcBn)))) fka_bf0_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_bf0 : fcChkB [fba_bf0_0,fba_bf0_1,fba_bf0_2,fba_bf0_3] [] (pr P1 0) 0 14 0 FF 1 = false := by decide +kernel
lemma chk_bf0 : chk [] (pr P1 0) 0 14 0 FF 1 = false := (fcChkB_eq (fcBc fva_bf0_0 (fcBc fva_bf0_1 (fcBc fva_bf0_2 (fcBc fva_bf0_3 (fcBn))))) 0 FF 1).symm.trans fkr_bf0
set_option maxHeartbeats 0 in
def fba_bf1_0 : ℕ × List ℕ × List ℕ := (255,[167595315796827,166495804169094,237963791539019,236864279911286,167526327884748,166426816257015,235696535346146,235696803781559,237895340497739,236795828870006,237964278078366,236865034886046,676828662202595687,681332261829966140,383814310958430687,104874842958035260,
109379542097033489,681614836318304710,677111236690934257,379309611819432277,238032779451186,672325062575225103,110223967832471843,393388000612153762,397891600239524258,167389425802419,100651619064183055,398454549337307619,686683825977391587,115078518095968739,115079617339161059,114234093165836771,
686050508085098979,167526898310253,166289645739142,960273963750226383,167389157366875,384095785935141135,95865444680038741,681333396238203180,685836995865573633,964777563377596716,969281163004967169,969844112958388662,965340513331018209,969563737493305782,685839194888829411,965060137865935329,
681336694773086691,164983388478688,166082900106301,167182411734034,167457893620870,166358381993137,167388888931532,166289377303799,164983656913936,166083436977394,167182948605127,686683619818961379,398454343178877411,955771463634483663,397609919054051811,163883876850774,
677111271587543503,165189865675935,393106319426681315,393737609557539297,114516666848868609,110011967709870380,398242308696537526,970125587935099155,676833095145716107,393386900244887852,676831995634088374,397891599383886081,393668169063168438,393456065861351724,388951366722353615,676899168385726927,
397960765000349953,672329495518345473,398172868202166667,114515636912355746,686332051831617954,672328396006717740,397891394030762259,393387794403391763,681614871214913836,681969120385923494,686118470842284289,681970219897551227,105507268570872271,965345152432568699,965344052920940966,393669544325118300,
398173143952488796,686401045599058358,393668444209510881,398173143348509110,686613595544582492,114797180625320284,681897445971687905,684713226530945555],[965345153290295072,408,964778662893401440,1603972])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_0 : fcAllB [] (pr P1 0) 0 14 fba_bf1_0 = false := by decide +kernel
lemma fva_bf1_0 : fcBV (pr P1 0) 0 14 fba_bf1_0 := fcAllB_val (fcBn) fka_bf1_0
set_option maxHeartbeats 0 in
def fba_bf1_1 : ℕ × List ℕ × List ℕ := (255,[165052376390416,238032796228445,235660833430514,236760345058247,234423882849248,165258585152415,234492602325776,233324371221334,235592113953640,236691625581373,93790279015254,165258266385376,235696585677686,97227058158535,235696854113099,96127278095346,
234528035806160,97158338681661,236795778538466,235627278998480,237895290166199,96058558618472,164158754757462,238032460684052,94958778555152,237894753295106,236795241667373,94890059078624,96127345204145,97227125267334,236863961144247,237963472771980,
167595265465287,166495753837554,167526881532894,235695730039760,237964345187165,236865101994845,167251936516900,237963741207479,236864229579746,167595617786733,237895558601492,236796315409172,167526277552957,166426765925224,235627815869367,235628084304780,
236726790626093,237826302253826,95989839141693,97089619204882,163952596327254,234528304241453,238032192248804,234528572676866,97295777635108,166151619582781,167251131210514,167664253377316,162818188090257,236727595932644,237826839124964,969282262516595083,
964778662889224630,970126687446727069,167183217040420,166083168541800,167182680169533,167458162056414],[685908566665811938,391,690694844934477665,408])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_1 : fcAllB [fba_bf1_0] (pr P1 0) 0 14 fba_bf1_1 = false := by decide +kernel
lemma fva_bf1_1 : fcBV (pr P1 0) 0 14 fba_bf1_1 := fcAllB_val (fcBc fva_bf1_0 (fcBn)) fka_bf1_1
set_option maxHeartbeats 0 in
def fba_bf1_2 : ℕ × List ℕ × List ℕ := (255,[236727059061687,237826570689420,238032729119646,110224174041233842,163917699717920,685908566663723491,686752991593855459,398523714953771491],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_bf1_2 : fcAllB [fba_bf1_0,fba_bf1_1] (pr P1 0) 0 14 fba_bf1_2 = false := by decide +kernel
lemma fva_bf1_2 : fcBV (pr P1 0) 0 14 fba_bf1_2 := fcAllB_val (fcBc fva_bf1_0 (fcBc fva_bf1_1 (fcBn))) fka_bf1_2
set_option maxHeartbeats 0 in
def fba_bf1_3 : ℕ × List ℕ × List ℕ := (255,[235523394476861,236622906104594,236829064534820,167664303709107,97295827966899,167458145278899],[])
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
def fba_si_0 : ℕ × List ℕ × List ℕ := (255,[671268363181464579,675773062320463032,684713226530954260,685557857669848227,685839401651248221,684713226262519012,677111271587552208,680208527391956194,684713226799389854,684712127019326647,680207427611892781,684711027239263234,681053158530849910,685556758158220363,685557857938283570,680208527123520695,
684712126750891148,675703827984522448,680557037412916453,671549838158175235,685060637040286906,686402489026846258,979768614685219667,690412202043350151,685908602684415206,677742736033684529,681897652180458358,686401251807828811,686119776831118155,398173143398849355,681616177203747702,393668444259851126,
681615077373352749,686118677000723202,398523887289342887,979488239220136787,974985739104394067,403028586428341116,384096920611822544,965343846762519463,965344946274147196,691257931787901795,403027487990455182,691257932106668834,398524987606277006,965345152432577404,965344052920949671,970200596586142547,
685063935575170252,970199497342950227,691256695642626915,686753096283691875,974632796190645026,970130296074902306,686613595477482398,113951518677507724,685839401047269092,113952618189135588,974843902909717390,970059859366222716,685769033108397796,114797180558220190,970058759586159527,686402488976514718,
974845002689780622,109447918781701815,974982372923775827,979485972282710867,681264333700964023,685767933328334476,671265513034456083,388600520239193040,676054537297173688,979767446990986067,979206696060820307,974704195945077587,681334701908270775,685838301535641228,114515705581510302,690974121154288596,
686470521795353556,686332120500772510,113672310956990027,109167611817991798,685558064096714290,681055563980971570,684642033421491852,114513369119300354,110009769223494445,108323117849615917,112827816988614146,680138433794121399,398523888363084686,403028587233647502,398241244886834087,686050576854916771,
402744844782639996,114234161935654563,388882201105898448,112828022878609124,108324423251238628,686049477074853451,681545877447482998,681685447191272316,974913102936251170,112827817525485284,684643133201555172,681545877397151458,686049477024521911,681685446922836903,103820754904391308,103819655392763575,
681263233920900653,114234161885322772,686050576804584980,685766833548271106,103818487161659088],[383814310960529035,2419,383814310960529078,2403,677111236693032605,2421,393388000614250914,390,686050508087197411,384,384095785937239734,2420,672325062577323702,2420,672325062577323745,2404,
384095785937239777,2404,676831995636186806,372,393669544327215452,391,676833095147814539,388,686050508087196115,1414,114234093167933907,1414,109379542099130835,3445,104874842960132563,3445,
383814310960527714,3446,960273963752323451,2437,104874842960133859,2420,393106319428779747,388,681336694775185123,388,960273963752323494,2421,379309611821530668,2403,960273963752323535,357,
379309611821530625,2419,676828662204694035,2420,681333396240301612,369,393669269382200989,390,685836995867672065,385,690694844666052307,400,681336694775183827,1397,690694844666052307,384,
685839194890926547,1413,393387794405490195,389,969282262518692194,2422,964778662891321698,2438,100651619066281697,2405,100651619066281654,2421,965063472104831330,408,969848752062036435,406,
965060137868032481,374,379309611821529555,3446,960273963752323494,2422,960273963752323451,2438,393386900246985171,2438,969563737495402934,390,681332261832063414,1397,676828662204692961,1381,
969563737495402893,2422,681333396240301779,2433,965060137868032397,2438,965060137868032397,2437,964778662891322978,2435,964777563379695315,2435,960273963752324815,352,685836995867672275,2417,
383814310960527739,3445,383814310960527782,3429,685836995867670785,389,681333396240300332,373,374033192958786659,2416,374033192958786616,2432,378537960817261755,2432,676828662204692877,3445,
681332261832063373,3429,675771962810923619,2416,675771962810923576,2432,680276661949921979,2432,95865444682137132,2404,95865444682137089,2420,383041629164108874,2432,964777563381782482,1530244,
95865444682135931,3445,374032093447158908,2400,681333396240300499,2439,379309611821529510,3429,955771463636580774,2422,681333396240300499,2437,681336694775183827,1413,685836995867670995,2421,
969564872174163793,1673621,955771463636580731,2438,686190110362007949,1398,685836995867670995,1415,379309611821529467,3445,686190110362007949,1414,964777563381782482,1595780,685839194890926547,1397,
95865444682135974,3429,671199162670480508,3377,964778662891321766,1397,676831995636185526,374,676833095147813259,390,676829796612929958,2421,676829796612929915,2437,965340513333115277,2438,
969282262518692219,1413,969917917678500307,406,393456065863449043,2438,671199162670480526,3425,671199162670480483,3441,104874842960132450,3446,685839194890926434,1398,676831995636185442,2439,
114515636914452769,1415,393737609559636365,2439,676833095147813218,1415,397609919056148947,1414,681122392550112354,2435,686332051833714977,1415,393106319428778451,1414,681121293038484691,2435,
109379542099130722,3446,681336694775183714,1414,970199461374687629,407,379309611821529551,2388,960559872477460947,408,681336694775183843,391,672329495520442747,1414,374034292470414480,2432,
685839194890926563,391,672328396008815014,1398,690976388630673805,391,95865444682136019,3446,690976388630673805,407,955771463636580815,356,955771463636580774,2421,955771463636580731,2437,
398242344668985811,407,393668444211607949,2439,676829796612929915,2438,676829796612929958,2422,681333396240300370,3462,374032093447158996,2416,374032093447158953,2432,398243443912178131,407,
685836995867670866,3446,964777563379693906,3462,969281163007064402,3446,690976388681005345,391,690976388681005345,407,970130296026659213,407,965344947081542029,408,378536861305633934,2416,
378536861305633891,2432,964778662895498576,6565550468,974068471801534289,5796214,969564872174163793,9990518,964777563383870800,6569744772,969564872174163793,1534357,99316056035916941,2432,393386900249074898,1595776,
969848752064126162,1593728,94812387420634323,2432,100160481016380449,2435,94811287909006502,2416,94811287909006459,2432,99316055767481442,2432])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_0 : BinarySearch.fcAllB [] (pr G1 0) 0 15 1 fba_si_0 = false := by decide +kernel
lemma fva_si_0 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_0 := BinarySearch.fcAllB_val (BinarySearch.fcBn) fka_si_0
set_option maxHeartbeats 0 in
def fba_si_1 : ℕ × List ℕ × List ℕ := (255,[167389425811124,167526898318958,675771962808835213,680275562436205797,680276661947833365,167458162065119,684781361086831732,166083168550505,167388888940237,167457893629575,167182411742739,685627091687022308,164983656922641,166083436986099,103820823892303380,109379542097042194,
681122392548023991,681966817478155191,686190179079397022,677111236690942962,960273963750235088,672328396006726445,398454343178886116,686683619818970084,974630321970715516,681403936244211426,676833095145724812,969848545901517780,974351046017260500,969563737493314487,393106319426690020,104665249141202482,
100161580525919819,100160481014292086,99316055765393079,94813486930173442,103820824160738974,99316056033828578,685839194888838116,94811287906918096,686187842617187074,974982268233948003,969844112958397367,686119570622356407,690976388091714516,114798210863831883,110293511724833654,974632520993971043,
970130020878228323,397891394030770964,686401045599067063,685908635383209492,681121293036396077,974701892768865123,970199392653122403,686753095478385575,974350152664062844,974843902960048930,686471620501674919,685836995865582338,398172868202175372,974699693745609596,960559872475372500,974630528129145724,
402747043537460180,965063472102742883,105507268570880976,114515636862032660,686050508085107684,393737609557548002,398173143348517815,970056560026033063,970130296024570766,686613595544591197,393386900244896557,397891599383894786,681897651861691319,398521620351916967,403025220247722876,974911796947426260,
114795943607638924,398524918886800227,398242344130026407,402747043269024636,684784969664667348,969848752059947988,403307863455538062,398173143952497501,970057659806096295,686470521258482599,970199461372599182,686332051831626659,974701961488341902,686755363489553294,691257863605296014,979488170769095507,
689286370805653091,684784969933102691,691257932056337294,691257794885819235,686755294770076515,974842734410177379,974844933970303843,974843834190240611,691257863655627554,690976456811191907,974632727152401251,974841634630114260,690412270175624828,970130227036658531,398523888413416226,686190215100079650,
690693814459014690,680281370037296764],[393388000614252194,389,964778662893410145,1603972,672325062577322381,3446,969281163007064321,389,964778662891321766,1381,686683825979490019,384,685908566667908945,1674597,969281163007064531,2421,
964777563379694035,2437,690694844666051027,406,100651619066280333,3446])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_1 : BinarySearch.fcAllB [fba_si_0] (pr G1 0) 0 15 1 fba_si_1 = false := by decide +kernel
lemma fva_si_1 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_1 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBn)) fka_si_1
set_option maxHeartbeats 0 in
def fba_si_2 : ℕ × List ℕ × List ℕ := (255,[167389157375580,166289645747847,383814310958439392,684782460598459596,684779162063576250,684780261575204069,680277761459461279,167183217049125,167182680178238,166289377312504,166358382001842,166082900115006,164983388487393,167182948613832,671199162668391952,104874842958043965,
685625992175394444,686470417105525644,379309611819440982,681614836318313415,110223967832480548,672329495518354178,955771463634492368,970126722343345063,676831995634097079,685907535871581879,397891393225464578,393386694086466349,104665248872767139,965060137865944034,104946724134690397,397609919054060516,
103820823623868132,388951366722362320,99317155277020812,969564872169986983,94812387418545709,99317155545456311,974068471797357436,681336694773095396,681684242989816621,398172869007481758,393669269380111262,965340513331026914,676829796610841552,681615970994985954,681614871214922541,686118470842292994,
393387794403400468,974981168722320340,681897445971696610,676899168385735632,685624892663766530,974419318280526716,691256695105756028,969915718653156263,969846553036692391,974845002740112162,681333396238211885,393668169063177143,690975220129045372,970196094118239143,974912003105856468,970126928501775271,
398242344666897364,686190110359919380,686471654056106910,686332051781294868,114234093165845476,398242308696546231,393668444209519586,965344947079453582,974632796140313486,974560159653403516,114797180625328989,686401251489061772,677041109270240208,402745944294267860,398243443910089684,95865444680047446,
403027419270978403,110292343711833015,689287469780410068,686751996235193255,691255595862563708,974351252175690708,691538239338814350,974561259433466748,393669544325127005,974913102617484131,690974120885853052,114515636912364451,974985670653352787,676617693409025744,675777976299920995,689287470048845411,
105224694350978000,690694913115004628,691537071107709908,114798210813500343,403306695224433620,110293511674502114,686755363539884834,974562359213530068,974563458993593300,690412270712495715,675777976568356494,685908671353560675,403028587283979042,685908670548254375,691538170619337571,403307794736061283,
680280270525669031],[964777563381782482,1603972,685908566665820627,1397,685908566665820627,1413,964777563379693868,373,384095785937238413,3446,969281163007064443,2405,964777563379693990,2405,969282262518692219,1381,
398454549339406051,384,690694844666051027,390,690694844668139345,1673590,690694844936574801,1672566])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_2 : BinarySearch.fcAllB [fba_si_0] (pr G1 0) 0 15 1 fba_si_2 = false := by decide +kernel
lemma fva_si_2 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_2 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBn)) fka_si_2
set_option maxHeartbeats 0 in
def fba_si_3 : ℕ × List ℕ × List ℕ := (255,[234423882857953,236760345066952,235660833439219,238032779459891,233324371230039,238032511024548,236865085226291,237964328418611,676828662202604392,681332261829974845,235628084313485,235627815878072,95989839150398,97089619213587,236795241676078,237894753303811,
384095785935149840,167526881541599,672325062575233808,237895340506444,236795828878711,237895290174904,236795778547171,234528304250158,234528572685571,237895558610197,236796315417877,235696535354851,235696803790264,94958828895648,94890059087329,235627279007185,
974912896727489422,235695730048465,686683825977400292,398454549337316324,115078518095977444,115079617339169764,969917917676411860,974420417792154580,236864229588451,237963741216184,234528035814865,97158338690366,96058558627177,236865034894751,237964278087071,393388000612162467,
397891600239532963,397960765000358658,393456065861360429,166426816265720,681970219897559932,167526327893453,681969120385932199,974913171605396366,165258266394081,100651619064191760,236865102003550,164158754766167,237964345195870,393739844014283644,393738744502655911,114516666848877314,
110011967709879085,974842803129654158,686473819524930516,690976319640673236],[685908566665820643,391,690694844666051027,408,690694844934486370,408,965345153290303777,408,965414318051129682,1432,965413218539501906,2456,685908566665820498,3429,964778662891321698,2436,
969281163007064531,1415,964777563379694035,2439,969282262518692194,1415,964778662891321698,2439,964777563379694035,2436])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_3 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2] (pr G1 0) 0 15 1 fba_si_3 = false := by decide +kernel
lemma fva_si_3 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_3 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBn)))) fka_si_3
set_option maxHeartbeats 0 in
def fba_si_4 : ℕ × List ℕ × List ℕ := (255,[110224174041242547,235592113962345,236691625590078,970126687446735774,964778662889233335,969282262516603788,236727595941349,237826839133669,238032192257509,970125587935107860,236796365749668,237895608941988,969281163004975874,964777563377605421,166357778021694,167457289649427,
97158389022157,96058608958968,167664253386021,97295777643813,974982336953424782,398523714953780196,686752991593864164,965414318049041276,965413218537413543,166426765933929,167526277561662,691538239389145890,403307863505869602,965345153288215330,690694844932397923,685908566663732196,
403309992954010580,691539269594094548,691539269862529891,403309993222445923,690694844663962580],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_4 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3] (pr G1 0) 0 15 1 fba_si_4 = false := by decide +kernel
lemma fva_si_4 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_4 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBn))))) fka_si_4
set_option maxHeartbeats 0 in
def fba_si_5 : ℕ × List ℕ × List ℕ := (255,[236829064543525,235523394485566,236622906113299,163917699726625,162818188098962,234492602334481,167664303717812,97295827975604,167458145287604,238032460692757,238032729128351,238032796237150,236727059070392,237826570698125,236726790634798,237826302262531,
235696585686391,235696854121804],[])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fka_si_5 : BinarySearch.fcAllB [fba_si_0,fba_si_1,fba_si_2,fba_si_3,fba_si_4] (pr G1 0) 0 15 1 fba_si_5 = false := by decide +kernel
lemma fva_si_5 : BinarySearch.fcBV (pr G1 0) 0 15 1 fba_si_5 := BinarySearch.fcAllB_val (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBc fva_si_4 (BinarySearch.fcBn)))))) fka_si_5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_si_0 : BinarySearch.fcChkB [fba_si_0,fba_si_1,fba_si_2,fba_si_3,fba_si_4,fba_si_5] [] (pr G1 0) 0 15 1 (0x7ffffffffffffffffffffffffffffffffffffffff) 0 = false := by decide +kernel
lemma chk_si_0 : BinarySearch.chk [] (pr G1 0) 0 15 1 (0x7ffffffffffffffffffffffffffffffffffffffff) 0 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBc fva_si_4 (BinarySearch.fcBc fva_si_5 (BinarySearch.fcBn))))))) (0x7ffffffffffffffffffffffffffffffffffffffff) 0).symm.trans fkr_si_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fkr_si_1 : BinarySearch.fcChkB [fba_si_0,fba_si_1,fba_si_2,fba_si_3,fba_si_4,fba_si_5] [] (pr G1 0) 0 15 1 (0x3ffffffffffff80000000000000000000000000000000000000000) 1 = false := by decide +kernel
lemma chk_si_1 : BinarySearch.chk [] (pr G1 0) 0 15 1 (0x3ffffffffffff80000000000000000000000000000000000000000) 1 = false := (BinarySearch.fcChkB_eq (BinarySearch.fcBc fva_si_0 (BinarySearch.fcBc fva_si_1 (BinarySearch.fcBc fva_si_2 (BinarySearch.fcBc fva_si_3 (BinarySearch.fcBc fva_si_4 (BinarySearch.fcBc fva_si_5 (BinarySearch.fcBn))))))) (0x3ffffffffffff80000000000000000000000000000000000000000) 1).symm.trans fkr_si_1
def shards_si : List (ℕ × ℕ) := [(0x7ffffffffffffffffffffffffffffffffffffffff,0),(0x3ffffffffffff80000000000000000000000000000000000000000,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shardsCover_si : mFull shards_si = true := by decide +kernel
lemma chkAll_si : ∀ p ∈ shards_si, BinarySearch.chk [] (pr G1 0) 0 15 1 p.1 p.2 = false := by
  intro p hp
  simp only [shards_si, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact chk_si_0
  · exact chk_si_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma signedImpossible (S : Finset ℕ) (sw : (S : Set ℕ) ⊆ WZ [] 0) (hl : Live Z0 (mz 0) (tz 0) 15 1 S) : False := by
  refine BinarySearch.rejectMinimum (Q := pr G1 0) (L := 16) (by decide +kernel) (by decide) (by decide) ?_ sw hl baseFloor shards_si shardsCover_si chkAll_si
  intro e he
  exact G1ok e (List.mem_of_mem_filter he)

end PEqualNP.Outside.L_meta_52630

open PEqualNP.Outside.L_meta_52630 in
theorem PEqualNP.Outside.L_meta_52630 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
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
