import PEqualNP.Defs

/- The decision procedure and its soundness proof are adapted from the project proofs
L-meta-32910 and L-meta-1673, with new instance data and checked circuit bounds. -/

namespace PEqualNP.Outside.L_meta_35240_aux

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
  let low := Nat.land s l
  Nat.xor low (Nat.land (Nat.shiftRight s NN) (Bool.rec (motive := fun _ => Nat) low l d))
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
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
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
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)) b d
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
def guardedCoverage (nn : ℕ) (enabled d : Bool) (l : ℕ) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC nn d l v) l)) enabled
def lookCore (NN AA HX HY : Nat) (l m g : Nat) (enabled : Bool) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (guardedCoverage NN enabled (pos t) l v (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y))) true (Nat.ble v.length 1)) fuel
-- Check coverage at each step of the fourteen-gate search.
abbrev lookC (NN AA HX HY : Nat) (l m g fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  lookCore NN AA HX HY l m g (Nat.beq fuel 14) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel

def negCandidates (restrict : Bool) (wires : List W) : List W :=
  bif restrict then wires.filter (fun w => Nat.beq w.r 0) else wires

def mvRawC (NN AA HX HY : Nat) (restrict : Bool) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v (negCandidates restrict v))) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (negCandidates restrict v))) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def lookRawCore (NN AA HX HY : Nat) (restrict : Bool) (l m g : Nat) (enabled : Bool) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (guardedCoverage NN enabled (pos t) l v (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvRawC NN AA HX HY restrict ih l m g k t z v y))) true (Nat.ble v.length 1)) fuel
abbrev lookRawC (NN AA HX HY : Nat) (restrict : Bool) (l m g fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  lookRawCore NN AA HX HY restrict l m g (Nat.beq fuel 14) fuel
def look1RawC (reject : ℕ → ℕ → ℕ → List W → Bool) (NN AA HX HY : Nat) (restrict : Bool) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => bif reject k t z v then false else Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvRawC NN AA HX HY restrict (lookRawC NN AA HX HY restrict l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel

end coreC

def bigNat_0 : Nat := 0x7fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfff0000000000000000
def bigNat_1 : Nat := 0x1529549554000aaa000550002a8001400080012924a92a4925528001248001254924aa5000240009249240009240000000000000000000
def bigNat_2 : Nat := 0x800010200008000210000420000842400010800021088000210000421200008422000084221220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0xffff81ffff03c00000000000000000000ffff81e000000001ffff03c1e1c00001008200030a044189000c49106288314062c0040024430c0210c24c30c280080400421850861604161862424862600000000000000000208a04044501114283e28107a503c0082a101054211010542432e81e004130844255b03c1e1c08a0100860000000440000000011000080007ffe00c006c430c0210000c300000280c05420001bfff0c36180006dbfff05095e78da63bb83
def bigNat_4 : Nat := 0x7fffc0000001ffff7800000007fffc0f000000000000001ffff03c1ffff7801ec00002000900885460002a322152940a98854e0a9802184600004a2c1494d814980802184582a318a8c208248a8e618a9400000000000000000410408088242f0800421050ba2780010442429c80f0020284040304244a4e03c0294e7801ec01042000b008800000000022000140000bfff00000618460000da2c0000d80000180618458000180006186dbfff6180008333acbef42c83ce
def bigNat_5 : Nat := 0x7fffc0ffffbc01ffff7801ffff7bdc00000000000000001e45001b2800e95007c003c007800000010120280007449007c40900904a00f8003c6c06c006c6c0074000000000000000008230101118042604084c081038084821904042a042224bb0049763c0052ea780031ea7bdc00023000020000000045000028000157ffe00000000100050103602800000db7ffec0b01b05afffc00006c06c00006c00002bbde9588e747baf
def bigNat_6 : Nat := 0x3fffe07fffde007fffde00000001ffff7bdc000000000000000000008a00d45000722a03b0001d000e801d04009001080028401d80001d0da001b50006a001a869a0001c84901d800000000000000001044220222108484810909020c1109246e2048dc5e0028d35e10848040634b7bdc420300402044420008008a00005000002afffc0000000000000c01b00158002ad7ffe000000da001b500000000006db0000006dbfffc2fe323dd067eef3
def bigNat_7 : Nat := 0x1ffff000000ffffbc00000003fffef000000007fffdeffffbdec0000000000000000000000812000a00a9855455c002ac0015600ab01560d4c00015b690002960002960d2b4c000054c015304d34915700015600000000000000000208044143c2108080a1e13c4102200284e4f1010804030939e61273dec800c0080800c0800440804816000a00000555fff8000000000000000000d6c00015b6d8000000000000dab6c0000000000006db6dbfff000000731fc533d12e69c4
def bigNat_8 : Nat := 0x1ffff7fffde00000000000003fffef7fffdef7000000000000000000000000000000000000a40000aa8ce0000660003300019800cc01980d69b548000000031800031809a2692510670119c00000019800019800000000000000000410188183cc60f31e410600820c010304f8f609f1ef7401c00803808810070100100701084809018ac0000aabfff0000000000000000000000000d6db56c00000000000000000dab6db55afffdbfff00000000000000003dff840d09b9e83
def bigNat_9 : Nat := 0x7fffe01ffff7fffdeffffbdffff7bd80000000000000000000000000000000000000000000000000ad6ab6002f0000178000bc0005e002f005e0096d256c524d8297e00927e00000000000f8003e00000003e00003e0000000000000000007e0600103f040fc1e81f83d03f07bd80700000e0080000e00801c010000380210803802108000060ad6ab60000000000000000000000000000000d6db56d5b6daad7ffedb7ffe0000000000000000000000000000000083e001c11f614e20
def bigNat_10 : Nat := 0x7fffefc0000000000000000000000000000000000000000000000000000000000000000000000000084a2400300000180000c00006000300060000000000000000040000040000000000008000200000000200000200000000000000000007ff80fdfc007f0010fe0021fc004203f80087f0010847f0010fe002109fc004211fc004211091f80ad6ab6aabfff555fffaafffd57ffebfff7ffe00000000000000000000000000000000000000000000000000000000fc000185278004b9
def bigNat_11 : Nat := 0x7fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfffffffffffffffffff
def NN0 : Nat := 756
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 78), (78, 81), (81, 84), (84, 87), (87, 102), (102, 105), (105, 108), (108, 111), (111, 114), (114, 117), (117, 120), (120, 123), (123, 138), (138, 141), (141, 156), (156, 158), (158, 161), (161, 163), (163, 165), (165, 167), (167, 170), (170, 173), (173, 176), (176, 179), (179, 182), (182, 184), (184, 186), (186, 189), (189, 192), (192, 207), (207, 210), (210, 213), (213, 216), (216, 231), (231, 233), (233, 236), (236, 238), (238, 240), (240, 242), (242, 245), (245, 248), (248, 251), (251, 254), (254, 257), (257, 259), (259, 261), (261, 264), (264, 267), (267, 269), (269, 271), (271, 274), (274, 277), (277, 280), (280, 283), (283, 285), (285, 288), (288, 303), (303, 318), (318, 320), (320, 335), (335, 337), (337, 339), (339, 341), (341, 356), (356, 358), (358, 360), (360, 362), (362, 377), (377, 379), (379, 381), (381, 383), (383, 385), (385, 387), (387, 402), (402, 404), (404, 406), (406, 408), (408, 410), (410, 412), (412, 415), (415, 418), (418, 420), (420, 422), (422, 424), (424, 427), (427, 429), (429, 432), (432, 434), (434, 436)]
def segsY0 : List (ℕ × ℕ) := [(436, 449), (449, 453), (453, 456), (456, 461), (461, 465), (465, 470), (470, 475), (475, 493), (493, 497), (497, 502), (502, 507), (507, 525), (525, 528), (528, 533), (533, 538), (538, 556), (556, 561), (561, 579), (579, 583), (583, 588), (588, 593), (593, 611), (611, 616), (616, 634), (634, 637), (637, 642), (642, 647), (647, 665), (665, 670), (670, 688), (688, 693), (693, 711), (711, 729), (729, 736), (736, 755)]
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

abbrev mvRaw := mvRawC I.NN I.AA I.HX I.HY

abbrev lookRaw := lookRawC I.NN I.AA I.HX I.HY
abbrev look1Raw (reject : ℕ → ℕ → ℕ → List W → Bool) := look1RawC reject I.NN I.AA I.HX I.HY


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
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
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
lemma cov_full {t k k' z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hl : Live R m T k' t S) : Nat.beq (cov (pos' t) l v) l = true := by
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
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov := cov_full X hs hl
  simp only [cv, cvC, bR, hcov, cond_true] at h
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

def RawNegExcluded (R : ℕ → ℕ) (m T k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a, R a ≠ 0 → ∀ n < k, ∀ V : Finset ℕ,
    (V : Set ℕ) ⊆ insert (a ^^^ m) (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))) →
    Live Z0 m T n 0 V → False

lemma rawNegExcluded_after_bi {R : ℕ → ℕ} {m T k a b : ℕ} {d : Bool} {S S' : Finset ℕ}
    (excluded : RawNegExcluded R m T (k + 1) S) (move : Bi Z0 d a b S S') :
    RawNegExcluded R m T k S' := by
  intro x hx q hq V available live
  let out := op d a b
  let stock := insert (x ^^^ m) (C m ({r | R r ≠ 0} ∪ (S : Set ℕ)))
  have ha : a ∈ stock := Or.inr (Or.inl (Or.inr move.sub.1))
  have hb : b ∈ stock := Or.inr (Or.inl (Or.inr move.sub.2.1))
  have projected : (V : Set ℕ) ⊆ insert out stock := by
    intro r hr
    rcases available hr with rfl | ((hR | hs) | constants)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl (Or.inl hR)))
    · rcases Finset.mem_insert.mp (move.sub.2.2 hs) with rfl | hh
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl (Or.inr hh)))
    · exact Or.inr (Or.inr (Or.inr constants))
  by_cases found : out ∈ V
  · let kept := V.erase out
    have tail : Live Z0 m T q 0 (insert (op d a b) kept) := by
      change Live Z0 m T q 0 (insert out (V.erase out))
      rw [Finset.insert_erase found]
      exact live
    have head := Live.bi move.1 (al0 d a b) tail
    refine excluded x hx (q+1) (by omega) _ ?_ head
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_insert] at hr
    rcases hr with rfl | rfl | here
    · exact ha
    · exact hb
    · obtain ⟨ne,member⟩ := Finset.mem_erase.mp here
      exact (projected member).resolve_left ne
  · refine excluded x hx q (by omega) V ?_ live
    intro r hr
    exact (projected hr).resolve_left fun same => found (same ▸ hr)

lemma rawNegExcluded_un {R : ℕ → ℕ} {m T k a : ℕ} {S S' : Finset ℕ}
    (excluded : RawNegExcluded R m T (k+1) S) (move : Un m a S S')
    (raw : R a ≠ 0) (tail : Live Z0 m T k 0 S') : False := by
  refine excluded a raw k (Nat.lt_succ_self k) S' ?_ tail
  intro r hr
  rcases Finset.mem_insert.mp (move.sub.2 hr) with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Or.inr hs))

def RawMode (restrict : Bool) (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop :=
  restrict = true → t ≤ 1 ∧ (t = 1 → RawNegExcluded R m T k S)

lemma rawMode_binary {restrict : Bool} {R R' : ℕ → ℕ} {m T k t a b : ℕ} {d : Bool} {S S' : Finset ℕ}
    (prior : RawMode restrict R m T (k+1) t S) (move : Bi R' d a b S S') :
    RawMode restrict R m T k t S' := by
  intro enabled
  obtain ⟨bound, neg⟩ := prior enabled
  refine ⟨bound, fun ht => ?_⟩
  exact rawNegExcluded_after_bi (neg ht) (move.rel fun d a b _ => al0 d a b)

lemma rawMode_allowed {restrict : Bool} {R : ℕ → ℕ} {m T k t : ℕ} {S S' : Finset ℕ}
    {v : List W} {a : W} (prior : RawMode restrict R m T (k+1) (t+1) S)
    (move : Un m a.s S S') (live : Live R m T k t S') (cod : Cod R v) (member : a ∈ v) :
    a ∈ negCandidates restrict v := by
  cases h : restrict
  · simpa [negCandidates, h] using member
  · have ⟨bound, neg⟩ := prior h
    have ht : t = 0 := by omega
    have eq : a.r = 0 := by
      by_contra ne
      have related := (cod a member).resolve_left ne
      have live0 : Live Z0 m T k 0 S' := by
        simpa only [ht] using live.rel (fun d a b _ => al0 d a b)
      exact rawNegExcluded_un (neg (by omega)) move (by rwa [← related]) live0
    simp [negCandidates, member, eq]

lemma mvRaw_false (restrict : Bool) (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mvRaw restrict F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v (negCandidates restrict v))))) m g (k - s - y) v.length z 0 v (negCandidates restrict v) = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v (negCandidates restrict v))) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v (negCandidates restrict v))) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h

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

lemma mvRaw_sound (restrict : Bool) (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, Min R m T k' t S → RawMode restrict R m T k' t S → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mvRaw restrict F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → RawMode restrict R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm ready hy
  obtain ⟨hA, hN⟩ := mvRaw_false restrict F l m g k t z v y h
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
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2) (rawMode_binary ready hb)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    have permitted := rawMode_allowed ready hu hl1 hcod hwa
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) permitted h2
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
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2) (by
      intro on
      have bound := (ready on).1
      exact ⟨by omega, by omega⟩)
  · have denied : restrict = false := by
      cases h : restrict
      · rfl
      · have bound := (ready h).1
        omega
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    simp only [negCandidates, denied, Bool.cond_false] at h2
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
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2) (by simp [RawMode, denied])
theorem lookRawCore_sound (restrict : Bool) (hR : RR R) (enabled : Bool) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), lookRawCore I.NN I.AA I.HX I.HY restrict l m g enabled fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, Min R m T k' t S → RawMode restrict R m T k' t S → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [lookRawCore] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm ready
    change (Bool.rec (motive := fun _ => Bool) (guardedCoverage I.NN enabled (pos t) l v (tst (pos t) l (k + 1 - t) v (fun y => mvRaw restrict (lookRawCore I.NN I.AA I.HX I.HY restrict l m g enabled fuel) l m g k t z v y))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have same (b : Bool) : guardedCoverage I.NN enabled (pos' t) l v b = b := by
        have hc := cov_full X hs hm.1
        cases enabled <;> simp [guardedCoverage, bR, hc]
      rw [same] at h
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mvRaw_sound X restrict hR ih hs hcod hlen hy k' hk hm ready hyk
theorem lookRaw_sound (restrict : Bool) (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), lookRaw restrict l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, Min R m T k' t S → RawMode restrict R m T k' t S → False := by
  intro fuel
  exact lookRawCore_sound X restrict hR (Nat.beq fuel 14) fuel

theorem lookCore_sound (hR : RR R) (enabled : Bool) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), lookCore I.NN I.AA I.HX I.HY l m g enabled fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [lookCore] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (guardedCoverage I.NN enabled (pos t) l v (tst (pos t) l (k + 1 - t) v (fun y => mv (lookCore I.NN I.AA I.HX I.HY l m g enabled fuel) l m g k t z v y))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have same (b : Bool) : guardedCoverage I.NN enabled (pos' t) l v b = b := by
        have hc := cov_full X hs hm.1
        cases enabled <;> simp [guardedCoverage, bR, hc]
      rw [same] at h
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  exact lookCore_sound X hR (Nat.beq fuel 14) fuel
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

lemma oneRaw_sound (restrict : Bool) (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → RawMode restrict R m T k' t S → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (ready : RawMode restrict R m T k' t S)
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mvRaw restrict (lookRaw restrict l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (XW → XW → Bool) → List XW → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mvRaw_sound X restrict hR (lookRaw_sound X restrict hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ ready (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
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
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_ (rawMode_binary ready hb)
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e))
end sound


def RejectSound (restrict : Bool) (R : ℕ → ℕ) (m T : ℕ) (reject : ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ {k t z v S k'}, Rep v S → k' ≤ k → Live Z0 m T k' t S →
    (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) →
    RawMode restrict R m T k' t S → reject k t z v = true → False

section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
theorem look1Raw_sound (reject : ℕ → ℕ → ℕ → List W → Bool) (restrict : Bool) (valid : RejectSound restrict R m T reject) (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1Raw reject restrict l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → RawMode restrict R m T k' t S → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1Raw, look1RawC] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW ready
    have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs =>
      hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
    cases pruned : reject k t z v
    case true => exact valid hs.rep hk hl hmW ready pruned
    change (bif reject k t z v then false else Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mvRaw restrict (lookRaw restrict l m g K) l m g k t z v y) true
        (node (look1Raw reject restrict l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pruned, Bool.cond_false, bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine oneRaw_sound X restrict hR hR2 ih hs hcod hlen hk hl hmW ready hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e))
end sound

end engine_ok
def xw (e : ℕ × ℕ) : ℕ := I.rawP.getD e.1 0 ^^^ (2 ^ (I.NN + I.NN) - 1)
def rawL (E : List (ℕ × ℕ)) : List ℕ := I.rawP ++ E.map xw
def six : List (ℕ × ℕ) := [(0, 0), (1, 0), (2, 0), (6, 0), (7, 0)]
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawG_good : rawG.all (fun w => I.segsX.all (segGood w 0) &&
    I.segsY.all (segGood w I.NN)) = true := by decide +kernel

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
  have h := List.all_eq_true.1 rawG_good w hw
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
def topRawCC (reject : ℕ → ℕ → ℕ → List W → Bool) (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvRawC NN AA HX HY true (lookRawC NN AA HX HY true l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (look1RawC reject NN AA HX HY true l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
abbrev topRawC (reject : ℕ → ℕ → ℕ → List W → Bool) := topRawCC reject I.NN I.AA I.HX I.HY
def startRawvC (reject : ℕ → ℕ → ℕ → List W → Bool) (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topRawCC reject NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
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


noncomputable def chkRaw (reject : ℕ → ℕ → ℕ → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startRawvC reject nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)


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
  intro q hq sol
  classical
  let existsSol : ∃ n, Sol Z0 (mz Z) (tz Z) n (C (mz Z) (WZ E Z)) := ⟨q, sol⟩
  have leastLt : Nat.find existsSol < L := lt_of_le_of_lt (Nat.find_min' existsSol sol) hq
  obtain ⟨k, hk, t, S, stock, live⟩ := (Nat.find_spec existsSol).live
  have equal : k = Nat.find existsSol :=
    le_antisymm hk (Nat.find_min' existsSol (live.sol.mono le_rfl stock))
  have minimal : ∀ n < k, ¬ Sol Z0 (mz Z) (tz Z) n (C (mz Z) (WZ E Z)) := by
    intro n hn
    exact Nat.find_min existsSol (by omega)
  have stateMin : Min Z0 (mz Z) (tz Z) k t S := ⟨live, fun n hn short =>
    minimal n hn (short.mono le_rfl (fun _ h => h.elim (fun h => stock h) Or.inr))⟩
  exact imp_of_live hE hp hL hI (by omega) stock live minimal
    (hb.imp id (fun h => h t (lt_of_le_of_lt stateMin.size.2 (by omega))))

def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel

lemma singletonCheck {E Q : List (ℕ × ℕ)} {Z K t : ℕ}
    (checked : chk E Q Z K t FF 1 = false) :
    ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun p hp => by
    have same : p = (FF, 1) := by simpa using hp
    exact same.symm ▸ checked⟩

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

open Classical in
noncomputable def notCount : List Gate → ℕ
  | [] => 0
  | g :: gs => (if g.op = .not then 1 else 0) + notCount gs

def UniqueNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j

lemma count_noNot {gs : List Gate} (h : ∀ g ∈ gs, g.op ≠ .not) :
    notCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [notCount, h g (by simp), ih (fun w hw => h w (by simp [hw]))]

lemma count_pos {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) :
    1 ≤ notCount gs := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨w, hw, hn⟩ := h
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [notCount, hn]
    · have hle := ih ⟨w, hw, hn⟩
      simp only [notCount]
      omega

lemma count_le_one {gs : List Gate} (h : UniqueNot gs) : notCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases hn : g.op = .not
    · have tailNo : ∀ w ∈ gs, w.op ≠ .not := by
        intro w hw hnot
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
        have he := h i.succ ⟨0, by simp⟩ hnot hn
        exact Nat.succ_ne_zero i.val (congrArg Fin.val he)
      simp [notCount, hn, count_noNot tailNo]
    · have ht : UniqueNot gs := by
        intro i j hi hj
        have he := h i.succ j.succ hi hj
        exact Fin.ext (Nat.succ.inj (congrArg Fin.val he))
      simp [notCount, hn, ih ht]

lemma live_biBack {m T k t a b : ℕ} {S : Set ℕ} {S0 : Finset ℕ} (d : Bool)
    (ha : a ∈ S) (hb : b ∈ S) (hS : (S0 : Set ℕ) ⊆ insert (op d a b) S)
    (hl : Live Z0 m T k t S0) :
    ∃ inc ≤ 1, ∃ S1 : Finset ℕ, (S1 : Set ℕ) ⊆ S ∧ Live Z0 m T (k+inc) t S1 := by
  by_cases hout : op d a b ∈ S0
  · by_cases hab : a = b
    · exact ⟨0, by decide, S0, fun x hx => (hS hx).elim
        (fun e => by rw [hab, op_self] at e; exact e ▸ hb) id, by simpa using hl⟩
    · refine ⟨1, by decide, insert a (insert b (S0.erase (op d a b))), ?_,
        Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hout])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hS h1).resolve_left h2
  · exact ⟨0, by decide, S0, fun x hx => (hS hx).resolve_left (fun e => hout (e ▸ hx)),
      by simpa using hl⟩

lemma ex_liveCount {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k t : ℕ, t ≤ notCount gs ∧ k + notCount gs ≤ gs.length + t ∧
      ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    have hi : (ex m [] w).getD i 0 ∈ S := getD_mem hw h0 i
    exact ⟨0, 0, by decide, by decide, {_}, by simpa using hi, .stop⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stays (h : gv m w g ∈ S) :
        ∃ k t : ℕ, t ≤ notCount (g :: gs) ∧
          k + notCount (g :: gs) ≤ (g :: gs).length + t ∧
          ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
      have hw' : ∀ x ∈ w ++ [gv m w g], x ∈ S := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h
      obtain ⟨k,t,ht,hk,S0,hS,hl⟩ := ih _ _ hw' h0 hm hgs hT
      refine ⟨k,t,?_,?_,S0,hS,hl⟩ <;> simp only [notCount, List.length_cons] <;>
        split <;> omega
    have hw' : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inr (hw x hx)
      · exact Or.inl rfl
    obtain ⟨k,t,ht,hk,S0,hS,hl⟩ := ih _ _ hw' (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, _⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stays hm
      | [i] => exact stays (rd i)
      | i :: j :: _ =>
        obtain ⟨inc,hinc,S1,hs,hLive⟩ := live_biBack false (rd i) (rd j) hS hl
        refine ⟨k+inc,t,?_,?_,S1,hs,hLive⟩ <;> simp [notCount] <;> omega
    · match l with
      | [] => exact stays h0
      | [i] => exact stays (rd i)
      | i :: j :: _ =>
        obtain ⟨inc,hinc,S1,hs,hLive⟩ := live_biBack true (rd i) (rd j) hS hl
        refine ⟨k+inc,t,?_,?_,S1,hs,hLive⟩ <;> simp [notCount] <;> omega
    · match l with
      | [] => exact stays hm
      | i :: _ =>
        change (S0 : Set ℕ) ⊆ insert (w.getD i 0 ^^^ m) S at hS
        by_cases hz : w.getD i 0 ^^^ m ∈ S0
        · refine ⟨k+1,t+1,?_,?_,insert (w.getD i 0) (S0.erase (w.getD i 0 ^^^ m)),?_,
            Live.un (by rwa [Finset.insert_erase hz])⟩
          · simp [notCount]
            omega
          · simp [notCount]
            omega
          · intro x hx
            simp at hx
            rcases hx with rfl | ⟨ha,hb⟩
            · exact rd i
            · exact (hS ha).resolve_left hb
        · refine ⟨k,t,?_,?_,S0,fun x hx => (hS hx).resolve_left (fun e => hz (e ▸ hx)),hl⟩ <;>
            simp [notCount] <;> omega

def picked {X : Type} (F : X → Bool) (G : Fin 8 → X → Bool) : Prop :=
  ∀ x, F x = true → ∃ b, G b x = true

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
      cases scan (fun e => bif PEqualNP.Outside.L_meta_35240_aux.hb H (x.s + e.s) then q b x e else false) xs <;> rfl
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

lemma noMovesRaw {v : List W} (h : v.any (fun w => Nat.beq w.r 0) = false)
    (nn aa hx hy l m g k z y : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool) :
    mvRawC nn aa hx hy true F l m g k 0 z v y = false :=
  noMoves h nn aa hx hy l m g k z y F

noncomputable def topPairPicked (reject : ℕ → ℕ → ℕ → List W → Bool) (NN AA HX HY l m g K H ph k t z : ℕ)
    (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (mvRawC NN AA HX HY true (lookRawC NN AA HX HY true l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodePicked NN (look1RawC reject NN AA HX HY true l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v H kind))) true (Nat.ble v.length 1)

lemma topPair_picked (reject : ℕ → ℕ → ℕ → List W → Bool) (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topRawCC reject nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPairPicked reject nn aa hx hy l m g K H ph k t z v (cvOp b) = true := by
  simp only [topRawCC, topPairPicked, bR]
  cases ht : Nat.ble v.length 1
  · simp only [ht, Bool.cond_false]
    apply tst_picked
    intro y h
    dsimp only at h ⊢
    cases hx' : nodeC nn (look1RawC reject nn aa hx hy true l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hx', Bool.cond_false] at h
      refine ⟨0, ?_⟩
      rw [h]
      cases nodePicked nn (look1RawC reject nn aa hx hy true l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v H (cvOp 0) <;> rfl
    · obtain ⟨b,hb⟩ := node_picked _ _ _ _ _ _ _ _ _ _ _ hx'
      exact ⟨b, by simp only [hb, Bool.cond_true]⟩
  · simp only [ht, Bool.cond_true]
    exact fun _ => ⟨0,by simp⟩

noncomputable def startPairPicked (reject : ℕ → ℕ → ℕ → List W → Bool) (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPairPicked reject NN AA HX HY l m g K H ph K t z r kind) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

lemma startPair_picked (reject : ℕ → ℕ → ℕ → List W → Bool) (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startRawvC reject nn aa hx hy l m g B K t p H ph)
      (fun b v => startPairPicked reject nn aa hx hy l m g B K t p H ph v (cvOp b)) := by
  intro v
  simp only [startRawvC, startPairPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact topPair_picked reject _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def chkPairPicked (reject : ℕ → ℕ → ℕ → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPairPicked reject nn aa hx hy l m g B K t p H ph r kind)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma noNodePicked {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d kind : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodePicked nn f d l m g e n z v H kind = false := by
  simp only [nodePicked, pairImpossible _ h, bR, Bool.cond_self]

lemma inactiveTopPicked (reject : ℕ → ℕ → ℕ → List W → Bool) {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) (kind : Bool) :
    topPairPicked reject nn aa hx hy l m g K H ph k t z v kind = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topPairPicked, hl, noNodePicked hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMovesRaw hv, Bool.cond_self, tst_const_false]

lemma inactiveStartPicked (reject : ℕ → ℕ → ℕ → List W → Bool) {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) (kind : Bool) :
    startPairPicked reject nn aa hx hy l m g B K t p H ph v kind = false := by
  simp only [startPairPicked, child, st_eq, inactiveTopPicked reject h, bR, Bool.cond_self]

noncomputable def chkPairFast (reject : ℕ → ℕ → ℕ → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p v =>
    startPairPicked reject nn aa hx hy l m g B K t p H ph v kind)

lemma chkPairFast_eq (reject : ℕ → ℕ → ℕ → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) :
    chkPairFast reject E Q Z K t H ph kind = chkPairPicked reject E Q Z K t H ph kind := by
  unfold chkPairFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStartPicked reject h nn aa hx hy l m g B K p kind)]
  rfl

lemma chkPair_picked (reject : ℕ → ℕ → ℕ → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Bool, chkPairPicked reject E Q Z K t H ph b = false) : chkRaw reject E Q Z K t H ph = false := by
  suffices chkRaw reject E Q Z K t H ph = true → False by
    cases he : chkRaw reject E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chkRaw, chkPairPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (startPair_picked reject _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h (cvOp b)).symm.trans hb)

end BinaryPartition

section
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X

set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
lemma oneRaw_bi_sound (restrict : Bool) (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → RawMode restrict R m T k' t S → False)
    {k t z y : ℕ} {v : List W} {S S1 : Finset ℕ} (hs : StOk P T l k z v S)
    (hcod : ∀ w ∈ v, w.r = R w.s)
    {k0 : ℕ} (hk : k0+1 ≤ k) (hl : Live Z0 m T (k0+1) t S)
    {a b : ℕ} {d : Bool} (ha : R a ≠ 0) (hb' : R b ≠ 0) (hb : Bi Z0 d a b S S1)
    (hl1 : Live Z0 m T k0 t S1)
    (hmW : ∀ q < k0+1, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (ready : RawMode restrict R m T (k0+1) t S)
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T (k0+1) t S))
    (h1 : ∀ wa ∈ v, ∀ wb ∈ v, wa.s = a → wb.s = b → wa.s ≠ wb.s → wa.r ≠ 0 → wb.r ≠ 0 →
      ∃ go : (XW → XW → Bool) → List XW → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) wa) (mkx (pos' t) l (wst (pos' t) l v) wb) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) wb) (mkx (pos' t) l (wst (pos' t) l v) wa) = false) : False := by
  have hmin : Min Z0 m T (k0+1) t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb rfl rfl hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
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
  refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_ (rawMode_binary ready hb)
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
set_option maxHeartbeats 0 in
lemma topRawC_bi_sound (reject : ℕ → ℕ → ℕ → List W → Bool) (valid : RejectSound true R m T reject) (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b)
    {K k t z H : ℕ} {v : List W} {S S1 : Finset ℕ}
    (h : topRawC reject l m g K H 0 k t z v = false)
    (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k0 a b : ℕ} {d : Bool} (hk : k0+1 ≤ k) (hl : Live Z0 m T (k0+1) t S)
    (ha : R a ≠ 0) (hb' : R b ≠ 0) (hb0 : Bi Z0 d a b S S1) (hTail : Live Z0 m T k0 t S1)
    (hash : hb H (a+b) = true)
    (ready : RawMode true R m T (k0+1) t S)
    (hmW : ∀ q < k0+1, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  have un : tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (mvRaw true (lookRaw true l m g K) l m g k t z v y) (Nat.beq 0 1)) true
      (node (look1Raw reject true l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v
        (fun f xs => pairsC H f (fs xs)))) = false := by
    change (Bool.rec (motive := fun _ => Bool)
      (tst (pos t) l (k + 1 - t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
           (mvRaw true (lookRaw true l m g K) l m g k t z v y) (Nat.beq 0 1)) true
        (node (look1Raw reject true l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v
          (fun f xs => pairsC H f (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false => rw [h0, cond_false] at h; exact h
  have hmin : Min Z0 m T (k0+1) t S := ⟨hl, fun q hq sq => hmW q hq
    (sq.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y,hFy,hyk⟩ := tst_sound X hs hmin hk
  have hthen := (hFy _).symm.trans un
  have hnode := (or_false' X hthen).1
  refine oneRaw_bi_sound X true hR hR2 (K := K) (f := look1Raw reject true l m g K K) (look1Raw_sound X reject true valid hR hR2 (K := K) K)
      hs hcod hk hl ha hb' hb0 hTail hmW ready hyk ?_
  intro wa hwa wb hwb ea eb hne har hcr
  refine ⟨_,hnode,fun f' hp => ?_⟩
  have hpw := pairsC_false hp
  have symm : Std.Symm (fun a b : XW => hb H (a.s + b.s) = true → (f' a b = false ∨ f' b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  exact (hpw.imp (S := fun a b => hb H (a.s + b.s) = true → (f' a b = false ∨ f' b a = false))
    fun hh e => Or.inl (hh e)).forall (fs_mem (List.mem_map_of_mem hwa) har)
      (fs_mem (List.mem_map_of_mem hwb) hcr) (fun e => hne (congrArg XW.s e)) (by
        change hb H (wa.s + wb.s) = true
        rw [ea,eb]
        exact hash)

end

set_option maxHeartbeats 0 in
theorem imp_of_bi {Q : List (ℕ × ℕ)} {Z L k0 t H a b : ℕ} {d : Bool}
    {S S1 : Finset ℕ} {reject : ℕ → ℕ → ℕ → List W → Bool} (valid : RejectSound true (RZ [] Z) (mz Z) (tz Z) reject)
    (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp [] e.1 e.2)
    (hk : k0+1 < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z))
    (hl : Live Z0 (mz Z) (tz Z) (k0+1) t S)
    (ha : a ∈ WZ [] Z) (hwB : b ∈ WZ [] Z)
    (bi : Bi Z0 d a b S S1) (tail : Live Z0 (mz Z) (tz Z) k0 t S1)
    (hash : hb H (a+b) = true)
    (hmin : ∀ q < k0+1, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ [] Z)))
    (excludeRaw : ∀ a ∈ WZ [] Z, ∀ n < k0+1, ∀ V : Finset ℕ,
      (V : Set ℕ) ⊆ insert (a ^^^ mz Z) (C (mz Z) (WZ [] Z)) → Live Z0 (mz Z) (tz Z) n 0 V → False)
    (ht1 : t ≤ 1) (hchk : chkRaw reject [] Q Z (L-1) t H 0 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ ([] : List (ℕ × ℕ)), e ∈ six := by simp
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) (k0+1) t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ [] Z := by
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
  have hhas : hasP (pwr [] Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have top : topRawC reject (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) H 0 (L - 1) t
      (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    have h2 := hchk
    simp only [chkRaw, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startRawvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topRawC reject (lz Z) (mz Z) _ (L - 1) H 0 (L - 1) t z r)
      (fun h => rfl) hst hm (by omega) h3
  have haR : RZ [] Z a ≠ 0 := by rw [← RZ_set] at ha; exact ha
  have hbR : RZ [] Z b ≠ 0 := by rw [← RZ_set] at hwB; exact hwB
  have ready : RawMode true (RZ [] Z) (mz Z) (tz Z) (k0+1) t S := by
    intro _
    refine ⟨ht1, fun _ a ha n hn V hV hh => ?_⟩
    change a ∈ {s | RZ [] Z s ≠ 0} at ha
    rw [RZ_set] at ha
    apply excludeRaw a ha n hn V _ hh
    rw [RZ_set] at hV
    intro r hr
    rcases hV hr with neg | ((raw | hs) | constant)
    · exact Or.inl neg
    · exact Or.inr (Or.inl raw)
    · exact Or.inr (Or.inl (hSW hs))
    · exact Or.inr (Or.inr constant)
  refine topRawC_bi_sound X reject valid (RZ_R [] Z) (RZ_R2 [] Z) top hst hcod (by omega) hl
    haR hbR bi tail hash ready ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

section inst_data
def rt4 : List (ℕ × ℕ) := [(15, 2), (23, 4), (27, 5), (29, 2), (30, 4), (39, 4), (43, 4), (45, 4), (46, 2), (51, 3), (53, 4), (54, 5), (57, 4), (58, 4), (60, 2), (71, 3), (75, 5), (77, 5), (78, 5), (83, 5), (85, 3), (86, 5), (89, 5), (90, 5), (92, 5), (99, 3), (101, 5), (102, 5), (105, 5), (106, 3), (108, 5), (113, 3), (114, 5), (116, 5), (120, 3), (135, 1), (139, 2), (141, 1), (142, 1), (147, 4), (149, 1), (150, 4), (153, 2), (154, 4), (156, 1), (163, 2), (165, 3), (166, 2), (169, 3), (170, 1), (172, 1), (177, 2), (178, 4), (180, 2), (184, 1), (195, 1), (197, 1), (198, 2), (201, 3), (202, 2), (204, 3), (209, 1), (210, 4), (212, 2), (216, 2), (225, 1), (226, 1), (228, 3), (232, 1), (240, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r4 : rt4.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma i4 : ∀ e ∈ rt4, Imp [] e.1 e.2 := okAll (T := []) r4 (by simp)

def rt3 : List (ℕ × ℕ) := [(7, 5), (11, 6), (13, 5), (14, 5), (19, 6), (21, 5), (22, 7), (25, 6), (26, 7), (28, 5), (35, 5), (37, 7), (38, 6), (41, 7), (42, 5), (44, 5), (49, 5), (50, 6), (52, 6), (56, 5), (67, 6), (69, 6), (70, 6), (73, 8), (74, 6), (76, 8), (81, 6), (82, 7), (84, 6), (88, 6), (97, 6), (98, 6), (100, 8), (104, 6), (112, 6), (131, 4), (133, 3), (134, 4), (137, 4), (138, 4), (140, 3), (145, 4), (146, 7), (148, 4), (152, 4), (161, 4), (162, 4), (164, 4), (168, 3), (176, 4), (193, 3), (194, 4), (196, 4), (200, 4), (208, 4), (224, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3 : rt3.all (fun e => okE [] (pr rt4 e.1) e) = true := by decide +kernel
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll (T := rt4) r3 i4

def rt2 : List (ℕ × ℕ) := [(3, 8), (5, 8), (6, 8), (9, 9), (10, 8), (12, 8), (17, 8), (18, 10), (20, 8), (24, 8), (33, 8), (34, 8), (36, 9), (40, 8), (48, 8), (65, 9), (66, 9), (68, 9), (72, 9), (80, 9), (96, 9), (129, 6), (130, 7), (132, 6), (136, 6), (144, 7), (160, 6), (192, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2 : rt2.all (fun e => okE [] (pr (rt3 ++ rt4) e.1) e) = true := by decide +kernel
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll (T := (rt3 ++ rt4)) r2 (apI i3 i4)

def rt : List (ℕ × ℕ) := (rt2 ++ (rt3 ++ rt4))
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := (apI i2 (apI i3 i4))

open PEqualNP.CircuitLowerBounds

def witness : List Gate := [⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [16, 0]⟩, ⟨.and, [17, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [20, 14]⟩, ⟨.or, [21, 18]⟩]

theorem witness_basis : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

theorem f_graph (x : Fin 8 → Bool) : f x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  have hx : f x = true ↔ (x 0 = true ∧ x 3 = true) ∨ (x 1 = true ∧ x 4 = true) ∨ (x 0 = true ∧ x 5 = true) ∨ (x 2 = true ∧ x 5 = true) ∨ (x 2 = true ∧ x 6 = true) ∨ (x 3 = true ∧ x 6 = true) ∨ (x 0 = true ∧ x 7 = true) ∨ (x 1 = true ∧ x 7 = true) ∨ (x 2 = true ∧ x 7 = true) ∨ (x 3 = true ∧ x 7 = true) ∨ (x 4 = true ∧ x 7 = true) ∨ (x 5 = true ∧ x 7 = true) := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  rw [Bool.eq_iff_iff, hx, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h)
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
  · rintro ⟨i, hi, h⟩
    have hi' : i < 12 := hi
    interval_cases i <;> simp_all

def EF : ℕ := ((((((((((((rawP0.getD 0 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 5 0 &&& rawP0.getD 7 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 8 := rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
def selectedBits (flag : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if flag n then selectedBits flag n ||| 2 ^ n else selectedBits flag n

lemma selectedBits_bit (flag : ℕ → Bool) (n k : ℕ) :
    (selectedBits flag n).testBit k = (decide (k < n) && flag k) := by
  induction n with
  | zero => simp [selectedBits]
  | succ n ih =>
    rw [selectedBits]
    cases hk : flag n
    · simp only [hk, Bool.false_eq_true, ite_false, ih]
      by_cases lt : k < n
      · simp [lt, show k < n + 1 by omega]
      · by_cases eq : k = n
        · subst k
          simp [hk]
        · simp [lt, show ¬ k < n + 1 by omega]
    · simp only [hk, ite_true, Nat.testBit_or, ih, Nat.testBit_two_pow]
      by_cases lt : k < n
      · simp [lt, show k < n + 1 by omega, show k ≠ n by omega, show n ≠ k by omega]
      · by_cases eq : k = n
        · subst k
          simp [hk]
        · simp [lt, eq, Ne.symm eq, show ¬ k < n + 1 by omega]

theorem Live.mapSignals {m T m' T' k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (f : ℕ → ℕ) (htarget : f T = T') (hneg : ∀ a, f (a ^^^ m) = f a ^^^ m')
    (hbin : ∀ d a b, f (op d a b) = op d (f a) (f b)) :
    ∃ k' t' : ℕ, t' ≤ t ∧ k' + t ≤ k + t' ∧
      ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ f '' (S : Set ℕ) ∧ Live Z0 m' T' k' t' S' := by
  induction hl with
  | stop =>
    exact ⟨0,0,le_rfl,le_rfl,{T'},by
      intro x hx
      simp at hx
      subst x
      exact ⟨T,by simp,htarget⟩,.stop⟩
  | @un k t a U hl ih =>
    obtain ⟨k',t',ht,hk,S',hs,hLive⟩ := ih
    by_cases used : f (a ^^^ m) ∈ S'
    · refine ⟨k'+1,t'+1,by omega,by omega,insert (f a) (S'.erase (f (a ^^^ m))),?_,
        Live.un ?_⟩
      · intro x hx
        simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hx
        rcases hx with rfl | ⟨hne,hx⟩
        · exact ⟨a,by simp,rfl⟩
        · obtain ⟨v,hv,rfl⟩ := hs hx
          have hu : v ∈ U := by
            rcases Finset.mem_insert.mp hv with ev | hv
            · exact (hne (congrArg f ev)).elim
            · exact hv
          exact ⟨v,by simp [hu],rfl⟩
      · rw [← hneg, Finset.insert_erase used]
        exact hLive
    · refine ⟨k',t',by omega,by omega,S',?_,hLive⟩
      intro x hx
      obtain ⟨v,hv,rfl⟩ := hs hx
      have hu : v ∈ U := by
        rcases Finset.mem_insert.mp hv with ev | hv
        · exact (used ((congrArg f ev) ▸ hx)).elim
        · exact hv
      exact ⟨v,by simp [hu],rfl⟩
  | @bi k t d a b U hab hal hl ih =>
    obtain ⟨k',t',ht,hk,S',hs,hLive⟩ := ih
    by_cases used : f (op d a b) ∈ S'
    · by_cases heq : f a = f b
      · refine ⟨k',t',ht,by omega,S',?_,hLive⟩
        intro x hx
        obtain ⟨v,hv,rfl⟩ := hs hx
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨b,by simp,by rw [hbin, heq, op_self]⟩
        · exact ⟨v,by simp [hv],rfl⟩
      · refine ⟨k'+1,t',ht,by omega,
          insert (f a) (insert (f b) (S'.erase (f (op d a b)))),?_,
          Live.bi (d := d) heq (al0 _ _ _) ?_⟩
        · intro x hx
          simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hx
          rcases hx with rfl | rfl | ⟨hne,hx⟩
          · exact ⟨a,by simp,rfl⟩
          · exact ⟨b,by simp,rfl⟩
          · obtain ⟨v,hv,rfl⟩ := hs hx
            rcases Finset.mem_insert.mp hv with ev | hv
            · exact (hne (congrArg f ev)).elim
            · exact ⟨v,by simp [hv],rfl⟩
        · rw [← hbin, Finset.insert_erase used]
          exact hLive
    · refine ⟨k',t',ht,by omega,S',?_,hLive⟩
      intro x hx
      obtain ⟨v,hv,rfl⟩ := hs hx
      rcases Finset.mem_insert.mp hv with ev | hv
      · exact (used ((congrArg f ev) ▸ hx)).elim
      · exact ⟨v,by simp [hv],rfl⟩

theorem Sol.mapSignals {m T m' T' k : ℕ} {S : Set ℕ} (hl : Sol Z0 m T k S)
    (f : ℕ → ℕ) (htarget : f T = T') (hneg : ∀ a, f (a ^^^ m) = f a ^^^ m')
    (hbin : ∀ d a b, f (op d a b) = op d (f a) (f b)) :
    Sol Z0 m' T' k (f '' S) := by
  induction hl with
  | @done q U h =>
    exact .done ⟨T,h,htarget⟩
  | @un q U a ha _ ih =>
    refine .un (a := f a) ⟨a,ha,rfl⟩ (ih.mono le_rfl ?_)
    rintro _ ⟨w,hw,rfl⟩
    rcases hw with rfl | hw
    · exact Or.inl (hneg a)
    · exact Or.inr ⟨w,hw,rfl⟩
  | @bi q U d a b ha hb _ _ ih =>
    refine .bi (d := d) (a := f a) (b := f b) ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ (al0 _ _ _) (ih.mono le_rfl ?_)
    rintro _ ⟨w,hw,rfl⟩
    rcases hw with rfl | hw
    · exact Or.inl (hbin d a b)
    · exact Or.inr ⟨w,hw,rfl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def permutations : List (List (Fin 8)) :=
  [[0,1,2,3,4,5,6,7], [5,1,3,2,4,0,6,7], [0,4,2,3,1,5,6,7], [5,4,3,2,1,0,6,7]]

def permuted (a : Fin 4) (i : Fin 8) : Fin 8 :=
  (permutations.getD a.val []).getD i.val i

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma permuted_preserves_f : ∀ a : Fin 4, ∀ x : Fin 8 → Bool,
    f (fun i => x (permuted a i)) = f x := by
  decide +kernel

def fullMask : ℕ := 2 ^ 256 - 1

def fullWire (i : Fin 8) : ℕ := selectedBits (·.testBit i.val) 256

def fullBank : List ℕ := List.ofFn fullWire

def fullTarget : ℕ := selectedBits (fun k => f (fun i : Fin 8 => k.testBit i.val)) 256

def fullStock : Set ℕ := {a | a ∈ fullBank}

lemma fullWire_mask (i : Fin 8) : fullWire i &&& fullMask = fullWire i := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, fullWire, selectedBits_bit, fullMask, Nat.testBit_two_pow_sub_one]
  cases decide (k < 256) <;> simp

lemma fullTarget_mask : fullTarget &&& fullMask = fullTarget := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, fullTarget, selectedBits_bit, fullMask, Nat.testBit_two_pow_sub_one]
  cases decide (k < 256) <;> simp

lemma fullStock_rows {x : ℕ} (h : x ∈ fullStock) : ∃ v : Fin 8, x = fullWire v := by
  simpa [fullStock, fullBank, eq_comm] using (List.mem_ofFn.mp h)

lemma fullStock_mask {x : ℕ} (h : x ∈ C fullMask fullStock) : x &&& fullMask = x := by
  rcases h with h | h
  · obtain ⟨i,rfl⟩ := fullStock_rows h
    exact fullWire_mask i
  · simp at h
    rcases h with rfl | rfl <;> simp

lemma fullBridge (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩)
    (hf : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = f x) :
    ∃ k t : ℕ, t ≤ notCount gates ∧ k + notCount gates ≤ gates.length+t ∧
      ∃ S : Finset ℕ, (S : Set ℕ) ⊆ C fullMask fullStock ∧ Live Z0 fullMask fullTarget k t S := by
  have hmasked : ∀ w ∈ fullBank, w &&& fullMask = w := fun _ h => fullStock_mask (Or.inl h)
  have hinit : ∀ w ∈ fullBank, w ∈ C fullMask fullStock := fun _ h => Or.inl h
  have hsub := ex_sub fullMask (gs := gates) hmasked
  have hget := getD_mem (S := {x | x &&& fullMask = x}) hsub (by simp) o
  have hresult : (ex fullMask gates fullBank).getD o 0 = fullTarget := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 256
    · have hm : fullMask.testBit k = true := by
        rw [fullMask,Nat.testBit_two_pow_sub_one]
        simp [hk]
      have hrows : fullBank.map (fun v => v.testBit k) = List.ofFn (fun v : Fin 8 => k.testBit v.val) := by
        rw [fullBank,List.map_ofFn]
        apply congrArg (fun u : Fin 8 → Bool => List.ofFn u)
        funext v
        simp [Function.comp_def, fullWire, selectedBits_bit,hk]
      rw [← getD_map, ex_bit fullMask hm gates fullBank hD,hrows]
      have hev := hf (fun v : Fin 8 => k.testBit v.val)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun v : Fin 8 => k.testBit v.val)).getD o false = f (fun v : Fin 8 => k.testBit v.val) at hev
      rw [hev]
      simp [fullTarget,selectedBits_bit,hk]
    · have hm : fullMask.testBit k = false := by
        rw [fullMask,Nat.testBit_two_pow_sub_one]
        simp [hk]
      have hs := congrArg (fun n => n.testBit k) hget
      simp only [Set.mem_setOf_eq,Nat.testBit_and,hm,Bool.and_false] at hs
      rw [← hs]
      simp [fullTarget,selectedBits_bit,hk]
  exact ex_liveCount fullMask gates fullBank (C fullMask fullStock) hinit
    (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨o,hresult⟩

def sampleIndex (a : Fin 4) (k : ℕ) : ℕ :=
  selectedBits (fun i =>
    (rawP0.getD (permuted a ⟨i % 8, Nat.mod_lt _ (by decide)⟩).val 0).testBit k) 8 % 256

lemma sampleIndex_lt (a : Fin 4) (k : ℕ) : sampleIndex a k < 256 := Nat.mod_lt _ (by decide)

lemma sampleIndex_bit (a : Fin 4) (k : ℕ) (i : Fin 8) :
    (sampleIndex a k).testBit i.val = (rawP0.getD (permuted a i).val 0).testBit k := by
  unfold sampleIndex
  rw [show (256:ℕ) = 2^8 by decide, Nat.testBit_mod_two_pow, selectedBits_bit]
  simp [i.isLt, Nat.mod_eq_of_lt i.isLt]

def pull (a : Fin 4) (w : ℕ) : ℕ :=
  selectedBits (fun k => (mz 0).testBit k && w.testBit (sampleIndex a k)) (I.NN + I.NN)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma sampleMaskBound : mz 0 < 2^(I.NN + I.NN) := by decide +kernel

lemma pull_bit (a : Fin 4) (w k : ℕ) :
    (pull a w).testBit k = ((mz 0).testBit k && w.testBit (sampleIndex a k)) := by
  unfold pull
  rw [selectedBits_bit]
  by_cases hk : k < I.NN + I.NN
  · simp [hk]
  · have hb := Nat.testBit_lt_two_pow (lt_of_lt_of_le sampleMaskBound (Nat.pow_le_pow_right (by decide) (by omega : I.NN+I.NN ≤ k)))
    simp [hk,hb]

lemma pull_zero (a : Fin 4) : pull a 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp [pull_bit]

lemma pull_mask (a : Fin 4) : pull a fullMask = mz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit,fullMask,Nat.testBit_two_pow_sub_one]
  simp [sampleIndex_lt]

lemma pull_neg (a : Fin 4) (w : ℕ) : pull a (w ^^^ fullMask) = pull a w ^^^ mz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit, Nat.testBit_xor, Nat.testBit_xor, pull_bit, fullMask, Nat.testBit_two_pow_sub_one]
  simp only [sampleIndex_lt,decide_true]
  cases (mz 0).testBit k <;> cases w.testBit (sampleIndex a k) <;> rfl

lemma pull_op (a : Fin 4) (d : Bool) (u v : ℕ) :
    pull a (op d u v) = op d (pull a u) (pull a v) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit, op_bit, op_bit, pull_bit, pull_bit]
  cases d <;> cases (mz 0).testBit k <;> cases u.testBit (sampleIndex a k) <;>
    cases v.testBit (sampleIndex a k) <;> rfl

lemma pull_fullWire (a : Fin 4) (i : Fin 8) :
    pull a (fullWire i) = rawP0.getD (permuted a i).val 0 &&& mz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit, Nat.testBit_and, fullWire, selectedBits_bit, sampleIndex_bit]
  simp [sampleIndex_lt,Bool.and_comm]

lemma pull_target (a : Fin 4) : pull a fullTarget = tz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [← EF_ok,pull_bit, Nat.testBit_and, f_bit, fullTarget, selectedBits_bit]
  simp only [sampleIndex_lt,decide_true,Bool.true_and]
  have equiv : (fun i : Fin 8 => (sampleIndex a k).testBit i.val) =
      fun i : Fin 8 => (rawP0.getD (permuted a i).val 0).testBit k := by
    funext i
    exact sampleIndex_bit a k i
  have same := permuted_preserves_f a (fun v => (rawP0.getD v.val 0).testBit k)
  rw [equiv, same, Bool.and_comm]

lemma pull_initial (a : Fin 4) :
    pull a '' C fullMask fullStock ⊆ C (mz 0) (WZ [] 0) := by
  rintro _ ⟨v,hv,rfl⟩
  rcases hv with hv | hv
  · obtain ⟨i,rfl⟩ := fullStock_rows hv
    rw [pull_fullWire]
    refine Or.inl ⟨_,?_,rfl⟩
    apply List.mem_append_left
    have hh : (permuted a i).val < rawP0.length := by simpa [rawP_len0] using (permuted a i).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]
    exact List.getElem_mem _
  · simp at hv
    rcases hv with rfl | rfl
    · rw [pull_zero]
      exact Or.inr (Set.mem_insert _ _)
    · rw [pull_mask]
      exact Or.inr (Set.mem_insert_of_mem _ rfl)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness table specifies one source sample position for each of the 256 assignments. -/
def cofactorPosition (a : Fin 4) (table k : ℕ) : ℕ :=
  (table >>> (13 * sampleIndex a k)) &&& 8191

def cofactorAlignment (known other table : ℕ) (a : Fin 4) : Bool :=
  (List.range (I.NN + I.NN)).all fun k =>
    !(mz known).testBit k ||
      ((mz other).testBit (cofactorPosition a table k) &&
        (sampleIndex 0 (cofactorPosition a table k) == sampleIndex a k))

lemma cofactorAlignment_sound {known other table : ℕ} {a : Fin 4}
    (h : cofactorAlignment known other table a = true) {k : ℕ}
    (hk : k < I.NN + I.NN) (hm : (mz known).testBit k = true) :
    (mz other).testBit (cofactorPosition a table k) = true ∧
      sampleIndex 0 (cofactorPosition a table k) = sampleIndex a k := by
  have ha := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa [hm] using ha

def cofactorPull (known table : ℕ) (a : Fin 4) (w : ℕ) : ℕ :=
  selectedBits (fun k => (mz known).testBit k && w.testBit (cofactorPosition a table k)) (I.NN + I.NN)

lemma cofactorPull_bit {known : ℕ} (bound : mz known < 2 ^ (I.NN + I.NN))
    (a : Fin 4) (table w k : ℕ) :
    (cofactorPull known table a w).testBit k = ((mz known).testBit k && w.testBit (cofactorPosition a table k)) := by
  rw [cofactorPull, selectedBits_bit]
  by_cases hk : k < I.NN + I.NN
  · simp [hk]
  · have hm := Nat.testBit_lt_two_pow
      (bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega : I.NN + I.NN ≤ k)))
    simp [hk,hm]

lemma rawP_getD_mem (i : Fin 8) : rawP0.getD i.val 0 ∈ rawP0 := by
  have h : i.val < rawP0.length := by rw [rawP_len0]; exact i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem _

lemma rawP_mem_getD {w : ℕ} (h : w ∈ rawP0) : ∃ i : Fin 8, w = rawP0.getD i.val 0 := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨i,by simpa only [rawP_len0] using hi⟩,?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact eq.symm

set_option maxHeartbeats 0 in
lemma cofactorMaps {known other table : ℕ} {a : Fin 4}
    (bound : mz known < 2 ^ (I.NN + I.NN))
    (aligned : cofactorAlignment known other table a = true)
    (fKnown : EF &&& mz known = tz known) (fOther : EF &&& mz other = tz other) :
    let map := cofactorPull known table a
    map (tz other) = tz known ∧
      (∀ w, map (w ^^^ mz other) = map w ^^^ mz known) ∧
      (∀ d x y, map (op d x y) = op d (map x) (map y)) ∧
      map '' C (mz other) (WZ [] other) ⊆ C (mz known) (WZ [] known) ∧
      (∀ i : Fin 8, map (rawP0.getD i.val 0 &&& mz other) =
        rawP0.getD (permuted a i).val 0 &&& mz known) := by
  let map := cofactorPull known table a
  have bit := cofactorPull_bit bound a table
  have data (k : ℕ) (hm : (mz known).testBit k = true) := by
    have hk : k < I.NN + I.NN := by
      by_contra h
      have zero := Nat.testBit_lt_two_pow
        (bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega : I.NN + I.NN ≤ k)))
      rw [zero] at hm
      exact Bool.noConfusion hm
    exact cofactorAlignment_sound aligned hk hm
  have row (k : ℕ) (i : Fin 8) (hm : (mz known).testBit k = true) :
      (rawP0.getD i.val 0).testBit (cofactorPosition a table k) =
        (rawP0.getD (permuted a i).val 0).testBit k := by
    have h := congrArg (fun x : ℕ => x.testBit i.val) (data k hm).2
    simpa only [sampleIndex_bit, show permuted 0 i = i from by
      fin_cases i <;> rfl] using h
  have m : map (mz other) = mz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [show map (mz other) = cofactorPull known table a (mz other) from rfl,bit]
    by_cases hm : (mz known).testBit k = true
    · rw [(data k hm).1,hm,Bool.and_true]
    · simp [Bool.eq_false_iff.mpr hm]
  have z : map 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [show map 0 = cofactorPull known table a 0 from rfl,bit]
    simp
  have neg (w : ℕ) : map (w ^^^ mz other) = map w ^^^ mz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (w ^^^ mz other)).testBit k =
      (cofactorPull known table a w ^^^ mz known).testBit k
    rw [bit,Nat.testBit_xor,Nat.testBit_xor,bit]
    by_cases hm : (mz known).testBit k = true
    · simp only [(data k hm).1,hm,Bool.true_and]
    · simp [Bool.eq_false_iff.mpr hm]
  have bin (d : Bool) (x y : ℕ) : map (op d x y) = op d (map x) (map y) := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (op d x y)).testBit k =
      (op d (cofactorPull known table a x) (cofactorPull known table a y)).testBit k
    rw [bit,op_bit,op_bit,bit,bit]
    cases d <;> cases (mz known).testBit k <;> rfl
  have target : map (tz other) = tz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (tz other)).testBit k = (tz known).testBit k
    rw [bit,← fOther,← fKnown,Nat.testBit_and,Nat.testBit_and]
    by_cases hm : (mz known).testBit k = true
    · rw [(data k hm).1,hm,Bool.and_true,Bool.and_true,Bool.true_and,f_bit,f_bit]
      have eq : (fun i : Fin 8 => (rawP0.getD i.val 0).testBit (cofactorPosition a table k)) =
          fun i : Fin 8 => (rawP0.getD (permuted a i).val 0).testBit k := funext fun i => row k i hm
      rw [eq]
      exact permuted_preserves_f a (fun i : Fin 8 => (rawP0.getD i.val 0).testBit k)
    · simp [Bool.eq_false_iff.mpr hm]
  have wire (i : Fin 8) : map (rawP0.getD i.val 0 &&& mz other) =
      rawP0.getD (permuted a i).val 0 &&& mz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (rawP0.getD i.val 0 &&& mz other)).testBit k =
      (rawP0.getD (permuted a i).val 0 &&& mz known).testBit k
    rw [bit,Nat.testBit_and,Nat.testBit_and]
    by_cases hm : (mz known).testBit k = true
    · rw [(data k hm).1,row k i hm,hm,Bool.and_true,Bool.true_and]
    · simp [Bool.eq_false_iff.mpr hm]
  have initial : map '' C (mz other) (WZ [] other) ⊆ C (mz known) (WZ [] known) := by
    rintro _ ⟨w,h,rfl⟩
    rcases h with h | h
    · obtain ⟨v,hv,rfl⟩ := h
      have hv' : v ∈ rawP0 := by
        change v ∈ I.rawP
        simpa only [rawL,List.map_nil,List.append_nil] using hv
      obtain ⟨i,rfl⟩ := rawP_mem_getD hv'
      refine Or.inl ⟨_,List.mem_append_left _ (rawP_getD_mem (permuted a i)),?_⟩
      exact wire i
    · simp at h
      rcases h with rfl | rfl
      · rw [z]
        exact Or.inr (Set.mem_insert _ _)
      · rw [m]
        exact Or.inr (Set.mem_insert_of_mem _ rfl)
  exact ⟨target, neg, bin, initial, wire⟩

set_option maxHeartbeats 0 in
lemma imp_by_cofactor_symmetry {known other L table : ℕ} {a : Fin 4}
    (bound : mz known < 2 ^ (I.NN + I.NN))
    (aligned : cofactorAlignment known other table a = true)
    (fKnown : EF &&& mz known = tz known) (fOther : EF &&& mz other = tz other)
    (lower : Imp [] known L) : Imp [] other L := by
  obtain ⟨target, neg, bin, initial, _⟩ := cofactorMaps bound aligned fKnown fOther
  intro q hq sol
  exact lower q hq ((sol.mapSignals _ target neg bin).mono le_rfl initial)

def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeAppend (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all

noncomputable def singletonTest (Q : List (ℕ × ℕ)) (Z K t : ℕ) : Bool :=
  !chkFast [] Q Z K t FF 1

lemma singletonCertified {Q : List (ℕ × ℕ)} {Z K start count t : ℕ}
    (checked : rangeCheck (singletonTest Q Z K) start count = true)
    (low : start ≤ t) (high : t < start + count) :
    ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] Q Z K t a.1 a.2 = false := by
  have h := List.all_eq_true.mp checked t (List.mem_range'_1.mpr ⟨low,high⟩)
  rw [singletonTest, chkFast_eq] at h
  exact singletonCheck (boolOfNeg h)

def q1 : List (ℕ × ℕ) := pr rt 1
lemma co1_p : pOk 1 q1 = true := by decide +kernel
lemma co1_id : ∀ a ∈ q1, Imp [] a.1 a.2 := by
  intro a ha
  unfold q1 pr at ha
  exact ir a (List.mem_of_mem_filter ha)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1Singletons : rangeCheck (singletonTest q1 1 10) 0 11 = true := by decide +kernel

lemma co1 : Imp [] 1 11 := imp_of (Or.inl rfl) co1_p (by norm_num) co1_id
    (Or.inr fun t ht => singletonCertified co1Singletons (by omega) (by omega))

def q2 : List (ℕ × ℕ) := pr rt 2
lemma co2_p : pOk 2 q2 = true := by decide +kernel
lemma co2_id : ∀ a ∈ q2, Imp [] a.1 a.2 := by
  intro a ha
  unfold q2 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
noncomputable def restrictedTest (Q : List (ℕ × ℕ)) (Z t : ℕ)
    (cases : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  let a := cases.getD i (0,0)
  !chkFast [] Q Z 11 t a.1 a.2

lemma restrictedWitness (Q : List (ℕ × ℕ)) (Z t : ℕ) (M : List (ℕ × ℕ))
    (covers : mFull M = true) (checked : rangeCheck (restrictedTest Q Z t M) 0 M.length = true) :
    ∃ cases : List (ℕ × ℕ), mFull cases = true ∧
      ∀ a ∈ cases, chk [] Q Z 11 t a.1 a.2 = false := by
  refine ⟨M,covers,?_⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
  have h := boolOfNeg (rangeCheck_at checked hi)
  simpa only [restrictedTest, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, chkFast_eq] using h

def co2t0_cov : List (ℕ × ℕ) := [(0x0, 1), (0x20, 0), (0x2000, 0), (0x400000000, 0), (0x40000000000, 0), (0x400000000000000, 0), (0x800000000000000, 0), (0x8000000000000000, 0), (0x40000000000000000, 0), (0x100000000000000000, 0), (0x800000000000000000, 0), (0x10000000000000000000, 0), (0x800000000000000000000, 0), (0x10000000000000000000000, 0), (0x200000000000000000000000, 0), (0x10000000000000000000000000000, 0), (0x200000000000000000000000000000, 0), (0x4000000000000000000000000000000, 0), (0x200000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000000, 0), (0x3ffbffffffffffff7bdffffbdeffffdef7ef6b73fffbfbffffdfdf, 0)]

noncomputable def co2zeroTest := restrictedTest q2 2 0 co2t0_cov

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero0 : rangeCheck co2zeroTest 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero1 : rangeCheck co2zeroTest 2 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero2 : rangeCheck co2zeroTest 4 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero3 : rangeCheck co2zeroTest 6 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero4 : rangeCheck co2zeroTest 8 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero5 : rangeCheck co2zeroTest 10 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero6 : rangeCheck co2zeroTest 12 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero7 : rangeCheck co2zeroTest 14 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero8 : rangeCheck co2zeroTest 16 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero9 : rangeCheck co2zeroTest 18 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero10 : rangeCheck co2zeroTest 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zero11 : rangeCheck co2zeroTest 22 1 = true := by decide +kernel

abbrev co2zeroAppend := @rangeAppend co2zeroTest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2zeroAll : rangeCheck co2zeroTest 0 23 = true :=
  (@co2zeroAppend 0 12 11 (@co2zeroAppend 0 6 6 (@co2zeroAppend 0 2 4 co2zero0 (@co2zeroAppend 2 2 2 co2zero1 co2zero2)) (@co2zeroAppend 6 2 4 co2zero3 (@co2zeroAppend 8 2 2 co2zero4 co2zero5))) (@co2zeroAppend 12 6 5 (@co2zeroAppend 12 2 4 co2zero6 (@co2zeroAppend 14 2 2 co2zero7 co2zero8)) (@co2zeroAppend 18 2 3 co2zero9 (@co2zeroAppend 20 2 1 co2zero10 co2zero11))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co2t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 0 a.1 a.2 = false :=
  restrictedWitness q2 2 0 co2t0_cov (by decide +kernel) co2zeroAll

def co2t1_cov : List (ℕ × ℕ) := [(0x0, 1), (0x20, 0), (0x2000, 0), (0x400000000, 0), (0x40000000000, 0), (0x400000000000000, 0), (0x800000000000000, 0), (0x8000000000000000, 0), (0x40000000000000000, 0), (0x100000000000000000, 0), (0x800000000000000000, 0), (0x10000000000000000000, 0), (0x800000000000000000000, 0), (0x10000000000000000000000, 0), (0x200000000000000000000000, 0), (0x10000000000000000000000000000, 0), (0x200000000000000000000000000000, 0), (0x4000000000000000000000000000000, 0), (0x200000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000000, 0), (0x3ffbffffffffffff7bdffffbdeffffdef7ef6b73fffbfbffffdfdf, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch0 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch1 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch2 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch3 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch4 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch5 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 20 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co2t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 1 a.1 a.2 = false :=
  restrictedWitness q2 2 1 co2t1_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 0 12 11
      (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 0 4 8
       co2t1batch0
       (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 4 4 4
        co2t1batch1
        co2t1batch2))
      (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 12 4 7
       co2t1batch3
       (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 16 4 3
        co2t1batch4
        co2t1batch5)))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2Singletons : rangeCheck (singletonTest q2 2 11) 2 10 = true := by decide +kernel

lemma co2 : Imp [] 2 12 := imp_of (Or.inl rfl) co2_p (by norm_num) co2_id
    (Or.inr fun t ht => by
  by_cases small : t < 2
  · interval_cases t
    · exact co2t0
    · exact co2t1
  · exact singletonCertified co2Singletons (by omega) (by omega))

def q4 : List (ℕ × ℕ) := pr rt 4
lemma co4_p : pOk 4 q4 = true := by decide +kernel
lemma co4_id : ∀ a ∈ q4, Imp [] a.1 a.2 := by
  intro a ha
  unfold q4 pr at ha
  exact ir a (List.mem_of_mem_filter ha)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4Singletons : rangeCheck (singletonTest q4 4 10) 0 11 = true := by decide +kernel

lemma co4 : Imp [] 4 11 := imp_of (Or.inl rfl) co4_p (by norm_num) co4_id
    (Or.inr fun t ht => singletonCertified co4Singletons (by omega) (by omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co8_alignment : cofactorAlignment 4 8 0x1b300000000000000000000000000000000000000000006c40001ae00000000000000000000000000000000000002800000003580180000000000000000000000000000000680321a50d1809c33a3590000000000000000000000000000000000000000000000000199000000000000000000000000000000000000000000064c0000170000000000000000000000000000000002fc03d00000002f403c000000000000000000000000000aa000c2a003b09f80740744210000000000000000000000000001c000000011c000046422c35800000000000000000000000000000043804c10c0848d5c20c3fb0000000000000000000000000000000001f80f907b03cc6ac3e80000000000000000000000000006b034c0360c11aa8f2078a3bd0000000000000000000000000001800bc05c0b4000004c15c3a300000000000000000000000000015827c0180140458e000f83760000000000000000000000000000400086a235f01500846b8350000000000000000000000000001a70d787223831ad8d346e234c 1 = true := by decide +kernel

lemma co8 : Imp [] 8 11 :=
  imp_by_cofactor_symmetry (by decide +kernel) co8_alignment (by decide +kernel) (by decide +kernel) co4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co16_alignment : cofactorAlignment 2 16 0xa000000000000000006c40001ae0000000000000000000000000000000000000000000000000000000000000000500000fc0001a700000680321a50d1809c33a34100000000000000000000000000000000000000000000000000000000000000000000065c0001950000000000000000064c000017000000000000000000000000000000000000000000000000000000005a400016700000880000040aa000c2a003b09f807407442100000000000000000000000000000000000000000000000000000048000000037000044c020036000043804c10c0848cfc20c3fb000000000000000000000000000000000000000000000000000000000d402c0ef07683a81d00d906b034c0360c119e8f2078a3bd000000000000000000000000000000000000000000000000000000080b40000a80078cec058398015827c0180140458e000f837600000000000000000000000000000000000000000000000000000118ce00a43470278d1005233719b0e4c68c3831a1909466a334 2 = true := by decide +kernel

lemma co16 : Imp [] 16 12 :=
  imp_by_cofactor_symmetry (by decide +kernel) co16_alignment (by decide +kernel) (by decide +kernel) co2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co32_alignment : cofactorAlignment 1 32 0x2000000000000280000000358018000000000000500000fc0001a700000680321a50d1809c33a341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000182000000000003e00000002fc03d00000002f403c00005a400016700000880000040aa000c2a003b09f80740744210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a800000000e00000002040ff00000001f80f907b03cc67c3e800000d402c0ef07683a81d00d906b034c0360c119e8f2078a3bd00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012004801a33a01280180e0365004000867235f01500846b83500118ce00a43470278d1005233719b0d7868c3b61a18d3466a334 1 = true := by decide +kernel

lemma co32 : Imp [] 32 11 :=
  imp_by_cofactor_symmetry (by decide +kernel) co32_alignment (by decide +kernel) (by decide +kernel) co1

def q64 : List (ℕ × ℕ) := pr rt 64
lemma co64_p : pOk 64 q64 = true := by decide +kernel
lemma co64_id : ∀ a ∈ q64, Imp [] a.1 a.2 := by
  intro a ha
  unfold q64 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
def co64t0_cov : List (ℕ × ℕ) := [(0x0, 1), (0x1, 0), (0x2, 0), (0x40, 0), (0x80, 0), (0x400, 0), (0x1000, 0), (0x2000, 0), (0x10000, 0), (0x20000000, 0), (0x40000000, 0), (0x200000000, 0), (0x800000000, 0), (0x4000000000, 0), (0x8000000000, 0), (0x4000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000000000000000000, 0), (0x33dfbfefbfffffffffffffffffffffffffffffffffff359ffecb3c, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch0 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch1 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch2 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch3 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch4 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch5 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co64t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 0 a.1 a.2 = false :=
  restrictedWitness q64 64 0 co64t0_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 0 12 10
      (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 0 4 8
       co64t0batch0
       (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 4 4 4
        co64t0batch1
        co64t0batch2))
      (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 12 4 6
       co64t0batch3
       (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 16 4 2
        co64t0batch4
        co64t0batch5)))

def co64t1_cov : List (ℕ × ℕ) := [(0x0, 1), (0x1, 0), (0x2, 0), (0x40, 0), (0x80, 0), (0x400, 0), (0x1000, 0), (0x2000, 0), (0x10000, 0), (0x20000000, 0), (0x40000000, 0), (0x200000000, 0), (0x800000000, 0), (0x4000000000, 0), (0x8000000000, 0), (0x4000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000000000000000000, 0), (0x33dfbfefbfffffffffffffffffffffffffffffffffff359ffecb3c, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch0 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch1 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch2 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch3 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch4 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch5 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co64t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 1 a.1 a.2 = false :=
  restrictedWitness q64 64 1 co64t1_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 0 12 10
      (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 0 4 8
       co64t1batch0
       (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 4 4 4
        co64t1batch1
        co64t1batch2))
      (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 12 4 6
       co64t1batch3
       (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 16 4 2
        co64t1batch4
        co64t1batch5)))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64Singletons : rangeCheck (singletonTest q64 64 11) 2 10 = true := by decide +kernel

lemma co64 : Imp [] 64 12 := imp_of (Or.inl rfl) co64_p (by norm_num) co64_id
    (Or.inr fun t ht => by
  by_cases small : t < 2
  · interval_cases t
    · exact co64t0
    · exact co64t1
  · exact singletonCertified co64Singletons (by omega) (by omega))

def q128 : List (ℕ × ℕ) := pr rt 128
lemma co128_p : pOk 128 q128 = true := by decide +kernel
lemma co128_id : ∀ a ∈ q128, Imp [] a.1 a.2 := by
  intro a ha
  unfold q128 pr at ha
  exact ir a (List.mem_of_mem_filter ha)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128Singletons : rangeCheck (singletonTest q128 128 8) 0 9 = true := by decide +kernel

lemma co128 : Imp [] 128 9 := imp_of (Or.inl rfl) co128_p (by norm_num) co128_id
    (Or.inr fun t ht => singletonCertified co128Singletons (by omega) (by omega))

def rt1 : List (ℕ × ℕ) := [(1, 11), (2, 12), (4, 11), (8, 11), (16, 12), (32, 11), (64, 12), (128, 9)]
lemma i1 : ∀ a ∈ rt1, Imp [] a.1 a.2 := by
  intro a ha
  simp only [rt1, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact co1
  · exact co2
  · exact co4
  · exact co8
  · exact co16
  · exact co32
  · exact co64
  · exact co128
def pins4 : List (ℕ × ℕ) := [(525, 1), (533, 2), (537, 3), (540, 2), (549, 3), (553, 3), (556, 1), (561, 3), (564, 3), (568, 2), (581, 1), (585, 3), (588, 3), (593, 2), (596, 3), (600, 3), (609, 1), (612, 3), (616, 1), (624, 2), (645, 2), (649, 3), (652, 2), (657, 4), (660, 4), (664, 4), (673, 3), (676, 3), (680, 2), (688, 4), (705, 2), (708, 3), (712, 3), (720, 4), (736, 2), (780, 2), (788, 2), (792, 3), (804, 2), (808, 3), (816, 3), (836, 3), (840, 2), (848, 2), (864, 2), (900, 2), (904, 3), (912, 3), (928, 3), (960, 2), (1545, 3), (1553, 2), (1560, 2), (1569, 2), (1576, 2), (1584, 3), (1601, 2), (1608, 2), (1616, 3), (1632, 3), (1665, 2), (1672, 2), (1680, 3), (1696, 3), (1728, 3), (1800, 3), (1808, 3), (1824, 3), (1856, 3), (1920, 3), (2565, 2), (2577, 3), (2580, 2), (2593, 2), (2596, 3), (2608, 2), (2625, 3), (2628, 2), (2640, 3), (2656, 2), (2689, 3), (2692, 2), (2704, 3), (2720, 2), (2752, 3), (3585, 3), (3600, 3), (3616, 3), (3648, 3), (3712, 3), (4103, 2), (4107, 3), (4109, 1), (4110, 2), (4131, 3), (4133, 3), (4134, 3), (4137, 3), (4138, 2), (4140, 1), (4163, 2), (4165, 1), (4166, 3), (4169, 3), (4170, 3), (4172, 3), (4193, 1), (4194, 2), (4196, 3), (4200, 1), (4227, 4), (4229, 2), (4230, 4), (4233, 3), (4234, 4), (4236, 2), (4257, 3), (4258, 4), (4260, 3), (4264, 2), (4289, 2), (4290, 4), (4292, 3), (4296, 3), (4320, 2), (4358, 2), (4362, 3), (4364, 2), (4386, 3), (4388, 2), (4392, 3), (4418, 2), (4420, 3), (4424, 2), (4448, 2), (4482, 3), (4484, 2), (4488, 3), (4512, 3), (4544, 2), (5123, 2), (5129, 3), (5130, 2), (5153, 2), (5154, 3), (5160, 2), (5185, 2), (5186, 3), (5192, 2), (5216, 3), (5249, 2), (5250, 3), (5256, 2), (5280, 3), (5312, 3), (5378, 3), (5384, 3), (5408, 3), (5440, 3), (5504, 3), (6147, 3), (6149, 2), (6150, 2), (6177, 2), (6178, 2), (6180, 3), (6209, 3), (6210, 3), (6212, 2), (6240, 2), (6273, 3), (6274, 3), (6276, 2), (6304, 2), (6336, 3), (7169, 3), (7170, 3), (7200, 3), (7232, 3), (7296, 3), (8709, 3), (8713, 2), (8716, 2), (8721, 3), (8724, 3), (8728, 2), (8769, 2), (8772, 2), (8776, 3), (8784, 2), (8833, 3), (8836, 3), (8840, 2), (8848, 3), (8896, 2), (10753, 3), (10756, 3), (10768, 3), (10816, 3), (10880, 3), (12291, 3), (12293, 3), (12294, 3), (12297, 2), (12298, 2), (12300, 2), (12353, 2), (12354, 2), (12356, 2), (12360, 3), (12417, 3), (12418, 3), (12420, 3), (12424, 2), (12480, 2), (14337, 3), (14338, 3), (14340, 3), (14400, 3), (14464, 3), (16391, 3), (16395, 3), (16397, 5), (16398, 5), (16403, 3), (16405, 3), (16406, 5), (16409, 3), (16410, 5), (16412, 5), (16419, 3), (16421, 5), (16422, 3), (16425, 5), (16426, 3), (16428, 5), (16433, 3), (16434, 3), (16436, 3), (16440, 3), (16515, 1), (16517, 2), (16518, 2), (16521, 2), (16522, 2), (16524, 3), (16529, 1), (16530, 3), (16532, 2), (16536, 2), (16545, 3), (16546, 1), (16548, 2), (16552, 2), (16560, 1), (16646, 2), (16650, 2), (16652, 3), (16658, 3), (16660, 2), (16664, 2), (16674, 2), (16676, 3), (16680, 3), (16688, 2), (16770, 2), (16772, 3), (16776, 3), (16784, 2), (16800, 3), (16901, 2), (16905, 2), (16908, 3), (16913, 2), (16916, 3), (16920, 3), (16929, 3), (16932, 2), (16936, 2), (16944, 2), (17025, 2), (17028, 3), (17032, 3), (17040, 3), (17056, 2), (17156, 3), (17160, 3), (17168, 3), (17184, 3), (17280, 3), (20483, 2), (20485, 2), (20486, 3), (20489, 2), (20490, 3), (20492, 3), (20513, 3), (20514, 2), (20516, 2), (20520, 2), (20609, 2), (20610, 3), (20612, 3), (20616, 3), (20640, 2), (20738, 3), (20740, 3), (20744, 3), (20768, 3), (20864, 3), (24579, 2), (24581, 3), (24582, 2), (24585, 3), (24586, 2), (24588, 3), (24593, 2), (24594, 3), (24596, 2), (24600, 2), (24705, 3), (24706, 2), (24708, 3), (24712, 3), (24720, 2), (25089, 3), (25092, 3), (25096, 3), (25104, 3), (25216, 3), (28673, 3), (28674, 3), (28676, 3), (28680, 3), (28800, 3), (49155, 3), (49157, 3), (49158, 3), (49161, 3), (49162, 3), (49164, 3), (49169, 3), (49170, 3), (49172, 3), (49176, 3), (49185, 3), (49186, 3), (49188, 3), (49192, 3), (49200, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins4_ok : pins4.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma pins4_I : ∀ e ∈ pins4, Imp [] e.1 e.2 := okAll (T := []) pins4_ok (by simp)

def pins3 : List (ℕ × ℕ) := [(517, 3), (521, 4), (524, 3), (529, 5), (532, 5), (536, 5), (545, 4), (548, 4), (552, 3), (560, 5), (577, 3), (580, 4), (584, 4), (592, 5), (608, 3), (641, 5), (644, 5), (648, 5), (656, 7), (672, 5), (704, 5), (772, 3), (776, 4), (784, 4), (800, 4), (832, 3), (896, 4), (1537, 3), (1544, 3), (1552, 4), (1568, 4), (1600, 4), (1664, 4), (1792, 4), (2561, 4), (2564, 3), (2576, 4), (2592, 3), (2624, 4), (2688, 4), (3584, 4), (4099, 5), (4101, 3), (4102, 5), (4105, 4), (4106, 5), (4108, 3), (4129, 4), (4130, 5), (4132, 4), (4136, 3), (4161, 3), (4162, 5), (4164, 4), (4168, 4), (4192, 3), (4225, 5), (4226, 7), (4228, 5), (4232, 5), (4256, 5), (4288, 5), (4354, 4), (4356, 3), (4360, 4), (4384, 4), (4416, 3), (4480, 4), (5121, 3), (5122, 4), (5128, 3), (5152, 4), (5184, 4), (5248, 4), (5376, 4), (6145, 4), (6146, 4), (6148, 3), (6176, 3), (6208, 4), (6272, 4), (7168, 4), (8705, 4), (8708, 4), (8712, 3), (8720, 4), (8768, 3), (8832, 4), (10752, 4), (12289, 4), (12290, 4), (12292, 4), (12296, 3), (12352, 3), (12416, 4), (14336, 4), (16387, 4), (16389, 6), (16390, 6), (16393, 6), (16394, 6), (16396, 8), (16401, 4), (16402, 6), (16404, 6), (16408, 6), (16417, 6), (16418, 4), (16420, 6), (16424, 6), (16432, 4), (16513, 3), (16514, 3), (16516, 4), (16520, 4), (16528, 3), (16544, 3), (16642, 3), (16644, 4), (16648, 4), (16656, 3), (16672, 4), (16768, 4), (16897, 3), (16900, 4), (16904, 4), (16912, 4), (16928, 3), (17024, 4), (17152, 4), (20481, 3), (20482, 4), (20484, 4), (20488, 4), (20512, 3), (20608, 4), (20736, 4), (24577, 4), (24578, 3), (24580, 4), (24584, 4), (24592, 3), (24704, 4), (25088, 4), (28672, 4), (49153, 4), (49154, 4), (49156, 4), (49160, 4), (49168, 4), (49184, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins3_ok : pins3.all (fun e => okE [] (pr pins4 e.1) e) = true := by decide +kernel
lemma pins3_I : ∀ e ∈ pins3, Imp [] e.1 e.2 := okAll (T := pins4) pins3_ok pins4_I

def pins2 : List (ℕ × ℕ) := [(513, 6), (516, 6), (520, 6), (528, 8), (544, 6), (576, 6), (640, 8), (768, 5), (1536, 5), (2560, 5), (4097, 6), (4098, 8), (4100, 6), (4104, 6), (4128, 6), (4160, 6), (4224, 8), (4352, 5), (5120, 5), (6144, 5), (8704, 5), (12288, 5), (16385, 7), (16386, 7), (16388, 9), (16392, 9), (16400, 7), (16416, 7), (16512, 5), (16640, 5), (16896, 5), (20480, 5), (24576, 5), (49152, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins2_ok : pins2.all (fun e => okE [] (pr (pins3 ++ pins4) e.1) e) = true := by decide +kernel
lemma pins2_I : ∀ e ∈ pins2, Imp [] e.1 e.2 := okAll (T := (pins3 ++ pins4)) pins2_ok (apI pins3_I pins4_I)

def pins1 : List (ℕ × ℕ) := [(512, 9), (4096, 9), (16384, 10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins1_ok : pins1.all (fun e => okE [] (pr (pins2 ++ (pins3 ++ pins4)) e.1) e) = true := by decide +kernel
lemma pins1_I : ∀ e ∈ pins1, Imp [] e.1 e.2 := okAll (T := (pins2 ++ (pins3 ++ pins4))) pins1_ok (apI pins2_I (apI pins3_I pins4_I))

def pinsAll : List (ℕ × ℕ) := (pins1 ++ (pins2 ++ (pins3 ++ pins4)))
lemma pinsAll_I : ∀ e ∈ pinsAll, Imp [] e.1 e.2 := (apI pins1_I (apI pins2_I (apI pins3_I pins4_I)))
def pinsSelected : List (ℕ × ℕ) := pinsAll.filter (fun e => e.2 ≥ 7)
lemma pinsSelected_I : ∀ e ∈ pinsSelected, Imp [] e.1 e.2 := by
  intro e he
  unfold pinsSelected at he
  exact pinsAll_I e (List.mem_of_mem_filter he)

def rootBounds : List (ℕ × ℕ) := ((rt1 ++ rt).filter (fun a => a.2 ≥ 7)) ++ pinsSelected
lemma rootBounds_I : ∀ a ∈ rootBounds, Imp [] a.1 a.2 := by
  apply apI _ pinsSelected_I
  intro a ha
  exact apI i1 ir a (List.mem_of_mem_filter ha)
lemma rootBounds_p : pOk 0 rootBounds = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root0_res : chk [] rootBounds 0 13 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root1_res : chk [] rootBounds 0 13 1 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root2_res : chk [] rootBounds 0 13 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root3_res : chk [] rootBounds 0 13 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem irootSingletons : rangeCheck (singletonTest rootBounds 0 13) 4 10 = true := by decide +kernel

lemma iroot : Imp [] 0 14 := imp_ts (Or.inl rfl) rootBounds_p (by norm_num) rootBounds_I (fun t ht => by
  by_cases small : t < 4
  · interval_cases t
    · exact singletonCheck root0_res
    · exact singletonCheck root1_res
    · exact singletonCheck root2_res
    · exact singletonCheck root3_res
  · exact singletonCertified irootSingletons (by omega) (by omega))

def sampleWire (i : ℕ) : ℕ := rawP0.getD i 0 &&& mz 0

lemma sampleWire_ok (i : Fin 8) : sampleWire i.val ∈ WZ [] 0 := by
  refine ⟨rawP0.getD i.val 0,?_,rfl⟩
  apply List.mem_append_left
  have hh : i.val < rawP0.length := by simpa [rawP_len0] using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hh]
  exact List.getElem_mem _


lemma sampleWire_covers {s : ℕ} (hs : s ∈ WZ [] 0) : ∃ i : Fin 8, s = sampleWire i.val := by
  obtain ⟨w, hw, rfl⟩ := hs
  change w ∈ rawP0 ++ [] at hw
  rw [List.append_nil] at hw
  obtain ⟨i, rfl⟩ := rawP_mem_getD hw
  exact ⟨i, rfl⟩

def binaryRepresentatives : List (ℕ × ℕ) :=
  [(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,2),(1,4),(1,6),(1,7),(2,3),(2,6),(2,7),(6,7)]

def unaryRepresentatives : List ℕ := [0,1,2,6,7]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma binaryOrbit : ∀ i j : Fin 8, i ≠ j →
    ∃ a : Fin 4, ∃ p ∈ binaryRepresentatives,
      ((permuted a i).val = p.1 ∧ (permuted a j).val = p.2) ∨
      ((permuted a i).val = p.2 ∧ (permuted a j).val = p.1) := by decide +kernel

lemma unaryOrbit : ∀ i : Fin 8, ∃ a : Fin 4, (permuted a i).val ∈ unaryRepresentatives := by decide +kernel

def BinaryCertificates (reject : ℕ → ℕ → ℕ → List W → Bool) (Q : List (ℕ × ℕ)) : Prop :=
    ∀ p ∈ binaryRepresentatives, ∃ H : ℕ,
      hb H (sampleWire p.1 + sampleWire p.2) = true ∧ chkRaw reject [] Q 0 14 1 H 0 = false

def UnaryCertificates : Prop :=
    ∀ (i : Fin 8), i.val ∈ unaryRepresentatives →
    ∀ (k : ℕ), k ≤ 13 →
    ∀ S : Finset ℕ, (S : Set ℕ) ⊆ insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)) →
      Live Z0 (mz 0) (tz 0) k 0 S → False

lemma fullLower (lower : Imp [] 0 14) {k : ℕ} (hk : k < 14)
    (hl : Sol Z0 fullMask fullTarget k (C fullMask fullStock)) : False :=
  lower k hk ((hl.mapSignals (pull 0) (pull_target 0) (pull_neg 0) (pull_op 0)).mono le_rfl (pull_initial 0))

-- Store one active position per sampled assignment.
def rootSamplePositions : ℕ := 0x1b30000000000000000000000000a000000000000000006c40001ae0000000000000000000000002000000000000280000000358018000000000000500000fc0001a700000680321a50d1809c33a3410038000000000000000000019b000000000000000000000001990000000000000000065c0001950000000000000000064c0000170000000000182000000000003e00000002fc03d00000002f403c00005a400016700000880000040aa000c2a003b09f807407442100000e401600000e000000011e01c000000011c000046422c3400048000000037000044c020036000043804c10c0848cfc20c3fb00a800000000e00000002040ff00000001f80f907b03cc67c3e800000d402c0ef07683a81d00d906b034c0360c119e8f2078a3bd00f80d006603200f00c402233c01800bc05c0b4000004c15c3a300080b40000a80078cec058398015827c0180140458e000f8376012004801a33a01280180e0365004000867235f01500846b83500118ce00a43470278d1005233719b0d7868c3831a18d3466a334

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootSampleAlignment : ∀ a : Fin 4, cofactorAlignment 0 0 rootSamplePositions a = true := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma sampleUnaryBySymmetry (certs : UnaryCertificates) (i : Fin 8) {n : ℕ} (hn : n ≤ 13)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)))
    (live : Live Z0 (mz 0) (tz 0) n 0 S) : False := by
  obtain ⟨a,representative⟩ := unaryOrbit i
  obtain ⟨target,neg,bin,initial,wire⟩ :=
    cofactorMaps sampleMaskBound (rootSampleAlignment a) EF_ok EF_ok
  obtain ⟨q,t,ht,hq,V,hV,hLive⟩ := live.mapSignals _ target neg bin
  have ht0 : t = 0 := by omega
  subst t
  refine certs (permuted a i) representative q (by omega) V ?_ hLive
  intro w hw
  obtain ⟨w',hw',rfl⟩ := hV hw
  rcases hS hw' with rfl | stock
  · exact Or.inl (by simp only [sampleWire, neg, wire])
  · exact Or.inr (initial ⟨w',stock,rfl⟩)

set_option maxHeartbeats 0 in
lemma projectBinary {Q : List (ℕ × ℕ)} {reject : ℕ → ℕ → ℕ → List W → Bool}
    (valid : RejectSound true (RZ [] 0) (mz 0) (tz 0) reject) (pQ : pOk 0 Q = true)
    (lowerQ : ∀ e ∈ Q, Imp [] e.1 e.2) (lower : Imp [] 0 14)
    (certs : BinaryCertificates reject Q) (unary : UnaryCertificates)
    {d : Bool} {i j : Fin 8} (hij : i ≠ j) (U : Finset ℕ) (hU : (U : Set ℕ) ⊆ C fullMask fullStock)
    (tail : Live Z0 fullMask fullTarget 13 1 (insert (op d (fullWire i) (fullWire j)) U)) :
    False := by
  obtain ⟨a,p,hp,hor⟩ := binaryOrbit i j hij
  obtain ⟨H,hhash,hchk⟩ := certs p hp
  let x := sampleWire (permuted a i).val
  let y := sampleWire (permuted a j).val
  let z := op d x y
  have px : pull a (fullWire i) = x := pull_fullWire _ _
  have py : pull a (fullWire j) = y := pull_fullWire _ _
  have pz : pull a (op d (fullWire i) (fullWire j)) = z := by rw [pull_op,px,py]
  have hx : x ∈ WZ [] 0 := sampleWire_ok (permuted a i)
  have hy : y ∈ WZ [] 0 := sampleWire_ok (permuted a j)
  have hash : hb H (x+y) = true := by
    rcases hor with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · simpa only [x,y,hi,hj] using hhash
    · simpa only [x,y,hi,hj,Nat.add_comm] using hhash
  obtain ⟨k,t,ht,hk,V,hV,hLive⟩ := tail.mapSignals (pull a) (pull_target a) (pull_neg a) (pull_op a)
  have kle : k ≤ 13 := by omega
  have lift : (V : Set ℕ) ⊆ insert z (C (mz 0) (WZ [] 0)) := by
    intro u hu
    obtain ⟨w,hw,rfl⟩ := hV hu
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Or.inl pz
    · exact Or.inr (pull_initial a ⟨w, hU hw, rfl⟩)
  have hUsed : z ∈ V := by
    by_contra hz
    refine lower k (by omega) (hLive.sol.mono le_rfl ?_)
    intro u hu
    exact (lift hu).resolve_left (fun eq => hz (eq ▸ hu))
  have hne : x ≠ y := by
    intro eq
    have heq : z = y := by rw [show z=op d x y from rfl,eq,op_self]
    refine lower k (by omega) (hLive.sol.mono le_rfl ?_)
    intro u hu
    rcases lift hu with h | h
    · exact Or.inl (h.trans heq ▸ hy)
    · exact h
  let U' := V.erase z
  let S := insert x (insert y U')
  have hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) := by
    intro u hu
    simp only [S, U', Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hu
    rcases hu with rfl | rfl | ⟨hne,hm⟩
    · exact Or.inl hx
    · exact Or.inl hy
    · exact (lift hm).resolve_left hne
  have hIns : insert z U' = V := Finset.insert_erase hUsed
  have hTail : Live Z0 (mz 0) (tz 0) k t (insert (op d x y) U') := by
    change Live Z0 (mz 0) (tz 0) k t (insert z U')
    rw [hIns]
    exact hLive
  have hNew := Live.bi (d := d) hne (al0 _ _ _) hTail
  have hSize : k = 13 := by
    by_contra hc
    exact lower (k+1) (by omega) (hNew.sol.mono le_rfl hS)
  have hNot : t = 1 := by omega
  subst k
  subst t
  refine imp_of_bi (L := 15) valid pQ (by decide) lowerQ (by decide) hS hNew hx hy
    ⟨hne,U',rfl,rfl,al0 _ _ _⟩ hTail hash (fun _ h => lower _ h) ?_ (by decide) hchk
  intro a ha n hn V hV hl
  obtain ⟨i, rfl⟩ := sampleWire_covers ha
  exact sampleUnaryBySymmetry unary i (by omega) hV hl

lemma projectUnary (certs : UnaryCertificates) {i : Fin 8} (U : Finset ℕ)
    (hU : (U : Set ℕ) ⊆ C fullMask fullStock)
    (tail : Live Z0 fullMask fullTarget 13 0 (insert (fullWire i ^^^ fullMask) U)) : False := by
  obtain ⟨a,ha⟩ := unaryOrbit i
  obtain ⟨k,t,ht,hk,V,hV,hLive⟩ := tail.mapSignals (pull a) (pull_target a) (pull_neg a) (pull_op a)
  have ht : t = 0 := by omega
  subst t
  refine certs (permuted a i) ha k (by omega) V ?_ hLive
  intro u hu
  obtain ⟨w,hw,rfl⟩ := hV hu
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Or.inl (by rw [pull_neg, pull_fullWire]; rfl)
  · exact Or.inr (pull_initial a ⟨w,hU hw,rfl⟩)

set_option maxHeartbeats 0 in
theorem fullExclusion {Q : List (ℕ × ℕ)} {reject : ℕ → ℕ → ℕ → List W → Bool}
    (valid : RejectSound true (RZ [] 0) (mz 0) (tz 0) reject) (pQ : pOk 0 Q = true)
    (lowerQ : ∀ e ∈ Q, Imp [] e.1 e.2) (lower : Imp [] 0 14)
    (bin : BinaryCertificates reject Q) (un : UnaryCertificates)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C fullMask fullStock)
    (live : Live Z0 fullMask fullTarget 14 1 S) : False := by
  have min : Min Z0 fullMask fullTarget 14 1 S := ⟨live, fun q hq proof =>
    fullLower lower hq (proof.mono le_rfl (fun x hx => hx.elim (fun a => hS a) Or.inr))⟩
  have hnonzero : fullTarget ≠ 0 := by decide +kernel
  have hnonall : fullTarget ≠ fullMask := by decide +kernel
  obtain ⟨h0,h1⟩ := min.proper fullTarget_mask hnonzero hnonall fun _ hm => fullStock_mask (hS hm)
  have real : ∀ x ∈ S, x ∈ fullStock := by
    intro x hx
    rcases hS hx with hx | hx'
    · exact hx
    · simp at hx'
      rcases hx' with rfl | rfl
      · exact (h0 hx).elim
      · exact (h1 hx).elim
  cases live with
  | @un _ _ a U tail =>
    obtain ⟨i,hi⟩ := fullStock_rows (real a (Finset.mem_insert_self _ _))
    exact projectUnary un U (fun _ hu => hS (Finset.mem_insert_of_mem hu)) (hi ▸ tail)
  | @bi _ _ d a b U hab hal tail =>
    obtain ⟨i,hi⟩ := fullStock_rows (real a (by simp))
    obtain ⟨j,hj⟩ := fullStock_rows (real b (by simp))
    refine projectBinary valid pQ lowerQ lower bin un (d := d) (i := i) (j := j) ?_ U (fun _ hu => hS (by simp [hu])) ?_
    · intro he
      exact hab (hi.trans (he ▸ hj.symm))
    · rw [← hi, ← hj]
      exact tail

def unaryBounds (Q : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  Q.filter fun e =>
    let signal := xw (i,0) &&& mz e.1
    Nat.beq signal 0 || Nat.beq signal (mz e.1)

lemma unary_restriction {Q : List (ℕ × ℕ)} (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (i : ℕ) : ∀ e ∈ unaryBounds Q i, Imp [(i,0)] e.1 e.2 := by
  intro e he k hk hSol
  obtain ⟨inside, hconst⟩ := List.mem_filter.mp he
  simp only [Bool.or_eq_true, Nat.beq_eq] at hconst
  apply hQ e inside k hk
  refine hSol.mono le_rfl ?_
  rintro r (hr | hr)
  · obtain ⟨w,hw,rfl⟩ := hr
    simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩
    · rcases hconst with h | h
      · rw [h]
        exact Or.inr (Set.mem_insert _ _)
      · rw [h]
        exact Or.inr (Set.mem_insert_of_mem _ rfl)
  · exact Or.inr hr

lemma unary_augmented {i : Fin 8}
    (heq : xw (i.val,0) &&& mz 0 = sampleWire i.val ^^^ mz 0) :
    C (mz 0) (WZ [(i.val,0)] 0) ⊆ insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)) := by
  rintro r (hr | hr)
  · obtain ⟨w,hw,rfl⟩ := hr
    simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩)
    · exact Or.inl heq
  · exact Or.inr (Or.inr hr)

lemma unary_ready {i : Fin 8}
    (heq : xw (i.val,0) &&& mz 0 = sampleWire i.val ^^^ mz 0) :
    insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)) ⊆ C (mz 0) (WZ [(i.val,0)] 0) := by
  rintro r (rfl | (hr | hr))
  · exact Or.inl ⟨xw (i.val,0),List.mem_append_right _ (by simp),heq.symm⟩
  · obtain ⟨w,hw,rfl⟩ := hr
    simp [rawL] at hw
    exact Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩
  · exact Or.inr hr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def unaryConstant (i z : ℕ) : Bool :=
  let signal := xw (i,0) &&& mz z
  signal == 0 || signal == mz z

def unaryCharge (i : ℕ) (e : ℕ × ℕ) : ℕ × ℕ :=
  if unaryConstant i e.1 then e else (e.1,e.2 - 1)

def unaryBoundsStrong (Q : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  Q.map (unaryCharge i)

lemma unaryCharge_fst (i : ℕ) (e : ℕ × ℕ) : (unaryCharge i e).1 = e.1 := by
  by_cases h : unaryConstant i e.1 = true <;> simp [unaryCharge,h]

lemma unary_pos_strong (Q : List (ℕ × ℕ)) (hp : pOk 0 Q = true) (i : ℕ) :
    pOk 0 (unaryBoundsStrong Q i) = true := by
  simp only [pOk, Bool.and_eq_true, List.all_eq_true] at hp ⊢
  refine ⟨hp.1,?_⟩
  intro e he
  obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp he
  simp only [unaryCharge_fst]
  exact hp.2 original hOriginal

lemma unary_augmented_at {i : Fin 8} (z : ℕ)
    (heq : xw (i.val,0) &&& mz z = (rawP0.getD i.val 0 &&& mz z) ^^^ mz z) :
    C (mz z) (WZ [(i.val,0)] z) ⊆
      insert ((rawP0.getD i.val 0 &&& mz z) ^^^ mz z) (C (mz z) (WZ [] z)) := by
  rintro r (hr | hr)
  · obtain ⟨w,hw,rfl⟩ := hr
    simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩)
    · exact Or.inl heq
  · exact Or.inr (Or.inr hr)

set_option maxHeartbeats 0 in
lemma unary_restriction_strong {Q : List (ℕ × ℕ)} (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (i : Fin 8)
    (hEq : ∀ e ∈ Q, xw (i.val,0) &&& mz e.1 = (rawP0.getD i.val 0 &&& mz e.1) ^^^ mz e.1) :
    ∀ e ∈ unaryBoundsStrong Q i.val, Imp [(i.val,0)] e.1 e.2 := by
  intro e he
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
  by_cases hc : unaryConstant i.val original.1 = true
  · simp only [unaryCharge,hc,ite_true]
    apply unary_restriction hQ i.val original
    apply List.mem_filter.mpr
    exact ⟨ho,hc⟩
  · have hoff := Bool.eq_false_iff.mpr hc
    simp only [unaryCharge,hoff,Bool.false_eq_true,ite_false]
    intro k hk hs
    have raw : rawP0.getD i.val 0 &&& mz original.1 ∈ C (mz original.1) (WZ [] original.1) := by
      exact Or.inl ⟨rawP0.getD i.val 0,List.mem_append_left _ (rawP_getD_mem i),rfl⟩
    exact hQ original ho (k+1) (by omega) (.un raw (hs.mono le_rfl (unary_augmented_at _ (hEq original ho))))

set_option maxHeartbeats 0 in
theorem build_unary_strong_certificates {Q : List (ℕ × ℕ)}
    (pQ : pOk 0 Q = true) (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (lower : Imp [] 0 14)
    (hSix : ∀ i ∈ unaryRepresentatives, (i,0) ∈ six)
    (hEq : ∀ i : Fin 8, xw (i.val,0) &&& mz 0 = sampleWire i.val ^^^ mz 0)
    (hCut : ∀ i : Fin 8, i.val ∈ unaryRepresentatives →
      ∀ e ∈ Q, xw (i.val,0) &&& mz e.1 = (rawP0.getD i.val 0 &&& mz e.1) ^^^ mz e.1)
    (hChk : ∀ i ∈ unaryRepresentatives, chk [(i,0)] (unaryBoundsStrong Q i) 0 13 0 FF 1 = false) :
    UnaryCertificates := by
  intro i hi k hk S hS hLive
  have raw : sampleWire i.val ∈ C (mz 0) (WZ [] 0) := Or.inl (sampleWire_ok i)
  by_cases hm : k < 13
  · exact lower (k+1) (by omega) (.un raw (hLive.sol.mono le_rfl hS))
  have kEq : k = 13 := by omega
  subst k
  refine imp_of_live (L := 14) (Or.inr ⟨(i.val,0),hSix _ hi,rfl,lower⟩)
    (unary_pos_strong Q pQ _) (by decide) (unary_restriction_strong hQ i (hCut i hi)) (by decide)
    (hS.trans (unary_ready (hEq i))) hLive ?_ (Or.inr (one (hChk _ hi)))
  intro q hq hSol
  exact lower (q+1) (by omega) (.un raw (hSol.mono le_rfl (unary_augmented (hEq i))))

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
      cases ha : Nat.beq (Nat.mul da dc) 0
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
      (bif Nat.ble v.length 1 then true else
        tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y)) := by
  change Bool.rec (motive := fun _ => Bool)
      (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y) true
          (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1) = _
  simp only [bR]


lemma look1RawC_step (reject : ℕ → ℕ → ℕ → List W → Bool) (nn aa hx hy l m g K fuel k t z : ℕ) (v : List W) :
    look1RawC reject nn aa hx hy true l m g K fuel.succ k t z v =
      (bif reject k t z v then false else bif Nat.ble v.length 1 then true else
        tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC nn (look1RawC reject nn aa hx hy true l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else mvRawC nn aa hx hy true (lookRawC nn aa hx hy true l m g K) l m g k t z v y)) := by
  change (bif reject k t z v then false else Bool.rec (motive := fun _ => Bool)
      (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvRawC nn aa hx hy true (lookRawC nn aa hx hy true l m g K) l m g k t z v y) true
          (nodeC nn (look1RawC reject nn aa hx hy true l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) = _
  simp only [bR]


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

def rootPreparedWords : List W := [
  ⟨0x7fffefc0000000000000000000000000000000000000000000000000000000000000000000000000084a2400300000180000c00006000300060000000000000000040000040000000000008000200000000200000200000000000000000007ff80fdfc007f0010fe0021fc004203f80087f0010847f0010fe002109fc004211fc004211091f80ad6ab6aabfff555fffaafffd57ffebfff7ffe00000000000000000000000000000000000000000000000000000000fc000185278004b9, 0x42000000004010000008000000000042000000000000000000000000000800000000, 0x0, 0x42000000004010000008000000000042000000000000000000000000000800000000, 3⟩,
  ⟨0x7fffe01ffff7fffdeffffbdffff7bd80000000000000000000000000000000000000000000000000ad6ab6002f0000178000bc0005e002f005e0096d256c524d8297e00927e00000000000f8003e00000003e00003e0000000000000000007e0600103f040fc1e81f83d03f07bd80700000e0080000e00801c010000380210803802108000060ad6ab60000000000000000000000000000000d6db56d5b6daad7ffedb7ffe0000000000000000000000000000000083e001c11f614e20, 0x421080000000108421080000000000000000000040000000, 0x800108421080000040000000000000000000000000000000000000000000000000000, 0x800108421080000040000421080000000108421080000000000000000000040000000, 3⟩,
  ⟨0x1ffff7fffde00000000000003fffef7fffdef7000000000000000000000000000000000000a40000aa8ce0000660003300019800cc01980d69b548000000031800031809a2692510670119c00000019800019800000000000000000410188183cc60f31e410600820c010304f8f609f1ef7401c00803808810070100100701084809018ac0000aabfff0000000000000000000000000d6db56c00000000000000000dab6db55afffdbfff00000000000000003dff840d09b9e83, 0x100000000000000000400004200000100000004210840000000000000002000000, 0x0, 0x100000000000000000400004200000100000004210840000000000000002000000, 3⟩,
  ⟨0x1ffff000000ffffbc00000003fffef000000007fffdeffffbdec0000000000000000000000812000a00a9855455c002ac0015600ab01560d4c00015b690002960002960d2b4c000054c015304d34915700015600000000000000000208044143c2108080a1e13c4102200284e4f1010804030939e61273dec800c0080800c0800440804816000a00000555fff8000000000000000000d6c00015b6d8000000000000dab6c0000000000006db6dbfff000000731fc533d12e69c4, 0x2008000000000800008020000010840008000004000002108400000000000100000, 0x40000000004200002000000000000000000000000000000000000000000000000000, 0x42008000004200802008020000010840008000004000002108400000000000100000, 3⟩,
  ⟨0x7fffc0000001ffff7800000007fffc0f000000000000001ffff03c1ffff7801ec00002000900885460002a322152940a98854e0a9802184600004a2c1494d814980802184582a318a8c208248a8e618a9400000000000000000410408088242f0800421050ba2780010442429c80f0020284040304244a4e03c0294e7801ec01042000b008800000000022000140000bfff00000618460000da2c0000d80000180618458000180006186dbfff6180008333acbef42c83ce, 0x40000001000200000008020000010802000001000000800008001004010000000020, 0x2000000000010800100000000000000000000000000000000000000000000000000, 0x42000001000210800108020000010802000001000000800008001004010000000020, 3⟩,
  ⟨0xffff81ffff03c00000000000000000000ffff81e000000001ffff03c1e1c00001008200030a044189000c49106288314062c0040024430c0210c24c30c280080400421850861604161862424862600000000000000000208a04044501114283e28107a503c0082a101054211010542432e81e004130844255b03c1e1c08a0100860000000440000000011000080007ffe00c006c430c0210000c300000280c05420001bfff0c36180006dbfff05095e78da63bb83, 0x80000000000000084200000000000080000040000400080210000000001, 0x0, 0x80000000000000084200000000000080000040000400080210000000001, 3⟩,
  ⟨0x3fffe07fffde007fffde00000001ffff7bdc000000000000000000008a00d45000722a03b0001d000e801d04009001080028401d80001d0da001b50006a001a869a0001c84901d800000000000000001044220222108484810909020c1109246e2048dc5e0028d35e10848040634b7bdc420300402044420008008a00005000002afffc0000000000000c01b00158002ad7ffe000000da001b500000000006db0000006dbfffc2fe323dd067eef3, 0x800000400000000000000001084010000000400000200002000021080000000008000, 0x0, 0x800000400000000000000001084010000000400000200002000021080000000008000, 3⟩,
  ⟨0x7fffc0ffffbc01ffff7801ffff7bdc00000000000000001e45001b2800e95007c003c007800000010120280007449007c40900904a00f8003c6c06c006c6c0074000000000000000008230101118042604084c081038084821904042a042224bb0049763c0052ea780031ea7bdc00023000020000000045000028000157ffe00000000100050103602800000db7ffec0b01b05afffc00006c06c00006c00002bbde9588e747baf, 0x800000020000000000000401000200800000020000010000100020004200000000400, 0x0, 0x800000020000000000000401000200800000020000010000100020004200000000400, 3⟩]
def rootPreparedMask : ℕ := 0x7fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfff00000000000000007fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfffffffffffffffffff
def rootPreparedSlots : ℕ := 0x8421084210842108421084210842108421084210842108421084210842108421084210
def rootPreparedBudget : ℕ := 0xb5ef7bd6b7bdad6b52b5bdaf6b5ef7bdef5ad6b5adad5b5ad6a5ad6adad6aca729ce53

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

noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

abbrev SearchState := ℕ × List W

-- A renaming that is injective on the generated signals preserves the exact live stock.
lemma Live.renameOn {m T k t : ℕ} {S : Finset ℕ} (live : Live Z0 m T k t S)
    {D : Set ℕ} (inside : (S : Set ℕ) ⊆ D)
    (closedNeg : ∀ a ∈ D, a ^^^ m ∈ D)
    (closedOp : ∀ d a b, a ∈ D → b ∈ D → op d a b ∈ D)
    (f : ℕ → ℕ) (injective : Set.InjOn f D) (target : f T = T)
    (neg : ∀ a, f (a ^^^ m) = f a ^^^ m)
    (bin : ∀ d a b, f (op d a b) = op d (f a) (f b)) :
    Live Z0 m T k t (S.image f) := by
  induction live with
  | stop => simpa [Finset.image_singleton, target] using (Live.stop (R := Z0) (m := m) (T := T))
  | @un k t a U next ih =>
    have fromD : ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ) ⊆ D := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact closedNeg a (inside (by simp))
      · exact inside (by simp [hx])
    rw [Finset.image_insert]
    refine Live.un ?_
    simpa only [Finset.image_insert, neg] using ih fromD
  | @bi k t d a b U distinct _ next ih =>
    have aD : a ∈ D := inside (by simp)
    have bD : b ∈ D := inside (by simp)
    have fromD : ((insert (op d a b) U : Finset ℕ) : Set ℕ) ⊆ D := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact closedOp d a b aD bD
      · exact inside (by simp [hx])
    rw [Finset.image_insert, Finset.image_insert]
    refine Live.bi (d := d) (fun eq => distinct (injective aD bD eq)) (al0 _ _ _) ?_
    simpa only [Finset.image_insert, bin] using ih fromD

abbrev rotateSample (a : Fin 4) := cofactorPull 0 rootSamplePositions a

lemma rotation_target (a : Fin 4) : rotateSample a (tz 0) = tz 0 :=
  (cofactorMaps sampleMaskBound (rootSampleAlignment a) EF_ok EF_ok).1

lemma rotation_neg (a : Fin 4) (w : ℕ) :
    rotateSample a (w ^^^ mz 0) = rotateSample a w ^^^ mz 0 :=
  (cofactorMaps sampleMaskBound (rootSampleAlignment a) EF_ok EF_ok).2.1 w

lemma rotation_op (a : Fin 4) (d : Bool) (w w' : ℕ) :
    rotateSample a (op d w w') = op d (rotateSample a w) (rotateSample a w') :=
  (cofactorMaps sampleMaskBound (rootSampleAlignment a) EF_ok EF_ok).2.2.1 d w w'

lemma rotation_wire (a : Fin 4) (i : Fin 8) :
    rotateSample a (sampleWire i.val) = sampleWire (permuted a i).val :=
  (cofactorMaps sampleMaskBound (rootSampleAlignment a) EF_ok EF_ok).2.2.2.2 i

lemma rotation_zero (a : Fin 4) : rotateSample a 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  change (cofactorPull 0 rootSamplePositions a 0).testBit k = _
  rw [cofactorPull_bit sampleMaskBound]
  simp

lemma rotation_mask (a : Fin 4) : rotateSample a (mz 0) = mz 0 := by
  simpa only [Nat.zero_xor, rotation_zero] using rotation_neg a 0

inductive SampleSignal : ℕ → Prop where
  | raw (i : Fin 8) : SampleSignal (sampleWire i.val)
  | zero : SampleSignal 0
  | full : SampleSignal (mz 0)
  | neg {w : ℕ} : SampleSignal w → SampleSignal (w ^^^ mz 0)
  | gate {w w' : ℕ} (d : Bool) : SampleSignal w → SampleSignal w' → SampleSignal (op d w w')

lemma rotation_involutive_on {w : ℕ} (a : Fin 4) (generated : SampleSignal w) :
    rotateSample a (rotateSample a w) = w := by
  have permutes : ∀ i : Fin 8, permuted a (permuted a i) = i := by
    fin_cases a <;> decide
  induction generated with
  | raw i => simp only [rotation_wire, permutes]
  | zero => simp only [rotation_zero]
  | full => simp only [rotation_mask]
  | neg _ ih => simp only [rotation_neg, ih]
  | gate d _ _ ih₁ ih₂ => simp only [rotation_op, ih₁, ih₂]

lemma rotation_injective (a : Fin 4) : Set.InjOn (rotateSample a) {w | SampleSignal w} := by
  intro x hx y hy he
  have same := congrArg (rotateSample a) he
  rwa [rotation_involutive_on a hx, rotation_involutive_on a hy] at same

lemma rotation_bank (a : Fin 4) {x : ℕ} (hx : x ∈ WZ [] 0) : rotateSample a x ∈ WZ [] 0 := by
  obtain ⟨i, rfl⟩ := sampleWire_covers hx
  rw [rotation_wire]
  exact sampleWire_ok (permuted a i)

set_option maxRecDepth 100000 in
lemma Live.rotateStock {k t : ℕ} {S : Finset ℕ} (live : Live Z0 (mz 0) (tz 0) k t S)
    (inside : ∀ x ∈ S, SampleSignal x) (a : Fin 4) :
    Live Z0 (mz 0) (tz 0) k t (S.image (rotateSample a)) :=
  live.renameOn (D := {w | SampleSignal w}) (fun x hx => inside x hx)
    (fun _ hx => SampleSignal.neg hx) (fun d _ _ hx hy => SampleSignal.gate d hx hy)
    (rotateSample a) (rotation_injective a) (rotation_target a) (rotation_neg a) (rotation_op a)

lemma bankSampleSignal {x : ℕ} (hx : x ∈ WZ [] 0) : SampleSignal x := by
  obtain ⟨i,rfl⟩ := sampleWire_covers hx
  exact SampleSignal.raw i

lemma rotation_generated {x : ℕ} (a : Fin 4) (hx : SampleSignal x) : SampleSignal (rotateSample a x) := by
  induction hx with
  | raw i => rw [rotation_wire]; exact SampleSignal.raw (permuted a i)
  | zero => rw [rotation_zero]; exact SampleSignal.zero
  | full => rw [rotation_mask]; exact SampleSignal.full
  | neg _ ih => rw [rotation_neg]; exact SampleSignal.neg ih
  | gate d _ _ ih₁ ih₂ => rw [rotation_op]; exact SampleSignal.gate d ih₁ ih₂

def rotationStock (a : Fin 4) (S : Finset ℕ) := S.image (rotateSample a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rotateAvailable (a : Fin 4) {S : Finset ℕ}
    (inside : ∀ x ∈ S, SampleSignal x) {x : ℕ}
    (available : x ∈ C (mz 0) (WZ [] 0 ∪ (rotationStock a S : Set ℕ))) :
    rotateSample a x ∈ C (mz 0) (WZ [] 0 ∪ (S : Set ℕ)) := by
  rcases available with (raw | stock) | constant
  · exact Or.inl (Or.inl (rotation_bank a raw))
  · obtain ⟨original, member, rfl⟩ := Finset.mem_image.mp stock
    rw [rotation_involutive_on a (inside original member)]
    exact Or.inl (Or.inr member)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at constant
    rcases constant with rfl | rfl
    · rw [rotation_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [rotation_mask]; exact Or.inr (Set.mem_insert_of_mem _ rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rotatedStockGenerated (a : Fin 4) {S : Finset ℕ}
    (inside : ∀ x ∈ S, SampleSignal x) {x : ℕ}
    (available : x ∈ C (mz 0) (WZ [] 0 ∪ (rotationStock a S : Set ℕ))) : SampleSignal x := by
  rcases available with (raw | stock) | constant
  · exact bankSampleSignal raw
  · obtain ⟨original, member, rfl⟩ := Finset.mem_image.mp stock
    exact rotation_generated a (inside original member)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at constant
    rcases constant with rfl | rfl
    · exact SampleSignal.zero
    · exact SampleSignal.full

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rotateShortExclusion (a : Fin 4) {S : Finset ℕ} {k : ℕ}
    (inside : ∀ x ∈ S, SampleSignal x)
    (short : ∀ q < k, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) ({x | RZ [] 0 x ≠ 0} ∪ (S : Set ℕ)))) :
    ∀ q < k, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) ({x | RZ [] 0 x ≠ 0} ∪ (rotationStock a S : Set ℕ))) := by
  rw [RZ_set] at short ⊢
  intro q hq sol
  have renamed := sol.mapSignals (rotateSample a) (rotation_target a) (rotation_neg a) (rotation_op a)
  apply short q hq (renamed.mono le_rfl ?_)
  intro w h
  obtain ⟨x,hx,eq⟩ := h
  rw [← eq]
  exact rotateAvailable a inside hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rotateRawMode (a : Fin 4) {S : Finset ℕ} {k t : ℕ}
    (inside : ∀ x ∈ S, SampleSignal x)
    (ready : RawMode true (RZ [] 0) (mz 0) (tz 0) k t S) :
    RawMode true (RZ [] 0) (mz 0) (tz 0) k t (rotationStock a S) := by
  obtain ⟨limit,exclusion⟩ := ready rfl
  intro _
  refine ⟨limit, fun ht => ?_⟩
  have source := exclusion ht
  unfold RawNegExcluded at source ⊢
  intro x hraw n hn V available live
  have xBank : x ∈ WZ [] 0 := by
    rw [← RZ_set]
    exact hraw
  have rotatedRaw : RZ [] 0 (rotateSample a x) ≠ 0 := by
    have bank := rotation_bank a xBank
    rw [← RZ_set] at bank
    exact bank
  rw [RZ_set] at source available
  have gen (w : ℕ) (hw : w ∈ V) : SampleSignal w := by
    rcases available hw with eq | stock
    · rw [eq]; exact SampleSignal.neg (bankSampleSignal xBank)
    · exact rotatedStockGenerated a inside stock
  refine source _ rotatedRaw n hn (rotationStock a V) ?_ (live.rotateStock gen a)
  intro w hw
  obtain ⟨old, mem, rfl⟩ := Finset.mem_image.mp hw
  rcases available mem with rfl | stock
  · exact Or.inl (rotation_neg a x)
  · exact Or.inr (rotateAvailable a inside stock)

structure InputGate where
  disj : Bool
  left : W
  right : W

def InputGate.output (g : InputGate) : W := opW g.disj g.left g.right

def InputGate.eliminated (g : InputGate) (j : ℕ) : Bool :=
  (g.left.c ||| g.right.c).testBit (5*j)

def projectedCost (gates : List InputGate) (j : ℕ) : ℕ :=
  (gates.filter fun gate => !(gate.eliminated j)).length

def gateProjection (mask : ℕ) (gates : List InputGate) : Set ℕ :=
  {x | ∃ gate ∈ gates, x = gate.output.s &&& mask}

lemma extendCofactor {P : List ℕ} {T q j : ℕ} (valid : j < P.length)
    (gates : List InputGate) {bank : Set ℕ}
    (facts : ∀ g ∈ gates, WOk P g.left ∧ WOk P g.right ∧ g.left.s ∈ bank ∧ g.right.s ∈ bank)
    {base : Set ℕ} (lift : ∀ x ∈ bank, x &&& P.getD j 0 ∈ base)
    (zero : 0 ∈ base) (mask : P.getD j 0 ∈ base)
    (sol : Sol Z0 (P.getD j 0) T q (base ∪ gateProjection (P.getD j 0) gates)) :
    Sol Z0 (P.getD j 0) T (q + projectedCost gates j) base := by
  induction gates generalizing base with
  | nil => simpa [gateProjection, projectedCost] using sol
  | cons g rest ih =>
    have root := facts g (by simp)
    have remaining : ∀ gate ∈ rest, WOk P gate.left ∧ WOk P gate.right ∧ gate.left.s ∈ bank ∧ gate.right.s ∈ bank :=
      fun gate h => facts gate (by simp [h])
    have generated : g.output.s &&& P.getD j 0 =
        op g.disj (g.left.s &&& P.getD j 0) (g.right.s &&& P.getD j 0) := by
      rw [InputGate.output, opW_s, and_op]
    have includeHead {B : Set ℕ} (baseSub : base ⊆ B) (head : g.output.s &&& P.getD j 0 ∈ B) :
        base ∪ gateProjection (P.getD j 0) (g :: rest) ⊆ B ∪ gateProjection (P.getD j 0) rest := by
      rintro x (h | ⟨gate,h,rfl⟩)
      · exact Or.inl (baseSub h)
      · rcases List.mem_cons.mp h with rfl | inside
        · exact Or.inl head
        · exact Or.inr ⟨gate,inside,rfl⟩
    cases saved : g.eliminated j
    · have tail := sol.mono le_rfl (includeHead (B := insert (g.output.s &&& P.getD j 0) base)
        (Set.subset_insert _ _) (Set.mem_insert _ _))
      have next := ih remaining (fun x h => Set.mem_insert_of_mem _ (lift x h))
        (Set.mem_insert_of_mem _ zero) (Set.mem_insert_of_mem _ mask) tail
      rw [generated] at next
      have one := Sol.bi (d := g.disj) (lift _ root.2.2.1) (lift _ root.2.2.2) (al0 _ _ _) next
      simpa [projectedCost, saved, Nat.add_assoc] using one
    · have constant : Cst (P.getD j 0) g.left.s ∨ Cst (P.getD j 0) g.right.s := by
        simp only [InputGate.eliminated, Nat.testBit_or, Bool.or_eq_true] at saved
        exact saved.elim (fun h => Or.inl (root.1.cst valid h)) (fun h => Or.inr (root.2.1.cst valid h))
      have present : g.output.s &&& P.getD j 0 ∈ base := by
        rw [InputGate.output,opW_s]
        rcases constant with ha | hb
        · rcases op_cst (b := g.right.s) g.disj ha with h | h | h <;> rw [h]
          · exact zero
          · exact mask
          · exact lift _ root.2.2.2
        · rw [op_comm]
          rcases op_cst (b := g.left.s) g.disj hb with h | h | h <;> rw [h]
          · exact zero
          · exact mask
          · exact lift _ root.2.2.1
      have next := ih remaining lift zero mask (sol.mono le_rfl (includeHead subset_rfl present))
      simpa [projectedCost, saved] using next

lemma stock_cofactor_facts (j : ℕ) (hj : j < (PZ rootBounds).length) :
    (PZ rootBounds).getD j 0 = mz (rootBounds.getD j (0,14)).1 ∧
    rootBounds.getD j (0,14) ∈ rootBounds := by
  simp only [PZ, List.length_map] at hj
  simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]

lemma rootCofactorValid (e : ℕ × ℕ) (he : e ∈ rootBounds) :
    mz e.1 &&& mz 0 = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
  have h := rootBounds_p
  simp only [pOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨a,b⟩,c⟩ := h.2 e he
  exact ⟨Nat.eq_of_beq_eq_true a, fun eq => by simp [eq] at b, fun eq => by simp [eq] at c⟩

lemma rootWordFacts (w : W) (h : w ∈ rootPreparedWords) :
    WOk (PZ rootBounds) w ∧ Good I.AA w.s ∧ w.s ∈ WZ [] 0 ∧ w.r = 3 := by
  rw [← rootPreparedWords_eq] at h
  obtain ⟨_,members,_⟩ := avl_spec (PZ rootBounds) (mz 0) (rawL [])
  obtain ⟨raw, member, rfl⟩ := members w h
  have empty : ∀ e ∈ ([] : List (ℕ × ℕ)), e ∈ six := by simp
  refine ⟨mkW_ok _ _, ?_, ⟨raw,member,rfl⟩,rfl⟩
  rw [← rootPreparedL_eq]
  exact wire_good (rawL_sub empty member) 0

lemma initialGateFacts (g : InputGate)
    (hl : g.left ∈ rootPreparedWords) (hr : g.right ∈ rootPreparedWords) :
    WOk (PZ rootBounds) g.output ∧ Good I.AA g.output.s := by
  have left := rootWordFacts _ hl
  have right := rootWordFacts _ hr
  refine ⟨opW_ok _ left.1 right.1, ?_⟩
  rw [InputGate.output, opW_s]
  exact op_good _ left.2.1 right.2.1

lemma cofactorBudget_sound (k : ℕ) (gates : List InputGate)
    (support : ∀ g ∈ gates, g.left ∈ rootPreparedWords ∧ g.right ∈ rootPreparedWords)
    {S : Finset ℕ} (covered : ∀ x ∈ S, x ∈ WZ [] 0 ∨ ∃ g ∈ gates, x = g.output.s) :
    Cl (PZ rootBounds) (tz 0) k
      (fun j => k + projectedCost gates j - (rootBounds.getD j (0,14)).2) S := by
  intro j hj q hq sol
  obtain ⟨maskEq, member⟩ := stock_cofactor_facts j hj
  let e := rootBounds.getD j (0,14)
  have valid := (rootCofactorValid e member).1
  have raw (x : ℕ) (hx : x ∈ WZ [] 0) : x &&& (PZ rootBounds).getD j 0 ∈ C (mz e.1) (WZ [] e.1) := by
    rw [maskEq]
    obtain ⟨w, hw, rfl⟩ := hx
    apply Or.inl
    refine ⟨w, hw, ?_⟩
    rw [Nat.and_assoc, Nat.and_comm (mz 0), valid]
  have axes : tz 0 &&& (PZ rootBounds).getD j 0 = tz e.1 := by
    rw [maskEq]; exact tz_sub valid
  rw [axes] at sol
  apply rootBounds_I e member (q + projectedCost gates j) (by change q + (k + projectedCost gates j - e.2) < k at hq; omega)
  have zero : 0 ∈ C (mz e.1) (WZ [] e.1) := by simp [C]
  have top : (PZ rootBounds).getD j 0 ∈ C (mz e.1) (WZ [] e.1) := by
    rw [maskEq]
    exact Or.inr (Set.mem_insert_of_mem _ rfl)
  have available : ∀ g ∈ gates, WOk (PZ rootBounds) g.left ∧ WOk (PZ rootBounds) g.right ∧
      g.left.s ∈ WZ [] 0 ∧ g.right.s ∈ WZ [] 0 := by
    intro g hg
    have hl := rootWordFacts _ (support g hg).1
    have hr := rootWordFacts _ (support g hg).2
    exact ⟨hl.1,hr.1,hl.2.2.1,hr.2.2.1⟩
  have extension := extendCofactor (T := tz e.1) (q := q) hj gates available raw zero top
  rw [maskEq] at extension sol
  apply extension (sol.mono le_rfl ?_)
  rintro x (⟨y,hy,rfl⟩ | constant)
  · rcases covered y hy with old | ⟨g,hg,rfl⟩
    · exact Or.inl (by simpa only [maskEq] using raw y old)
    · exact Or.inr ⟨g,hg,rfl⟩
  · exact Or.inl (Or.inr constant)

lemma rootStockContext : Ctx (PZ rootBounds) I.AA (mz 0) rootPreparedSlots (tz 0) := by
  refine ⟨fun i hi => lz_lg 0 i (by rwa [rootPreparedL_eq]), ?_, ?_⟩
  · intro j hj
    obtain ⟨eq,member⟩ := stock_cofactor_facts j hj
    have h := rootCofactorValid _ member
    rw [eq, tz_sub h.1]
    exact h
  · rw [← rootPreparedSlots_eq, pL_pk]
    simp only [PZ, List.length_map]
    refine pk_congr fun j hj => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl

noncomputable def canonicalStock (inputs : List W) (gates : List InputGate) : List W :=
  gates.foldr (fun g stock => addS g.output stock) inputs

lemma canonicalStock_support {v : List W} (sorted : Srt v) (gates : List InputGate) :
    Srt (canonicalStock v gates) ∧
    ∀ w ∈ canonicalStock v gates, w ∈ v ∨ ∃ g ∈ gates, w = g.output := by
  induction gates with
  | nil => exact ⟨sorted, fun _ h => Or.inl h⟩
  | cons g rest ih =>
    obtain ⟨h, present, _, _⟩ := addS_spec (o := g.output) ih.1
    refine ⟨h, fun w member => ?_⟩
    rcases present w member with rfl | hm
    · exact Or.inr ⟨g,by simp,rfl⟩
    · rcases ih.2 w hm with raw | ⟨gate, found, eq⟩
      · exact Or.inl raw
      · exact Or.inr ⟨gate,by simp [found],eq⟩

def canonicalSlot (k : ℕ) (gates : List InputGate) (j : ℕ) : ℕ :=
  k + projectedCost gates j - (rootBounds.getD j (0,14)).2

def canonicalBudget (k : ℕ) (gates : List InputGate) (v : List W) : ℕ :=
  pL ((List.range rootBounds.length).map fun j => 16 + canonicalSlot k gates j) - sumc v

lemma cnt_length_le (v : List W) (j : ℕ) : cnt v j ≤ v.length := by
  induction v with
  | nil => rfl
  | cons w rest ih =>
    rw [cnt_cons, List.length_cons]
    have bound := fl_le w j
    omega

lemma rootCanonicalState {v : List W} {S : Finset ℕ} (rep : Rep v S)
    (k : ℕ) (gates : List InputGate) (cap : k + gates.length ≤ 14) (len : v.length ≤ 15)
    (sources : ∀ g ∈ gates, g.left ∈ rootPreparedWords ∧ g.right ∈ rootPreparedWords)
    (everyWire : ∀ w ∈ v, w ∈ rootPreparedWords ∨ ∃ g ∈ gates, w = g.output) :
    StOk (PZ rootBounds) (tz 0) I.AA k (canonicalBudget k gates v) v S := by
  have good (w : W) (hw : w ∈ v) : WOk (PZ rootBounds) w ∧ Good I.AA w.s := by
    rcases everyWire _ hw with raw | ⟨g,hg,rfl⟩
    · have h := rootWordFacts w raw
      exact ⟨h.1,h.2.1⟩
    · exact initialGateFacts g (sources g hg).1 (sources g hg).2
  have covered (w : ℕ) (mem : w ∈ S) : w ∈ WZ [] 0 ∨ ∃ g ∈ gates, w = g.output.s := by
    obtain ⟨s,hs,rfl⟩ := rep.mem.1 mem
    rcases everyWire s hs with raw | ⟨g,hg,rfl⟩
    · exact Or.inl (rootWordFacts _ raw).2.2.1
    · exact Or.inr ⟨g,hg,rfl⟩
  refine ⟨rep, fun w hw => (good w hw).1, fun w hw => (good w hw).2,
    canonicalSlot k gates, ?_, cofactorBudget_sound k gates sources covered, ?_⟩
  · intro j _
    have cost : projectedCost gates j ≤ gates.length := List.length_filter_le _ _
    unfold canonicalSlot
    omega
  · have base : pL ((List.range rootBounds.length).map fun j => 16 + canonicalSlot k gates j) =
        pk (PZ rootBounds).length (fun j => 16 + canonicalSlot k gates j) := by
      rw [pL_pk]
      simp only [List.length_map, List.length_range, PZ]
      refine pk_congr (fun j hj => ?_)
      have rangeBound : j < (List.range rootBounds.length).length := by simpa using hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem rangeBound]
    rw [canonicalBudget, base, sumc_eq (fun w hw => (good w hw).1), pk_sub]
    intro j _
    exact (cnt_length_le v j).trans (by omega)

lemma pk_slot_top {n j : ℕ} {digits : ℕ → ℕ}
    (bound : ∀ i < n, digits i < 32) (slot : j < n) :
    (pk n digits).testBit (5*j+4) = (digits j).testBit 4 := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    have below : ∀ i < n, digits i < 32 := fun i hi => bound i (by omega)
    rw [pk_succ, Nat.testBit_two_pow_mul_add _ (pk_lt below)]
    by_cases hj : j < n
    · rw [if_pos (by omega : 5*j+4 < 5*n)]
      exact ih below hj
    · have same : j = n := by omega
      subst j
      rw [if_neg (by omega : ¬ 5*n+4 < 5*n)]
      congr 1
      omega

def packedEliminations (gates : List InputGate) : ℕ :=
  (gates.map fun g => g.left.c ||| g.right.c).sum

def eliminatedCount (gates : List InputGate) (j : ℕ) : ℕ :=
  (gates.filter fun g => g.eliminated j).length

lemma splitGateCount (gates : List InputGate) (j : ℕ) :
    projectedCost gates j + eliminatedCount gates j = gates.length := by
  induction gates with
  | nil => rfl
  | cons g rest ih =>
    unfold projectedCost eliminatedCount at *
    cases value : g.eliminated j
    · simp [List.filter_cons,value]; omega
    · simp [List.filter_cons,value]; omega

lemma packedEliminations_eq (gates : List InputGate)
    (valid : ∀ g ∈ gates, WOk (PZ rootBounds) g.left ∧ WOk (PZ rootBounds) g.right) :
    packedEliminations gates = pk (PZ rootBounds).length (eliminatedCount gates) := by
  induction gates with
  | nil => simp [packedEliminations,pk,eliminatedCount]
  | cons g rest ih =>
    have head := valid g (by simp)
    have tail : ∀ w ∈ rest, WOk (PZ rootBounds) w.left ∧ WOk (PZ rootBounds) w.right :=
      fun w hw => valid w (by simp [hw])
    have one := pk_of (isPk_or head.1.pc head.2.pc)
    change (g.left.c ||| g.right.c) + packedEliminations rest = _
    rw [one, ih tail, pk_add]
    refine pk_congr fun j _ => ?_
    unfold eliminatedCount InputGate.eliminated
    rw [List.filter_cons]
    cases h : (g.left.c ||| g.right.c).testBit (5*j) <;> simp [Nat.add_comm]

def rapidBudget (k : ℕ) (gates : List InputGate) (v : List W) : ℕ :=
  let packed := rootPreparedBudget - (packedEliminations gates + sumc v)
  if packed &&& rootPreparedSlots == rootPreparedSlots then packed else canonicalBudget k gates v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rapidBudget_eq (k : ℕ) (gates : List InputGate) (v : List W)
    (cap : k + gates.length = 14) (stock : gates.length + v.length ≤ 16)
    (gateFacts : ∀ g ∈ gates, WOk (PZ rootBounds) g.left ∧ WOk (PZ rootBounds) g.right)
    (facts : ∀ w ∈ v, WOk (PZ rootBounds) w) :
    rapidBudget k gates v = canonicalBudget k gates v := by
  unfold rapidBudget
  dsimp only
  split
  case isFalse => rfl
  case isTrue tagged =>
    let limit := (PZ rootBounds).length
    let lower := fun j => (rootBounds.getD j (0,14)).2
    let digits := fun j => 16+(14-lower j)-(eliminatedCount gates j + cnt v j)
    have base : rootPreparedBudget = pk limit (fun j => 16+(14-lower j)) := by
      rw [← rootPreparedBudget_eq, pk16]
    have entry : rootPreparedBudget - (packedEliminations gates + sumc v) = pk limit digits := by
      rw [base, packedEliminations_eq gates gateFacts, sumc_eq facts, pk_add, pk_sub]
      intro j _
      have count := cnt_length_le v j
      have elim : eliminatedCount gates j ≤ gates.length := List.length_filter_le _ _
      omega
    have bitBound : ∀ j < limit, digits j < 32 := by intro j _; dsimp [digits]; omega
    have high : ∀ j < limit, 16 ≤ digits j := by
      intro j hj
      have eq := congrArg (fun a : ℕ => a.testBit (5*j+4)) (beq_iff_eq.mp tagged)
      rw [entry, rootStockContext.hg, Nat.testBit_and, pk_slot_top bitBound hj,
        pk_slot_top (digits := fun _ => 16) (fun _ _ => by decide) hj] at eq
      simp only [show (16:ℕ).testBit 4 = true by rfl, Bool.and_true] at eq
      have small := bitBound j hj
      generalize digits j = x at eq small ⊢
      interval_cases x <;> first | decide | exact Bool.noConfusion (show false = true from eq)
    have canonical : canonicalBudget k gates v =
        pk limit (fun j => 16 + canonicalSlot k gates j - cnt v j) := by
      have base' : pL ((List.range rootBounds.length).map fun j => 16 + canonicalSlot k gates j) =
          pk limit (fun j => 16 + canonicalSlot k gates j) := by
        rw [pL_pk]
        simp only [List.length_map,List.length_range,limit,PZ]
        refine pk_congr fun j hj => ?_
        have inside : j < (List.range rootBounds.length).length := by simpa using hj
        simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem inside]
      rw [canonicalBudget,base',sumc_eq facts,pk_sub]
      intro j _
      have count := cnt_length_le v j
      omega
    rw [entry,canonical]
    refine pk_congr fun j hj => ?_
    have room := high j hj
    have count := splitGateCount gates j
    dsimp [digits,lower]
    unfold canonicalSlot
    dsimp [digits,lower] at room
    omega

def wordModulus : ℕ := 371
def recipeTable : ℕ := 0xfcfbebdead7e3ce8d362cf6ef9b3d6af1a3f4eb932d4ab122b46bcb9e2c74a9c286c99a247c38e0c3428c082c18a042408
def rotationTable : List ℕ := [0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040, 0xffe5544d2e78df63ceaeaa682ca964cf2c7034cb6c8e28607de2486da5d6658f7cefa450d749e6bee75c1c6004083045, 0xffef7cefa8607de75ccf2c70bee658aeaa689e65d68e2e78df6d746dab6c9645544d245024834c2ca3ce1c61410c2100, 0xffe5544d28607de248aeaa682ca5d6cf2c7034c6588e2e78df63ce6da964b6cf7cefa45075c9e6beed741c6001083105]
def wordLookup : List ℕ := [0x620000000000007000000000000000000052c0000000000000001c80, 0x1800000000000000000000000000001800134000000000000, 0x20f0000000000000000000000001a00, 0x6c0003c0000000000002200000000000000460001800000000000a00, 0x1000000000000002d5820000000480000000000000000000, 0x640000000000540000e000002f00000000000180000002d, 0x2700b000000cc0000001d000000b80000002000200000000000, 0x38000000000000000000000000000000000767800000000112a84900, 0x3d00000000000000000001b000000014000000000f930001300, 0x38d0000000000000000dc02e520000000d400000000004a00009, 0x20000000000000000000000000007c000003ac0000, 0x64000000001f8000a00000000000]
def orbitSecondRecords : List ℕ := [0xf1ffdadbff1f33fc8dbfb1a37fc3cdffaf33fc8ccff2b37fcc59ff670bfc699ff378ffd651fd3433fdd04ff750bfc6c9ff2a8ffc88cff742ffc6c8ff696fdedefbf372efc6d3ff1b17fd9dbff730ffd6d5ff1b0fecde3bf, 0xd0ffc341ff0d17f8343fe0d07f9a59ffb123fcdccff1917fc644ffb10ffc642ffb107fec53ef5957f5ac2ffb137fc689ff376efc74fffe527fc74ffbb15ffc84fffe523fcdccbf1a4ffc681ff9d17fc3c4ff9d0ffdd03ff, 0x1313fc143ffa50ffc4c3ffa50bfc4c2ff0307fc141ffa507fc1c1ff040ff81c1fe7527fc441fd75277c0c2fa1b33fe74bff0513d8acbff6a67fc84dff1537fc8cfff173ff48cffb6567fcae3ffa537fc4cdffb127fc345ff, 0x6907fe887ffb18ffd94fff7513fda53ff1327fd7c9ff090ffc545ffed27fdb41ff376afd9c9df373efc8e27b2f5efda4fff1323fc845ff210ffd781ffad0ffd981ff2107fc88dff1507f4248de3535fcccdffa517fc4c5ff, 0xb17f82c3fe9d33fdd43ff234ffc8d1ffaf17fc8c5ff2313fc5c3ff230ffc8c1ff2b33fc8c3fb7517fcccbbf3766fedddff0d2ffc34c7e6a27fda81ffaf37fc8cdff1e17fca4dffb12ffcd0dff6a4ffda8fff6927fc885ff, 0x3716fca8dffb7c7fcdc4bf370efcdc2bf3706fca4bbf7327fc8e2fb270ffcd4dff1d5ffe75bffaf27fdac9ff7307fddeb3f1b6bcc7c5ff1f0ffc7c3fb3736fc8e1ff733ffdcd3ffaf23fdac8ff0b0ffe2c7ffaf07fdac1ff, 0x2133fdd01ff6b0ffdcc5ff3727fc44cff1333fc8dfff374ffdd5bff3723fcdc5ff6b17dc8cbff370fffdedff2b35fddeabf6b5ffc34cfe6a0ffc6d9ff3165fca63ff378dfcdcdff3786fcdc9bfb133fda43ff374efcdc8bf, 0x6c4f7]
def orbitSecondBuckets : List ℕ := [0x28000808000, 0x800001000081007, 0x80000000808800000d, 0x808000000000000011, 0x10080008013, 0x800000108000000017, 0x80080000000080001b, 0x280000000000000081e, 0x100000080001000024, 0x808100000000000029, 0x1082d, 0x1000000000000000830, 0x80000028033, 0x3180000000000001039, 0x980000080808008844, 0x611080801080000004d, 0x401088000800000062, 0x103900008000001006f, 0xb00800000000007d, 0x808000800000000085, 0x80010100000000088, 0x88000808800000008d, 0x1000000408008000092, 0x18000800c900000009e, 0x8000080898000080ae, 0x882001000080b6, 0x80000180000000bf, 0x810000080c3, 0x800808088000080c7, 0x1080080080cd, 0x10000000a00080008d2, 0x9000000888000000db]
def orbitThirdRecords : List ℕ := [0x744cbff1b4c8ff734c3ff6b243ff676c1ff6b0c1ff1b248de676c1f7216c1fb77ad3bf77ac8bf378c5bf77ac53fb7bc1bf75d04df5e6c1fb214ccff378df3b1b4c5ff1b4c3ff6b4c3ffaf9c1ff374c9ff1b441fd77b41ff2b88d7f2a8cdff1b4c3fbb5bcdff75acdff3534bff378c3bf, 0x378c3fb378e2bb2334cfe758cc7f742c1fff4c45ff6ba83f7b7bc9bf77cc9bfb7b4bbfeb942f7377c5bf377c3bf75542dfb168dff1b4c9ff5f6c1ff1b547ff730c1ff1b243fe377c3bb1b243fb1b243fab174def374cbbf77ac9bfb7bc8bf77ac1bf74a41ff75885ff758c47f77d43bf, 0xa174dff6b6d3f76b7dbf7236c3fb2384cff71a59ffb1443ffb1442ff236c4f3377c3fb376d9bff5b5adf77ac9ff77ac1ff2b4cdff2b7cd7f2b343ff77d43ff758dfdf2b343fe77ad3ff2b345f72164ffd2b345f675d05df77ac577674c2ff1a641fd6b845f7afacd7f75ae37f296cdf7, 0x5e441fdad743ef758e27be5248de6b6c9f7333cdff2b88dff1f6c3fb6b143f7376cdbf74acbff9d143ff9d0c1ff9d141ff6b6c1ff6b6c8f76b6c1f73534cfe9d6ccff756c3ff2b1c1ff742c5fe9d144f62b1c1fe758c9ff758c1ff758c9df77d2b3f6b6d3ff37c593ff4745ff756c3fb, 0x6b9c2f765448f7696c3f325443ff2b8d9ff1a4c9ffb1345ffb1343ff6d681ff75741ff757d9dfb1343fef7b5bbfb14cdef1d3c5ff9d245ff9d241ff9d243fe1d3c5fb1d3c4fb1d3c3fb25443f725442f75f441fd6d441fd2f641fd758c4ff77ac5bf750c2fa6b6c9ff744c3ff77ac5b7, 0xb1845ffb1843ff69741ff316d97f3798dbfb5c4d7f378dffb751c1fe75d235fafacdff2b8cdfff5c49ffb1945efb1943efb1942ef67655fd19141fdb1941ef6d655fdf5c49df191c1fca974dff65449ff65441fd65449f765441f5758ccff378cc7fb1acbff6b4c2ff37c597fb1b4def, 0x69641fd751c1ff75541fd15341fca3745ff74ac3ffa3741ffab94bf7a3745fba3744fba3743fba3741fbf5c44ff2b8c1ffb194fefa5343ffa5341ff1d641fdb1841ff37699bfa5345fea5343fea5341fe0d0c1fe0d141fe0d1c1feb1853efb144bff19241fd3764fbd758c5ff77d04bf, 0xa53cdffe57c5ff13143ff9f741ff13103fe75a53fff5749ffa51c3efa51c1ef3768dbff5749dfa51c1ee75549df9f743fb130c2fa77d51bf1b4ccff9d2c1ff5f793dbaf741ef6b441fd6b448f7378ccbf2354ff9b184ffff5943fff1a49ff21343ff21345fe21343feaf44dff6b6c5f7, 0x77d05bff3949ff15144f61d3cbfb2544bf7238857bb134c7e210c1ff67781df6b74fff75a49ffad84dff2ba8df775a49df13248deb18cdff353417f67981d7353417e37ae33f754cbffeb949ff33343ff746c1ff33345fe33343fe2374ffb258d1f7ef949ef73441fd655d1f56b449f7, 0x69541fd6b64ffd75a4d7f6b655fdf3c41ff752c9ff752c1ff752c9dff5c45ff6ba9377b3c4bbf2f5c8bff5744fff5b44ffb1a41ff1e341fe13245ff13243ff1d441fd677c1ff6d7c1ff6d9c1ffa5841ff211c1ff13243fe09143fe211c1fe37681bf65445f711241fd1934bff77651fd, 0x6a4c9ff6a7c1ffa58cdff23341ff1b64ffd23341feaf94def2b34cfef5bc1ffb17596f77ad93f1b699f35f4c4ff75ccbbf294cdff657c1ff65781ff67941ff29343fe224c5ff6d241ff6ba59ffb774dffb194befb12c7ef378ccff2f5c9bf6ba89776ba8177e9749ff21241ff67241df, 0xeb945f723143fb234c3fb23103fa77d6b3f236ccffb19c1ff1b68df3f5745ff23144f61f341ff332c1bff5b45df2134c7e236ccfb233cbfb291c1fe75849df37644bfb7c43bfb7c42bf2384dffb1a4bbf77d05ff0d2c1feb19c3ff316d9ff1134c7eb5c4dff75841ff316997faf8ddeb, 0x132c3ff738c3fb77d679faf0c1ff23841ff6b781ff6b9c1ff132c5fe1f144f6132c3fe75d0b5f17248de6b248de23543fb75acbff759c3ff757c3df759c3df75243fe75243deb7c48bfb7c45bf234c5ff234c4ff23143ff234c3ff37653bd9d6cdff757c3fb752c5fe27345f623441fd, 0xf1a83ff750c1ff75243df35341ff35341fe37ae3bf6b859ff77d53bf37345bf6b4c9ff23245ff77d5f9faf243ff739c1ff6b7c1ff6dac1ffaf243fe23243fe739c1df77ad97f23243fb23243faf7b6b3f1f4c3ff1b681f3754c3ff1f143fb1f4c3fb67785d7b7c49bf37343bf6b4c8ff, 0x298cdffef449ff73941ff6b941ff371c1be27845f773241ff23755fb378cd7f271c1ff271c1fe7584cffb7c43ff2b64d7f67141f71f243fa779d5bf77d49bf77d41bf734c9ff77d499faf241ff73b41ff6b241ff0b243fe737c1df23885fb77acf3f37acc3f75103fe270c1ff1f4c5ff, 0x37345fe298c1ff77a53bff19dbf7b7c63bfb16c4f7378c17fb184cff75845fff1ac3ffb7c49ff37343ff37343fe37241bf316536d77d6abf37541bd37d4d3f6ba89f7694c3ff69243fe75a83ffb7c48ffb7c45ff75a4dffb7c53ef37445bfb7943bff5942ffb71c5bf37447bf371c1bf, 0x232c3faf4c4bffb16c8ff75ac3ff370c1ffab94d7f2b3417f77d49ff316487ff5b635f77d41ff77d4cbf77d49df77a49bf77a41bf3764bbfab94d77af8c3fb31699ff27881ffb16c5ffb16c3fff3c43ffb16c1ffb16d3ef7794fbf374cdff316457f316447f77d44bf719d97f316427f, 0x748c3fbad8cbff6b957f7656d9ff6b4c5ff6b7c5ff1b4cdff77d741fb16c9ff1b343fff5bc3ffb7941ff371c1ff757dbdf1b343fe371c1fe316497f6b4c5f76b7c5f7237c4fbaf7c3fb237c3fb1b343fb759dbd7378cdbf6b8dbfb234cbffaf8c1ff75d035f2134cfe2b8dbf3232c3fb, 0x1b0c1ffa56c1ff1b1c1ff6d6d5df756c9ff756c9df77ad9ffe775bf71b0c1fb237c9fb6b141f72388c7b378c1bf758cb7f73ac9ffeb743ff278c1ff734c5ffaf7c1ff756c1ff37241ff2b84d7f75d0bdf74a4bbf37541fd1f2c3fb37d4d7f1f2c3fab7bcdbf3734bbfefac9ff75143ff, 0xb1743efb1741ef379c3bf31653ed6b6d9ff37d4dbf318d97f696c9f7696c1f7744c4ff6b6d9f777d745f754c2ff26343fe1b241ff756c4f7696d3f7356cd7f77d6bff2a8c3fb77ac33ff1957efb1acdff376dab377d4cff1b541fd77acfbf372c1bf37accbff19c2ffb1981ff77d45bf, 0x75d03df9d341fef1949ef2b8cffb73ac5f7b174febab94dff2b341ff75d1b5f31648ff2b341fe236cdfff58ddfbf1948ef6b5c5f7236cdfb31645ff77d45ff31644ff31643ff31642ff261c1feb1681ff756ccffb1693ef37a8dbf2a8c9fff4c43ff378c1ff3164b7fb1745ef193c4fd, 0x1d3cdff37acd3f758cbfff5949fff5949df1d3cdfb2544df72b84dfff1a4fff37d4dff6b642ff75681ffedadbff744c5ff6b6cff7236c1fb75441fd2b6ccf73734cbe756c5ff758c37f31649ff1a4cdffb1689ff2b8cfff65651fd9d345ff9d343ff758c37b9d341ff9d345fe0f343fe, 0xb184dff268c1ff376d3bf376c8bf2174ffbb15c8ff2364ffd3734cfe3784cbfb18ddeb356cdff6b885f777ac3bfb194defb1347ef19341fca1741ff376c3bbb15c5ffb15c3ffb574d7f75ac2ff1a541fd676c3fb3568d7f74144f6276c3f32b8e27b77adb372544dff1a1c1fe1a349fe, 0x9d34c7e194c8fd19544fd67641fdb1b42ef21641fdb1248dea374dfff5c4bff173cdfd233cdfb6b85bf319143ff67741ff66741ffb10c1ffb1141ffb1103fe37acd7f3164bffb14c5efb14c4efb14c3efb14c2ef77d0bbf376c9bfb10c2fa6974ffbb16ccffb15c9ffb1144f6b174bef, 0xb13c5ffb13c4ffb13c3ff2b8d3ff2b8c5ff2b8c3ff2b6cd7f13345ffb1245fff5945ff13343ffb1243ff758c3fbb1241ff13345fe13343fe0d143feb1243fe194c9fd11341fd5f641fdb1b41ef2b8c3fb11341fc2b8c5f7f4bc5ff758db7b9d34bff1b34cfe74ac5f76ba99776964ffd, 0x70c1fe07141fe378cf3b754c9ff757c1ff75b41ff754c9df757c9df6b6c3f70d243fead345fe75b41dfa50c2fa6b6c3fb6b6c3f3a385dfb75bd7bf2388d7bf1448ff2b4cbff2b8c8ffafac1ffa584dffb1885ff21341ffb1b4fef759c1ff21341fe759c1df758c3ff738dfdb3384dbf, 0x759cd5fb7743bf6b0c2faa58e27b238817be7943ff3568dff75941ff738c1fff1a89ff22345ff150c1fd21441fd75241ff22345feaf441fd75241df2b8e2fb753497e353495ef574bff33341ff77adbb7f5b4bdfb78dd3ff17c4ffb1781ffb1a4dff37acdbff1449ffa50c1ff2b8c9ff, 0xb18c5ffb18c4ffb18c3ff15241fd6b741ff75a89df6b653fd353497f373c8bfb7745bf77d03bfb7741bfb18c3fba53c5ff754c4ffa53c3ff757c4df214c5ffa5243ff214c3ffa5241ffe7749df891c3fe091c1fe5f541fd6d541fd151c1fc354cd7ff594dff353457f353437f757cd5f, 0x298cffbb17c5ffb17c3ffb17c1ff37acdff1e1c1ff1e1c1fe378cf7b653c9ff1f643fb29341fe694c9ff34345fe34343fe6da41fff7d71bf37689bff1ac8ffb12c3ff73741ffb12c1ffb12c5fe739d9df194cbfd6b641fd373c9bff5c43ff653c8ff1d541fd697c1ff22141ff37693bf, 0x759c5df75d015f1f343fb1f343fab13cbff37641bdab74d7f2b6cdf71334bffb12c9ffaf341ff75ac1ff0d2c3feaf541fdaf341fe1334c7eea749ff234cdfff1ac9ff23345ffaf343ff23343ff3774fbfaf345fe23345feaf343fe23343fe75a8d7f73641fd23343fb3774fbb23343fa, 0x6b541fd75cc9df6b443f723843fb2388dfb69643fff5743ff27341fff5b43dfaf3cdffa58c5ffa58c3ff230c1ff23141ffa58c1ff231c1ff231c1feb7741ff755c9ff75ac9ff75cc1fff5bc9df75ac9dfa58c3fb2d54bdf230c1fb65645ff2b6cdff754c5ff757c5ff334cbbf757c5df, 0x9d6c3fbb5bcd7f75acd7f3534b7f378cfbf378c33f1b693f3a57c3ff746c3fb1f141ff6d545ffa174cff1f1c1fef7ae5b7378c33b75141ff332c9bf75245df2234c7e75144f61f443fb1f0c1fb3764dffb7c61bfeb943ff37341bfeb748ff37341bef7949ff0b0c1fe0b1c1feaf941ef, 0x35345ff35343ff757cddf35343fe37641fd3784dbff494bff294cbbf370c2ba77ad33f376ccbf77ac83f77adf3f75d045f27243df75a43ff27243de270c2fa6b94fff75349feb794dbf35349de677c3fb9d6c1ff6ba53ffeb749ff23241ff752c3fe6b94ff7731c1ffad2c7ef3774ffb, 0x37243beaf8cdff6ba837777d4bbf27841fff1ac5ff1b64dff35349ff3164d7f374c5bf374c4bf37143bf374c3bf374c2bff1ac5f775accff3434bffe56c9ff752c3ff37441bd372489e73841bf1d6cffbb18cbff378c93fb7b633f777de9b274c3ff1b689f375d0c5f759e2df354cdff, 0x6a4c3ff27889dff5bc5ff75ac5ffb794dffb16c7ef6b853ff75a8dff374c9bf37245bf316417d37547bf75ac5f76a7c3fb6b9e1f72334bfff7ae5f7378c37b378e23bb17cbff75889df37341ffaf34c7e2334c7eb7347fe374c8bf37243bf777c1bf37544bf779c1bf37542bfb7847bf, 0xf5c42ffeb745ff237c1ffa56cdff748c5ff374c5ff779d3ff1b341ff1b341fe318597f7754ffd6b849ff37248deeb745f7edac5f76b841ff232c1ff77ac97f77ac17f2b4cd7fab74dff75cc5ff2b3437f37a4dbf758df5f759e35f696d9f777ad37f2b8ccff2b34577758df5b75d055f, 0x1b4c4f7f4943ff737c3db378c3bb1b103f23534c7e6b7c3ff6b9c3ff1f2c1ff374c8ff6b243fe37243ff777c1ff779c1ff758c97f37243fe758c17f758c95f6b9c3f7216cdfb77a89bff4c44ff278c5f76b6d1f7]
def orbitThirdBuckets : List ℕ := [0x108800020190988000, 0x2800880013000902812, 0x180800010a88808829, 0x10000808010008839, 0x980800008000881041, 0x100000002100000084b, 0x1881800008188900054, 0x2800100819908008863, 0x901908000809000876, 0x1010b80808000000884, 0x8808088000008a9893, 0x41100808080080108a2, 0x10018000008000010b5, 0x2b980000900000018bd, 0x9128801880200088d2, 0x20a20880909008108e7, 0x89991082120100100, 0x18c2100888089008919, 0x1801088200010809934, 0x8a0900890000008146, 0x881110111880808154, 0x2109820018800008166, 0x1108801219818809179, 0x1080108141890800192, 0x18908089139808901a9, 0x880111012900089c4, 0x8081010ba8880881d7, 0x80081088900801ee, 0x8081020411008109f8, 0x89080212110080210, 0x20080009398a8889a24, 0x100000111110901242, 0x800001020889910253, 0x1080088001264, 0x88000001088081926b, 0x2800000008080101a77, 0x888800028889090283, 0x2a09080011800000a94, 0x801800020081000aa7, 0x1088900000088180ab3, 0x880100800080880ac0, 0x10889008000000012c9, 0x10000100888080092d3, 0x31008018880000012de, 0x3880001008080a8aee, 0x4221000110808800301, 0x1a90000008808019b1a, 0x21a3008080008810b2d, 0x90a980889100018345, 0x18a190a20000001035b, 0x818a8920800000373, 0x1098a12110800008385, 0x800082a900909839c, 0x19880888b18000003b1, 0x18800003919180083c5, 0x29192081919108083db, 0x908081218991903fa, 0x1108809981080802413, 0x880088b0a90880428, 0x1000111b880008c3d, 0x900080911208880c50, 0x1000000021808001463, 0x800928928000c6f, 0x108800890a990108c81]

abbrev WireRecipe := Fin 8 ⊕ (Bool × Fin 8 × Fin 8)

def rawRecipeWord (i : Fin 8) : W := rootPreparedWords.getD (([5, 4, 7, 6, 3, 2, 1, 0] : List ℕ).getD i.val 0) ⟨0,0,0,0,3⟩

def recipeValue (r : WireRecipe) : W :=
  match r with
  | .inl i => rawRecipeWord i
  | .inr (d,a,b) => opW d (rawRecipeWord a) (rawRecipeWord b)

def wireRecipe (i : Fin 64) : WireRecipe :=
  if h : i.val < 8 then .inl ⟨i.val,h⟩ else
    let code := (recipeTable >>> (7 * (i.val-8))) % 128
    .inr (code.testBit 6, Fin.ofNat 8 code, Fin.ofNat 8 (code >>> 3))

def rotateRecipe (a : Fin 4) : WireRecipe → WireRecipe
  | .inl i => .inl (permuted a i)
  | .inr (d,i,j) =>
    let l := permuted a i
    let r := permuted a j
    if l.val ≤ r.val then .inr (d,l,r) else .inr (d,r,l)

def rotateLabel (a : Fin 4) (i : Fin 64) : Fin 64 :=
  Fin.ofNat 64 ((rotationTable.getD a.val 0) >>> (6*i.val))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawRecipe_signal : ∀ i : Fin 8, (rawRecipeWord i).s = sampleWire i.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma recipeRotation_checked : ∀ a : Fin 4, ∀ i : Fin 64,
    wireRecipe (rotateLabel a i) = rotateRecipe a (wireRecipe i) := by decide +kernel

lemma recipe_rotation (a : Fin 4) (r : WireRecipe) :
    rotateSample a (recipeValue r).s = (recipeValue (rotateRecipe a r)).s := by
  rcases r with i | ⟨d,i,j⟩
  · simpa only [recipeValue, rotateRecipe, rawRecipe_signal] using rotation_wire a i
  · simp only [recipeValue, opW_s, rawRecipe_signal, rotation_op, rotation_wire, rotateRecipe]
    by_cases order : (permuted a i).val ≤ (permuted a j).val
    · simp only [if_pos order, recipeValue, opW_s, rawRecipe_signal]
    · simp only [if_neg order, recipeValue, opW_s, rawRecipe_signal]
      exact op_comm _ _ _

def labelSignal (i : Fin 64) : ℕ := (recipeValue (wireRecipe i)).s

lemma label_rotates (a : Fin 4) (i : Fin 64) : rotateSample a (labelSignal i) = labelSignal (rotateLabel a i) := by
  unfold labelSignal
  rw [recipeRotation_checked,recipe_rotation]

lemma label_generated (i : Fin 64) : SampleSignal (labelSignal i) := by
  unfold labelSignal
  cases e : wireRecipe i with
  | inl j => rw [recipeValue,rawRecipe_signal]; exact .raw j
  | inr data =>
    obtain ⟨d,j,k⟩ := data
    simp only [recipeValue,opW_s,rawRecipe_signal]
    exact .gate d (.raw j) (.raw k)

def readLabel (w : W) : Option (Fin 64) :=
  let pos := w.s % wordModulus
  let id := ((wordLookup.getD (pos / 32) 0) >>> (7 * (pos % 32))) % 128
  if 1 ≤ id && id ≤ 64 then
    let label := Fin.ofNat 64 (id-1)
    if labelSignal label == w.s then some label else none
  else none

lemma readLabel_exact {w : W} {label : Fin 64} (found : readLabel w = some label) : labelSignal label = w.s := by
  unfold readLabel at found
  dsimp only at found
  split at found
  · split at found
    · rename_i heq
      obtain rfl := Option.some.inj found
      exact beq_iff_eq.mp heq
    · simp at found
  · simp at found

def readStock : List W → Option (List (Fin 64))
  | [] => some []
  | head :: rest => do
    let i ← readLabel head
    let labels ← readStock rest
    return i :: labels

lemma readStock_exact {ws : List W} {labels : List (Fin 64)} (found : readStock ws = some labels) :
    labels.map labelSignal = ws.map W.s := by
  induction ws generalizing labels with
  | nil => cases found; rfl
  | cons w ws ih =>
    cases head : readLabel w with
    | none => simp [readStock,head] at found
    | some i =>
      cases rest : readStock ws with
      | none => simp [readStock,head,rest] at found
      | some is =>
        simp [readStock,head,rest] at found
        subst labels
        simp only [List.map_cons, readLabel_exact head, ih rest]

def labelStock (labels : List (Fin 64)) : Finset ℕ := (labels.map labelSignal).toFinset

def shapeBits (a : Fin 4) (labels : List (Fin 64)) : ℕ :=
  labels.foldr (fun i bits => (1 <<< (rotateLabel a i).val) ||| bits) 0

lemma bitOfShape (a : Fin 4) (labels : List (Fin 64)) (j : Fin 64) :
    (shapeBits a labels).testBit j.val = true ↔ ∃ i ∈ labels, rotateLabel a i = j := by
  induction labels with
  | nil => simp [shapeBits]
  | cons i rest ih =>
    simp only [shapeBits, List.foldr_cons, Nat.testBit_or] at ih ⊢
    simp only [Bool.or_eq_true, ih, List.mem_cons]
    rw [show (1 <<< (rotateLabel a i).val : ℕ) = 2 ^ (rotateLabel a i).val by
      rw [Nat.shiftLeft_eq]; simp]
    simp only [Nat.testBit_two_pow, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro (current | ⟨l,hl,eq⟩)
      · exact ⟨i, Or.inl rfl, Fin.ext current⟩
      · exact ⟨l, Or.inr hl, eq⟩
    · rintro ⟨l, mem, eq⟩
      rcases mem with rfl | rest
      · exact Or.inl (congrArg Fin.val eq)
      · exact Or.inr ⟨l,rest,eq⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma equalRotatedShape {a b : Fin 4} {as bs : List (Fin 64)} (same : shapeBits a as = shapeBits b bs) :
    rotationStock a (labelStock as) = rotationStock b (labelStock bs) := by
  have sub {p q : Fin 4} {ps qs : List (Fin 64)} (eq : shapeBits p ps = shapeBits q qs) :
      rotationStock p (labelStock ps) ⊆ rotationStock q (labelStock qs) := by
    intro x hx
    obtain ⟨old,ho,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
    have h := (bitOfShape p ps (rotateLabel p i)).2 ⟨i,hi,rfl⟩
    rw [eq] at h
    obtain ⟨j,hj,e⟩ := (bitOfShape q qs (rotateLabel p i)).mp h
    apply Finset.mem_image.mpr
    refine ⟨labelSignal j, List.mem_toFinset.mpr (List.mem_map_of_mem hj), ?_⟩
    rw [label_rotates, label_rotates, e]
  exact Finset.Subset.antisymm (sub same) (sub same.symm)

def chooseRotation (labels : List (Fin 64)) : Fin 4 :=
  [1,2,3].foldl (fun best turn => if shapeBits turn labels < shapeBits best labels then turn else best) 0

structure OrbitRecord where
  retained : List (Fin 8)
  gates : List (Fin 56)
  turn : Fin 4

def decodeOrbitRecord (width code : ℕ) : OrbitRecord := ⟨
  (List.finRange 8).filter (fun i => code.testBit i.val),
  (List.range width).map (fun k => Fin.ofNat 56 ((code >>> (8 + 6*k)) % 64)),
  Fin.ofNat 4 (code >>> (8+6*width))⟩

def orbitRecordAt (width index : ℕ) : OrbitRecord :=
  let words := if width = 2 then orbitSecondRecords else orbitThirdRecords
  let bits := 10 + 6*width
  let packed := (words.getD (index / 32) 0) >>> (bits * (index % 32))
  decodeOrbitRecord width packed

def recipeOfPair (id : Fin 56) : Bool × Fin 8 × Fin 8 :=
  let c := (recipeTable >>> (7*id.val)) % 128
  (c.testBit 6, Fin.ofNat 8 c, Fin.ofNat 8 (c >>> 3))

def inputGate (id : Fin 56) : InputGate :=
  let recipe := recipeOfPair id
  ⟨recipe.1, rawRecipeWord recipe.2.1, rawRecipeWord recipe.2.2⟩

def rawLabel (i : Fin 8) : Fin 64 := ⟨i.val, by omega⟩
def pairLabel (i : Fin 56) : Fin 64 := ⟨8+i.val, by omega⟩

def OrbitRecord.labels (record : OrbitRecord) : List (Fin 64) :=
  record.retained.map rawLabel ++ record.gates.map pairLabel

def OrbitRecord.key (record : OrbitRecord) : ℕ := shapeBits record.turn record.labels

def orbitCount (width : ℕ) : ℕ := if width = 2 then 225 else 1176

def orbitFind (width key : ℕ) : Option ℕ :=
  let rows := if width = 2 then orbitSecondBuckets else orbitThirdBuckets
  let bucket := (key % 65521) % (if width = 2 then 512 else 1024)
  let block := rows.getD (bucket / 16) 0
  let counts := block >>> 11
  let size := fun i => (counts >>> (4*i)) % 16
  let start := (List.range (bucket % 16)).foldl (fun pos i => pos + size i) (block % 2048)
  (List.range' start (size (bucket % 16))).find? (fun i =>
    i < orbitCount width && (orbitRecordAt width i).key == key)

def lookupOrbit (width : ℕ) (ws : List W) : Option ℕ := do
  let labels ← readStock ws
  orbitFind width (shapeBits (chooseRotation labels) labels)

lemma orbitFind_exact {width key i : ℕ} (found : orbitFind width key = some i) :
    i < orbitCount width ∧ (orbitRecordAt width i).key = key := by
  unfold orbitFind at found
  dsimp only at found
  have got := List.find?_some found
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using got

lemma rawRecipe_inBank (i : Fin 8) : rawRecipeWord i ∈ rootPreparedWords := by
  have valid : ([5,4,7,6,3,2,1,0] : List ℕ).getD i.val 0 < rootPreparedWords.length := by
    fin_cases i <;> decide
  unfold rawRecipeWord
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid]
  exact List.getElem_mem valid

lemma gate_inBank (code : Fin 56) :
    (inputGate code).left ∈ rootPreparedWords ∧ (inputGate code).right ∈ rootPreparedWords :=
  ⟨rawRecipe_inBank _, rawRecipe_inBank _⟩

lemma recipeValue_raw (i : Fin 8) : recipeValue (wireRecipe (rawLabel i)) = rawRecipeWord i := by
  simp [recipeValue,wireRecipe,rawLabel,i.isLt]

lemma recipeValue_pair (i : Fin 56) : recipeValue (wireRecipe (pairLabel i)) = (inputGate i).output := by
  have notRaw : ¬ (8 + i.val < 8) := by omega
  simp [recipeValue,wireRecipe,pairLabel,notRaw,inputGate,recipeOfPair,InputGate.output]

noncomputable def sortRaw (inputs : List (Fin 8)) : List W := (inputs.map rawRecipeWord).foldr addS []

noncomputable def OrbitRecord.stock (record : OrbitRecord) : List W :=
  canonicalStock (sortRaw record.retained) (record.gates.map inputGate)

noncomputable def OrbitRecord.state (k : ℕ) (record : OrbitRecord) : SearchState :=
  let ws := record.stock
  (rapidBudget k (record.gates.map inputGate) ws, ws)

lemma stockFold (words start : List W) (ordered : Srt start) :
    Srt (words.foldr addS start) ∧
    ((words.foldr addS start).map W.s).toFinset = (words.map W.s).toFinset ∪ (start.map W.s).toFinset := by
  induction words with
  | nil => exact ⟨ordered, by simp⟩
  | cons w words ih =>
    obtain ⟨sorted, remains, new, old⟩ := addS_spec (o := w) ih.1
    refine ⟨sorted, ?_⟩
    ext x
    simp only [List.foldr_cons, List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      rcases remains v hv with rfl | h
      · exact Or.inl (Or.inl rfl)
      · have := List.mem_toFinset.mpr (List.mem_map_of_mem (f := W.s) h)
        rw [ih.2,Finset.mem_union] at this
        exact this.elim (fun found => Or.inl (Or.inr found)) Or.inr
    · intro hx
      rcases hx with (rfl | hw) | init
      · obtain ⟨v,hv,he⟩ := new
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v,hv,he⟩)
      · have stock : x ∈ ((words.foldr addS start).map W.s).toFinset := by rw [ih.2]; exact Finset.mem_union_left _ hw
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp stock)
        exact List.mem_toFinset.mpr (List.mem_map_of_mem (old v hv))
      · have stock : x ∈ ((words.foldr addS start).map W.s).toFinset := by rw [ih.2]; exact Finset.mem_union_right _ init
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp stock)
        exact List.mem_toFinset.mpr (List.mem_map_of_mem (old v hv))

lemma OrbitRecord.sorted_stock (o : OrbitRecord) : Srt o.stock := by
  exact (canonicalStock_support (stockFold _ [] (by simp [Srt])).1 _).1

lemma OrbitRecord.stock_rep (o : OrbitRecord) : Rep o.stock (labelStock o.labels) := by
  have sorted := o.sorted_stock
  have raw := (stockFold (o.retained.map rawRecipeWord) [] (by simp [Srt])).2
  have gates := (stockFold ((o.gates.map inputGate).map InputGate.output) (sortRaw o.retained)
    (stockFold _ [] (by simp [Srt])).1).2
  refine ⟨?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    exact sorted.imp fun h => Ne.symm (Nat.ne_of_lt h)
  · change (o.stock.map W.s).toFinset = _
    unfold OrbitRecord.stock canonicalStock
    rw [← List.foldr_map, gates]
    change _ ∪ (((o.retained.map rawRecipeWord).foldr addS []).map W.s).toFinset = _
    rw [raw]
    simp only [List.map_nil,List.toFinset_nil,Finset.union_empty]
    unfold labelStock OrbitRecord.labels
    simp only [List.map_append,List.toFinset_append,List.map_map,Function.comp_def,
      labelSignal,recipeValue_raw,recipeValue_pair]
    exact Finset.union_comm _ _

lemma orbitRawFacts (inputs : List (Fin 8)) {w : W} (member : w ∈ sortRaw inputs) : w ∈ rootPreparedWords := by
  have ext (words : List W) (source : ∀ x ∈ words, x ∈ rootPreparedWords) :
      Srt (words.foldr addS []) ∧ ∀ x ∈ words.foldr addS [], x ∈ rootPreparedWords := by
    induction words with
    | nil => simp [Srt]
    | cons x rest ih =>
      obtain ⟨sorted, members⟩ := ih (fun w h => source w (by simp [h]))
      have add := addS_spec (o := x) sorted
      exact ⟨add.1,fun w h => (add.2.1 w h).elim (fun eq => eq ▸ source x (by simp)) (members w)⟩
  exact (ext _ (fun x hx => by obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx; exact rawRecipe_inBank v)).2 w member

lemma OrbitRecord.stock_support (o : OrbitRecord) :
    ∀ w ∈ o.stock, w ∈ rootPreparedWords ∨ ∃ g ∈ o.gates.map inputGate, w = g.output := by
  intro w hw
  obtain ⟨_,covers⟩ := canonicalStock_support (stockFold _ [] (by simp [Srt])).1 (o.gates.map inputGate)
  exact (covers w hw).elim (fun raw => Or.inl (orbitRawFacts _ raw)) Or.inr

lemma OrbitRecord.budget_sound (o : OrbitRecord) {k : ℕ}
    (gates : k + o.gates.length = 14) (len : o.stock.length ≤ 15)
    (total : o.gates.length + o.stock.length ≤ 16) :
    StOk (PZ rootBounds) (tz 0) I.AA k (o.state k).1 o.stock (labelStock o.labels) := by
  have sources : ∀ g ∈ o.gates.map inputGate, g.left ∈ rootPreparedWords ∧ g.right ∈ rootPreparedWords := by
    intro g hg
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
    exact gate_inBank i
  have slotBound : k + (o.gates.map inputGate).length = 14 := by simpa using gates
  have wireBound : (o.gates.map inputGate).length + o.stock.length ≤ 16 := by simpa using total
  have exactState := rootCanonicalState o.stock_rep k (o.gates.map inputGate)
    (Nat.le_of_eq slotBound) len sources o.stock_support
  have gateFacts (g : InputGate) (hg : g ∈ o.gates.map inputGate) :
      WOk (PZ rootBounds) g.left ∧ WOk (PZ rootBounds) g.right :=
    ⟨(rootWordFacts _ (sources g hg).1).1,(rootWordFacts _ (sources g hg).2).1⟩
  change StOk (PZ rootBounds) (tz 0) I.AA k (rapidBudget k (o.gates.map inputGate) o.stock) o.stock _
  rw [rapidBudget_eq k (o.gates.map inputGate) o.stock slotBound wireBound gateFacts exactState.wok]
  exact exactState

lemma codeStock_generated (labels : List (Fin 64)) : ∀ x ∈ labelStock labels, SampleSignal x := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact label_generated i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rotateStock_twice (a : Fin 4) {S : Finset ℕ} (gen : ∀ x ∈ S, SampleSignal x) :
    rotationStock a (rotationStock a S) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨before, h, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨orig, ho, rfl⟩ := Finset.mem_image.mp h
    rwa [rotation_involutive_on a (gen orig ho)]
  · intro h
    exact Finset.mem_image.mpr ⟨rotateSample a x, Finset.mem_image_of_mem _ h, rotation_involutive_on a (gen x h)⟩

abbrev NoShorter (S : Finset ℕ) (k : ℕ) :=
  ∀ q < k, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) ({x | RZ [] 0 x ≠ 0} ∪ (S : Set ℕ)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma orbitProblem {width idx : ℕ} {v : List W} {S : Finset ℕ} {k t : ℕ}
    (found : lookupOrbit width v = some idx) (rep : Rep v S)
    (live : Live Z0 (mz 0) (tz 0) k t S) (short : NoShorter S k)
    (ready : RawMode true (RZ [] 0) (mz 0) (tz 0) k t S) :
    let target := labelStock (orbitRecordAt width idx).labels
    Live Z0 (mz 0) (tz 0) k t target ∧ NoShorter target k ∧
    RawMode true (RZ [] 0) (mz 0) (tz 0) k t target := by
  cases stock : readStock v with
  | none => simp [lookupOrbit,stock] at found
  | some labels =>
    let a := chooseRotation labels
    let o := orbitRecordAt width idx
    have lookup : orbitFind width (shapeBits a labels) = some idx := by simpa [lookupOrbit,stock,a] using found
    have repr : S = labelStock labels := by
      dsimp only [labelStock]
      rw [readStock_exact stock, rep.2]
    have align : rotationStock a S = rotationStock o.turn (labelStock o.labels) := by
      rw [repr]
      exact equalRotatedShape (orbitFind_exact lookup).2.symm
    have gen : ∀ x ∈ S, SampleSignal x := by rw [repr]; exact codeStock_generated labels
    have live1 := live.rotateStock gen a
    have short1 := rotateShortExclusion a gen short
    have ready1 := rotateRawMode a gen ready
    change Live Z0 (mz 0) (tz 0) k t (rotationStock a S) at live1
    rw [align] at live1 short1 ready1
    have gen2 : ∀ x ∈ rotationStock o.turn (labelStock o.labels), SampleSignal x := by
      intro x hx
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
      exact rotation_generated o.turn (codeStock_generated _ w hw)
    have restore := rotateStock_twice o.turn (codeStock_generated o.labels)
    have live2 := live1.rotateStock gen2 o.turn
    have short2 := rotateShortExclusion o.turn gen2 short1
    have ready2 := rotateRawMode o.turn gen2 ready1
    change Live Z0 (mz 0) (tz 0) k t (rotationStock o.turn (rotationStock o.turn (labelStock o.labels))) at live2
    rw [restore] at live2 short2 ready2
    exact ⟨live2,short2,ready2⟩


lemma orbitRecord_counts (width idx : ℕ) :
    (orbitRecordAt width idx).retained.length ≤ 8 ∧ (orbitRecordAt width idx).gates.length = width := by
  unfold orbitRecordAt decodeOrbitRecord
  exact ⟨(List.length_filter_le _ _).trans (by simp), by simp⟩

lemma OrbitRecord.card_stock_le (o : OrbitRecord) :
    o.stock.length ≤ o.retained.length + o.gates.length := by
  have h := List.toFinset_card_le (o.labels.map labelSignal)
  change (labelStock o.labels).card ≤ _ at h
  rw [o.stock_rep.card] at h
  simpa [OrbitRecord.labels] using h

def rootGatesDistinct : Bool := (List.finRange 56).all fun gate =>
  !(rootPreparedWords.any fun wire => wire.s == (inputGate gate).output.s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootGatesDistinct_checked : rootGatesDistinct = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma newGateIsDerived (code : Fin 56) : (inputGate code).output.s ∉ WZ [] 0 := by
  intro old
  obtain ⟨i,same⟩ := sampleWire_covers old
  have belongs := rawRecipe_inBank i
  have wrong : (rootPreparedWords.any fun wire => wire.s == (inputGate code).output.s) = true := by
    apply List.any_eq_true.mpr
    exact ⟨rawRecipeWord i,belongs,by rw [rawRecipe_signal,← same,beq_self_eq_true]⟩
  have known := List.all_eq_true.mp rootGatesDistinct_checked code (by simp)
  simp [wrong] at known

lemma OrbitRecord.exact_raw_tags (o : OrbitRecord) : ∀ w ∈ o.stock, w.r = RZ [] 0 w.s := by
  intro w hw
  rcases o.stock_support w hw with raw | ⟨g,member,rfl⟩
  · obtain ⟨_,_,present,tag⟩ := rootWordFacts _ raw
    rw [tag,RZ,if_pos present]
  · obtain ⟨code,_,rfl⟩ := List.mem_map.mp member
    rw [RZ,if_neg (newGateIsDerived code),InputGate.output,opW_r]

-- Verify each representative with the ordinary recursive search. The earlier frontier
-- can reuse the already certified representatives for its pure successors.
def ignoreOrbit (_ _ _ : ℕ) (_ : List W) : Bool := false

def rejectOrbit (target width k t _ : ℕ) (ws : List W) : Bool :=
  (k == target) && (t == 1) && (lookupOrbit width ws).isSome

abbrev rejectThird := rejectOrbit 11 3

def rootReject (k t z : ℕ) (ws : List W) : Bool :=
  rejectOrbit 12 2 k t z ws || rejectThird k t z ws

noncomputable def orbitCheck (reject : ℕ → ℕ → ℕ → List W → Bool)
    (width fuel k idx : ℕ) : Bool :=
  let entry := (orbitRecordAt width idx).state k
  !(frc entry.2 (fun ws => st entry.1 (fun budget =>
    look1RawC reject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 fuel k 1 budget ws)))

lemma lookupOrbit_bound {width : ℕ} {ws : List W} {idx : ℕ} (found : lookupOrbit width ws = some idx) :
    idx < orbitCount width := by
  cases h : readStock ws with
  | none => simp [lookupOrbit,h] at found
  | some labels =>
    have atIndex : orbitFind width (shapeBits (chooseRotation labels) labels) = some idx := by
      simpa [lookupOrbit,h] using found
    exact (orbitFind_exact atIndex).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rejectOrbit_sound {inner : ℕ → ℕ → ℕ → List W → Bool}
    (valid : RejectSound true (RZ [] 0) (mz 0) (tz 0) inner)
    {width fuel k₀ : ℕ} (cap : k₀ + width = 14) (widthBound : width ≤ 4)
    (checked : rangeCheck (orbitCheck inner width fuel k₀) 0 (orbitCount width) = true) :
    RejectSound true (RZ [] 0) (mz 0) (tz 0) (rejectOrbit k₀ width) := by
  intro k t z ws S k' rep size live short ready reject
  simp only [rejectOrbit, Bool.and_eq_true, beq_iff_eq] at reject
  obtain ⟨⟨same,one⟩,found⟩ := reject
  subst k
  subst t
  cases record : lookupOrbit width ws with
  | none => simp [record] at found
  | some idx =>
    obtain ⟨renamed,minimum,ready'⟩ := orbitProblem record rep live short ready
    let entry := orbitRecordAt width idx
    obtain ⟨inputs,gates⟩ := orbitRecord_counts width idx
    change entry.retained.length ≤ 8 at inputs
    change entry.gates.length = width at gates
    have len : entry.stock.length ≤ 15 := entry.card_stock_le.trans (by omega)
    have total : entry.gates.length + entry.stock.length ≤ 16 := by
      have size := entry.card_stock_le
      omega
    have witness := entry.budget_sound (by omega : k₀ + entry.gates.length = 14) len total
    have hd := boolOfNeg (rangeCheck_at checked (lookupOrbit_bound record))
    simp only [orbitCheck, frc_eq, st_eq, ← rootPreparedMask_eq] at hd
    exact look1Raw_sound rootStockContext inner true valid (RZ_R [] 0) (RZ_R2 [] 0)
      fuel k₀ 1 (entry.state k₀).1 entry.stock _ hd witness entry.exact_raw_tags k' size renamed minimum ready'

lemma ignoreOrbit_sound : RejectSound true (RZ [] 0) (mz 0) (tz 0) ignoreOrbit := by
  intro k t z ws S k' _ _ _ _ _ h
  simp [ignoreOrbit] at h

noncomputable def orbitThirdCheck := orbitCheck ignoreOrbit 3 12 11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird0 : rangeCheck orbitThirdCheck 0 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird1 : rangeCheck orbitThirdCheck 65 59 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird2 : rangeCheck orbitThirdCheck 124 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird3 : rangeCheck orbitThirdCheck 192 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird4 : rangeCheck orbitThirdCheck 260 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird5 : rangeCheck orbitThirdCheck 328 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird6 : rangeCheck orbitThirdCheck 396 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird7 : rangeCheck orbitThirdCheck 464 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird8 : rangeCheck orbitThirdCheck 532 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird9 : rangeCheck orbitThirdCheck 600 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird10 : rangeCheck orbitThirdCheck 668 55 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird11 : rangeCheck orbitThirdCheck 723 52 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird12 : rangeCheck orbitThirdCheck 775 66 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird13 : rangeCheck orbitThirdCheck 841 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird14 : rangeCheck orbitThirdCheck 865 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird15 : rangeCheck orbitThirdCheck 933 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird16 : rangeCheck orbitThirdCheck 1001 52 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird17 : rangeCheck orbitThirdCheck 1053 68 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird18 : rangeCheck orbitThirdCheck 1121 37 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThird19 : rangeCheck orbitThirdCheck 1158 18 = true := by decide +kernel

abbrev orbitThirdAppend := @rangeAppend orbitThirdCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitThirdAll : rangeCheck orbitThirdCheck 0 1176 = true :=
  (@orbitThirdAppend 0 668 508 (@orbitThirdAppend 0 328 340 (@orbitThirdAppend 0 124 204 (@orbitThirdAppend 0 65 59 orbitThird0 orbitThird1) (@orbitThirdAppend 124 68 136 orbitThird2 (@orbitThirdAppend 192 68 68 orbitThird3 orbitThird4))) (@orbitThirdAppend 328 136 204 (@orbitThirdAppend 328 68 68 orbitThird5 orbitThird6) (@orbitThirdAppend 464 68 136 orbitThird7 (@orbitThirdAppend 532 68 68 orbitThird8 orbitThird9)))) (@orbitThirdAppend 668 265 243 (@orbitThirdAppend 668 107 158 (@orbitThirdAppend 668 55 52 orbitThird10 orbitThird11) (@orbitThirdAppend 775 66 92 orbitThird12 (@orbitThirdAppend 841 24 68 orbitThird13 orbitThird14))) (@orbitThirdAppend 933 120 123 (@orbitThirdAppend 933 68 52 orbitThird15 orbitThird16) (@orbitThirdAppend 1053 68 55 orbitThird17 (@orbitThirdAppend 1121 37 18 orbitThird18 orbitThird19)))))

lemma rejectThird_sound : RejectSound true (RZ [] 0) (mz 0) (tz 0) rejectThird :=
  rejectOrbit_sound ignoreOrbit_sound (by decide) (by decide) orbitThirdAll

noncomputable def orbitSecondCheck := orbitCheck rejectThird 2 13 12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond0 : rangeCheck orbitSecondCheck 0 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond1 : rangeCheck orbitSecondCheck 11 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond2 : rangeCheck orbitSecondCheck 25 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond3 : rangeCheck orbitSecondCheck 39 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond4 : rangeCheck orbitSecondCheck 53 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond5 : rangeCheck orbitSecondCheck 59 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond6 : rangeCheck orbitSecondCheck 60 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond7 : rangeCheck orbitSecondCheck 63 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond8 : rangeCheck orbitSecondCheck 77 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond9 : rangeCheck orbitSecondCheck 81 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond10 : rangeCheck orbitSecondCheck 91 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond11 : rangeCheck orbitSecondCheck 99 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond12 : rangeCheck orbitSecondCheck 100 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond13 : rangeCheck orbitSecondCheck 103 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond14 : rangeCheck orbitSecondCheck 117 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond15 : rangeCheck orbitSecondCheck 131 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond16 : rangeCheck orbitSecondCheck 143 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond17 : rangeCheck orbitSecondCheck 154 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond18 : rangeCheck orbitSecondCheck 168 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond19 : rangeCheck orbitSecondCheck 174 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond20 : rangeCheck orbitSecondCheck 181 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond21 : rangeCheck orbitSecondCheck 195 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond22 : rangeCheck orbitSecondCheck 205 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecond23 : rangeCheck orbitSecondCheck 214 11 = true := by decide +kernel

abbrev orbitSecondAppend := @rangeAppend orbitSecondCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem orbitSecondAll : rangeCheck orbitSecondCheck 0 225 = true :=
  (@orbitSecondAppend 0 100 125 (@orbitSecondAppend 0 60 40 (@orbitSecondAppend 0 39 21 (@orbitSecondAppend 0 11 28 orbitSecond0 (@orbitSecondAppend 11 14 14 orbitSecond1 orbitSecond2)) (@orbitSecondAppend 39 14 7 orbitSecond3 (@orbitSecondAppend 53 6 1 orbitSecond4 orbitSecond5))) (@orbitSecondAppend 60 21 19 (@orbitSecondAppend 60 3 18 orbitSecond6 (@orbitSecondAppend 63 14 4 orbitSecond7 orbitSecond8)) (@orbitSecondAppend 81 10 9 orbitSecond9 (@orbitSecondAppend 91 8 1 orbitSecond10 orbitSecond11)))) (@orbitSecondAppend 100 68 57 (@orbitSecondAppend 100 31 37 (@orbitSecondAppend 100 3 28 orbitSecond12 (@orbitSecondAppend 103 14 14 orbitSecond13 orbitSecond14)) (@orbitSecondAppend 131 12 25 orbitSecond15 (@orbitSecondAppend 143 11 14 orbitSecond16 orbitSecond17))) (@orbitSecondAppend 168 27 30 (@orbitSecondAppend 168 6 21 orbitSecond18 (@orbitSecondAppend 174 7 14 orbitSecond19 orbitSecond20)) (@orbitSecondAppend 195 10 20 orbitSecond21 (@orbitSecondAppend 205 9 11 orbitSecond22 orbitSecond23)))))

lemma rootReject_sound : RejectSound true (RZ [] 0) (mz 0) (tz 0) rootReject := by
  have second : RejectSound true (RZ [] 0) (mz 0) (tz 0) (rejectOrbit 12 2) :=
    rejectOrbit_sound rejectThird_sound (by decide) (by decide) orbitSecondAll
  intro k t z ws S k' rep size live short ready found
  simp only [rootReject, Bool.or_eq_true] at found
  exact found.elim (second rep size live short ready) (rejectThird_sound rep size live short ready)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootStart_eq (H : ℕ) (kind : Bool) :
    startPairPicked rootReject I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots rootPreparedBudget
      14 1 0 H 0 rootPreparedWords kind =
    initialBinary H kind (look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) := by
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 8 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  simp only [startPairPicked, child, st_eq, topPairPicked, bR, haveRequired, len, budget,
    show Nat.ble 8 (Nat.sub 15 1) = true from rfl, show Nat.ble 8 1 = false from rfl,
    Bool.cond_true, Bool.cond_false]
  change (bif initialBinary H kind (look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) then true else false) = _
  cases initialBinary H kind (look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialBinary_of_check (H : ℕ) (kind : Bool)
    (h : chkPairPicked rootReject [] rootBounds 0 14 1 H 0 kind = true) :
    initialBinary H kind
      (look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = true := by
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
      look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false) :
    chkPairPicked rootReject [] rootBounds 0 14 1 H 0 kind = false := by
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

noncomputable def opening_0_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_0_and_complete : initialBinary 0x200000000000000000000000000000000000000000 false (frontierMissing opening_0_and) = false := by decide +kernel

noncomputable def opening_0_or : List (ℕ × List W) := [⟨0x9ce55ace74a527294e929ce7394e739d6939ce72952939ce948ce9394e72a465194a11, rootWithGate 4 5 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_0_or_complete : initialBinary 0x200000000000000000000000000000000000000000 true (frontierMissing opening_0_or) = false := by decide +kernel

noncomputable def opening_1_and : List (ℕ × List W) := [⟨0x8d295ace359d294a4e94a46918ca54956b39ce338d291a4a9294a548ca52a465194230, rootWithGate 5 7 255 false⟩]
set_option maxRecDepth 100000 in
theorem opening_1_and_complete : initialBinary 0x10000000000000000000000000000000000000000 false (frontierMissing opening_1_and) = false := by decide +kernel

noncomputable def opening_1_or : List (ℕ × List W) := [⟨0x95295ace55a5294a4e94a4a9294e549d6b39ce5395292a4e9394e7494e53a465194631, rootWithGate 5 7 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_1_or_complete : initialBinary 0x10000000000000000000000000000000000000000 true (frontierMissing opening_1_or) = false := by decide +kernel

noncomputable def opening_2_and : List (ℕ × List W) := [⟨0x8d295ac6759d294a4e94a4e918ca52a56b39c6738d253a4a5494a528d252a465184a30, rootWithGate 5 6 255 false⟩]
set_option maxRecDepth 100000 in
theorem opening_2_and_complete : initialBinary 0x400000000000000000000000000000000000000000000000 false (frontierMissing opening_2_and) = false := by decide +kernel

noncomputable def opening_2_or : List (ℕ × List W) := [⟨0x95295aca75a5294a4e94a4e928ca73a56b39ca7395273a4e7494e738d273a46518ca31, rootWithGate 5 6 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_2_or_complete : initialBinary 0x400000000000000000000000000000000000000000000000 true (frontierMissing opening_2_or) = false := by decide +kernel

noncomputable def opening_3_and : List (ℕ × List W) := [⟨0x9d293ace759d294a4e94a46938ca54a56b19ce738ca5194a9494a948d252a461194a30, rootWithGate 2 5 255 false⟩]
set_option maxRecDepth 100000 in
theorem opening_3_and_complete : initialBinary 0x10000000000000000 false (frontierMissing opening_3_and) = false := by decide +kernel

noncomputable def opening_3_or : List (ℕ × List W) := [⟨0x9d294ace75a5294a4e94a4a9394a54a56b29ce7394e729ca9494e9495273a463194a31, rootWithGate 2 5 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_3_or_complete : initialBinary 0x10000000000000000 true (frontierMissing opening_3_or) = false := by decide +kernel

noncomputable def opening_4_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_4_and_complete : initialBinary 0x20000000000000 false (frontierMissing opening_4_and) = false := by decide +kernel

noncomputable def opening_4_or : List (ℕ × List W) := [⟨0x8d2939c6339d294a4694a4a728ce74a56b294a528d293a4e9494e9495273a425194a31, rootWithGate 1 5 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_4_or_complete : initialBinary 0x20000000000000 true (frontierMissing opening_4_or) = false := by decide +kernel

noncomputable def opening_5_and : List (ℕ × List W) := [⟨0x9ca55ace759ca92a4e9494e938ca54a4e739ce738d293a4a9494a948d2529465194a30, rootWithGate 0 5 255 false⟩]
set_option maxRecDepth 100000 in
theorem opening_5_and_complete : initialBinary 0x100000000000000000000000 false (frontierMissing opening_5_and) = false := by decide +kernel

noncomputable def opening_5_or : List (ℕ × List W) := [⟨0x9ce75ace75a4e93a4e949ce9394e74a52939ce7395293a4e9494e94952739c65194a31, rootWithGate 0 5 255 true⟩, ⟨0x8ce539c6339d272946929ca52952939d69294a51952939d2948d2939ce93a425194a12, rootWithGate 1 4 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_5_or_complete : initialBinary 0x100000000000000000000000 true (frontierMissing opening_5_or) = false := by decide +kernel

noncomputable def opening_6_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_6_and_complete : initialBinary 0x80000000000000000000000000000000000000000000000000 false (frontierMissing opening_6_and) = false := by decide +kernel

noncomputable def opening_6_or : List (ℕ × List W) := [⟨0x94e55ace54ad27294e929ca729d273956939ce529d2929d2938d2739ca73a465194612, rootWithGate 4 7 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_6_or_complete : initialBinary 0x80000000000000000000000000000000000000000000000000 true (frontierMissing opening_6_or) = false := by decide +kernel

noncomputable def opening_7_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_7_and_complete : initialBinary 0x1000000000000000000000000 false (frontierMissing opening_7_and) = false := by decide +kernel

noncomputable def opening_7_or : List (ℕ × List W) := [⟨0x9ca55a4e74aca5294e5294e539d2929529394e729ce939d27384e939ce93a465094a12, rootWithGate 3 4 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_7_or_complete : initialBinary 0x1000000000000000000000000 true (frontierMissing opening_7_or) = false := by decide +kernel

noncomputable def opening_9_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_9_and_complete : initialBinary 0x800000000000000000000000000000000 false (frontierMissing opening_9_and) = false := by decide +kernel

noncomputable def opening_9_or : List (ℕ × List W) := [⟨0x9ca55ace74ace7294e9294e739d2939d2739ce729d2939d2948d2939ce939c65194a12, rootWithGate 0 4 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_9_or_complete : initialBinary 0x800000000000000000000000000000000 true (frontierMissing opening_9_or) = false := by decide +kernel

noncomputable def opening_10_and : List (ℕ × List W) := [⟨0x8d295ac635ad294a4e94a46918ca52956b39c6339d251a5252952528ca54a465184232, rootWithGate 6 7 255 false⟩]
set_option maxRecDepth 100000 in
theorem opening_10_and_complete : initialBinary 0x400 false (frontierMissing opening_10_and) = false := by decide +kernel

noncomputable def opening_10_or : List (ℕ × List W) := [⟨0x8d295aca55ad294a4e94a4a9194e739d6b39ca539d272a52739525394e74a46518c632, rootWithGate 6 7 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_10_or_complete : initialBinary 0x400 true (frontierMissing opening_10_or) = false := by decide +kernel

noncomputable def opening_11_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_11_and_complete : initialBinary 0x8000000000000000000000 false (frontierMissing opening_11_and) = false := by decide +kernel

noncomputable def opening_11_or : List (ℕ × List W) := [⟨0x8d2939c6339d294a4694a4671952749d6b294a3295292a5293952749ce74a425194632, rootWithGate 1 7 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_11_or_complete : initialBinary 0x8000000000000000000000 true (frontierMissing opening_11_or) = false := by decide +kernel

noncomputable def opening_12_and : List (ℕ × List W) := [⟨0x8ca55ace35aca92a4e94946919d25494e739ce339d291a5292952549ca549465194232, rootWithGate 0 7 255 false⟩]
set_option maxRecDepth 100000 in
theorem opening_12_and_complete : initialBinary 0x40000000000000000000000000000000 false (frontierMissing opening_12_and) = false := by decide +kernel

noncomputable def opening_12_or : List (ℕ × List W) := [⟨0x94e75ace55ace93a4e949ca929d2749d2939ce539d292a5293952749ce749c65194632, rootWithGate 0 7 255 true⟩]
set_option maxRecDepth 100000 in
theorem opening_12_or_complete : initialBinary 0x40000000000000000000000000000000 true (frontierMissing opening_12_or) = false := by decide +kernel

noncomputable def opening_13_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
theorem opening_13_and_complete : initialBinary 0x80000 false (frontierMissing opening_13_and) = false := by decide +kernel

noncomputable def opening_13_or : List (ℕ × List W) := [⟨0x8ce739c6339ce93a46949ca7295294a529294a5295293a5294952949d2949c25194a32, rootWithGate 0 1 255 true⟩, ⟨0x94e74a4a54a4e93a4a949ce939d294a52939ce739d293a5294952949d2949c65194a32, rootWithGate 0 1 253 true⟩]
set_option maxRecDepth 100000 in
theorem opening_13_or_complete : initialBinary 0x80000 true (frontierMissing opening_13_or) = false := by decide +kernel

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f true I.AA rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 12 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvRawC I.NN I.AA I.HX I.HY true
      (lookRawC I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 13 12 1 z v))

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
    look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (14 : ℕ) = Nat.succ 13 from rfl, look1RawC_step]
  simp only [show rootReject 13 1 state.1 state.2 = false from rfl, lengthOkay, Bool.cond_false]
  change tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 _ = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change (bif pureSecond state
      (look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 13 12 1)
    then true else _) = _
  rw [pure, mixed]
  rfl

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

  opening_0_or.getD 0 (0, []),
  opening_1_and.getD 0 (0, []),
  opening_1_or.getD 0 (0, []),
  opening_2_and.getD 0 (0, []),
  opening_2_or.getD 0 (0, []),
  opening_3_and.getD 0 (0, []),
  opening_3_or.getD 0 (0, []),
  opening_4_or.getD 0 (0, []),
  opening_5_and.getD 0 (0, []),
  opening_5_or.getD 0 (0, []),
  opening_5_or.getD 1 (0, []),
  opening_6_or.getD 0 (0, []),
  opening_7_or.getD 0 (0, []),
  opening_9_or.getD 0 (0, []),
  opening_10_and.getD 0 (0, []),
  opening_10_or.getD 0 (0, []),
  opening_11_or.getD 0 (0, []),
  opening_12_and.getD 0 (0, []),
  opening_12_or.getD 0 (0, []),
  opening_13_or.getD 0 (0, []),
  opening_13_or.getD 1 (0, [])]

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def transitionFromCode (width : ℕ) (parentAt : ℕ → SearchState) (entry : ℕ) : SearchState :=
  let before := parentAt (entry % 2 ^ width)
  let left := (entry >>> width) % 16
  let right := (entry >>> (width + 4)) % 16
  let dropLeft := if entry.testBit (width + 8) then 2 ^ left else 0
  let dropRight := if entry.testBit (width + 9) then 2 ^ right else 0
  let kept := 2 ^ before.2.length - 1 - dropLeft - dropRight
  secondTransition before left right kept (entry.testBit (width + 10))

-- Each block packs parent indices relative to a shared base.
def relativeTransitionCode (parentWidth block index : ℕ) : ℕ :=
  let base := block % (1 <<< parentWidth)
  let width := (block >>> parentWidth) % 16
  let entry := block >>> (parentWidth + 4 + (11 + width) * index)
  let parent := base + entry % (1 <<< width)
  parent + (((entry >>> width) % 2048) <<< parentWidth)

def decodeDeltas (fuel : ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ) (fun _ _ => [])
    (fun _ rest before data =>
      let lead := data % 256
      if lead = 0 then []
      else if lead = 255 then
        let count := (data >>> 8) % 256
        List.range' before count ++ rest (before + count) (data >>> 16)
      else if lead = 254 then
        let following := before + (data >>> 8) % 65536
        (following - 1) :: rest following (data >>> 24)
      else
        let following := before + lead
        (following - 1) :: rest following (data >>> 8)) fuel


noncomputable def openingContinuation (state : SearchState) : Bool :=
  look1RawC rootReject I.NN I.AA I.HX I.HY true I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2

noncomputable def openingOrbitCoverage (i : ℕ) : Bool :=
  pureSecond (firstAt i) (fun _ wires => !(lookupOrbit 2 wires).isSome)

lemma finishOpeningByOrbit (i : ℕ)
    (two : 1 < (firstAt i).2.length) (small : (firstAt i).2.length < 12)
    (mixed : mixedSecond (firstAt i) = false)
    (complete : openingOrbitCoverage i = false) : openingContinuation (firstAt i) = false := by
  refine afterFirst_false (firstAt i) two small mixed ?_
  refine pureAt_of_covered 12 (firstAt i) afterSecond (fun _ wires => !(lookupOrbit 2 wires).isSome) complete ?_
  intro z wires found
  have certified : (lookupOrbit 2 wires).isSome = true := by simpa using found
  have rejected : rootReject 12 1 z wires = true := by simp [rootReject, rejectOrbit, certified]
  simp only [afterSecond, frc_eq, st_eq, show (13 : ℕ) = Nat.succ 12 from rfl,
    look1RawC_step, rejected, Bool.cond_true]

noncomputable def openingOrbitTest (i : ℕ) : Bool := !openingOrbitCoverage i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch0 : rangeCheck openingOrbitTest 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch1 : rangeCheck openingOrbitTest 3 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch2 : rangeCheck openingOrbitTest 6 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch3 : rangeCheck openingOrbitTest 9 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch4 : rangeCheck openingOrbitTest 12 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch5 : rangeCheck openingOrbitTest 15 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitBatch6 : rangeCheck openingOrbitTest 18 3 = true := by decide +kernel

abbrev openingOrbitAppend := @rangeAppend openingOrbitTest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem openingOrbitAll : rangeCheck openingOrbitTest 0 21 = true :=
  (@openingOrbitAppend 0 9 12 (@openingOrbitAppend 0 3 6 openingOrbitBatch0 (@openingOrbitAppend 3 3 3 openingOrbitBatch1 openingOrbitBatch2)) (@openingOrbitAppend 9 6 6 (@openingOrbitAppend 9 3 3 openingOrbitBatch3 openingOrbitBatch4) (@openingOrbitAppend 15 3 3 openingOrbitBatch5 openingOrbitBatch6)))

lemma openingOrbit_complete {i : ℕ} (inside : i < 21) : openingOrbitCoverage i = false :=
  boolOfNeg (rangeCheck_at openingOrbitAll inside)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first0_mixed : mixedSecond (firstAt 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first0_checked : openingContinuation (firstAt 0) = false :=
  finishOpeningByOrbit 0 (by decide +kernel) (by decide +kernel) first0_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first1_mixed : mixedSecond (firstAt 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first1_checked : openingContinuation (firstAt 1) = false :=
  finishOpeningByOrbit 1 (by decide +kernel) (by decide +kernel) first1_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first2_mixed : mixedSecond (firstAt 2) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first2_checked : openingContinuation (firstAt 2) = false :=
  finishOpeningByOrbit 2 (by decide +kernel) (by decide +kernel) first2_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first3_mixed : mixedSecond (firstAt 3) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first3_checked : openingContinuation (firstAt 3) = false :=
  finishOpeningByOrbit 3 (by decide +kernel) (by decide +kernel) first3_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first4_mixed : mixedSecond (firstAt 4) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first4_checked : openingContinuation (firstAt 4) = false :=
  finishOpeningByOrbit 4 (by decide +kernel) (by decide +kernel) first4_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first5_mixed : mixedSecond (firstAt 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first5_checked : openingContinuation (firstAt 5) = false :=
  finishOpeningByOrbit 5 (by decide +kernel) (by decide +kernel) first5_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first6_mixed : mixedSecond (firstAt 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first6_checked : openingContinuation (firstAt 6) = false :=
  finishOpeningByOrbit 6 (by decide +kernel) (by decide +kernel) first6_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first7_mixed : mixedSecond (firstAt 7) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first7_checked : openingContinuation (firstAt 7) = false :=
  finishOpeningByOrbit 7 (by decide +kernel) (by decide +kernel) first7_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first8_mixed : mixedSecond (firstAt 8) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first8_checked : openingContinuation (firstAt 8) = false :=
  finishOpeningByOrbit 8 (by decide +kernel) (by decide +kernel) first8_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first9_mixed : mixedSecond (firstAt 9) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first9_checked : openingContinuation (firstAt 9) = false :=
  finishOpeningByOrbit 9 (by decide +kernel) (by decide +kernel) first9_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first10_mixed : mixedSecond (firstAt 10) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first10_checked : openingContinuation (firstAt 10) = false :=
  finishOpeningByOrbit 10 (by decide +kernel) (by decide +kernel) first10_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first11_mixed : mixedSecond (firstAt 11) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first11_checked : openingContinuation (firstAt 11) = false :=
  finishOpeningByOrbit 11 (by decide +kernel) (by decide +kernel) first11_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first12_mixed : mixedSecond (firstAt 12) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first12_checked : openingContinuation (firstAt 12) = false :=
  finishOpeningByOrbit 12 (by decide +kernel) (by decide +kernel) first12_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first13_mixed : mixedSecond (firstAt 13) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first13_checked : openingContinuation (firstAt 13) = false :=
  finishOpeningByOrbit 13 (by decide +kernel) (by decide +kernel) first13_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first14_mixed : mixedSecond (firstAt 14) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first14_checked : openingContinuation (firstAt 14) = false :=
  finishOpeningByOrbit 14 (by decide +kernel) (by decide +kernel) first14_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first15_mixed : mixedSecond (firstAt 15) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first15_checked : openingContinuation (firstAt 15) = false :=
  finishOpeningByOrbit 15 (by decide +kernel) (by decide +kernel) first15_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first16_mixed : mixedSecond (firstAt 16) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first16_checked : openingContinuation (firstAt 16) = false :=
  finishOpeningByOrbit 16 (by decide +kernel) (by decide +kernel) first16_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first17_mixed : mixedSecond (firstAt 17) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first17_checked : openingContinuation (firstAt 17) = false :=
  finishOpeningByOrbit 17 (by decide +kernel) (by decide +kernel) first17_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first18_mixed : mixedSecond (firstAt 18) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first18_checked : openingContinuation (firstAt 18) = false :=
  finishOpeningByOrbit 18 (by decide +kernel) (by decide +kernel) first18_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first19_mixed : mixedSecond (firstAt 19) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first19_checked : openingContinuation (firstAt 19) = false :=
  finishOpeningByOrbit 19 (by decide +kernel) (by decide +kernel) first19_mixed (openingOrbit_complete (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first20_mixed : mixedSecond (firstAt 20) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem first20_checked : openingContinuation (firstAt 20) = false :=
  finishOpeningByOrbit 20 (by decide +kernel) (by decide +kernel) first20_mixed (openingOrbit_complete (by decide))

noncomputable abbrev rootPairCheck (hash : ℕ) (kind : Bool) := chkPairPicked rootReject [] rootBounds 0 14 1 hash 0 kind
noncomputable abbrev rootCircuitCheck (hash : ℕ) := chkRaw rootReject [] rootBounds 0 14 1 hash 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_0_and : rootPairCheck 0x200000000000000000000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x200000000000000000000000000000000000000000 false opening_0_and opening_0_and_complete
  intro state member
  simp [opening_0_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_0_or : rootPairCheck 0x200000000000000000000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x200000000000000000000000000000000000000000 true opening_0_or opening_0_or_complete
  intro state member
  simp only [opening_0_or, List.mem_singleton] at member
  subst state
  exact first0_checked

theorem caseBinary_0 : rootCircuitCheck 0x200000000000000000000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_0_and
  · exact caseBinary_0_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_1_and : rootPairCheck 0x10000000000000000000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x10000000000000000000000000000000000000000 false opening_1_and opening_1_and_complete
  intro state member
  simp only [opening_1_and, List.mem_singleton] at member
  subst state
  exact first1_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_1_or : rootPairCheck 0x10000000000000000000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x10000000000000000000000000000000000000000 true opening_1_or opening_1_or_complete
  intro state member
  simp only [opening_1_or, List.mem_singleton] at member
  subst state
  exact first2_checked

theorem caseBinary_1 : rootCircuitCheck 0x10000000000000000000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_1_and
  · exact caseBinary_1_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_2_and : rootPairCheck 0x400000000000000000000000000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x400000000000000000000000000000000000000000000000 false opening_2_and opening_2_and_complete
  intro state member
  simp only [opening_2_and, List.mem_singleton] at member
  subst state
  exact first3_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_2_or : rootPairCheck 0x400000000000000000000000000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x400000000000000000000000000000000000000000000000 true opening_2_or opening_2_or_complete
  intro state member
  simp only [opening_2_or, List.mem_singleton] at member
  subst state
  exact first4_checked

theorem caseBinary_2 : rootCircuitCheck 0x400000000000000000000000000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_2_and
  · exact caseBinary_2_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_3_and : rootPairCheck 0x10000000000000000 false = false := by
  apply initialBinary_from_frontier 0x10000000000000000 false opening_3_and opening_3_and_complete
  intro state member
  simp only [opening_3_and, List.mem_singleton] at member
  subst state
  exact first5_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_3_or : rootPairCheck 0x10000000000000000 true = false := by
  apply initialBinary_from_frontier 0x10000000000000000 true opening_3_or opening_3_or_complete
  intro state member
  simp only [opening_3_or, List.mem_singleton] at member
  subst state
  exact first6_checked

theorem caseBinary_3 : rootCircuitCheck 0x10000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_3_and
  · exact caseBinary_3_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_4_and : rootPairCheck 0x20000000000000 false = false := by
  apply initialBinary_from_frontier 0x20000000000000 false opening_4_and opening_4_and_complete
  intro state member
  simp [opening_4_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_4_or : rootPairCheck 0x20000000000000 true = false := by
  apply initialBinary_from_frontier 0x20000000000000 true opening_4_or opening_4_or_complete
  intro state member
  simp only [opening_4_or, List.mem_singleton] at member
  subst state
  exact first7_checked

theorem caseBinary_4 : rootCircuitCheck 0x20000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_4_and
  · exact caseBinary_4_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_5_and : rootPairCheck 0x100000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x100000000000000000000000 false opening_5_and opening_5_and_complete
  intro state member
  simp only [opening_5_and, List.mem_singleton] at member
  subst state
  exact first8_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_5_or : rootPairCheck 0x100000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x100000000000000000000000 true opening_5_or opening_5_or_complete
  intro state member
  simp only [opening_5_or, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact first9_checked
  · exact first10_checked

theorem caseBinary_5 : rootCircuitCheck 0x100000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_5_and
  · exact caseBinary_5_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_6_and : rootPairCheck 0x80000000000000000000000000000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x80000000000000000000000000000000000000000000000000 false opening_6_and opening_6_and_complete
  intro state member
  simp [opening_6_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_6_or : rootPairCheck 0x80000000000000000000000000000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x80000000000000000000000000000000000000000000000000 true opening_6_or opening_6_or_complete
  intro state member
  simp only [opening_6_or, List.mem_singleton] at member
  subst state
  exact first11_checked

theorem caseBinary_6 : rootCircuitCheck 0x80000000000000000000000000000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_6_and
  · exact caseBinary_6_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_7_and : rootPairCheck 0x1000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x1000000000000000000000000 false opening_7_and opening_7_and_complete
  intro state member
  simp [opening_7_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_7_or : rootPairCheck 0x1000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x1000000000000000000000000 true opening_7_or opening_7_or_complete
  intro state member
  simp only [opening_7_or, List.mem_singleton] at member
  subst state
  exact first12_checked

theorem caseBinary_7 : rootCircuitCheck 0x1000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_7_and
  · exact caseBinary_7_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_9_and : rootPairCheck 0x800000000000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x800000000000000000000000000000000 false opening_9_and opening_9_and_complete
  intro state member
  simp [opening_9_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_9_or : rootPairCheck 0x800000000000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x800000000000000000000000000000000 true opening_9_or opening_9_or_complete
  intro state member
  simp only [opening_9_or, List.mem_singleton] at member
  subst state
  exact first13_checked

theorem caseBinary_9 : rootCircuitCheck 0x800000000000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_9_and
  · exact caseBinary_9_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_10_and : rootPairCheck 0x400 false = false := by
  apply initialBinary_from_frontier 0x400 false opening_10_and opening_10_and_complete
  intro state member
  simp only [opening_10_and, List.mem_singleton] at member
  subst state
  exact first14_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_10_or : rootPairCheck 0x400 true = false := by
  apply initialBinary_from_frontier 0x400 true opening_10_or opening_10_or_complete
  intro state member
  simp only [opening_10_or, List.mem_singleton] at member
  subst state
  exact first15_checked

theorem caseBinary_10 : rootCircuitCheck 0x400 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_10_and
  · exact caseBinary_10_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_11_and : rootPairCheck 0x8000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x8000000000000000000000 false opening_11_and opening_11_and_complete
  intro state member
  simp [opening_11_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_11_or : rootPairCheck 0x8000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x8000000000000000000000 true opening_11_or opening_11_or_complete
  intro state member
  simp only [opening_11_or, List.mem_singleton] at member
  subst state
  exact first16_checked

theorem caseBinary_11 : rootCircuitCheck 0x8000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_11_and
  · exact caseBinary_11_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_12_and : rootPairCheck 0x40000000000000000000000000000000 false = false := by
  apply initialBinary_from_frontier 0x40000000000000000000000000000000 false opening_12_and opening_12_and_complete
  intro state member
  simp only [opening_12_and, List.mem_singleton] at member
  subst state
  exact first17_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_12_or : rootPairCheck 0x40000000000000000000000000000000 true = false := by
  apply initialBinary_from_frontier 0x40000000000000000000000000000000 true opening_12_or opening_12_or_complete
  intro state member
  simp only [opening_12_or, List.mem_singleton] at member
  subst state
  exact first18_checked

theorem caseBinary_12 : rootCircuitCheck 0x40000000000000000000000000000000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_12_and
  · exact caseBinary_12_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_13_and : rootPairCheck 0x80000 false = false := by
  apply initialBinary_from_frontier 0x80000 false opening_13_and opening_13_and_complete
  intro state member
  simp [opening_13_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_13_or : rootPairCheck 0x80000 true = false := by
  apply initialBinary_from_frontier 0x80000 true opening_13_or opening_13_or_complete
  intro state member
  simp only [opening_13_or, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact first19_checked
  · exact first20_checked

theorem caseBinary_13 : rootCircuitCheck 0x80000 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_13_and
  · exact caseBinary_13_or

theorem binaryCertificates : BinaryCertificates rootReject rootBounds := by
  intro p hp
  simp only [binaryRepresentatives,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0x200000000000000000000000000000000000000000, by decide +kernel,caseBinary_0⟩
  · exact ⟨0x10000000000000000000000000000000000000000, by decide +kernel,caseBinary_1⟩
  · exact ⟨0x400000000000000000000000000000000000000000000000, by decide +kernel,caseBinary_2⟩
  · exact ⟨0x10000000000000000, by decide +kernel,caseBinary_3⟩
  · exact ⟨0x20000000000000, by decide +kernel,caseBinary_4⟩
  · exact ⟨0x100000000000000000000000, by decide +kernel,caseBinary_5⟩
  · exact ⟨0x80000000000000000000000000000000000000000000000000, by decide +kernel,caseBinary_6⟩
  · exact ⟨0x1000000000000000000000000, by decide +kernel,caseBinary_7⟩
  · exact ⟨0x100000000000000000000000, by decide +kernel,caseBinary_5⟩
  · exact ⟨0x800000000000000000000000000000000, by decide +kernel,caseBinary_9⟩
  · exact ⟨0x400, by decide +kernel,caseBinary_10⟩
  · exact ⟨0x8000000000000000000000, by decide +kernel,caseBinary_11⟩
  · exact ⟨0x40000000000000000000000000000000, by decide +kernel,caseBinary_12⟩
  · exact ⟨0x80000, by decide +kernel,caseBinary_13⟩

def subChoices (nn : ℕ) (d : Bool) (l : ℕ) (words : List W) : ℕ → List (List W) :=
  List.rec (fun _ => [[]]) (fun w rest later bits =>
    (later (Nat.lor bits (spC nn d l w.s))).map (w :: ·) ++
      if Nat.beq (Nat.lor bits (covC nn d l rest)) l then later bits else []) words

lemma anySub_choices (nn : ℕ) (d : Bool) (l : ℕ) (words : List W) (bits : ℕ)
    (test : List W → Bool) :
    anySubC nn d l words bits test = (subChoices nn d l words bits).any test := by
  induction words generalizing bits test with
  | nil => simp [anySubC, subChoices]
  | cons w rest ih =>
    let included := Nat.lor bits (spC nn d l w.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l rest)) l
    change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l rest bits test) skip)
        true (st included fun c => anySubC nn d l rest c (fun r => test (w :: r)))) =
      (((subChoices nn d l rest included).map (w :: ·)) ++
        if skip then subChoices nn d l rest bits else []).any test
    simp only [bR, st_eq, ih, List.any_append, List.any_map, Function.comp_def]
    cases skip <;> cases (subChoices nn d l rest included).any (fun r => test (w :: r)) <;> simp

lemma startvC_hasP (nn aa hx hy l m g B K t p H ph : ℕ) (v : List W) :
    startvC nn aa hx hy l m g B K t p H ph v =
      (hasP p v && startvC nn aa hx hy l m g B K t 0 H ph v) := by
  unfold startvC
  rw [show hasP 0 v = true from rfl]
  cases hasP p v <;> rfl

lemma chk_preselected (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (v : List W)
    (chosen : ((subChoices I.NN (pos t) (lz Z) (avl (PZ Q) (mz Z) (rawL E)) 0).filter
      (hasP (pwr E Z))) = [v]) :
    chk E Q Z K t H ph = startvC I.NN I.AA I.HX I.HY (lz Z) (mz Z)
      (pL (Q.map fun _ => 16)) (pL (Q.map fun e => 16 + (K - e.2))) K t 0 H ph v := by
  simp only [chk, frc_eq, st_eq, anySub_choices]
  simp_rw [startvC_hasP _ _ _ _ _ _ _ _ _ _ (pwr E Z)]
  rw [← List.any_filter, chosen]
  simp only [List.any_cons, List.any_nil, Bool.or_false]

abbrev rawNegBounds := rootBounds

def rawNegCofactors (i : ℕ) : List (ℕ × ℕ) := rawNegBounds.map (unaryCharge i)

noncomputable def rawNegWords (i : ℕ) : List W :=
  avl (PZ (rawNegCofactors i)) rootPreparedMask (rawL [(i,0)])

noncomputable def rawNegSlots : ℕ := rootPreparedSlots

noncomputable def rawNegRoot (i : ℕ) : SearchState :=
  (pL ((rawNegCofactors i).map fun e => 16 + (13 - e.2)) - sumc (rawNegWords i), rawNegWords i)

noncomputable def rawNegOpen (i : ℕ) (next : ℕ → List W → Bool) : Bool :=
  nodeC I.NN next false I.AA rootPreparedMask rawNegSlots 13 (rawNegWords i).length
    (rawNegRoot i).1 (rawNegWords i) (fun h xs => pairsC FF h (fs xs))

noncomputable def rawNegAfterOpen : ℕ → List W → Bool :=
  look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 13 12 0

lemma noMixedRaw (nn aa hx hy l m g k z : ℕ) (v : List W)
    (F : ℕ → ℕ → ℕ → List W → Bool) (raw : ∀ w ∈ v, w.r ≠ 0) :
    mvC nn aa hx hy F l m g k 0 z v 0 = false := by
  have noInternal : fr (mkXC nn false l (wstC nn false l v) v) = [] := by
    rw [fr_eq_filter, List.filter_eq_nil_iff]
    intro a ha
    rw [mkXC_map] at ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    exact fun h => raw w hw (Nat.eq_of_beq_eq_true h)
  simp only [mvC, pos, prd, Nat.sub_zero, bR]
  rw [nodeC_as_mode]
  simp [pairsN, noInternal, pairs, scan]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawNegSlots_eq (i : ℕ) : pL ((rawNegCofactors i).map fun _ => 16) = rawNegSlots := by
  simp only [rawNegCofactors, List.map_map, Function.comp_def]
  rfl

lemma rawNegSelection (i : ℕ)
    (selected : ((subChoices I.NN false I.AA (rawNegWords i) 0).filter
      (hasP (pwr [(i,0)] 0))) = [rawNegWords i])
    (hlen : (rawNegWords i).length = 9) (hraw : ∀ w ∈ rawNegWords i, w.r ≠ 0) :
    chk [(i,0)] (rawNegCofactors i) 0 13 0 FF 1 =
      (bif Nat.beq (Nat.land (rawNegRoot i).1 rawNegSlots) rawNegSlots
        then rawNegOpen i rawNegAfterOpen else false) := by
  have hselected : ((subChoices I.NN (pos 0) (lz 0)
      (avl (PZ (rawNegCofactors i)) (mz 0) (rawL [(i,0)])) 0).filter
      (hasP (pwr [(i,0)] 0))) = [rawNegWords i] := by
    rw [show pos 0 = false from rfl, rootPreparedL_eq, rootPreparedMask_eq]
    exact selected
  rw [chk_preselected _ _ _ _ _ _ _ _ hselected, rootPreparedL_eq, rootPreparedMask_eq, rawNegSlots_eq]
  simp only [startvC, hasP, bR, Nat.beq_refl, Bool.cond_true, hlen, child, st_eq]
  simp only [show Nat.ble 9 (Nat.sub 14 0) = true from rfl, Bool.cond_true]
  change (bif Nat.beq (Nat.land (rawNegRoot i).1 rawNegSlots) rawNegSlots then
    topCC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 FF 1 13 0 (rawNegRoot i).1
      (rawNegWords i) else false) = _
  simp only [topCC, hlen, pos, bR, show Nat.ble 9 1 = false from rfl, Bool.cond_false]
  simp only [tstC, hlen, bR, show Nat.beq 9 (Nat.sub 14 0) = false from rfl,
    show Nat.beq 10 (Nat.sub 14 0) = false from rfl, Bool.cond_false]
  have toBool (b : Bool) : (bif b then true else false) = b := by cases b <;> rfl
  simp only [noMixedRaw _ _ _ _ _ _ _ _ _ _ _ hraw, Bool.cond_false,
    Bool.cond_self, toBool, rawNegOpen, rawNegAfterOpen, hlen]
  rfl

lemma rawNegHashFull (x : ℕ) : hb FF x = true := by
  have hm : x % MM < MM := Nat.mod_lt _ (by decide)
  have bit : FF.testBit (x % MM) = true := by simpa [FF] using hm
  have positive : (1 &&& (FF >>> (x % MM))) ≠ 0 := by simpa [Nat.testBit] using bit
  have small : 1 &&& (FF >>> (x % MM)) ≤ 1 := Nat.and_le_left
  rw [hb, Nat.beq_eq]
  change (FF >>> (x % MM)) &&& 1 = 1
  rw [Nat.and_comm]
  omega

lemma rawNegPairs (f : XW → XW → Bool) (xs : List XW) : pairsC FF f xs = pairs f xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [pairsC_eq, ih]
    simp only [rawNegHashFull, Bool.true_and]
    simp only [pairs, bR, scan_eq_any]
    cases rest.any (f a) <;> rfl

noncomputable def rawNegPure (e : ℕ) (state : SearchState) (next : ℕ → List W → Bool) : Bool :=
  nodeC I.NN next false I.AA rootPreparedMask rawNegSlots e state.2.length state.1 state.2 pairsS

lemma rawNegOpening_eq (i : ℕ) (next : ℕ → List W → Bool) :
    rawNegOpen i next = rawNegPure 13 (rawNegRoot i) next := by
  unfold rawNegOpen rawNegPure pairsS
  simp only [rawNegPairs, rawNegRoot]

lemma rawNegPure_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : rawNegPure e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    rawNegPure e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [rawNegPure, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rawNegSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => frontierMissing states)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : frontierMissing states z v
        · exact Bool.noConfusion ((checked _ (frontierMissing_false missed)).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

noncomputable def rawNegMixed (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13)
      I.AA rootPreparedMask rawNegSlots 12 0 z v 0))

noncomputable def rawNegAfterTwo (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 12 11 0 z v))

lemma rawNegAfterOpen_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : rawNegMixed state = false)
    (pure : rawNegPure 12 state (fun z v => rawNegAfterTwo (z,v)) = false) :
    rawNegAfterOpen state.1 state.2 = false := by
  have hl : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [rawNegAfterOpen, show (13 : ℕ) = Nat.succ 12 from rfl, look1C_step, hl, Bool.cond_false]
  change tstC I.NN I.AA I.HX I.HY false I.AA 13 state.2 _ = _
  rw [choose0]
  simp only [rawNegAfterTwo, frc_eq, st_eq] at pure
  simp only [rawNegMixed, frc_eq, st_eq] at mixed
  change (bif rawNegPure 12 state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 12 11 0)
    then true else _) = _
  rw [pure, mixed]
  rfl

noncomputable def rawNegStoredWords (index : ℕ) : List W :=
  let word := rootPreparedWords.getD index ⟨0,0,0,0,3⟩
  addS ⟨rootPreparedMask ^^^ word.s, word.b, word.a, word.c, 3⟩ rootPreparedWords

noncomputable def rawNegStarts : List SearchState := [⟨0x9d295ace759d294a4e94a4e938ca54a56b39ce738d293a4a9494a948d252a465194a30, rawNegStoredWords 5⟩, ⟨0x8d295ace35ad294a4e94a46919d254956b39ce339d291a5292952549ca54a465194232, rawNegStoredWords 7⟩, ⟨0x9ca55ace75aca92a4e9494e939d294a4e739ce739d293a5294952949d2949465194a32, rawNegStoredWords 0⟩]
def rawNegFirstCodes : List ℕ := [
0x10860c8604861202020211c201c2118201821142110210c200c21842104211d911d5119511d11191115111cd118d114d110d11c5118501851145110510c5188505c1058104c10441121c121411d4121011d01150120c020c11cc114c110c12081148110810c81204020411c41144110410c400c418841084060005c004c00440, 0x121e021e121a021a11da01da121611d61196121211d211921152120e020e11ce01ce118e018e114e110e160a120a060a020a15ca11ca05ca01ca158a118a058a018a154a114a150a110a14ca10ca04ca00ca120611c611861146110610c61886,
]

-- Decode the retained inputs and the two primitive gates without replaying their path.
def rawNegInputMasks : List ℕ := [0x3feffdff7fdff3fbfeffdfd7efb7f3f5fe, 0x5ff7fdff7fdffbfffddfb7df6fe7fbf1fa, 0x7fbeeff7bdfeefb7ebfbfcff9fbfefe7fdff]
def rawNegPrimitiveCodes : List ℕ := [0x200e030c3e16eb84ba5530683b9d4e8782a950a658140dc6a341988c42121, 0x70300c2ed75b2dd2c954b9d8ea743b8d84c351a0cc42121, 0x2a341c2dd6cb84ba592a953a1a00e060a85006021c3a1d0c76419cd0472c35db0773b198f0572b118aa542990cb0371b0cc64380b85826110]
def rawNegFlatCodes : List (List ℕ) := [[0xc183050c103033c007000b842c10a842810984241088420107841c1068418105841410484028038402620980250090023208c04100804200, 0xd3c34e0d343485d183450d103430d007360cd03320cc432f4cb832d0ca03264c943240c8c3201be02d80ae029809e02580c3cf0b0c283080, 0x7021a0840250083820c093020a0820206081022c06a01a4068819c066819808582140848210074018a062018606101b575d543530d483515, 0x98da43688e9e3a70e9c3668e9a3660d963650d923640dd03630d8a3620d852612d84a6115844610eae08b022a08a02260890222088021e08, 0x7959c5c695985651592564158e56315ae46b11aa46a12e64b912e2468119e467119a4b611964649190463918c46291ca46b8dac36a8da836, 0x921a28e7a19c866a198865a194864a18f563cd8f26b9b6c66a9b686699b64668999e6d7199a664198e66b95ac5ca972856995a45c895a056, 0xa36dcda735acc6a31a4c67319ac6b2f28b68ad9ab6b29a8ab8a99ca65aa2c96a25a4968a69c966a59898ba3ae86b23ac86aa1a88ea21a686, 0x2f66bd1ad4eb51ab46b4dab3dbc9ab169c5a516849aefdb3da8f693daee6b3b28e69b9aed6b35aad6], [0x98023228489f227489b22648a472918a44290ca42490022128049e127049a126049612504921240482720988a120908232088c2220804200, 0x501d207401cc07281c807181c407a3ca8d2a30a8b6a28a892a20a876a18a842a0ca8229c0a6e29b0a6b29a966929a0a672999664298ca622, 0x80e1e3870eda3b60ed63850e123840ece3830e0a3820e483888a202878a1c2868a182858a942a48a902a38a0c2930a082818a1e07681d807, 0x81a1e6d79a1c6869b5a6861a166851b526841a0e6939a0b082ba0ac829e0a6d892204c7931c48692184c592144849310483920c482922238, 0x7b61cdb8b222be7ae1ab862e20a872a18a85aaa2987a71c986a622888221e886a2d28a89fa07e79e1c7e69e187859f947849e107889b6268, 0x22f883f20ee7ba22d88361edd], [0x10030c050c03080304035c005800540050004c004800440440043c0438043800340430042c0428042800240320031c0318031402100110000c010c0008000400, 0x858484e48480847086027c0378035c0374035803700354036c03500368034c0348034402640264034002600260033c0238023803340230022c02280228031005, 0x50104c174c104414641464104014601460103c1438143810341430142c162c14241020101c101810141480128013101110100c100811081085f0857085607210, 0x82327e207a205e2076205a20722056206e2052206a204e204a20662462243a2432282a24262022201e201a2082227c1078105c10741058107010541754105017, 0xc210c2091f091506e409140919490a49090906092027e307a305e3076305a30723056306e3052306a304e304a30663462343a3436392a34263022301e301a30, 0x78205c2b5c20582b582054206c20502068204c2b4c204424642464204024602460203c2a3c24342430242c2428242820242020201c2018201424802280231020, 0x6c30503d50304c304830443464346430403c40343c3438343830343430342c3428342830243020301c301830143480328033103095709550953094a496027c20, 0x444e44444044604460403c4438443840344430442c4428442840244020401c40184014448042804399609940993098e49a027c3d7c305c307430583d58305430, 0x56036e0352036a034e034a0381126602660381026202620380f23a023a0380d280c280b22a022a037c4f7c405c4f5c4058407040544f5440504068404c404840, 0x50504c504850385428547e027a025e0276025a027202be02ba02b602b202ae02aa02a60256026e0252026a024e024a02a2029e027e037a035e0376035a037203, 0xa4605467506750604c60a0609c6044644460406440603c643c603864386034643460306430602c642c6024631c635c545854545450544c5448545c5058505450, 0x3470307430702c742c70287428701c835f105b10571053104f104b103b142b145f005b00570053004f004b003b042b045c605860bc60b860b460b060ac60a860, 0x3c843c8034843480308430802c842c80288428805c7b5c70587bbc70b870b470b070ac70a870a470547050704c70a0709c7044744470407440703c743c703474, 0x44944490409440903c943c903894389034943490309430902c942c907c8d5c80bc80b880b480b080ac80a880a480548050804c80a0809c804484448040844080, 0x2a767ca05ca058a070a02957294729372914290460a460a028f438a438a028d428c428b67c9f5c905890bc90b890b490b090ac90a890a49050904c90a0909c90, 0x58b470b454b450b44cb47cb078b05cb074b058b070b054b050b04cb064b460b438b47ca45ca458a470a4bca4b8a4b4a4b0a4aca4a8a4a4a42956294629362a86, 0x38d47cc478c45cc474c458c470c454c46cc450c468c44cc448c47cc078c05cc074c058c070c054c06cc050c068c04cc048c064c460c438c47cb478b45cb474b4, 0x393b391464e464e0390438fa7cd478d45cd474d458d470d454d46cd450d468d44cd448d47cd078d05cd074d058d070d054d06cd050d068d04cd048d064d460d4, 0x78f05cf058f054f06cf050f068f04cf064f460f47ce4397a396a3af43ae43ada3ac43ab43aaa3a9439546ce43944393a3a843a747ce0397b396b39506ce03940, 0x6174616c62f462ec62d462c462bc62a462946154614c61346284627461fd6170616d6150614d61306114610c7cf478f45cf458f454f46cf450f468f44cf47cf0, 0x655e654465346684667465ff657f6560655f65406530651e7d045d047504590455046d0451044d0449047d005d007500590055006d0051004d004900650461fc, 0x7270567052704e707d145d14591471145514511469144d1449147d105d10591071105510511069104d10491065fe657e656466fe66e466d466ce66b466a46694, 0x5d305930bd30b930b530b130ad30a930a53055305137513049f04af04ae04ac04ab04a907e807a805e8076805a80728056805280a1307e707a705e7076705a70, 0xa5506dff6d606ee06ed06eb06ea06e907d4d7d405d407540594d5940bd40b940b540b140ad40a940a54055406d4769706af06ad06ac06aa06a907d3079305d3b, 0x7ad05ed05ad07ec05ec05ac072c07eb05eb076b05ab07ea07aa05ea05aa07e907a905e9076905a9072907d505d5f5d5059507150bd50b950b550b150ad50a950, 0x7d7f7d707d605d6071fd717b7ef05ef05af072f07ee05ee076e05ae07ed0]]

def rawNegSecondRows : List ℕ := [
0x1aff, 0xfff1b, 0xcff2b, 0xdff38,
0xfff2b1a01, 0x13ff1e0d0f1a02, 0x5ff14104303, 0x14ff0613100e0d0f180104,
0x12ff150513100e0d0f1806, 0x10ff1201140513100e0d0f1807, 0xbff11111517011e0d0f170108, 0x1010c10112c520a,
0x10ff0e10111501150112010d0d0f160b, 0x6ff111d111529400c, 0x4ff171d2609202b150d, 0x3ff05162f1409202b150e,
0x4ff100e1e111429400f, 0x5ff05040b0e110d1113011a0f120d2110, 0x3ff05010409060e110d1112011b0f120d2111, 0x3ff2a110d11121c210d0f1212,
0x4b112e4f13, 0x1011704060d110c11131b11110d2014, 0x301040d0e0d0b060c1113100b11110d101015, 0x1030a230b060c11131b221d1016,
0x3ff0a0405040504050b01110c11131b121e0f1017, 0x2020e1d0d050c11131b231c1018, 0x20102080404050504050901120c11131b131e0e1019, 0x1060504041b01130c11131b241b101a,
0x12fff8, 0xbff010bfe, 0xcff0117fe, 0xbff0124fe,
0xaff190c1201f8, 0xeff0b0c0c0c1101fa, 0xeff0f0a0c0c0c11fc, 0xcff0e010e0a0c0c0c11fd,
0x4ff0d0d193500fefe, 0xeff050c0d0f01090d0c0c1000fffe, 0x9ff0e01040c0d0f170c0c100100fe, 0x4ff0a0d110d0f0b0c0c1c0101fe,
0x3ff05090d110d0f0b0c0c1c0102fe, 0x3ff110d110d0f0b0c0c1c0103fe, 0x3ff04100d110d0f170c1c0104fe, 0x403100d09080d0f0c0b0c100c0105fe,
0x4ff040904060c01110d0f0c0b1c0c0106fe, 0x10507050a0c0b070d0f240f0c0107fe, 0x1020301040805050b01120d0f0d0b1b0c0108fe, 0x1030909050b0d060d0f250e0c0109fe,
0x405010804050a01130d0f330c010afe, 0x1aff019ffe, 0x1fff01bafe, 0x8ff01dafe,
0x24ff291b019ffe, 0x15ff0208fe, 0x15ff021efe, 0x8ff0234fe,
0x22ff5901281b01a0fe, 0x4ff0260fe, 0x20ff27015828011a0101a1fe, 0x4ff0286fe,
0x1fff2626580127011a0101a3fe, 0x19ff2025265801e8fe, 0x14ff39061f071f0d16161f0f01dafe, 0x7ff02dafe,
0x5ff552526584501a5fe, 0x1eff5a25260e16161e4501a6fe, 0x7ff0307fe, 0x7ff030ffe,
0x1dff2f59252624161e113401a7fe, 0x1bff1e87252624161e113401a8fe, 0x1bff685825261014161e4501a9fe, 0x10ff381d3e2e01192526871601aafe,
0xfff481d0a0874250d191114164c1601abfe, 0xbff211c1a1d303d02adfe, 0x8ff481a1d3057252659012d1601acfe, 0xeff351b1a1d303e02aefe,
0xbff5e1a1d305825263c1d2e1601adfe, 0xeff4f1a1a1d303f02affe, 0xbff771a1d3059252627322e1601aefe, 0xbff1b1b151d011967152a0119257f2e1601affe,
0xfff8d4808175911144e161b17171601b0fe, 0xaff1c67191c1d2e4002b2fe, 0x8ffa61c1d2e5a252701572e1601b1fe, 0x7ff14361b151b01bf01194c582e01c8fe,
0xeff0176fe4c291619191501c9fe, 0x9ff172f651a1c1d2e3f02b5fe, 0x8ffce1c1d2e59260125582e1801b2fe, 0x6ff132a1a011b1b15d9013f26582e01cbfe,
0xeff01c2fe261a1116172e01ccfe, 0x8ff16292d67191c1d2e3e02b8fe, 0x8fff41c1d2e59012426582e1a01b3fe, 0x8ff21292c671f1c1d2e3302c5fe,
0x8ff29292c671f1c1d2e3302c6fe, 0x5ff1b091f09540c0f0c95082706150e1a255216441a01b4fe, 0xeff0f0908090e0809090f080b091009100c0f0c0d091109161c1d1608101706150e1a180d190d012b1616012d1a01b5fe, 0x5ff2e094a09290c0f0cdf0e1a4b2c164401d0fe,
0xeff14010e0907090f0809090f080a0911090f0c0f0c0e091109161c1d16080f011706140e1a190c01251e0e1616012d1b01b6fe, 0x6ff0f5b09210911090f0c0f0cdf0e3f261e0e164401d2fe, 0xbff15140f0907090f0808091008090911090f0c0f0c0f091109321d16080f1806130e1a01241c0a1e0e1616012d1c01b7fe, 0x5ff0c070d080c092e292b68201b1d2d3102cdfe,
0x3ff11070d080c37292b68201b1d2d3102cefe, 0x3ff14070d140a2d292b68201b1d2d3102cffe, 0x3ff1714090b0a2d292b68201b1d2d3102d0fe, 0x3ff1a080c090b37292b68201b1d2d3102d1fe,
0x3ff1d080c140b2c292b68201b1d2d3102d2fe, 0x3ff20140a0a0b2c292b68201b1d2d3102d3fe, 0x1040c0e053e0907097b0c0f0c0f090a10a6151a771616230b01d4fe, 0x105050403050405050a0a011415090709090f0809090f09090a100e0c0f0c0f090a1011381d08081f060b151a1c090125012b1616230b1d01b8fe,
0xc09192a093009520c0f0c0f09c0153f5216162e01d6fe, 0x10202020405030405040501130d080114090809090f07090a0f09090a100d0c0f0c0f090b10111c1b011d08081f060a151a01241f07012b1616240a1e01b9fe, 0xc042e15095b09270c0f0c0f09c015652c16162e01d8fe, 0x1010202040404040404060c0701140f06090909090f07090a0f08090b100c0c0f0c0f090c10111c77151a0124012523091616250901d9fe,
]

noncomputable def rawNegStart (i : ℕ) : SearchState := rawNegStarts.getD i (0, [])

noncomputable def rawNegFirst (i : ℕ) : SearchState :=
  let block := rawNegFirstCodes.getD (i / 64) 0
  transitionFromCode 2 rawNegStart ((block >>> (16 * (i % 64))) % 65536)

def selectRawNegInputs (inputs : List W) : ℕ → List W :=
  List.rec (motive := fun _ => ℕ → List W) (fun _ => [])
    (fun wire _ rest mask =>
      let tail := rest (mask >>> 1)
      if mask.testBit 0 then wire :: tail else tail) inputs

noncomputable def rawNegPrimitive (root : List W) (data id : ℕ) : W × ℕ :=
  let code := (data >>> (9*id)) % 512
  let zero : W := ⟨0,0,0,0,3⟩
  let a := root.getD (code % 16) zero
  let b := root.getD ((code >>> 4) % 16) zero
  (opW (code.testBit 8) a b, Nat.lor a.c b.c)

noncomputable def rawNegSecond (i : ℕ) : SearchState :=
  let (axis, index) := if i < 247 then (0,i) else if i < 414 then (1,i-247) else (2,i-414)
  let width := if axis = 2 then 6 else 5
  let base := rawNegStart axis
  let packed := ((rawNegFlatCodes.getD axis []).getD (index / 32) 0) >>> ((4+2*width) * (index % 32))
  let mask := (rawNegInputMasks.getD axis 0) >>> (9 * (packed % 16))
  let raw := selectRawNegInputs base.2 mask
  let records := rawNegPrimitiveCodes.getD axis 0
  let a := rawNegPrimitive base.2 records ((packed >>> 4) % 2^width)
  let b := rawNegPrimitive base.2 records ((packed >>> (4+width)) % 2^width)
  let stock := addS a.1 (addS b.1 raw)
  (base.1 + sumc base.2 - (a.2 + b.2 + sumc (a.1 :: b.1 :: raw)), stock)

def rawNegSuccessors (i : ℕ) : List ℕ := decodeDeltas 64 0 (rawNegSecondRows.getD i 0)

noncomputable def rawNegCover (i : ℕ) : Bool :=
  let state := rawNegFirst i
  let ids := rawNegSuccessors i
  (!rawNegPure 12 state (frontierMissing (ids.map rawNegSecond))) &&
    ((ids.all fun j => decide (j < 1229)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def rawNegMixedTest (i : ℕ) : Bool := !rawNegMixed (rawNegFirst i)
noncomputable def rawNegSecondTest (i : ℕ) : Bool := !rawNegAfterTwo (rawNegSecond i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegStored0 : rawNegRoot 0 = rawNegStart 0 := Eq.refl _

noncomputable def rawNegOpening0 : List SearchState := (List.range' 0 28).map rawNegFirst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegOpening0_complete :
    rawNegPure 13 (rawNegStart 0) (frontierMissing rawNegOpening0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegStored2 : rawNegRoot 2 = rawNegStart 1 := Eq.refl _

noncomputable def rawNegOpening2 : List SearchState := (List.range' 28 21).map rawNegFirst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegOpening2_complete :
    rawNegPure 13 (rawNegStart 1) (frontierMissing rawNegOpening2) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegStored7 : rawNegRoot 7 = rawNegStart 2 := Eq.refl _

noncomputable def rawNegOpening7 : List SearchState := (List.range' 49 63).map rawNegFirst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegOpening7_complete :
    rawNegPure 13 (rawNegStart 2) (frontierMissing rawNegOpening7) = false := by decide +kernel

lemma rawNegFirst_checked (i : ℕ) (hi : i < 112)
    (coverage : rangeCheck rawNegCover 0 112 = true)
    (mixed : rangeCheck rawNegMixedTest 0 112 = true)
    (second : rangeCheck rawNegSecondTest 0 1229 = true) :
    rawNegAfterOpen (rawNegFirst i).1 (rawNegFirst i).2 = false := by
  have finish (state : SearchState) (ids : List ℕ) (next : ℕ → SearchState)
      (checked : (!rawNegPure 12 state (frontierMissing (ids.map next))) &&
        ((ids.all fun j => decide (j < 1229)) &&
         (decide (1 < state.2.length) && decide (state.2.length < 12))) = true)
      (hm : rawNegMixed state = false)
      (hn : ∀ j < 1229, rawNegAfterTwo (next j) = false) :
      rawNegAfterOpen state.1 state.2 = false := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    obtain ⟨complete, valid, htwo, hsmall⟩ := checked
    refine rawNegAfterOpen_false state htwo hsmall hm ?_
    refine rawNegPure_from_frontier 12 state (ids.map next) rawNegAfterTwo (boolOfNeg complete) ?_
    rintro _ member
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
    exact hn j (of_decide_eq_true (List.all_eq_true.mp valid j hj))
  have hc := @rangeCheck_at rawNegCover 112 i coverage hi
  simp only [rawNegCover] at hc
  have hm := @rangeCheck_at rawNegMixedTest 112 i mixed hi
  simp only [rawNegMixedTest] at hm
  have tails (j : ℕ) (hj : j < 1229) : rawNegAfterTwo (rawNegSecond j) = false := by
    have h := @rangeCheck_at rawNegSecondTest 1229 j second hj
    simp only [rawNegSecondTest] at h
    exact boolOfNeg h
  exact finish (rawNegFirst i) (rawNegSuccessors i) rawNegSecond hc (boolOfNeg hm) tails

lemma rawNeg_checked (i root start count : ℕ)
    (selected : ((subChoices I.NN false I.AA (rawNegWords i) 0).filter
      (hasP (pwr [(i,0)] 0))) = [rawNegWords i])
    (len : (rawNegWords i).length = 9) (raw : ∀ w ∈ rawNegWords i, w.r ≠ 0)
    (stored : rawNegRoot i = rawNegStart root) (bound : start+count ≤ 112)
    (opening : rawNegPure 13 (rawNegStart root)
      (frontierMissing ((List.range' start count).map rawNegFirst)) = false)
    (coverage : rangeCheck rawNegCover 0 112 = true)
    (mixed : rangeCheck rawNegMixedTest 0 112 = true)
    (second : rangeCheck rawNegSecondTest 0 1229 = true) :
    chk [(i,0)] (rawNegCofactors i) 0 13 0 FF 1 = false := by
  rw [rawNegSelection i selected len raw, rawNegOpening_eq, stored]
  have result := rawNegPure_from_frontier 13 (rawNegStart root)
    ((List.range' start count).map rawNegFirst) (fun s => rawNegAfterOpen s.1 s.2) opening (by
      intro state h
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      have hbound := (List.mem_range'_1.mp hj).2
      exact rawNegFirst_checked j (by omega) coverage mixed second)
  rw [result]
  cases Nat.beq (Nat.land (rawNegStart root).1 rawNegSlots) rawNegSlots <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover0 : rangeCheck rawNegCover 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover1 : rangeCheck rawNegCover 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover2 : rangeCheck rawNegCover 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover3 : rangeCheck rawNegCover 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover4 : rangeCheck rawNegCover 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover5 : rangeCheck rawNegCover 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover6 : rangeCheck rawNegCover 96 16 = true := by decide +kernel

abbrev appendNegCoverage := @rangeAppend rawNegCover

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCoverAll : rangeCheck rawNegCover 0 112 = true :=
  (@appendNegCoverage 0 48 64
    (@appendNegCoverage 0 16 32
     negCover0
     (@appendNegCoverage 16 16 16
      negCover1
      negCover2))
    (@appendNegCoverage 48 32 32
     (@appendNegCoverage 48 16 16
      negCover3
      negCover4)
     (@appendNegCoverage 80 16 16
      negCover5
      negCover6)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed0 : rangeCheck rawNegMixedTest 0 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed1 : rangeCheck rawNegMixedTest 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed2 : rangeCheck rawNegMixedTest 48 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed3 : rangeCheck rawNegMixedTest 72 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed4 : rangeCheck rawNegMixedTest 96 16 = true := by decide +kernel

abbrev negMixedAppend := @rangeAppend rawNegMixedTest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixedAll : rangeCheck rawNegMixedTest 0 112 = true :=
  (@negMixedAppend 0 48 64 (@negMixedAppend 0 24 24 negMixed0 negMixed1) (@negMixedAppend 48 24 40 negMixed2 (@negMixedAppend 72 24 16 negMixed3 negMixed4)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond0 : rangeCheck rawNegSecondTest 0 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond1 : rangeCheck rawNegSecondTest 25 31 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond2 : rangeCheck rawNegSecondTest 56 41 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond3 : rangeCheck rawNegSecondTest 97 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond4 : rangeCheck rawNegSecondTest 159 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond5 : rangeCheck rawNegSecondTest 221 53 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond6 : rangeCheck rawNegSecondTest 274 31 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond7 : rangeCheck rawNegSecondTest 305 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond8 : rangeCheck rawNegSecondTest 367 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond9 : rangeCheck rawNegSecondTest 429 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond10 : rangeCheck rawNegSecondTest 457 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond11 : rangeCheck rawNegSecondTest 489 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond12 : rangeCheck rawNegSecondTest 551 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond13 : rangeCheck rawNegSecondTest 613 46 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond14 : rangeCheck rawNegSecondTest 659 54 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond15 : rangeCheck rawNegSecondTest 713 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond16 : rangeCheck rawNegSecondTest 775 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond17 : rangeCheck rawNegSecondTest 837 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond18 : rangeCheck rawNegSecondTest 899 57 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond19 : rangeCheck rawNegSecondTest 956 50 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond20 : rangeCheck rawNegSecondTest 1006 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond21 : rangeCheck rawNegSecondTest 1068 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond22 : rangeCheck rawNegSecondTest 1130 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond23 : rangeCheck rawNegSecondTest 1192 37 = true := by decide +kernel

abbrev negSecondAppend := @rangeAppend rawNegSecondTest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecondAll : rangeCheck rawNegSecondTest 0 1229 = true :=
  (@negSecondAppend 0 551 678 (@negSecondAppend 0 274 277 (@negSecondAppend 0 97 177 (@negSecondAppend 0 25 72 negSecond0 (@negSecondAppend 25 31 41 negSecond1 negSecond2)) (@negSecondAppend 97 62 115 negSecond3 (@negSecondAppend 159 62 53 negSecond4 negSecond5))) (@negSecondAppend 274 155 122 (@negSecondAppend 274 31 124 negSecond6 (@negSecondAppend 305 62 62 negSecond7 negSecond8)) (@negSecondAppend 429 28 94 negSecond9 (@negSecondAppend 457 32 62 negSecond10 negSecond11)))) (@negSecondAppend 551 348 330 (@negSecondAppend 551 162 186 (@negSecondAppend 551 62 100 negSecond12 (@negSecondAppend 613 46 54 negSecond13 negSecond14)) (@negSecondAppend 713 62 124 negSecond15 (@negSecondAppend 775 62 62 negSecond16 negSecond17))) (@negSecondAppend 899 169 161 (@negSecondAppend 899 57 112 negSecond18 (@negSecondAppend 956 50 62 negSecond19 negSecond20)) (@negSecondAppend 1068 62 99 negSecond21 (@negSecondAppend 1130 62 37 negSecond22 negSecond23)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase0 : chk [(0,0)] (rawNegCofactors 0) 0 13 0 FF 1 = false := by
  have noInternal : (rawNegWords 0).all (fun w => !Nat.beq w.r 0) = true := by decide +kernel
  refine rawNeg_checked 0 0 0 28 rfl rfl ?_ rawNegStored0
    (by decide) rawNegOpening0_complete negCoverAll negMixedAll negSecondAll
  intro w hw h
  have bad := List.all_eq_true.mp noInternal w hw
  simp [h] at bad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase2 : chk [(2,0)] (rawNegCofactors 2) 0 13 0 FF 1 = false := by
  have noInternal : (rawNegWords 2).all (fun w => !Nat.beq w.r 0) = true := by decide +kernel
  refine rawNeg_checked 2 1 28 21 rfl rfl ?_ rawNegStored2
    (by decide) rawNegOpening2_complete negCoverAll negMixedAll negSecondAll
  intro w hw h
  have bad := List.all_eq_true.mp noInternal w hw
  simp [h] at bad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase7 : chk [(7,0)] (rawNegCofactors 7) 0 13 0 FF 1 = false := by
  have noInternal : (rawNegWords 7).all (fun w => !Nat.beq w.r 0) = true := by decide +kernel
  refine rawNeg_checked 7 2 49 63 rfl rfl ?_ rawNegStored7
    (by decide) rawNegOpening7_complete negCoverAll negMixedAll negSecondAll
  intro w hw h
  have bad := List.all_eq_true.mp noInternal w hw
  simp [h] at bad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase1 : chk [(1,0)] (rawNegCofactors 1) 0 13 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase6 : chk [(6,0)] (rawNegCofactors 6) 0 13 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unaryCertificates : UnaryCertificates :=
  build_unary_strong_certificates rootBounds_p rootBounds_I iroot
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by
      intro i hi
      simp only [unaryRepresentatives,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact rawNegCase0
      · exact rawNegCase1
      · exact rawNegCase2
      · exact rawNegCase6
      · exact rawNegCase7
    )


end inst_data
end PEqualNP.Outside.L_meta_35240_aux

open PEqualNP.Outside.L_meta_35240_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_35240 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfit hone hev
  have hf : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x :=
    fun x => (hev x).trans (f_graph x).symm
  by_cases hnot : ∃ g ∈ gates, g.op = .not
  · have hc : notCount gates = 1 := Nat.le_antisymm (count_le_one hone) (count_pos hnot)
    have hge : 15 ≤ gates.length := by
      by_contra hlt
      obtain ⟨k,t,ht,hk,S,hS,hl⟩ := fullBridge gates o (fanInTwo_of hfit) hf
      by_cases hsmall : k < 14
      · exact fullLower iroot hsmall (hl.sol.mono le_rfl hS)
      have he : k = 14 := by omega
      have ht1 : t = 1 := by omega
      subst k
      subst t
      exact fullExclusion rootReject_sound rootBounds_p rootBounds_I iroot binaryCertificates unaryCertificates hS hl
    have hw : witness.length = 15 := rfl
    exact ⟨witness, 22, witness_basis, by omega, fun x => (witness_eval x).trans (f_graph x)⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨ho, hlen⟩ := hfit g hg
    refine ⟨?_, hlen⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim
