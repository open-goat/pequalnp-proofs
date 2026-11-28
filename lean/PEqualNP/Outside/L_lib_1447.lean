import Mathlib
import PEqualNP.Defs

-- A monotone encoder of the down-closed sets of an ordered set whose words can be decoded after a
-- losses and f gains: wire counts, exact copies of each element, and the case of least width.
--
-- Write t = a + f + 1. Two different down-closed sets have words that differ by at least t wires in one
-- direction, otherwise one noisy word is close to both (`sep`). So adding one element gains at least t
-- wires (`gain`), and along any chain of down-closed sets the gains add up (`pot`): the surplus
-- (wires gained) - t * (elements added) only grows. With d the surplus of the whole order, one step
-- gains at most t + d wires (`single`) and two steps on one chain gain at most 2t + d (`double`).
-- For two elements u, w that can each be added to B, the wires switched on by either one alone are at
-- most the surplus of the larger of the two steps (`diamond`).
-- The copies of x are the wires gained by x both at the least set D (everything strictly below x) and at
-- the greatest set D with all elements incomparable to x. Moving from the first to the second by adding
-- the incomparable elements one at a time, a wire gained by x before a step and not after it is switched
-- on by the added element alone (`slide`), so each step loses at most a diamond overlap. If the first
-- overlap is paid by the surplus of x itself, the other L - 1 steps lose at most d each; otherwise it is
-- paid by the surplus v of the first added element, and every later step then has only d - v left.
-- At width n * t the surplus is 0, so every element has at least t copies; the copies of different
-- elements are disjoint (a principal down-set separates them), which forces exactly t each and all wires.

namespace PEqualNP.Outside.L_lib_1447

theorem ifT {α : Type} (c : Prop) [Decidable c] (x y : α) (h : c) : (if c then x else y) = x := by
  simp [h]

theorem ifF {α : Type} (c : Prop) [Decidable c] (x y : α) (h : ¬ c) : (if c then x else y) = y := by
  simp [h]

theorem card_chain {α : Type} [DecidableEq α] (X Y W : Finset α) (h1 : X ⊆ Y) (h2 : Y ⊆ W) :
    (W \ X).card = (Y \ X).card + (W \ Y).card := by
  have e : W \ X = (Y \ X) ∪ (W \ Y) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hw, hx⟩
      by_cases hy : v ∈ Y
      · exact Or.inl ⟨hy, hx⟩
      · exact Or.inr ⟨hw, hy⟩
    · rintro (⟨hy, hx⟩ | ⟨hw, hy⟩)
      · exact ⟨h2 hy, hx⟩
      · exact ⟨hw, fun hx => hy (h1 hx)⟩
  rw [e, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  exact (Finset.mem_sdiff.1 hv2).2 (Finset.mem_sdiff.1 hv1).1

theorem arith (v d m : ℕ) (hv : v ≤ d) : v + m * (d - v) ≤ max 1 m * d := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]
    simpa using hv
  · have e1 : max 1 m = m := max_eq_right hm
    have e2 : m * d = m * v + m * (d - v) := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hv]
    have e3 : v ≤ m * v := Nat.le_mul_of_pos_left v hm
    rw [e1, e2]
    omega

section
variable {n k : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin k)]

/-- Down-closed sets. -/
def Idl (R : Fin n → Fin n → Prop) (A : Finset (Fin n)) : Prop := ∀ i j, j ∈ A → R i j → i ∈ A

theorem exists_min (R : Fin n → Fin n → Prop) (htr : ∀ i j h, R i j → R j h → R i h)
    (has : ∀ i j, R i j → R j i → i = j) :
    ∀ (c : ℕ) (T : Finset (Fin n)), T.card = c → T.Nonempty →
      ∃ x ∈ T, ∀ y ∈ T, R y x → y = x := by
  intro c
  induction c with
  | zero =>
    intro T hc hne
    rw [Finset.card_eq_zero.1 hc] at hne
    exact absurd hne Finset.not_nonempty_empty
  | succ c ih =>
    intro T hc hne
    obtain ⟨x, hx⟩ := hne
    by_cases hT : (T.erase x).Nonempty
    · obtain ⟨m, hm, hmin⟩ := ih (T.erase x)
        (by rw [Finset.card_erase_of_mem hx, hc, Nat.add_sub_cancel]) hT
      have hmT : m ∈ T := Finset.mem_of_mem_erase hm
      by_cases hxm : R x m
      · refine ⟨x, hx, fun y hy hyx => ?_⟩
        by_contra hne2
        have hy' : y ∈ T.erase x := Finset.mem_erase.2 ⟨hne2, hy⟩
        have hym : y = m := hmin y hy' (htr y x m hyx hxm)
        rw [hym] at hyx
        have hmx : m = x := has m x hyx hxm
        rw [hmx] at hm
        exact Finset.notMem_erase x T hm
      · refine ⟨m, hmT, fun y hy hym => ?_⟩
        by_cases hyx : y = x
        · rw [hyx] at hym
          exact absurd hym hxm
        · exact hmin y (Finset.mem_erase.2 ⟨hyx, hy⟩) hym
    · refine ⟨x, hx, fun y hy _ => ?_⟩
      by_contra hne2
      exact hT ⟨y, Finset.mem_erase.2 ⟨hne2, hy⟩⟩

/-- A least element of `Z' \ Z` can be added to `Z`. -/
theorem idl_insert (R : Fin n → Fin n → Prop) (Z Z' : Finset (Fin n)) (hZ : Idl R Z)
    (hZ' : Idl R Z') (x : Fin n) (hx : x ∈ Z' \ Z) (hmin : ∀ y ∈ Z' \ Z, R y x → y = x) :
    Idl R (insert x Z) := by
  intro i j hj hij
  rcases Finset.mem_insert.1 hj with hjx | hjZ
  · rw [hjx] at hij
    by_cases hiZ : i ∈ Z
    · exact Finset.mem_insert_of_mem hiZ
    · have hiZ' : i ∈ Z' := hZ' i x (Finset.mem_sdiff.1 hx).1 hij
      rw [hmin i (Finset.mem_sdiff.2 ⟨hiZ', hiZ⟩) hij]
      exact Finset.mem_insert_self x Z
  · exact Finset.mem_insert_of_mem (hZ i j hjZ hij)

omit [DecidableEq (Fin n)] in
theorem sep {a f : ℕ} (R : Fin n → Fin n → Prop) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A)
    (A B : Finset (Fin n)) (hA : Idl R A) (hB : Idl R B) (hne : A ≠ B) :
    a + f + 1 ≤ (g A \ g B).card ∨ a + f + 1 ≤ (g B \ g A).card := by
  by_contra hcon
  have h1 : (g A \ g B).card ≤ a + f := by
    by_contra hc
    exact hcon (Or.inl (by omega))
  have h2 : (g B \ g A).card ≤ a + f := by
    by_contra hc
    exact hcon (Or.inr (by omega))
  obtain ⟨P', hP's, hP'c⟩ := Finset.exists_subset_card_eq
    (show min (g A \ g B).card f ≤ (g A \ g B).card from Nat.min_le_left _ _)
  obtain ⟨Q', hQ's, hQ'c⟩ := Finset.exists_subset_card_eq
    (show min (g B \ g A).card f ≤ (g B \ g A).card from Nat.min_le_left _ _)
  have cP := Finset.card_sdiff_add_card_eq_card hP's
  have cQ := Finset.card_sdiff_add_card_eq_card hQ's
  have e1 : h ((g A ∩ g B) ∪ P' ∪ Q') = A := by
    apply hh A hA
    · have hs : g A \ ((g A ∩ g B) ∪ P' ∪ Q') ⊆ (g A \ g B) \ P' := by
        intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hv ⊢
        exact ⟨⟨hv.1, fun hvB => hv.2 (Or.inl (Or.inl ⟨hv.1, hvB⟩))⟩,
          fun hvP => hv.2 (Or.inl (Or.inr hvP))⟩
      have := Finset.card_le_card hs
      omega
    · have hs : ((g A ∩ g B) ∪ P' ∪ Q') \ g A ⊆ Q' := by
        intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hv
        rcases hv.1 with (hv1 | hv1) | hv1
        · exact absurd hv1.1 hv.2
        · exact absurd (Finset.mem_sdiff.1 (hP's hv1)).1 hv.2
        · exact hv1
      have := Finset.card_le_card hs
      omega
  have e2 : h ((g A ∩ g B) ∪ P' ∪ Q') = B := by
    apply hh B hB
    · have hs : g B \ ((g A ∩ g B) ∪ P' ∪ Q') ⊆ (g B \ g A) \ Q' := by
        intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hv ⊢
        exact ⟨⟨hv.1, fun hvA => hv.2 (Or.inl (Or.inl ⟨hvA, hv.1⟩))⟩, fun hvQ => hv.2 (Or.inr hvQ)⟩
      have := Finset.card_le_card hs
      omega
    · have hs : ((g A ∩ g B) ∪ P' ∪ Q') \ g B ⊆ P' := by
        intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hv
        rcases hv.1 with (hv1 | hv1) | hv1
        · exact absurd hv1.2 hv.2
        · exact hv1
        · exact absurd (Finset.mem_sdiff.1 (hQ's hv1)).1 hv.2
      have := Finset.card_le_card hs
      omega
  exact hne (e1.symm.trans e2)

omit [DecidableEq (Fin n)] in
theorem gain {a f : ℕ} (R : Fin n → Fin n → Prop) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A)
    (A B : Finset (Fin n)) (hA : Idl R A) (hB : Idl R B) (hAB : A ⊆ B) (hne : A ≠ B) :
    a + f + 1 ≤ (g B \ g A).card := by
  rcases sep R g h hh A B hA hB hne with h1 | h1
  · rw [Finset.sdiff_eq_empty_iff_subset.2 (hg A B hA hB hAB)] at h1
    simp at h1
  · exact h1

omit [DecidableEq (Fin n)] in
theorem idl_empty (R : Fin n → Fin n → Prop) : Idl R (∅ : Finset (Fin n)) := by
  intro i j hj
  exact absurd hj (Finset.notMem_empty j)

omit [DecidableEq (Fin n)] in
theorem idl_univ (R : Fin n → Fin n → Prop) : Idl R (Finset.univ : Finset (Fin n)) := by
  intro i j _ _
  exact Finset.mem_univ i

/-- Along an inclusion of down-closed sets the wires gained are at least t per element. -/
theorem pot {a f : ℕ} (R : Fin n → Fin n → Prop) (htr : ∀ i j h, R i j → R j h → R i h)
    (has : ∀ i j, R i j → R j i → i = j) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A) :
    ∀ (c : ℕ) (Z Z' : Finset (Fin n)), (Z' \ Z).card = c → Idl R Z → Idl R Z' → Z ⊆ Z' →
      (g Z \ g ∅).card + (a + f + 1) * Z'.card ≤ (g Z' \ g ∅).card + (a + f + 1) * Z.card := by
  intro c
  induction c with
  | zero =>
    intro Z Z' hc hZ hZ' hsub
    have hZZ : Z' = Z := Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hc)) hsub
    rw [hZZ]
  | succ c ih =>
    intro Z Z' hc hZ hZ' hsub
    have hne : (Z' \ Z).Nonempty := by
      rw [← Finset.card_pos, hc]
      exact Nat.succ_pos c
    obtain ⟨x, hx, hmin⟩ := exists_min R htr has (Z' \ Z).card (Z' \ Z) rfl hne
    have hxZ : x ∉ Z := (Finset.mem_sdiff.1 hx).2
    have hZ1 : Idl R (insert x Z) := idl_insert R Z Z' hZ hZ' x hx hmin
    have hsub1 : insert x Z ⊆ Z' := Finset.insert_subset (Finset.mem_sdiff.1 hx).1 hsub
    have hc1 : (Z' \ insert x Z).card = c := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hx, hc, Nat.add_sub_cancel]
    have h1 := ih (insert x Z) Z' hc1 hZ1 hZ' hsub1
    have hgain := gain R g h hg hh Z (insert x Z) hZ hZ1 (Finset.subset_insert x Z)
      (fun e => hxZ (by rw [e]; exact Finset.mem_insert_self x Z))
    have hch := card_chain (g ∅) (g Z) (g (insert x Z))
      (hg ∅ Z (idl_empty R) hZ (Finset.empty_subset Z))
      (hg Z (insert x Z) hZ hZ1 (Finset.subset_insert x Z))
    rw [Finset.card_insert_of_notMem hxZ, Nat.mul_succ] at h1
    omega

/-- One step gains at most t + d wires. -/
theorem single {a f : ℕ} (R : Fin n → Fin n → Prop) (htr : ∀ i j h, R i j → R j h → R i h)
    (has : ∀ i j, R i j → R j i → i = j) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A)
    (Z : Finset (Fin n)) (u : Fin n) (hZ : Idl R Z) (hu : u ∉ Z) (hZu : Idl R (insert u Z)) :
    (g (insert u Z) \ g Z).card + (a + f + 1) * n ≤
      (g Finset.univ \ g ∅).card + (a + f + 1) := by
  have h1 := pot R htr has g h hg hh _ ∅ Z rfl (idl_empty R) hZ (Finset.empty_subset Z)
  have h2 := pot R htr has g h hg hh _ (insert u Z) Finset.univ rfl hZu (idl_univ R)
    (Finset.subset_univ _)
  have hch := card_chain (g ∅) (g Z) (g (insert u Z))
    (hg ∅ Z (idl_empty R) hZ (Finset.empty_subset Z))
    (hg Z (insert u Z) hZ hZu (Finset.subset_insert u Z))
  rw [Finset.card_insert_of_notMem hu, Nat.mul_succ, Finset.card_univ, Fintype.card_fin] at h2
  simp only [Finset.card_empty, Nat.mul_zero, Finset.sdiff_self, Nat.add_zero] at h1
  omega

/-- Two steps on one chain gain at most 2t + d wires. -/
theorem double {a f : ℕ} (R : Fin n → Fin n → Prop) (htr : ∀ i j h, R i j → R j h → R i h)
    (has : ∀ i j, R i j → R j i → i = j) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A)
    (Z1 Z3 : Finset (Fin n)) (u w : Fin n) (hZ1 : Idl R Z1) (hu : u ∉ Z1)
    (hZ1u : Idl R (insert u Z1)) (hZ3 : Idl R Z3) (h13 : insert u Z1 ⊆ Z3) (hw : w ∉ Z3)
    (hZ3w : Idl R (insert w Z3)) :
    (g (insert u Z1) \ g Z1).card + (g (insert w Z3) \ g Z3).card + (a + f + 1) * n ≤
      (g Finset.univ \ g ∅).card + 2 * (a + f + 1) := by
  have h1 := pot R htr has g h hg hh _ ∅ Z1 rfl (idl_empty R) hZ1 (Finset.empty_subset Z1)
  have h2 := pot R htr has g h hg hh _ (insert u Z1) Z3 rfl hZ1u hZ3 h13
  have h3 := pot R htr has g h hg hh _ (insert w Z3) Finset.univ rfl hZ3w (idl_univ R)
    (Finset.subset_univ _)
  have hch1 := card_chain (g ∅) (g Z1) (g (insert u Z1))
    (hg ∅ Z1 (idl_empty R) hZ1 (Finset.empty_subset Z1))
    (hg Z1 (insert u Z1) hZ1 hZ1u (Finset.subset_insert u Z1))
  have hch3 := card_chain (g ∅) (g Z3) (g (insert w Z3))
    (hg ∅ Z3 (idl_empty R) hZ3 (Finset.empty_subset Z3))
    (hg Z3 (insert w Z3) hZ3 hZ3w (Finset.subset_insert w Z3))
  rw [Finset.card_insert_of_notMem hu, Nat.mul_succ] at h2
  rw [Finset.card_insert_of_notMem hw, Nat.mul_succ, Finset.card_univ, Fintype.card_fin] at h3
  simp only [Finset.card_empty, Nat.mul_zero, Finset.sdiff_self, Nat.add_zero] at h1
  omega

/-- The wires switched on by either of two addable elements alone. -/
theorem diamond {a f : ℕ} (R : Fin n → Fin n → Prop) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A)
    (B : Finset (Fin n)) (u w : Fin n) (hB : Idl R B) (hu : u ∉ B) (huw : u ≠ w)
    (hBu : Idl R (insert u B)) (hBw : Idl R (insert w B)) :
    ((g (insert u B) \ g B) ∩ (g (insert w B) \ g B)).card + (a + f + 1) ≤
        (g (insert u B) \ g B).card ∨
      ((g (insert u B) \ g B) ∩ (g (insert w B) \ g B)).card + (a + f + 1) ≤
        (g (insert w B) \ g B).card := by
  have hne : insert u B ≠ insert w B := by
    intro e
    have hmem : u ∈ insert w B := by rw [← e]; exact Finset.mem_insert_self u B
    rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact huw h1
    · exact hu h1
  have gB1 := hg B (insert u B) hB hBu (Finset.subset_insert u B)
  have gB2 := hg B (insert w B) hB hBw (Finset.subset_insert w B)
  have s1 : g (insert u B) \ g (insert w B) ⊆
      (g (insert u B) \ g B) \ ((g (insert u B) \ g B) ∩ (g (insert w B) \ g B)) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hv ⊢
    exact ⟨⟨hv.1, fun hvB => hv.2 (gB2 hvB)⟩, fun hc => hv.2 hc.2.1⟩
  have s2 : g (insert w B) \ g (insert u B) ⊆
      (g (insert w B) \ g B) \ ((g (insert u B) \ g B) ∩ (g (insert w B) \ g B)) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hv ⊢
    exact ⟨⟨hv.1, fun hvB => hv.2 (gB1 hvB)⟩, fun hc => hv.2 hc.1.1⟩
  have c1 := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left : (g (insert u B) \ g B) ∩ (g (insert w B) \ g B) ⊆ _)
  have c2 := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_right : (g (insert u B) \ g B) ∩ (g (insert w B) \ g B) ⊆ _)
  have l1 := Finset.card_le_card s1
  have l2 := Finset.card_le_card s2
  rcases sep R g h hh (insert u B) (insert w B) hBu hBw hne with h1 | h1
  · left; omega
  · right; omega

/-- A wire gained by `x` before `y` is added and not after is switched on by `y` alone. -/
theorem slide (R : Fin n → Fin n → Prop) (g : Finset (Fin n) → Finset (Fin k))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (A : Finset (Fin n)) (x y : Fin n) (hAx : Idl R (insert x A))
    (hAxy : Idl R (insert x (insert y A))) :
    (g (insert x A) \ g A) \ (g (insert x (insert y A)) \ g (insert y A)) ⊆
      (g (insert x A) \ g A) ∩ (g (insert y A) \ g A) := by
  intro v hv
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hv ⊢
  have h1 : v ∈ g (insert x (insert y A)) :=
    hg (insert x A) (insert x (insert y A)) hAx hAxy
      (Finset.insert_subset_insert x (Finset.subset_insert y A)) hv.1.1
  have h2 : v ∈ g (insert y A) := by
    by_contra hc
    exact hv.2 ⟨h1, hc⟩
  exact ⟨hv.1, h2, hv.1.2⟩

theorem total {a f : ℕ} (R : Fin n → Fin n → Prop) (htr : ∀ i j h, R i j → R j h → R i h)
    (has : ∀ i j, R i j → R j i → i = j) (g : Finset (Fin n) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A) :
    n * (a + f + 1) ≤ (g Finset.univ \ g ∅).card := by
  have h1 := pot R htr has g h hg hh _ ∅ Finset.univ rfl (idl_empty R) (idl_univ R)
    (Finset.subset_univ _)
  simp only [Finset.card_empty, Nat.mul_zero, Finset.sdiff_self, Nat.add_zero, Finset.card_univ,
    Fintype.card_fin, Nat.zero_add] at h1
  rw [Nat.mul_comm]
  exact h1

omit [DecidableEq (Fin n)] [DecidableEq (Fin k)] in
/-- The copies of two different elements share no wire. -/
theorem cop_disj (R : Fin n → Fin n → Prop) (hrefl : ∀ i, R i i)
    (htr : ∀ i j h, R i j → R j h → R i h) (has : ∀ i j, R i j → R j i → i = j)
    (g : Finset (Fin n) → Finset (Fin k)) (i j : Fin n) (hij : i ≠ j) (v : Fin k)
    (hi : ∀ A, Idl R A → (v ∈ g A ↔ i ∈ A)) (hj : ∀ A, Idl R A → (v ∈ g A ↔ j ∈ A)) : False := by
  classical
  have hdown : ∀ z : Fin n, Idl R (Finset.univ.filter (fun y => R y z)) := by
    intro z p q hq hpq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨Finset.mem_univ p, htr p q z hpq hq.2⟩
  have h1 : j ∈ Finset.univ.filter (fun y => R y i) :=
    (hj _ (hdown i)).1 ((hi _ (hdown i)).2 (Finset.mem_filter.2 ⟨Finset.mem_univ i, hrefl i⟩))
  have h2 : i ∈ Finset.univ.filter (fun y => R y j) :=
    (hi _ (hdown j)).1 ((hj _ (hdown j)).2 (Finset.mem_filter.2 ⟨Finset.mem_univ j, hrefl j⟩))
  exact hij (has i j (Finset.mem_filter.1 h2).2 (Finset.mem_filter.1 h1).2)

/-- The number of copies of one element. -/
theorem core {a f : ℕ} (R : Fin n → Fin n → Prop) (hrefl : ∀ i, R i i)
    (htr : ∀ i j h, R i j → R j h → R i h) (has : ∀ i j, R i j → R j i → i = j)
    (g : Finset (Fin n) → Finset (Fin k)) (h : Finset (Fin k) → Finset (Fin n))
    (hg : ∀ A B, Idl R A → Idl R B → A ⊆ B → g A ⊆ g B)
    (hh : ∀ A, Idl R A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A)
    (x : Fin n) (D I : Finset (Fin n)) (cop : Finset (Fin k))
    (hD : ∀ y, y ∈ D ↔ R y x ∧ y ≠ x) (hI : ∀ y, y ∈ I ↔ ¬ R x y ∧ ¬ R y x)
    (hcop : ∀ v, v ∈ cop ↔ ∀ A, Idl R A → (v ∈ g A ↔ x ∈ A)) :
    (I = ∅ → a + f + 1 ≤ cop.card) ∧
    (I.Nonempty → a + f + 1 ≤ cop.card +
      max 1 (I.card - 1) * ((g Finset.univ \ g ∅).card - n * (a + f + 1))) := by
  have hnt := total R htr has g h hg hh
  -- the least and the greatest set at which x can be added
  have hDi : Idl R D := by
    intro i j hj hij
    rw [hD] at hj ⊢
    refine ⟨htr i j x hij hj.1, fun e => ?_⟩
    rw [e] at hij
    exact hj.2 (has j x hj.1 hij)
  have hDIi : Idl R (D ∪ I) := by
    intro i j hj hij
    rcases Finset.mem_union.1 hj with hj | hj
    · exact Finset.mem_union_left _ (hDi i j hj hij)
    · rw [hI] at hj
      by_cases hix : R i x
      · have hne : i ≠ x := fun e => hj.1 (by rw [← e]; exact hij)
        exact Finset.mem_union_left _ ((hD i).2 ⟨hix, hne⟩)
      · exact Finset.mem_union_right _ ((hI i).2 ⟨fun hxi => hj.1 (htr x i j hxi hij), hix⟩)
  have hxD : x ∉ D := fun hx => ((hD x).1 hx).2 rfl
  have hxDI : x ∉ D ∪ I := by
    intro hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hxD hx
    · exact ((hI x).1 hx).1 (hrefl x)
  have insx : ∀ B, Idl R B → D ⊆ B → Idl R (insert x B) := by
    intro B hB hDB i j hj hij
    rcases Finset.mem_insert.1 hj with hjx | hjB
    · rw [hjx] at hij
      by_cases hix : i = x
      · rw [hix]; exact Finset.mem_insert_self x B
      · exact Finset.mem_insert_of_mem (hDB ((hD i).2 ⟨hij, hix⟩))
    · exact Finset.mem_insert_of_mem (hB i j hjB hij)
  have hsup : (g (insert x D) \ g D) ∩ (g (insert x (D ∪ I)) \ g (D ∪ I)) ⊆ cop := by
    intro v hv
    rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_sdiff] at hv
    rw [hcop]
    intro A hA
    constructor
    · intro hvA
      by_contra hxA
      have hsub : A ⊆ D ∪ I := by
        intro y hy
        have hyx : y ≠ x := fun e => hxA (by rw [← e]; exact hy)
        by_cases hyR : R y x
        · exact Finset.mem_union_left _ ((hD y).2 ⟨hyR, hyx⟩)
        · exact Finset.mem_union_right _ ((hI y).2 ⟨fun hxy => hxA (hA x y hy hxy), hyR⟩)
      exact hv.2.2 (hg A (D ∪ I) hA hDIi hsub hvA)
    · intro hxA
      have hsub : insert x D ⊆ A := by
        intro y hy
        rcases Finset.mem_insert.1 hy with hy | hy
        · rw [hy]; exact hxA
        · exact hA y x hxA ((hD y).1 hy).1
      exact hg (insert x D) A (insx D hDi (Finset.Subset.refl D)) hA hsub hv.1.1
  have hgainD := gain R g h hg hh D (insert x D) hDi (insx D hDi (Finset.Subset.refl D))
    (Finset.subset_insert x D) (fun e => hxD (by rw [e]; exact Finset.mem_insert_self x D))
  constructor
  · intro hI0
    have hs := hsup
    rw [hI0, Finset.union_empty, Finset.inter_self] at hs
    exact le_trans hgainD (Finset.card_le_card hs)
  · intro hIne
    -- the incomparable elements, added one at a time
    have hrest : ∀ (s c : ℕ) (A : Finset (Fin n)), ((D ∪ I) \ A).card = c → Idl R A → D ⊆ A →
        A ⊆ D ∪ I →
        (∀ B y, Idl R B → A ⊆ B → B ⊆ D ∪ I → y ∈ D ∪ I → y ∉ B → Idl R (insert y B) →
          ((g (insert x B) \ g B) ∩ (g (insert y B) \ g B)).card ≤ s) →
        ((g (insert x A) \ g A) \ (g (insert x (D ∪ I)) \ g (D ∪ I))).card ≤ c * s := by
      intro s c
      induction c with
      | zero =>
        intro A hc _ _ hAsub _
        have hA : A = D ∪ I := Finset.Subset.antisymm hAsub
          (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hc))
        rw [hA, Finset.sdiff_self]
        simp
      | succ c ih =>
        intro A hc hA hDA hAsub hov
        have hne : ((D ∪ I) \ A).Nonempty := by
          rw [← Finset.card_pos, hc]
          exact Nat.succ_pos c
        obtain ⟨y, hy, hmin⟩ := exists_min R htr has ((D ∪ I) \ A).card ((D ∪ I) \ A) rfl hne
        have hyDI : y ∈ D ∪ I := (Finset.mem_sdiff.1 hy).1
        have hyA : y ∉ A := (Finset.mem_sdiff.1 hy).2
        have hA1 : Idl R (insert y A) := idl_insert R A (D ∪ I) hA hDIi y hy hmin
        have hc1 : ((D ∪ I) \ insert y A).card = c := by
          rw [Finset.sdiff_insert, Finset.card_erase_of_mem hy, hc, Nat.add_sub_cancel]
        have h1 := ih (insert y A) hc1 hA1 (hDA.trans (Finset.subset_insert y A))
          (Finset.insert_subset hyDI hAsub)
          (fun B y' hB hAB => hov B y' hB ((Finset.subset_insert y A).trans hAB))
        have h2 := hov A y hA (Finset.Subset.refl A) hAsub hyDI hyA hA1
        have h3 := Finset.card_le_card (slide R g hg A x y (insx A hA hDA)
          (insx (insert y A) hA1 (hDA.trans (Finset.subset_insert y A))))
        have hsplit : (g (insert x A) \ g A) \ (g (insert x (D ∪ I)) \ g (D ∪ I)) ⊆
            ((g (insert x A) \ g A) \ (g (insert x (insert y A)) \ g (insert y A))) ∪
            ((g (insert x (insert y A)) \ g (insert y A)) \
              (g (insert x (D ∪ I)) \ g (D ∪ I))) := by
          intro v hv
          rw [Finset.mem_sdiff] at hv
          by_cases hv1 : v ∈ g (insert x (insert y A)) \ g (insert y A)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hv1, hv.2⟩)
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hv.1, hv1⟩)
        have h4 := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
        rw [Nat.succ_mul]
        omega
    -- the first incomparable element
    have hT : ((D ∪ I) \ D).Nonempty := by
      obtain ⟨z, hz⟩ := hIne
      refine ⟨z, Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hz, fun hzD => ?_⟩⟩
      exact ((hI z).1 hz).2 ((hD z).1 hzD).1
    have hTI : (D ∪ I) \ D = I := by
      ext z
      rw [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz | hz, hzD⟩
        · exact absurd hz hzD
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, fun hzD => ((hI z).1 hz).2 ((hD z).1 hzD).1⟩
    obtain ⟨y1, hy1, hmin1⟩ := exists_min R htr has ((D ∪ I) \ D).card ((D ∪ I) \ D) rfl hT
    have hy1DI : y1 ∈ D ∪ I := (Finset.mem_sdiff.1 hy1).1
    have hy1D : y1 ∉ D := (Finset.mem_sdiff.1 hy1).2
    have hxy1 : x ≠ y1 := fun e => hxDI (by rw [e]; exact hy1DI)
    have hA1 : Idl R (insert y1 D) := idl_insert R D (D ∪ I) hDi hDIi y1 hy1 hmin1
    have hDx : Idl R (insert x D) := insx D hDi (Finset.Subset.refl D)
    have hc1 : ((D ∪ I) \ insert y1 D).card = I.card - 1 := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hy1, hTI]
    have hA1sub : insert y1 D ⊆ D ∪ I := Finset.insert_subset hy1DI Finset.subset_union_left
    have hDA1 : D ⊆ insert y1 D := Finset.subset_insert y1 D
    -- the loss over the first step and over the rest
    have hsplit : (g (insert x D) \ g D) \ (g (insert x (D ∪ I)) \ g (D ∪ I)) ⊆
        ((g (insert x D) \ g D) \ (g (insert x (insert y1 D)) \ g (insert y1 D))) ∪
        ((g (insert x (insert y1 D)) \ g (insert y1 D)) \
          (g (insert x (D ∪ I)) \ g (D ∪ I))) := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      by_cases hv1 : v ∈ g (insert x (insert y1 D)) \ g (insert y1 D)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hv1, hv.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hv.1, hv1⟩)
    have h4 := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
    have h3 := Finset.card_le_card (slide R g hg D x y1 hDx (insx (insert y1 D) hA1 hDA1))
    have hcap := Finset.card_sdiff_add_card_inter (g (insert x D) \ g D)
      (g (insert x (D ∪ I)) \ g (D ∪ I))
    have hcopge := Finset.card_le_card hsup
    have hdia := diamond R g h hg hh D x y1 hDi hxD hxy1 hDx hA1
    have hsy1 := single R htr has g h hg hh D y1 hDi hy1D hA1
    have hnt' : (a + f + 1) * n ≤ (g Finset.univ \ g ∅).card := by rw [Nat.mul_comm]; exact hnt
    rw [Nat.mul_comm n (a + f + 1)]
    rcases hdia with hd1 | hd1
    · -- the first overlap is paid by x itself
      have hr := hrest ((g Finset.univ \ g ∅).card - (a + f + 1) * n) (I.card - 1) (insert y1 D)
        hc1 hA1 hDA1 hA1sub (by
          intro B y hB hAB hBsub hyDI hyB hBy
          have hDB : D ⊆ B := hDA1.trans hAB
          have hxB : x ∉ B := fun hx => hxDI (hBsub hx)
          have hxy : x ≠ y := fun e => hxDI (by rw [e]; exact hyDI)
          have hs1 := single R htr has g h hg hh B x hB hxB (insx B hB hDB)
          have hs2 := single R htr has g h hg hh B y hB hyB hBy
          rcases diamond R g h hg hh B x y hB hxB hxy (insx B hB hDB) hBy with hd | hd
          · omega
          · omega)
      have hmul : (I.card - 1) * ((g Finset.univ \ g ∅).card - (a + f + 1) * n) ≤
          max 1 (I.card - 1) * ((g Finset.univ \ g ∅).card - (a + f + 1) * n) :=
        Nat.mul_le_mul_right _ (le_max_right 1 (I.card - 1))
      omega
    · -- the first overlap is paid by the surplus of the first added element
      have hr := hrest ((g Finset.univ \ g ∅).card - (a + f + 1) * n -
          ((g (insert y1 D) \ g D).card - (a + f + 1))) (I.card - 1) (insert y1 D)
        hc1 hA1 hDA1 hA1sub (by
          intro B y hB hAB hBsub hyDI hyB hBy
          have hDB : D ⊆ B := hDA1.trans hAB
          have hxB : x ∉ B := fun hx => hxDI (hBsub hx)
          have hxy : x ≠ y := fun e => hxDI (by rw [e]; exact hyDI)
          have hs1 := double R htr has g h hg hh D B y1 x hDi hy1D hA1 hB hAB hxB (insx B hB hDB)
          have hs2 := double R htr has g h hg hh D B y1 y hDi hy1D hA1 hB hAB hyB hBy
          rcases diamond R g h hg hh B x y hB hxB hxy (insx B hB hDB) hBy with hd | hd
          · omega
          · omega)
      have hgy1 := gain R g h hg hh D (insert y1 D) hDi hA1 hDA1
        (fun e => hy1D (by rw [e]; exact Finset.mem_insert_self y1 D))
      have har := arith ((g (insert y1 D) \ g D).card - (a + f + 1))
        ((g Finset.univ \ g ∅).card - (a + f + 1) * n) (I.card - 1) (by omega)
      omega

end

end PEqualNP.Outside.L_lib_1447

theorem PEqualNP.Outside.L_lib_1447 :
letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n k a f : Nat) (R : Fin n → Fin n → Prop),
  (∀ i, R i i) → (∀ i j h, R i j → R j h → R i h) → (∀ i j, R i j → R j i → i = j) →
  let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
  ∀ (g : Finset (Fin n) → Finset (Fin k)) (h : Finset (Fin k) → Finset (Fin n)),
    (∀ A B, ideal A → ideal B → A ⊆ B → g A ⊆ g B) →
    (∀ A, ideal A → ∀ Y, (g A \ Y).card ≤ a → (Y \ g A).card ≤ f → h Y = A) →
    let t := a+f+1
    let active := (g Finset.univ \ g ∅).card
    let d := active-n*t
    let copies := fun (i : Fin n) => Finset.univ.filter (fun v : Fin k => ∀ A, ideal A → (v ∈ g A ↔ i ∈ A))
    n*t ≤ active ∧ (∀ i j, i ≠ j → Disjoint (copies i) (copies j)) ∧
    (∀ i, let L := (Finset.univ.filter (fun j : Fin n => ¬ R i j ∧ ¬ R j i)).card
          t ≤ (copies i).card + (if L=0 then 0 else max 1 (L-1))*d) ∧
    (k=n*t → (∀ i, (copies i).card=t) ∧ ∀ v, ∃! i, v ∈ copies i) := by
  intro n k a f R hrefl htr has ideal g h hg hh t active d copies
  have htot : n * t ≤ active :=
    @PEqualNP.Outside.L_lib_1447.total n k (fun x y => Classical.propDecidable (x = y))
      (fun x y => Classical.propDecidable (x = y)) a f R htr has g h hg hh
  have hmem : ∀ (i : Fin n) (v : Fin k),
      v ∈ copies i ↔ ∀ A, ideal A → (v ∈ g A ↔ i ∈ A) := by
    intro i v
    simp [copies]
  have hdisj : ∀ i j, i ≠ j → Disjoint (copies i) (copies j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    exact PEqualNP.Outside.L_lib_1447.cop_disj R hrefl htr has g i j hij v ((hmem i v).1 hvi)
      ((hmem j v).1 hvj)
  let Iof : Fin n → Finset (Fin n) := fun i =>
    @Finset.filter (Fin n) (fun j => ¬ R i j ∧ ¬ R j i) (fun _ => Classical.propDecidable _)
      Finset.univ
  have hcore : ∀ i : Fin n, (Iof i = ∅ → t ≤ (copies i).card) ∧
      ((Iof i).Nonempty → t ≤ (copies i).card + max 1 ((Iof i).card - 1) * d) := fun i =>
    @PEqualNP.Outside.L_lib_1447.core n k (fun x y => Classical.propDecidable (x = y))
      (fun x y => Classical.propDecidable (x = y)) a f R hrefl htr has g h hg hh i
      (@Finset.filter (Fin n) (fun y => R y i ∧ y ≠ i) (fun _ => Classical.propDecidable _)
        Finset.univ)
      (Iof i) (copies i) (fun y => by simp) (fun y => by simp [Iof]) (hmem i)
  refine ⟨htot, hdisj, ?_, ?_⟩
  · intro i L
    split_ifs with hL
    · rw [Nat.zero_mul, Nat.add_zero]
      exact (hcore i).1 (Finset.card_eq_zero.1 hL)
    · exact (hcore i).2 (Finset.card_pos.1 (Nat.pos_of_ne_zero hL))
  · intro hk
    have hactive : active ≤ k :=
      le_trans (Finset.card_le_univ _) (le_of_eq (Fintype.card_fin k))
    have hd0 : d = 0 := by
      show active - n * t = 0
      omega
    have hge : ∀ i, t ≤ (copies i).card := by
      intro i
      rcases Finset.eq_empty_or_nonempty (Iof i) with hI | hI
      · exact (hcore i).1 hI
      · have h1 := (hcore i).2 hI
        rw [hd0, Nat.mul_zero, Nat.add_zero] at h1
        exact h1
    have hbu : (Finset.univ.biUnion copies).card = Finset.univ.sum (fun i => (copies i).card) :=
      Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)
    have hle : (Finset.univ.biUnion copies).card ≤ k :=
      le_trans (Finset.card_le_univ _) (le_of_eq (Fintype.card_fin k))
    have hsumt : Finset.univ.sum (fun _ : Fin n => t) = n * t := by
      simp
    have hsum_le : Finset.univ.sum (fun _ : Fin n => t) ≤
        Finset.univ.sum (fun i => (copies i).card) :=
      Finset.sum_le_sum (fun i _ => hge i)
    have hsum_eq : Finset.univ.sum (fun _ : Fin n => t) =
        Finset.univ.sum (fun i => (copies i).card) := by
      omega
    have hall : ∀ i, (copies i).card = t := by
      intro i
      have h1 := (Finset.sum_eq_sum_iff_of_le (fun i _ => hge i)).1 hsum_eq i (Finset.mem_univ i)
      exact h1.symm
    refine ⟨hall, fun v => ?_⟩
    have hfull : Finset.univ.biUnion copies = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hbu, ← hsum_eq, hsumt, Fintype.card_fin, hk]
    have hv : v ∈ Finset.univ.biUnion copies := by rw [hfull]; exact Finset.mem_univ v
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hv
    refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hne
    exact Finset.disjoint_left.1 (hdisj j i hne) hj hi
