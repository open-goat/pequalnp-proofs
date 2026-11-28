import Mathlib

namespace PEqualNP.Outside.L_lib_608_aux

private abbrev Deg {V : Type*} [DecidableEq V] (b : Nat) (f : (V → Bool) → Bool) : Prop :=
  ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
    ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)

private theorem deg_to_zmod2 {V : Type*} [DecidableEq V] {b : Nat} {f : (V → Bool) → Bool}
    (h : Deg b f) :
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, (if f input then (1 : ZMod 2) else 0) =
        ∑ mon ∈ terms, (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) := by
  obtain ⟨terms, hcard, heval⟩ := h
  refine ⟨terms, hcard, fun input => ?_⟩
  rw [heval input, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hmod : ((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card : ZMod 2) =
      (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2 : Nat) : ZMod 2) := by
    rw [← Nat.div_add_mod (terms.filter _).card 2]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp [h2]
  rw [hmod]
  rcases Nat.mod_two_eq_zero_or_one (terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card with h0 | h1
  · simp [h0]
  · simp [h1]

private theorem zmod2_to_deg {V : Type*} [DecidableEq V] [Fintype V] {b : Nat} {f : (V → Bool) → Bool}
    (c : Finset V → ZMod 2)
    (hsupp : ∀ mon, c mon ≠ 0 → mon.card ≤ b)
    (heval : ∀ input, (if f input then (1 : ZMod 2) else 0) =
      ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0)) :
    Deg b f := by
  let terms : Finset (Finset V) := Finset.univ.filter (fun mon => c mon ≠ 0)
  refine ⟨terms, fun mon hm => hsupp mon (Finset.mem_filter.mp hm).2, fun input => ?_⟩
  have h1 := heval input
  have hsum : ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) =
      ((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card : ZMod 2) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    have hsplit : ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) =
        ∑ mon ∈ terms, c mon * (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro mon _ hnot
      have h0 : c mon = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      simp [h0]
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro mon hm
    have hne : c mon ≠ 0 := (Finset.mem_filter.mp hm).2
    have hc1 : c mon = 1 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (c mon) with h0 | h1
      · exact absurd h0 hne
      · exact h1
    rw [hc1, one_mul]
    split_ifs <;> simp
  rw [hsum] at h1
  have hmod : ((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card : ZMod 2) =
      (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2 : Nat) : ZMod 2) := by
    rw [← Nat.div_add_mod (terms.filter _).card 2]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp [h2]
  rw [hmod] at h1
  rcases Nat.mod_two_eq_zero_or_one (terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card with h0 | h2
  · rw [h0] at h1
    have hgoal : f input = false := by
      cases hf : f input
      · rfl
      · rw [hf] at h1; simp at h1
    rw [hgoal]
    have hbeq : (false : Bool) = (0 == 1) := rfl
    rw [hbeq]
    congr 1
    symm
    convert h0
  · rw [h2] at h1
    have hgoal : f input = true := by
      cases hf : f input
      · rw [hf] at h1; simp at h1
      · rfl
    rw [hgoal]
    have hbeq : (true : Bool) = (1 == 1) := rfl
    rw [hbeq]
    congr 1
    symm
    convert h2

private theorem deg_of_sum_zmod2 {V : Type*} [DecidableEq V] [Fintype V] {ι : Type*}
    {b : Nat} {f : (V → Bool) → Bool} (s : Finset ι) (g : ι → (V → Bool) → ZMod 2)
    (hg : ∀ i ∈ s, ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ b) ∧
      ∀ x, g i x = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0))
    (heval : ∀ x, (if f x then (1 : ZMod 2) else 0) = ∑ i ∈ s, g i x) :
    Deg b f := by
  classical
  let coeff : ι → Finset V → ZMod 2 := fun i =>
    if h : i ∈ s then Classical.choose (hg i h) else fun _ => 0
  have hcoeff_supp : ∀ i ∈ s, ∀ mon, coeff i mon ≠ 0 → mon.card ≤ b := by
    intro i hi
    dsimp only [coeff]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hg i hi)).1
  have hcoeff_eval : ∀ i ∈ s, ∀ x,
      g i x = ∑ mon : Finset V, coeff i mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
    intro i hi
    dsimp only [coeff]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hg i hi)).2
  apply zmod2_to_deg (fun mon => ∑ i ∈ s, coeff i mon)
  · intro mon hne
    have hex : ∃ i ∈ s, coeff i mon ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Finset.sum_eq_zero hall)
    obtain ⟨i, hi, hci⟩ := hex
    exact hcoeff_supp i hi mon hci
  · intro x
    rw [heval x]
    calc ∑ i ∈ s, g i x
        = ∑ i ∈ s, ∑ mon : Finset V, coeff i mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl (fun i hi => hcoeff_eval i hi x)
      _ = ∑ mon : Finset V, ∑ i ∈ s, coeff i mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) :=
          Finset.sum_comm
      _ = ∑ mon : Finset V, (∑ i ∈ s, coeff i mon) * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
          apply Finset.sum_congr rfl
          intro mon _
          rw [Finset.sum_mul]

private theorem poly_mul_zmod2 {V : Type*} [DecidableEq V] [Fintype V]
    {b1 b2 : Nat} {g1 g2 : (V → Bool) → ZMod 2}
    (h1 : ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ b1) ∧
      ∀ x, g1 x = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0))
    (h2 : ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ b2) ∧
      ∀ x, g2 x = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0)) :
    ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ b1 + b2) ∧
      ∀ x, g1 x * g2 x = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
  obtain ⟨c1, hs1, he1⟩ := h1
  obtain ⟨c2, hs2, he2⟩ := h2
  let c : Finset V → ZMod 2 := fun mon =>
    ∑ p ∈ (Finset.univ : Finset (Finset V × Finset V)).filter (fun p => p.1 ∪ p.2 = mon),
      c1 p.1 * c2 p.2
  refine ⟨c, ?_, ?_⟩
  · intro mon hne
    have hex : ∃ p ∈ (Finset.univ : Finset (Finset V × Finset V)).filter (fun p => p.1 ∪ p.2 = mon),
        c1 p.1 * c2 p.2 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Finset.sum_eq_zero hall)
    obtain ⟨⟨m1, m2⟩, hp, hmul⟩ := hex
    have hunion : m1 ∪ m2 = mon := (Finset.mem_filter.mp hp).2
    have h1n : c1 m1 ≠ 0 := left_ne_zero_of_mul hmul
    have h2n : c2 m2 ≠ 0 := right_ne_zero_of_mul hmul
    rw [← hunion]
    exact le_trans (Finset.card_union_le m1 m2) (Nat.add_le_add (hs1 m1 h1n) (hs2 m2 h2n))
  · intro x
    rw [he1 x, he2 x, Finset.sum_mul_sum]
    have hpair : ∀ m1 m2 : Finset V,
        (c1 m1 * (if ∀ j ∈ m1, x j = true then (1 : ZMod 2) else 0)) *
        (c2 m2 * (if ∀ j ∈ m2, x j = true then (1 : ZMod 2) else 0)) =
        (c1 m1 * c2 m2) * (if ∀ j ∈ m1 ∪ m2, x j = true then (1 : ZMod 2) else 0) := by
      intro m1 m2
      by_cases h1x : ∀ j ∈ m1, x j = true <;> by_cases h2x : ∀ j ∈ m2, x j = true
      · have hu : ∀ j ∈ m1 ∪ m2, x j = true := fun j hj => by
          rcases Finset.mem_union.mp hj with h | h
          · exact h1x j h
          · exact h2x j h
        rw [ite_eq_left h1x, ite_eq_left h2x, ite_eq_left hu]
        ring
      · have hu : ¬ ∀ j ∈ m1 ∪ m2, x j = true := fun h => h2x (fun j hj => h j (Finset.mem_union_right _ hj))
        rw [ite_eq_left h1x, ite_eq_right h2x, ite_eq_right hu]
        ring
      · have hu : ¬ ∀ j ∈ m1 ∪ m2, x j = true := fun h => h1x (fun j hj => h j (Finset.mem_union_left _ hj))
        rw [ite_eq_right h1x, ite_eq_left h2x, ite_eq_right hu]
        ring
      · have hu : ¬ ∀ j ∈ m1 ∪ m2, x j = true := fun h => h1x (fun j hj => h j (Finset.mem_union_left _ hj))
        rw [ite_eq_right h1x, ite_eq_right h2x, ite_eq_right hu]
        ring
    calc ∑ m1 : Finset V, ∑ m2 : Finset V,
          (c1 m1 * (if ∀ j ∈ m1, x j = true then (1 : ZMod 2) else 0)) *
          (c2 m2 * (if ∀ j ∈ m2, x j = true then (1 : ZMod 2) else 0))
        = ∑ p : Finset V × Finset V,
          (c1 p.1 * c2 p.2) * (if ∀ j ∈ p.1 ∪ p.2, x j = true then (1 : ZMod 2) else 0) := by
          rw [← Finset.sum_product']
          exact Finset.sum_congr rfl (fun p _ => hpair p.1 p.2)
      _ = ∑ mon : Finset V, ∑ p ∈ (Finset.univ : Finset (Finset V × Finset V)).filter (fun p => p.1 ∪ p.2 = mon),
          (c1 p.1 * c2 p.2) * (if ∀ j ∈ p.1 ∪ p.2, x j = true then (1 : ZMod 2) else 0) := by
          symm
          exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
      _ = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
          apply Finset.sum_congr rfl
          intro mon _
          dsimp only [c]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]

private theorem poly_const_zmod2 {V : Type*} [DecidableEq V] [Fintype V] (a : ZMod 2) :
    ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ 0) ∧
      ∀ x : V → Bool, a = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
  refine ⟨fun mon => if mon = ∅ then a else 0, ?_, ?_⟩
  · intro mon hne
    by_cases h : mon = ∅
    · subst h; simp
    · simp [h] at hne
  · intro x
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro mon _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ ∅) h

private theorem poly_lit_zmod2 {V : Type*} [DecidableEq V] [Fintype V] (v : V) (want : Bool) :
    ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ 1) ∧
      ∀ x : V → Bool, (if x v = want then (1 : ZMod 2) else 0) =
        ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
  cases want
  · refine ⟨fun mon => if mon = ∅ then 1 else if mon = {v} then 1 else 0, ?_, ?_⟩
    · intro mon hne
      by_cases h0 : mon = ∅
      · subst h0; simp
      · by_cases h1 : mon = {v}
        · subst h1; simp
        · simp [h0, h1] at hne
    · intro x
      have hne01 : (∅ : Finset V) ≠ {v} := (Finset.singleton_ne_empty v).symm
      have hsub : ∑ mon : Finset V, (if mon = ∅ then (1 : ZMod 2) else if mon = {v} then 1 else 0) *
          (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) =
          ∑ mon ∈ ({∅, {v}} : Finset (Finset V)),
            (if mon = ∅ then (1 : ZMod 2) else if mon = {v} then 1 else 0) *
            (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro mon _ hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        simp [hnot.1, hnot.2]
      rw [hsub, Finset.sum_pair hne01]
      simp only [↓reduceIte, hne01.symm, Finset.notMem_empty, false_implies, implies_true,
        Finset.mem_singleton, forall_eq, one_mul]
      cases x v <;> decide
  · refine ⟨fun mon => if mon = {v} then 1 else 0, ?_, ?_⟩
    · intro mon hne
      by_cases h1 : mon = {v}
      · subst h1; simp
      · simp [h1] at hne
    · intro x
      rw [Finset.sum_eq_single {v}]
      · simp
      · intro mon _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ {v}) h

private theorem poly_prod_zmod2 {V : Type*} [DecidableEq V] [Fintype V] {ι : Type*}
    (s : Finset ι) (d : Nat) (g : ι → (V → Bool) → ZMod 2)
    (hg : ∀ i ∈ s, ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ d) ∧
      ∀ x, g i x = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0)) :
    ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ s.card * d) ∧
      ∀ x, (∏ i ∈ s, g i x) = ∑ mon : Finset V, c mon * (if ∀ j ∈ mon, x j = true then (1 : ZMod 2) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using poly_const_zmod2 (V := V) 1
  | @insert a t ha ih =>
    have h1 := hg a (Finset.mem_insert_self a t)
    have h2 := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    obtain ⟨c, hsupp, heval⟩ := poly_mul_zmod2 h1 h2
    refine ⟨c, ?_, ?_⟩
    · intro mon hne
      have hle := hsupp mon hne
      rw [Finset.card_insert_of_notMem ha]
      have : (t.card + 1) * d = d + t.card * d := by ring
      omega
    · intro x
      rw [Finset.prod_insert ha, heval x]

private theorem poly_X_add_one_pow_coeff (n k : Nat) :
    ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ n).coeff k =
      ((Nat.choose n k : Nat) : ZMod 2) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add]
    cases k with
    | zero =>
      simp [ih 0]
    | succ k =>
      rw [Polynomial.coeff_mul_X, ih k, ih (k + 1), Nat.choose_succ_succ]
      push_cast
      ring

private theorem poly_X_add_one_pow_two_pow (e : Nat) :
    (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ (2 ^ e) =
      Polynomial.X ^ (2 ^ e) + 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_mul, ih, add_sq]
    have h2 : (2 : Polynomial (ZMod 2)) = 0 := by
      have hC : (2 : Polynomial (ZMod 2)) = Polynomial.C (2 : ZMod 2) := by
        simpa using (Polynomial.C_eq_natCast (R := ZMod 2) 2).symm
      rw [hC, show (2 : ZMod 2) = 0 from rfl, map_zero]
    rw [mul_assoc, h2, zero_mul, add_zero, one_pow, ← pow_mul]

private theorem choose_two_pow_zmod2 (e s : Nat) (hs : s < 2 * 2 ^ e) :
    ((Nat.choose s (2 ^ e) : Nat) : ZMod 2) = if 2 ^ e ≤ s then 1 else 0 := by
  by_cases hle : 2 ^ e ≤ s
  · simp only [hle, ↓reduceIte]
    set r := s - 2 ^ e
    have hs_eq : s = 2 ^ e + r := by omega
    have hr_lt : r < 2 ^ e := by omega
    rw [hs_eq, ← poly_X_add_one_pow_coeff, pow_add, poly_X_add_one_pow_two_pow, add_mul, one_mul, Polynomial.coeff_add]
    have hfirst : (Polynomial.X ^ (2 ^ e) * (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r).coeff (2 ^ e) =
        ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r).coeff 0 := by
      have := Polynomial.coeff_X_pow_mul ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r) (2 ^ e) 0
      simpa using this
    rw [hfirst]
    have hcoeff0 : ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one, zero_add, one_pow]
    have hdeg : ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r).natDegree ≤ r := by
      calc ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r).natDegree
          ≤ r * (Polynomial.X + 1 : Polynomial (ZMod 2)).natDegree := Polynomial.natDegree_pow_le
        _ = r := by simp [Polynomial.natDegree_X_add_C]
    have hcoeff_hi : ((Polynomial.X + 1 : Polynomial (ZMod 2)) ^ r).coeff (2 ^ e) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hr_lt)
    rw [hcoeff0, hcoeff_hi, add_zero]
  · simp only [hle, ↓reduceIte]
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hle)]
    simp

private theorem sum_powersetCard_eq_choose {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (p : ι → Bool) (R : Nat) :
    (∑ S ∈ U.powersetCard R, ∏ i ∈ S, (if p i then (1 : ZMod 2) else 0)) =
      ((Nat.choose (U.filter (fun i => p i = true)).card R : Nat) : ZMod 2) := by
  let A := U.filter (fun i => p i = true)
  have h1 : ∀ S ∈ U.powersetCard R,
      (∏ i ∈ S, (if p i then (1 : ZMod 2) else 0)) =
        if S ⊆ A then (1 : ZMod 2) else 0 := by
    intro S hS
    have hSU : S ⊆ U := (Finset.mem_powersetCard.mp hS).1
    by_cases hSA : S ⊆ A
    · rw [if_pos hSA]
      apply Finset.prod_eq_one
      intro i hi
      have hp : p i = true := (Finset.mem_filter.mp (hSA hi)).2
      simp [hp]
    · rw [if_neg hSA]
      have hex : ∃ i ∈ S, p i = false := by
        by_contra hall
        push Not at hall
        apply hSA
        intro i hi
        exact Finset.mem_filter.mpr ⟨hSU hi, by cases hpi : p i with | false => exact absurd hpi (hall i hi) | true => rfl⟩
      obtain ⟨i, hi, hpi⟩ := hex
      exact Finset.prod_eq_zero hi (by simp [hpi])
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hfilt : (U.powersetCard R).filter (fun S => S ⊆ A) = A.powersetCard R := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hSA⟩
      exact ⟨hSA, hcard⟩
    · rintro ⟨hSA, hcard⟩
      exact ⟨⟨Finset.Subset.trans hSA (Finset.filter_subset _ U), hcard⟩, hSA⟩
  rw [hfilt, Finset.card_powersetCard]

private theorem deg_and_lb {T : Type*} [DecidableEq T] [Fintype T] {b : Nat}
    {R : (T → Bool) → Bool} (hdeg : Deg b R)
    (hR : ∀ z : T → Bool, R z = true ↔ ∀ t : T, z t = true) :
    Fintype.card T ≤ b := by
  by_contra hlt
  have hblt : b < Fintype.card T := Nat.lt_of_not_le hlt
  obtain ⟨terms, hcard, heval⟩ := deg_to_zmod2 hdeg
  have hsum_lhs : (∑ z : T → Bool, if R z then (1 : ZMod 2) else 0) = 1 := by
    rw [Finset.sum_eq_single (fun _ : T => true)]
    · have ht : R (fun _ : T => true) = true := (hR _).mpr (fun _ => rfl)
      simp [ht]
    · intro z _ hne
      have hf : R z = false := by
        cases hz : R z with
        | false => rfl
        | true =>
          exfalso
          apply hne
          ext t
          exact (hR z).mp hz t
      simp [hf]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsum_rhs : (∑ z : T → Bool, ∑ mon ∈ terms, if ∀ t ∈ mon, z t = true then (1 : ZMod 2) else 0) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro mon hmon
    have hm_lt : mon.card < Fintype.card T := lt_of_le_of_lt (hcard mon hmon) hblt
    have hex : ∃ t₀ : T, t₀ ∉ mon := by
      by_contra hall
      push Not at hall
      have : mon = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
      rw [this, Finset.card_univ] at hm_lt
      exact Nat.lt_irrefl _ hm_lt
    obtain ⟨t₀, ht₀⟩ := hex
    let flip : (T → Bool) → (T → Bool) := fun z t => if t = t₀ then !z t else z t
    have hflip_inv : ∀ z, flip (flip z) = z := by
      intro z; ext t; by_cases h : t = t₀ <;> simp [flip, h]
    have hflip_ne : ∀ z, flip z ≠ z := by
      intro z heq
      have := congrFun heq t₀
      simp [flip] at this
    have hflip_eq : ∀ z, (∀ t ∈ mon, flip z t = true) ↔ (∀ t ∈ mon, z t = true) := by
      intro z
      constructor <;> intro h t ht
      · have hne : t ≠ t₀ := fun heq => ht₀ (heq ▸ ht)
        simpa [flip, hne] using h t ht
      · have hne : t ≠ t₀ := fun heq => ht₀ (heq ▸ ht)
        simpa [flip, hne] using h t ht
    let P0 := Finset.univ.filter (fun z : T → Bool => z t₀ = false)
    let P1 := Finset.univ.filter (fun z : T → Bool => z t₀ = true)
    have hdisj : Disjoint P0 P1 := by
      rw [Finset.disjoint_left]
      intro z h0 h1
      simp only [P0, P1, Finset.mem_filter] at h0 h1
      rw [h0.2] at h1
      cases h1.2
    have hunion : P0 ∪ P1 = Finset.univ := by
      ext z
      simp only [P0, P1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases z t₀ <;> simp
    rw [← hunion, Finset.sum_union hdisj]
    have hbij : ∑ z ∈ P1, (if ∀ t ∈ mon, z t = true then (1 : ZMod 2) else 0) =
        ∑ z ∈ P0, (if ∀ t ∈ mon, z t = true then (1 : ZMod 2) else 0) := by
      apply Finset.sum_bij (fun z _ => flip z)
      · intro z hz
        simp only [P0, P1, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        simp [flip, hz]
      · intro z1 _ z2 _ h
        have := congrArg flip h
        rwa [hflip_inv, hflip_inv] at this
      · intro z hz
        refine ⟨flip z, ?_, hflip_inv z⟩
        simp only [P0, P1, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        simp [flip, hz]
      · intro z _
        simp [hflip_eq z]
    rw [hbij, ← two_mul]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_mul]
  have heq : (∑ z : T → Bool, if R z then (1 : ZMod 2) else 0) =
      ∑ z : T → Bool, ∑ mon ∈ terms, if ∀ t ∈ mon, z t = true then (1 : ZMod 2) else 0 :=
    Finset.sum_congr rfl (fun z _ => by convert heval z)
  rw [hsum_lhs, hsum_rhs] at heq
  exact one_ne_zero heq

private theorem deg_affine_pullback {V T : Type*} [DecidableEq V] [DecidableEq T] [Fintype T]
    {b : Nat} {f : (V → Bool) → Bool} (hdeg : Deg b f)
    (c0 : V → Bool) (slot : V → Option T) (flip : V → Bool) :
    Deg b (fun z : T → Bool => f (fun v => match slot v with
      | none => c0 v
      | some t => if flip v then !z t else z t)) := by
  obtain ⟨terms, hcard, heval⟩ := deg_to_zmod2 hdeg
  let sub : (T → Bool) → (V → Bool) := fun z v => match slot v with
    | none => c0 v
    | some t => if flip v then !z t else z t
  apply deg_of_sum_zmod2 terms (fun mon z => if ∀ v ∈ mon, sub z v = true then (1 : ZMod 2) else 0)
  · intro mon hmon
    have hprod : ∀ z : T → Bool,
        (if ∀ v ∈ mon, sub z v = true then (1 : ZMod 2) else 0) =
          ∏ v ∈ mon, (if sub z v = true then (1 : ZMod 2) else 0) := by
      intro z
      by_cases h : ∀ v ∈ mon, sub z v = true
      · rw [if_pos h]
        symm
        exact Finset.prod_eq_one (fun v hv => by simp [h v hv])
      · rw [if_neg h]
        push Not at h
        obtain ⟨v, hv, hne⟩ := h
        symm
        exact Finset.prod_eq_zero hv (by simp [hne])
    have h1 : ∀ v ∈ mon, ∃ c : Finset T → ZMod 2, (∀ m0, c m0 ≠ 0 → m0.card ≤ 1) ∧
        ∀ z, (if sub z v = true then (1 : ZMod 2) else 0) =
          ∑ m0 : Finset T, c m0 * (if ∀ t ∈ m0, z t = true then (1 : ZMod 2) else 0) := by
      intro v _
      have hcase : ∀ o : Option T, slot v = o →
          ∃ c : Finset T → ZMod 2, (∀ m0, c m0 ≠ 0 → m0.card ≤ 1) ∧
            ∀ z, (if sub z v = true then (1 : ZMod 2) else 0) =
              ∑ m0 : Finset T, c m0 * (if ∀ t ∈ m0, z t = true then (1 : ZMod 2) else 0) := by
        intro o ho
        cases o with
        | none =>
          obtain ⟨c, hs, he⟩ := poly_const_zmod2 (V := T) (if c0 v = true then 1 else 0)
          refine ⟨c, fun m0 hm0 => le_trans (hs m0 hm0) (Nat.zero_le 1), fun z => ?_⟩
          have hsub_eq : sub z v = c0 v := by dsimp only [sub]; rw [ho]
          rw [hsub_eq]; exact he z
        | some t =>
          cases hfl : flip v
          · obtain ⟨c, hs, he⟩ := poly_lit_zmod2 t true
            refine ⟨c, hs, fun z => ?_⟩
            have hsub_eq : sub z v = z t := by dsimp only [sub]; rw [ho, hfl]; rfl
            rw [hsub_eq]; exact he z
          · obtain ⟨c, hs, he⟩ := poly_lit_zmod2 t false
            refine ⟨c, hs, fun z => ?_⟩
            have hsub_eq : sub z v = !z t := by dsimp only [sub]; rw [ho, hfl]; rfl
            rw [hsub_eq]
            have hneg : (if (!z t) = true then (1 : ZMod 2) else 0) =
                (if z t = false then (1 : ZMod 2) else 0) := by
              cases z t <;> rfl
            rw [hneg]; exact he z
      exact hcase (slot v) rfl
    obtain ⟨c, hsupp, he⟩ := poly_prod_zmod2 mon 1 (fun v z => if sub z v = true then (1 : ZMod 2) else 0) h1
    refine ⟨c, fun m0 hm0 => le_trans (hsupp m0 hm0) (by simpa using hcard mon hmon), fun z => ?_⟩
    rw [hprod z, he z]
  · intro z
    exact heval (sub z)

private theorem run_foldl_lt (f : Nat → Nat → Bool) :
    ∀ n : Nat, (List.range n).foldl (fun h pos => h + ((f pos h).toNat <<< pos)) 0 < 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set h := (List.range n).foldl (fun h pos => h + ((f pos h).toNat <<< pos)) 0
    have hshift : (f n h).toNat <<< n ≤ 2 ^ n := by
      rw [Nat.shiftLeft_eq]
      cases f n h <;> simp
    have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    omega

private theorem run_foldl_testBit (f : Nat → Nat → Bool) :
    ∀ (n p : Nat), p < n →
      ((List.range n).foldl (fun h pos => h + ((f pos h).toNat <<< pos)) 0).testBit p =
        f p ((List.range p).foldl (fun h pos => h + ((f pos h).toNat <<< pos)) 0) := by
  intro n
  induction n with
  | zero => intro p hp; omega
  | succ n ih =>
    intro p hp
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set h := (List.range n).foldl (fun h pos => h + ((f pos h).toNat <<< pos)) 0
    have hh_lt : h < 2 ^ n := run_foldl_lt f n
    have hbit : ∀ q, (h + ((f n h).toNat <<< n)).testBit q =
        if q = n then f n h else h.testBit q := by
      intro q
      rw [Nat.shiftLeft_eq]
      cases hb : f n h
      · simp only [Bool.toNat_false, zero_mul, add_zero]
        by_cases hqn : q = n
        · subst hqn
          simp [Nat.testBit_lt_two_pow hh_lt]
        · simp [hqn]
      · simp only [Bool.toNat_true, one_mul]
        by_cases hqn : q = n
        · subst hqn
          simp only [↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
          have hdiv : (h + 2 ^ q) / 2 ^ q = 1 := by
            rw [Nat.add_div_right _ (Nat.two_pow_pos q), Nat.div_eq_of_lt hh_lt]
          rw [hdiv]
          rfl
        · simp only [hqn, ↓reduceIte]
          by_cases hlt : q < n
          · simp only [Nat.testBit_eq_decide_div_mod_eq]
            have hpow : 2 ^ n = 2 ^ q * (2 * 2 ^ (n - q - 1)) := by
              have hexp : n = q + 1 + (n - q - 1) := by omega
              conv_lhs => rw [hexp, pow_add, pow_add, pow_one]
              ring
            rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos q)]
            have hmod2 : (h / 2 ^ q + 2 * 2 ^ (n - q - 1)) % 2 = (h / 2 ^ q) % 2 := by omega
            rw [hmod2]
          · have hgt : n + 1 ≤ q := by omega
            have hlt1 : h + 2 ^ n < 2 ^ q := by
              have hle : 2 ^ (n + 1) ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hgt
              have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
              omega
            have hlt2 : h < 2 ^ q := by omega
            rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]
    rw [hbit p]
    by_cases hpn : p = n
    · subst hpn; simp [h]
    · simp only [hpn, ↓reduceIte]
      exact ih p (by omega)

private theorem surj_of_avoid {g a : Nat}
    (f : (Fin g × Fin (2 ^ a - 1) × Fin a → Bool) → (Fin g → Fin (2 ^ a)))
    (label : Fin g → Fin (2 ^ a - 1) → Fin (2 ^ a) → Fin a → Bool)
    (havoid : ∀ x j i, (fun rawBit => x (j, i, rawBit)) ≠ label j i (f x j)) :
    Function.Surjective f := by
  intro y0
  have hbij : ∀ j : Fin g, ∃ e : Fin (2 ^ a - 1) → Fin (2 ^ a),
      ∀ y : Fin (2 ^ a), y ≠ y0 j → ∃ i : Fin (2 ^ a - 1), e i = y := by
    intro j
    let S : Finset (Fin (2 ^ a)) := Finset.univ.erase (y0 j)
    have hcard : S.card = 2 ^ a - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have heq : S.equivFin.symm.toFun ≠ S.equivFin.symm.toFun → False := fun h => h rfl
    let e0 : Fin S.card ≃ S := S.equivFin.symm
    refine ⟨fun i => (e0 ⟨i.val, by omega⟩).val, fun y hy => ?_⟩
    have hyS : y ∈ S := Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩
    let idx := e0.symm ⟨y, hyS⟩
    refine ⟨⟨idx.val, by omega⟩, ?_⟩
    have h1 : (⟨idx.val, by omega⟩ : Fin S.card) = idx := Fin.ext rfl
    dsimp only
    rw [h1]
    simp [idx]
  choose e he using hbij
  let x : Fin g × Fin (2 ^ a - 1) × Fin a → Bool := fun p => label p.1 p.2.1 (e p.1 p.2.1) p.2.2
  refine ⟨x, ?_⟩
  ext j
  by_contra hne
  have hne' : f x j ≠ y0 j := fun h => hne (congrArg Fin.val h)
  obtain ⟨i, hi⟩ := he j (f x j) hne'
  have hbad := havoid x j i
  apply hbad
  ext rawBit
  dsimp only [x]
  rw [hi]

private theorem exists_adj_diff {g M : Nat} (F : (Fin g → Fin M) → Bool)
    (hnc : ∃ y1 y2, F y1 ≠ F y2) :
    ∃ (y0 : Fin g → Fin M) (j0 : Fin g) (c1 : Fin M),
      F y0 ≠ F (Function.update y0 j0 c1) := by
  obtain ⟨y1, y2, hne⟩ := hnc
  let mix : ℕ → Fin g → Fin M := fun k j => if j.val < k then y2 j else y1 j
  have h0 : mix 0 = y1 := by ext j; simp [mix]
  have hg : mix g = y2 := by ext j; simp [mix, j.isLt]
  have hstep : ∃ k < g, F (mix k) ≠ F (mix (k + 1)) := by
    by_contra hall
    push Not at hall
    have hsame : ∀ k ≤ g, F (mix k) = F (mix 0) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [← hall k hk, ih (Nat.le_of_lt hk)]
    have := hsame g le_rfl
    rw [h0, hg] at this
    exact hne this.symm
  obtain ⟨k, hk, hdiff⟩ := hstep
  refine ⟨mix k, ⟨k, hk⟩, y2 ⟨k, hk⟩, ?_⟩
  have hupd : Function.update (mix k) ⟨k, hk⟩ (y2 ⟨k, hk⟩) = mix (k + 1) := by
    ext j
    by_cases hj : j = ⟨k, hk⟩
    · subst hj; simp [mix]
    · rw [Function.update_of_ne hj]
      have hne' : j.val ≠ k := fun h => hj (Fin.ext h)
      dsimp only [mix]
      by_cases hlt : j.val < k
      · have hlt2 : j.val < k + 1 := by omega
        simp [hlt, hlt2]
      · have hlt2 : ¬ (j.val < k + 1) := by omega
        simp [hlt, hlt2]
  rwa [hupd]

private theorem solve :
    ∀ (g a : Nat), 0 < g → 0 < a →
      let M := 2^a
      let m := M-1
      let d := g*a
      let V := Fin g × Fin m × Fin a
      let W := V → Bool
      let deg := fun (b : Nat) (f : W → Bool) =>
        ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
          ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
      let Y := Fin g → Fin M
      let valid := fun (x : W) (choice : Y) =>
        ∀ j i, ∃ v : Fin a, x (j,i,v) ≠ (choice j).val.testBit v.val
      let run := fun (ask : Nat → Nat → W → Bool) (x : W) =>
        (List.range d).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
      (∃ (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
        (∀ (u : Fin d) (h : Nat),
          deg ((u.val % a+1)*2^(a-1-u.val % a)) (choose u.val h)) ∧
        ∀ input, valid input (decode (run choose input))) ∧
      (∀ (n : Nat) (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
        (∀ input, valid input (decode ((List.range n).foldl (fun trace tick =>
          trace + ((choose tick trace input).toNat <<< tick)) 0))) → d ≤ n) ∧
      ∀ (ask : Fin d → W → Bool) (report : (Fin d → Bool) → Y)
        (label : Fin g → Fin m → Fin M → Fin a → Bool),
        (∀ x j i, (fun rawBit => x (j,i,rawBit)) ≠ label j i (report (fun u => ask u x) j)) →
        ∀ (mask : Finset (Fin d)), mask.Nonempty → ∀ b : Nat,
          deg b (fun word => (((mask.filter (fun bitId => ask bitId word = true)).card % 2) == 1)) →
          2^(a-1) ≤ b := by
  intro g a hg ha
  dsimp only
  set M := 2 ^ a
  set m := M - 1
  set d := g * a
  have hMpos : 0 < M := Nat.two_pow_pos a
  refine ⟨?_, ?_, ?_⟩
  · let matchPref (j : Fin g) (k : Nat) (h : Nat) (x : (Fin g × Fin m × Fin a) → Bool) (i : Fin m) : Bool :=
      ((List.finRange a).take (k + 1)).all (fun v =>
        x (j, i, v) == (if v.val < k then h.testBit (j.val * a + v.val) else false))
    let choose : Nat → Nat → ((Fin g × Fin m × Fin a) → Bool) → Bool := fun u h x =>
      if hlt : u < d then
        let j : Fin g := ⟨u / a, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm a g]; exact hlt)⟩
        let k := u % a
        let R := 2 ^ (a - 1 - k)
        let cnt := (Finset.univ.filter (fun i : Fin m => matchPref j k h x i = true)).card
        decide (Nat.choose cnt R % 2 = 1)
      else false
    let decode : Nat → (Fin g → Fin M) := fun h j =>
      ⟨(h >>> (j.val * a)) % M, Nat.mod_lt _ hMpos⟩
    refine ⟨choose, decode, ?_, ?_⟩
    · intro u h
      have hlt : u.val < d := u.isLt
      set j : Fin g := ⟨u.val / a, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm a g]; exact hlt)⟩
      set k := u.val % a
      have hk_lt : k < a := Nat.mod_lt u.val ha
      set R := 2 ^ (a - 1 - k)
      have hDeg : Deg ((k + 1) * R) (choose u.val h) := by
        apply deg_of_sum_zmod2 ((Finset.univ : Finset (Fin m)).powersetCard R)
          (fun S x => ∏ i ∈ S, (if matchPref j k h x i = true then (1 : ZMod 2) else 0))
        · intro S hS
          have hScard : S.card = R := (Finset.mem_powersetCard.mp hS).2
          have hper_i : ∀ i ∈ S,
              ∃ c : Finset (Fin g × Fin m × Fin a) → ZMod 2,
                (∀ mon, c mon ≠ 0 → mon.card ≤ k + 1) ∧
                ∀ x, (if matchPref j k h x i = true then (1 : ZMod 2) else 0) =
                  ∑ mon : Finset (Fin g × Fin m × Fin a),
                    c mon * (if ∀ p ∈ mon, x p = true then (1 : ZMod 2) else 0) := by
            intro i _
            let vs : Finset (Fin a) := Finset.univ.filter (fun v : Fin a => v.val < k + 1)
            have hvs_card : vs.card = k + 1 := by
              have hbij : vs.card = (Finset.range (k + 1)).card := by
                apply Finset.card_bij (fun v _ => v.val)
                · intro v hv; exact Finset.mem_range.mpr (Finset.mem_filter.mp hv).2
                · intro v1 _ v2 _ h; exact Fin.ext h
                · intro t ht
                  have ht' : t < k + 1 := Finset.mem_range.mp ht
                  exact ⟨⟨t, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩, rfl⟩
              rw [hbij, Finset.card_range]
            have hmp : ∀ x, (if matchPref j k h x i = true then (1 : ZMod 2) else 0) =
                ∏ v ∈ vs, (if x (j, i, v) = (if v.val < k then h.testBit (j.val * a + v.val) else false)
                  then (1 : ZMod 2) else 0) := by
              intro x
              have hiff : matchPref j k h x i = true ↔
                  ∀ v ∈ vs, x (j, i, v) = (if v.val < k then h.testBit (j.val * a + v.val) else false) := by
                dsimp only [matchPref]
                rw [List.all_eq_true]
                constructor
                · intro hall v hv
                  have hvlt : v.val < k + 1 := (Finset.mem_filter.mp hv).2
                  have hmem : v ∈ (List.finRange a).take (k + 1) := by
                    rw [List.mem_iff_getElem]
                    have hlen : v.val < ((List.finRange a).take (k + 1)).length := by
                      simp [v.isLt, hvlt]
                    refine ⟨v.val, hlen, ?_⟩
                    apply Fin.ext
                    simp [List.getElem_take, List.getElem_finRange]
                  exact beq_iff_eq.mp (hall v hmem)
                · intro hall v hv
                  rw [List.mem_iff_getElem] at hv
                  obtain ⟨idx, hidx, rfl⟩ := hv
                  have hlt1 : idx < k + 1 := lt_of_lt_of_le hidx (List.length_take_le (k + 1) _)
                  have hlt2 : idx < a := by have := lt_of_lt_of_le hidx (List.length_take_le' (k + 1) _); simpa using this
                  have hget : ((List.finRange a).take (k + 1))[idx] = ⟨idx, hlt2⟩ := by
                    apply Fin.ext
                    simp [List.getElem_take, List.getElem_finRange]
                  rw [hget]
                  exact beq_iff_eq.mpr (hall ⟨idx, hlt2⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt1⟩))
              by_cases hm : matchPref j k h x i = true
              · rw [ite_eq_left hm]
                symm
                exact Finset.prod_eq_one (fun v hv => by rw [ite_eq_left (hiff.mp hm v hv)])
              · rw [ite_eq_right hm]
                have hnot : ¬ ∀ v ∈ vs, x (j, i, v) = (if v.val < k then h.testBit (j.val * a + v.val) else false) :=
                  fun h0 => hm (hiff.mpr h0)
                push Not at hnot
                obtain ⟨v, hv, hne⟩ := hnot
                symm
                exact Finset.prod_eq_zero hv (ite_eq_right hne)
            obtain ⟨c, hsupp, he⟩ := poly_prod_zmod2 vs 1
              (fun v x => if x (j, i, v) = (if v.val < k then h.testBit (j.val * a + v.val) else false)
                then (1 : ZMod 2) else 0)
              (fun v _ => poly_lit_zmod2 (j, i, v) (if v.val < k then h.testBit (j.val * a + v.val) else false))
            refine ⟨c, fun mon hne => by have := hsupp mon hne; rw [hvs_card, mul_one] at this; exact this, fun x => ?_⟩
            rw [hmp x, he x]
          obtain ⟨c, hsupp, he⟩ := poly_prod_zmod2 S (k + 1)
            (fun i x => if matchPref j k h x i = true then (1 : ZMod 2) else 0) hper_i
          refine ⟨c, fun mon hne => by have := hsupp mon hne; rw [hScard, mul_comm] at this; exact this, he⟩
        · intro x
          have hch : choose u.val h x =
              decide ((Finset.univ.filter (fun i : Fin m => matchPref j k h x i = true)).card.choose R % 2 = 1) := by
            dsimp only [choose]
            rw [dite_eq_left hlt]
          simp only [hch]
          rw [sum_powersetCard_eq_choose]
          set cnt := (Finset.univ.filter (fun i : Fin m => matchPref j k h x i = true)).card
          have hmod : ((Nat.choose cnt R : Nat) : ZMod 2) = (((Nat.choose cnt R % 2 : Nat) : ZMod 2)) := by
            rw [← Nat.div_add_mod (Nat.choose cnt R) 2]
            push_cast
            have h2 : (2 : ZMod 2) = 0 := rfl
            simp [h2]
          rw [hmod]
          rcases Nat.mod_two_eq_zero_or_one (Nat.choose cnt R) with h0 | h1
          · simp [h0]
          · simp [h1]
      obtain ⟨terms, hcard, heval⟩ := hDeg
      exact ⟨terms, hcard, fun input => by convert heval input⟩
    · intro x j
      set hAll := (List.range d).foldl (fun h pos => h + ((choose pos h x).toNat <<< pos)) 0
      have hbit_dec : ∀ v : Fin a, (decode hAll j).val.testBit v.val = hAll.testBit (j.val * a + v.val) := by
        intro v
        dsimp only [decode]
        simp [M, Nat.testBit_mod_two_pow, v.isLt, Nat.testBit_shiftRight]
      have hpref_inv : ∀ k ≤ a,
          (Finset.univ.filter (fun i : Fin m =>
            ∀ v : Fin a, v.val < k → x (j, i, v) = hAll.testBit (j.val * a + v.val))).card < 2 ^ (a - k) := by
        intro k
        induction k with
        | zero =>
          intro _
          have hcard_le : (Finset.univ.filter (fun i : Fin m =>
              ∀ v : Fin a, v.val < 0 → x (j, i, v) = hAll.testBit (j.val * a + v.val))).card ≤ m := by
            calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
              _ = m := by simp
          have : 2 ^ (a - 0) = M := by simp [M]
          omega
        | succ k ih =>
          intro hk
          have hk_lt : k < a := hk
          have hprev := ih (Nat.le_of_lt hk)
          set pos := j.val * a + k
          have hpos_lt : pos < d := by
            have hj1 : j.val + 1 ≤ g := j.isLt
            have hmul : (j.val + 1) * a ≤ g * a := Nat.mul_le_mul_right a hj1
            dsimp only [d, pos]
            nlinarith
          set hPre := (List.range pos).foldl (fun h p => h + ((choose p h x).toNat <<< p)) 0
          have hpre_eq : ∀ v : Fin a, v.val < k →
              hPre.testBit (j.val * a + v.val) = hAll.testBit (j.val * a + v.val) := by
            intro v hv
            have hp1 : j.val * a + v.val < pos := by dsimp only [pos]; omega
            have hp2 : j.val * a + v.val < d := lt_trans hp1 hpos_lt
            rw [run_foldl_testBit (fun p h => choose p h x) pos (j.val * a + v.val) hp1,
              run_foldl_testBit (fun p h => choose p h x) d (j.val * a + v.val) hp2]
          have hbit_k : hAll.testBit pos = choose pos hPre x :=
            run_foldl_testBit (fun p h => choose p h x) d pos hpos_lt
          have hdiv : pos / a = j.val := by
            dsimp only [pos]
            rw [Nat.mul_comm, Nat.mul_add_div ha, Nat.div_eq_of_lt hk_lt, Nat.add_zero]
          have hmod : pos % a = k := by
            dsimp only [pos]
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk_lt]
          let S_prev := Finset.univ.filter (fun i : Fin m =>
            ∀ v : Fin a, v.val < k → x (j, i, v) = hAll.testBit (j.val * a + v.val))
          have hprev' : S_prev.card < 2 ^ (a - k) := hprev
          let S0 := S_prev.filter (fun i => x (j, i, ⟨k, hk_lt⟩) = false)
          let S1 := S_prev.filter (fun i => x (j, i, ⟨k, hk_lt⟩) = true)
          have hS0_eq : Finset.univ.filter (fun i : Fin m => matchPref j k hPre x i = true) = S0 := by
            ext i
            simp only [S0, S_prev, Finset.mem_filter, Finset.mem_univ, true_and, matchPref, List.all_eq_true]
            constructor
            · intro hall
              refine ⟨fun v hv => ?_, ?_⟩
              · have hmem : v ∈ (List.finRange a).take (k + 1) := by
                  rw [List.mem_iff_getElem]
                  refine ⟨v.val, by simp [v.isLt, Nat.lt_succ_of_lt hv], ?_⟩
                  apply Fin.ext
                  simp [List.getElem_take, List.getElem_finRange]
                have h1 := beq_iff_eq.mp (hall v hmem)
                rw [ite_eq_left hv, hpre_eq v hv] at h1
                exact h1
              · have hmem : (⟨k, hk_lt⟩ : Fin a) ∈ (List.finRange a).take (k + 1) := by
                  rw [List.mem_iff_getElem]
                  refine ⟨k, by simp [hk_lt], ?_⟩
                  apply Fin.ext
                  simp [List.getElem_take, List.getElem_finRange]
                have h1 := beq_iff_eq.mp (hall ⟨k, hk_lt⟩ hmem)
                simp only [Nat.lt_irrefl, ↓reduceIte] at h1
                exact h1
            · rintro ⟨h1, h2⟩ v hv
              rw [List.mem_iff_getElem] at hv
              obtain ⟨idx, hidx, rfl⟩ := hv
              have hlt1 : idx < k + 1 := lt_of_lt_of_le hidx (List.length_take_le (k + 1) _)
              have hlt2 : idx < a := by have := lt_of_lt_of_le hidx (List.length_take_le' (k + 1) _); simpa using this
              have hget : ((List.finRange a).take (k + 1))[idx] = ⟨idx, hlt2⟩ := by
                apply Fin.ext
                simp [List.getElem_take, List.getElem_finRange]
              rw [hget]
              by_cases hlt_k : idx < k
              · simp only [hlt_k, ↓reduceIte, beq_iff_eq]
                rw [hpre_eq ⟨idx, hlt2⟩ hlt_k]
                exact h1 ⟨idx, hlt2⟩ hlt_k
              · have heq_k : idx = k := by omega
                subst heq_k
                simp only [Nat.lt_irrefl, ↓reduceIte, beq_iff_eq]
                exact h2
          have hdisj : Disjoint S0 S1 := by
            rw [Finset.disjoint_left]
            intro i h0 h1
            simp only [S0, S1, Finset.mem_filter] at h0 h1
            rw [h0.2] at h1; cases h1.2
          have hunion : S0 ∪ S1 = S_prev := by
            ext i
            simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
            cases x (j, i, ⟨k, hk_lt⟩) <;> simp
          have hsum_card : S0.card + S1.card = S_prev.card := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion]
          have h2pow : 2 ^ (a - k) = 2 * 2 ^ (a - 1 - k) := by
            have hsub : a - k = (a - 1 - k) + 1 := by omega
            rw [hsub, pow_succ]; ring
          have hS0_lt : S0.card < 2 * 2 ^ (a - 1 - k) := by omega
          have hch_val : choose pos hPre x = decide (2 ^ (a - 1 - k) ≤ S0.card) := by
            dsimp only [choose]
            rw [dite_eq_left hpos_lt]
            have hj_eq : (⟨pos / a, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm a g]; exact hpos_lt)⟩ : Fin g) = j :=
              Fin.ext hdiv
            simp only [hj_eq, hmod, hS0_eq]
            have hluc := choose_two_pow_zmod2 (a - 1 - k) S0.card hS0_lt
            have hmod2 : ((Nat.choose S0.card (2 ^ (a - 1 - k)) : Nat) : ZMod 2) =
                ((Nat.choose S0.card (2 ^ (a - 1 - k)) % 2 : Nat) : ZMod 2) := by
              rw [← Nat.div_add_mod (Nat.choose S0.card (2 ^ (a - 1 - k))) 2]
              push_cast
              have h2 : (2 : ZMod 2) = 0 := rfl
              simp [h2]
            rw [hmod2] at hluc
            rcases Nat.mod_two_eq_zero_or_one (Nat.choose S0.card (2 ^ (a - 1 - k))) with h0 | h1
            · rw [h0] at hluc ⊢
              by_cases hge : 2 ^ (a - 1 - k) ≤ S0.card
              · rw [ite_eq_left hge] at hluc; simp at hluc
              · simp [hge]
            · rw [h1] at hluc ⊢
              by_cases hge : 2 ^ (a - 1 - k) ≤ S0.card
              · simp [hge]
              · rw [ite_eq_right hge] at hluc; simp at hluc
          have hnext_eq : Finset.univ.filter (fun i : Fin m =>
              ∀ v : Fin a, v.val < k + 1 → x (j, i, v) = hAll.testBit (j.val * a + v.val)) =
              if 2 ^ (a - 1 - k) ≤ S0.card then S1 else S0 := by
            ext i
            by_cases hge : 2 ^ (a - 1 - k) ≤ S0.card
            · simp only [hge, ↓reduceIte, S1, S_prev, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro hall
                refine ⟨fun v hv => hall v (Nat.lt_succ_of_lt hv), ?_⟩
                have := hall ⟨k, hk_lt⟩ (Nat.lt_succ_self k)
                change x (j, i, ⟨k, hk_lt⟩) = hAll.testBit pos at this
                rw [hbit_k, hch_val, decide_eq_true hge] at this
                exact this
              · rintro ⟨h1, h2⟩ v hv
                by_cases hvk : v.val < k
                · exact h1 v hvk
                · have hveq : v = ⟨k, hk_lt⟩ := Fin.ext (by dsimp only; omega)
                  subst hveq
                  change x (j, i, ⟨k, hk_lt⟩) = hAll.testBit pos
                  rw [hbit_k, hch_val, decide_eq_true hge]
                  exact h2
            · simp only [hge, ↓reduceIte, S0, S_prev, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro hall
                refine ⟨fun v hv => hall v (Nat.lt_succ_of_lt hv), ?_⟩
                have := hall ⟨k, hk_lt⟩ (Nat.lt_succ_self k)
                change x (j, i, ⟨k, hk_lt⟩) = hAll.testBit pos at this
                rw [hbit_k, hch_val, decide_eq_false hge] at this
                exact this
              · rintro ⟨h1, h2⟩ v hv
                by_cases hvk : v.val < k
                · exact h1 v hvk
                · have hveq : v = ⟨k, hk_lt⟩ := Fin.ext (by dsimp only; omega)
                  subst hveq
                  change x (j, i, ⟨k, hk_lt⟩) = hAll.testBit pos
                  rw [hbit_k, hch_val, decide_eq_false hge]
                  exact h2
          rw [hnext_eq]
          have hsub_eq : a - (k + 1) = a - 1 - k := by omega
          rw [hsub_eq]
          split_ifs with hge
          · omega
          · omega
      have hzero := hpref_inv a le_rfl
      simp only [Nat.sub_self, pow_zero, Nat.lt_one_iff, Finset.card_eq_zero] at hzero
      intro i
      have hnot : i ∉ Finset.univ.filter (fun i : Fin m =>
          ∀ v : Fin a, v.val < a → x (j, i, v) = hAll.testBit (j.val * a + v.val)) := by
        rw [hzero]; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      push Not at hnot
      obtain ⟨v, _, hne⟩ := hnot
      exact ⟨v, by rwa [hbit_dec v]⟩
  · intro n choose decode hvalid
    let f : ((Fin g × Fin m × Fin a) → Bool) → (Fin g → Fin M) := fun x =>
      decode ((List.range n).foldl (fun trace tick => trace + ((choose tick trace x).toNat <<< tick)) 0)
    have hsurj : Function.Surjective f := by
      apply surj_of_avoid f (fun _ _ y v => y.val.testBit v.val)
      intro x j i heq
      obtain ⟨v, hv⟩ := hvalid x j i
      exact hv (congrFun heq v)
    let traceFn : ((Fin g × Fin m × Fin a) → Bool) → Fin (2 ^ n) := fun x =>
      ⟨(List.range n).foldl (fun trace tick => trace + ((choose tick trace x).toNat <<< tick)) 0,
        run_foldl_lt (fun tick tr => choose tick tr x) n⟩
    have hsurj_dec : Function.Surjective (fun t : Fin (2 ^ n) => decode t.val) := by
      intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨traceFn x, rfl⟩
    have hcard : Fintype.card (Fin g → Fin M) ≤ Fintype.card (Fin (2 ^ n)) :=
      Fintype.card_le_of_surjective _ hsurj_dec
    simp only [Fintype.card_fun, Fintype.card_fin] at hcard
    have hpow : 2 ^ d ≤ 2 ^ n := by
      dsimp only [d, M] at hcard ⊢
      rwa [← pow_mul, Nat.mul_comm] at hcard
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
  · intro ask report label havoid mask hmask b hdeg
    have hsurj_comp : Function.Surjective (fun x => report (fun u => ask u x)) :=
      surj_of_avoid (fun x => report (fun u => ask u x)) label havoid
    have hsurj_rep : Function.Surjective report := fun y => by
      obtain ⟨x, hx⟩ := hsurj_comp y
      exact ⟨fun u => ask u x, hx⟩
    have hcard_eq : Fintype.card (Fin d → Bool) = Fintype.card (Fin g → Fin M) := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, M, d, ← pow_mul, Nat.mul_comm]
    have hbij_rep : Function.Bijective report :=
      (Fintype.bijective_iff_surjective_and_card report).mpr ⟨hsurj_rep, hcard_eq⟩
    let repEquiv : (Fin d → Bool) ≃ (Fin g → Fin M) := Equiv.ofBijective report hbij_rep
    let par : (Fin d → Bool) → Bool := fun z =>
      (((mask.filter (fun bitId => z bitId = true)).card % 2) == 1)
    let F : (Fin g → Fin M) → Bool := fun y => par (repEquiv.symm y)
    have hF_eq : ∀ x, F (report (fun u => ask u x)) =
        (((mask.filter (fun bitId => ask bitId x = true)).card % 2) == 1) := by
      intro x
      dsimp only [F]
      have h1 : repEquiv.symm (report (fun u => ask u x)) = (fun u => ask u x) :=
        repEquiv.symm_apply_apply _
      rw [h1]
    have hnc : ∃ y1 y2, F y1 ≠ F y2 := by
      obtain ⟨u0, hu0⟩ := hmask
      let z0 : Fin d → Bool := fun _ => false
      let z1 : Fin d → Bool := fun u => decide (u = u0)
      have hz0 : par z0 = false := by
        dsimp only [par, z0]
        simp
      have hz1 : par z1 = true := by
        dsimp only [par, z1]
        have hfilt : mask.filter (fun bitId => decide (bitId = u0) = true) = {u0} := by
          ext u
          simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨h ▸ hu0, h⟩⟩
        rw [hfilt]
        simp
      refine ⟨repEquiv z0, repEquiv z1, ?_⟩
      dsimp only [F]
      rw [repEquiv.symm_apply_apply, repEquiv.symm_apply_apply, hz0, hz1]
      decide
    obtain ⟨y0, j0, c1, hdiff⟩ := exists_adj_diff F hnc
    let S0 := Finset.univ.filter (fun c : Fin M => F (Function.update y0 j0 c) = false)
    let S1 := Finset.univ.filter (fun c : Fin M => F (Function.update y0 j0 c) = true)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro c h0 h1
      simp only [S0, S1, Finset.mem_filter] at h0 h1
      rw [h0.2] at h1; cases h1.2
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext c
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases F (Function.update y0 j0 c) <;> simp
    have hsum : S0.card + S1.card = M := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have hne01 : S0.Nonempty ∧ S1.Nonempty := by
      have hy0_eq : Function.update y0 j0 (y0 j0) = y0 := Function.update_eq_self j0 y0
      cases hf0 : F y0 <;> cases hf1 : F (Function.update y0 j0 c1)
      · rw [hf0, hf1] at hdiff; exact absurd rfl hdiff
      · exact ⟨⟨y0 j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hy0_eq]⟩⟩,
          ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf1⟩⟩⟩
      · exact ⟨⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf1⟩⟩,
          ⟨y0 j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hy0_eq]⟩⟩⟩
      · rw [hf0, hf1] at hdiff; exact absurd rfl hdiff
    have h2pow : M = 2 * 2 ^ (a - 1) := by
      have ha1 : a = (a - 1) + 1 := by omega
      dsimp only [M]
      conv_lhs => rw [ha1, pow_succ]
      ring
    have hex_big : ∃ (targetVal : Bool) (T : Finset (Fin M)) (cStar : Fin M),
        2 ^ (a - 1) ≤ T.card ∧ cStar ∉ T ∧
        F (Function.update y0 j0 cStar) = targetVal ∧
        ∀ c ∈ T, F (Function.update y0 j0 c) = !targetVal := by
      by_cases hbig : 2 ^ (a - 1) ≤ S0.card
      · obtain ⟨cStar, hcStar⟩ := hne01.2
        have hnot : cStar ∉ S0 := Finset.disjoint_right.mp hdisj hcStar
        exact ⟨true, S0, cStar, hbig, hnot, (Finset.mem_filter.mp hcStar).2,
          fun c hc => (Finset.mem_filter.mp hc).2⟩
      · obtain ⟨cStar, hcStar⟩ := hne01.1
        have hnot : cStar ∉ S1 := Finset.disjoint_left.mp hdisj hcStar
        exact ⟨false, S1, cStar, by omega, hnot, (Finset.mem_filter.mp hcStar).2,
          fun c hc => by simp [(Finset.mem_filter.mp hc).2]⟩
    obtain ⟨targetVal, T, cStar, hTcard, hcStar_not, hFcStar, hFT⟩ := hex_big
    let Sother : Fin g → Finset (Fin M) := fun j =>
      if j = j0 then Finset.univ.erase cStar else Finset.univ.erase (y0 j)
    have hbij_j : ∀ j : Fin g, ∃ e : Fin m ≃ Sother j, True := by
      intro j
      have hcard_s : (Sother j).card = m := by
        dsimp only [Sother]
        split_ifs <;> rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      exact ⟨(Fin.castOrderIso hcard_s.symm).toEquiv.trans (Sother j).equivFin.symm, trivial⟩
    choose eJ _ using hbij_j
    let invT : T → Fin m := fun t => (eJ j0).symm ⟨t.val, by
      dsimp only [Sother]
      rw [if_pos rfl]
      exact Finset.mem_erase.mpr ⟨fun h => hcStar_not (h ▸ t.property), Finset.mem_univ _⟩⟩
    have hinvT_inj : Function.Injective invT := by
      intro t1 t2 h
      have h1 := (eJ j0).symm.injective h
      exact Subtype.ext (congrArg (fun p : Sother j0 => p.val) h1)
    let c0 : (Fin g × Fin m × Fin a) → Bool := fun p =>
      if hj : p.1 = j0 then
        if ((eJ j0 p.2.1).val ∈ T) then label j0 p.2.1 cStar p.2.2
        else label j0 p.2.1 (eJ j0 p.2.1).val p.2.2
      else label p.1 p.2.1 (eJ p.1 p.2.1).val p.2.2
    let slot : (Fin g × Fin m × Fin a) → Option T := fun p =>
      if hj : p.1 = j0 then
        if hmem : (eJ j0 p.2.1).val ∈ T then
          if label j0 p.2.1 (eJ j0 p.2.1).val p.2.2 = label j0 p.2.1 cStar p.2.2 then none
          else some ⟨(eJ j0 p.2.1).val, hmem⟩
        else none
      else none
    let flipB : (Fin g × Fin m × Fin a) → Bool := fun p =>
      if p.1 = j0 then label j0 p.2.1 cStar p.2.2 else false
    let sub : (T → Bool) → ((Fin g × Fin m × Fin a) → Bool) := fun z p =>
      match slot p with
      | none => c0 p
      | some t => if flipB p then !z t else z t
    have hsub_other : ∀ z (j : Fin g), j ≠ j0 → ∀ i v,
        sub z (j, i, v) = label j i (eJ j i).val v := by
      intro z j hj i v
      dsimp only [sub, slot, c0]
      simp [hj]
    have hsub_j0_notT : ∀ z (i : Fin m), (eJ j0 i).val ∉ T → ∀ v,
        sub z (j0, i, v) = label j0 i (eJ j0 i).val v := by
      intro z i hnot v
      dsimp only [sub, slot, c0]
      simp [hnot]
    have hsub_j0_T : ∀ z (i : Fin m) (hmem : (eJ j0 i).val ∈ T) (v : Fin a),
        sub z (j0, i, v) =
          if z ⟨(eJ j0 i).val, hmem⟩ then label j0 i (eJ j0 i).val v else label j0 i cStar v := by
      intro z i hmem v
      dsimp only [sub, slot, c0, flipB]
      simp only [↓reduceDIte, hmem, ↓reduceIte]
      by_cases heq : label j0 i (eJ j0 i).val v = label j0 i cStar v
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        cases h1 : label j0 i (eJ j0 i).val v <;> cases h2 : label j0 i cStar v <;>
          cases z ⟨(eJ j0 i).val, hmem⟩ <;> simp_all
    have hrep_other : ∀ z (j : Fin g), j ≠ j0 → report (fun u => ask u (sub z)) j = y0 j := by
      intro z j hj
      by_contra hne
      have hmemS : report (fun u => ask u (sub z)) j ∈ Sother j := by
        dsimp only [Sother]; rw [if_neg hj]
        exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
      let i := (eJ j).symm ⟨report (fun u => ask u (sub z)) j, hmemS⟩
      apply havoid (sub z) j i
      ext v
      rw [hsub_other z j hj i v]
      have hi : (eJ j i).val = report (fun u => ask u (sub z)) j := by
        dsimp only [i]; simp
      rw [hi]
    have hrep_j0_all : report (fun u => ask u (sub (fun _ => true))) j0 = cStar := by
      by_contra hne
      have hmemS : report (fun u => ask u (sub (fun _ => true))) j0 ∈ Sother j0 := by
        dsimp only [Sother]; rw [if_pos rfl]
        exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
      let i := (eJ j0).symm ⟨report (fun u => ask u (sub (fun _ => true))) j0, hmemS⟩
      apply havoid (sub (fun _ => true)) j0 i
      ext v
      have hi : (eJ j0 i).val = report (fun u => ask u (sub (fun _ => true))) j0 := by
        dsimp only [i]; simp
      by_cases hT : (eJ j0 i).val ∈ T
      · rw [hsub_j0_T _ i hT v]; simp [hi]
      · rw [hsub_j0_notT _ i hT v, hi]
    have hrep_j0_not_all : ∀ z : T → Bool, (∃ t : T, z t = false) →
        report (fun u => ask u (sub z)) j0 ∈ T := by
      intro z ⟨t0, ht0⟩
      by_contra hnotT
      by_cases hc : report (fun u => ask u (sub z)) j0 = cStar
      · let i := invT t0
        have hi_val : (eJ j0 i).val = t0.val := by dsimp only [i, invT]; simp
        have hi_mem : (eJ j0 i).val ∈ T := hi_val ▸ t0.property
        apply havoid (sub z) j0 i
        ext v
        rw [hsub_j0_T z i hi_mem v, hc]
        have ht_eq : (⟨(eJ j0 i).val, hi_mem⟩ : T) = t0 := Subtype.ext hi_val
        rw [ht_eq, ht0]
        rfl
      · have hmemS : report (fun u => ask u (sub z)) j0 ∈ Sother j0 := by
          dsimp only [Sother]; rw [if_pos rfl]
          exact Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩
        let i := (eJ j0).symm ⟨report (fun u => ask u (sub z)) j0, hmemS⟩
        have hi_val : (eJ j0 i).val = report (fun u => ask u (sub z)) j0 := by dsimp only [i]; simp
        have hnotT_i : (eJ j0 i).val ∉ T := hi_val ▸ hnotT
        apply havoid (sub z) j0 i
        ext v
        rw [hsub_j0_notT z i hnotT_i v, hi_val]
    have hrep_upd : ∀ z, report (fun u => ask u (sub z)) =
        Function.update y0 j0 (report (fun u => ask u (sub z)) j0) := by
      intro z; ext j
      by_cases hj : j = j0
      · subst hj; simp
      · rw [Function.update_of_ne hj, hrep_other z j hj]
    let R0 : (T → Bool) → Bool := fun z =>
      (((mask.filter (fun bitId => ask bitId (sub z) = true)).card % 2) == 1)
    have hdeg' : Deg b (fun word => (((mask.filter (fun bitId => ask bitId word = true)).card % 2) == 1)) := by
      obtain ⟨terms, ht1, ht2⟩ := hdeg
      exact ⟨terms, ht1, fun w => by convert ht2 w⟩
    have hdegR0 : Deg b R0 := by
      have h := deg_affine_pullback hdeg' c0 slot flipB
      obtain ⟨terms, ht1, ht2⟩ := h
      exact ⟨terms, ht1, fun z => by dsimp only [R0, sub]; convert ht2 z; rename_i p; cases slot p <;> cases flipB p <;> rfl⟩
    let R : (T → Bool) → Bool := fun z => if targetVal then R0 z else !R0 z
    have hdegR : Deg b R := by
      cases htv : targetVal
      · obtain ⟨c, hsupp, he⟩ := deg_to_zmod2 hdegR0
        have hb0 : 0 ≤ b := Nat.zero_le b
        apply deg_of_sum_zmod2 (Finset.univ : Finset (Fin 2))
          (fun idx z => if idx = 0 then (1 : ZMod 2) else if R0 z then 1 else 0)
        · intro idx _
          fin_cases idx
          · obtain ⟨c1, hs1, he1⟩ := poly_const_zmod2 (V := T) 1
            exact ⟨c1, fun mon hm => le_trans (hs1 mon hm) hb0, fun z => by simpa using he1 z⟩
          · refine ⟨fun mon => if mon ∈ c then 1 else 0, ?_, fun z => ?_⟩
            · intro mon hne
              by_cases hm : mon ∈ c
              · exact hsupp mon hm
              · simp [hm] at hne
            · have hsub : ∑ x : Finset T, (if x ∈ c then (1 : ZMod 2) else 0) *
                  (if ∀ j ∈ x, z j = true then (1 : ZMod 2) else 0) =
                  ∑ x ∈ c, (if x ∈ c then (1 : ZMod 2) else 0) *
                    (if ∀ j ∈ x, z j = true then (1 : ZMod 2) else 0) := by
                symm
                apply Finset.sum_subset (Finset.subset_univ _)
                intro x _ hnot; simp [hnot]
              change (if (1 : Fin 2) = 0 then (1 : ZMod 2) else if R0 z = true then 1 else 0) = _
              simp only [one_ne_zero, ↓reduceIte]
              rw [hsub, he z]
              apply Finset.sum_congr rfl
              intro mon hm
              rw [ite_eq_left hm, one_mul]
              congr 1
        · intro z
          rw [Fin.sum_univ_two]
          simp only [R, htv, Bool.false_eq_true, ↓reduceIte]
          cases R0 z <;> decide
      · simpa [R, htv] using hdegR0
    have hR_spec : ∀ z : T → Bool, R z = true ↔ ∀ t : T, z t = true := by
      intro z
      have hR0_eq : R0 z = F (Function.update y0 j0 (report (fun u => ask u (sub z)) j0)) := by
        dsimp only [R0]
        conv_lhs => rw [← hF_eq (sub z), hrep_upd z]
      by_cases hall : ∀ t : T, z t = true
      · have hz : z = (fun _ => true) := funext hall
        subst hz
        constructor
        · intro _ _; rfl
        · intro _
          dsimp only [R]
          rw [hR0_eq, hrep_j0_all, hFcStar]
          cases targetVal <;> rfl
      · have hex : ∃ t : T, z t = false := by
          push Not at hall
          obtain ⟨t, ht⟩ := hall
          refine ⟨t, ?_⟩
          cases hz : z t
          · rfl
          · exact absurd hz ht
        have hmem := hrep_j0_not_all z hex
        have hval := hFT _ hmem
        constructor
        · intro hRt
          exfalso
          dsimp only [R] at hRt
          rw [hR0_eq, hval] at hRt
          cases targetVal <;> simp at hRt
        · intro h; exact absurd h hall
    have hlb := deg_and_lb hdegR hR_spec
    rw [Fintype.card_coe] at hlb
    exact le_trans hTcard hlb

end PEqualNP.Outside.L_lib_608_aux

theorem PEqualNP.Outside.L_lib_608 : ∀ (g a : Nat), 0 < g → 0 < a →
  let M := 2^a
  let m := M-1
  let d := g*a
  let V := Fin g × Fin m × Fin a
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → Fin M
  let valid := fun (x : W) (choice : Y) =>
    ∀ j i, ∃ v : Fin a, x (j,i,v) ≠ (choice j).val.testBit v.val
  let run := fun (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range d).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  (∃ (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
    (∀ (u : Fin d) (h : Nat),
      deg ((u.val % a+1)*2^(a-1-u.val % a)) (choose u.val h)) ∧
    ∀ input, valid input (decode (run choose input))) ∧
  (∀ (n : Nat) (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
    (∀ input, valid input (decode ((List.range n).foldl (fun trace tick =>
      trace + ((choose tick trace input).toNat <<< tick)) 0))) → d ≤ n) ∧
  ∀ (ask : Fin d → W → Bool) (report : (Fin d → Bool) → Y)
    (label : Fin g → Fin m → Fin M → Fin a → Bool),
    (∀ x j i, (fun rawBit => x (j,i,rawBit)) ≠ label j i (report (fun u => ask u x) j)) →
    ∀ (mask : Finset (Fin d)), mask.Nonempty → ∀ b : Nat,
      deg b (fun word => (((mask.filter (fun bitId => ask bitId word = true)).card % 2) == 1)) →
      2^(a-1) ≤ b :=
  PEqualNP.Outside.L_lib_608_aux.solve
