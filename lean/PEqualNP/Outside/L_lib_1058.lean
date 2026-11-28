import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1058_aux

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hval : (x.val : ZMod 2) = x := ZMod.natCast_zmod_val x
  interval_cases hv : x.val
  · left
    rw [← hval]
    rfl
  · right
    rw [← hval]
    rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma vec_add_self {q : ℕ} (v : Fin q → ZMod 2) : v + v = 0 := by
  ext k
  exact zmod2_add_self (v k)

private lemma vec_add_cancel_right {q : ℕ} (u v : Fin q → ZMod 2) : u + v + v = u := by
  rw [add_assoc, vec_add_self, add_zero]

private lemma vec_ne_add_right {q : ℕ} {a b : Fin q → ZMod 2} (hb : b ≠ 0) : a ≠ a + b := by
  intro h
  have h1 := congrArg (fun v => a + v) h
  rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h1
  exact hb h1.symm

private lemma vec_ne_add_left {q : ℕ} {a b : Fin q → ZMod 2} (ha : a ≠ 0) : b ≠ a + b := by
  rw [add_comm]
  exact vec_ne_add_right ha

private lemma vec_add_eq_zero_iff {q : ℕ} {a b : Fin q → ZMod 2} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun v => v + b) h
    rw [vec_add_cancel_right, zero_add] at h1
    exact h1
  · rintro rfl
    exact vec_add_self a

private def dotV {q : ℕ} (a z : Fin q → ZMod 2) : ZMod 2 := ∑ k, a k * z k

private lemma dotV_add_right {q : ℕ} (a z₁ z₂ : Fin q → ZMod 2) :
    dotV a (z₁ + z₂) = dotV a z₁ + dotV a z₂ := by
  simp only [dotV, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dotV_add_left {q : ℕ} (a b z : Fin q → ZMod 2) :
    dotV (a + b) z = dotV a z + dotV b z := by
  simp only [dotV, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dotV_zero_left {q : ℕ} (z : Fin q → ZMod 2) : dotV 0 z = 0 := by
  simp [dotV]

private lemma dotV_smul_right {q : ℕ} (a : Fin q → ZMod 2) (c : ZMod 2) (z : Fin q → ZMod 2) :
    dotV a (c • z) = c * dotV a z := by
  simp only [dotV, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private lemma exists_dotV_eq_one {q : ℕ} (u : Fin q → ZMod 2) (hu : u ≠ 0) :
    ∃ z : Fin q → ZMod 2, dotV u z = 1 := by
  have hex : ∃ k : Fin q, u k ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  rcases hex with ⟨k, hk⟩
  refine ⟨Pi.single k 1, ?_⟩
  simp only [dotV]
  rw [Finset.sum_eq_single k]
  · simp only [Pi.single_eq_same, mul_one]
    rcases zmod2_cases (u k) with h0 | h1
    · exact (hk h0).elim
    · exact h1
  · intro j _ hjk
    simp [Pi.single_eq_of_ne hjk]
  · intro hk'
    exact (hk' (Finset.mem_univ k)).elim

private lemma exists_dotV_zero_zero_one {q : ℕ} (a b u : Fin q → ZMod 2)
    (h0 : u ≠ 0) (ha : u ≠ a) (hb : u ≠ b) (hab : u ≠ a + b) :
    ∃ z : Fin q → ZMod 2, dotV a z = 0 ∧ dotV b z = 0 ∧ dotV u z = 1 := by
  by_contra h
  push Not at h
  have hker : ∀ z : Fin q → ZMod 2, dotV a z = 0 → dotV b z = 0 → dotV u z = 0 := by
    intro z hza hzb
    rcases zmod2_cases (dotV u z) with hu0 | hu1
    · exact hu0
    · exact (h z hza hzb hu1).elim
  let M : Matrix (Fin 3) (Fin q) (ZMod 2) := fun i k =>
    match i with
    | ⟨0, _⟩ => a k
    | ⟨1, _⟩ => b k
    | ⟨2, _⟩ => u k
  let N : Matrix (Fin 2) (Fin q) (ZMod 2) := fun i k =>
    match i with
    | ⟨0, _⟩ => a k
    | ⟨1, _⟩ => b k
  have hker_eq : LinearMap.ker (Matrix.mulVecLin M) = LinearMap.ker (Matrix.mulVecLin N) := by
    ext z
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
    constructor
    · intro hz i
      fin_cases i
      · exact hz 0
      · exact hz 1
    · intro hz i
      fin_cases i
      · exact hz 0
      · exact hz 1
      · have hza : dotV a z = 0 := hz 0
        have hzb : dotV b z = 0 := hz 1
        exact hker z hza hzb
  have hrank_eq : M.rank = N.rank := by
    have hM := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    have hN := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin N)
    rw [hker_eq] at hM
    change Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin M)) =
      Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin N))
    omega
  have hrankT : M.transpose.rank = N.transpose.rank := by
    rw [Matrix.rank_transpose, Matrix.rank_transpose, hrank_eq]
  have hle : LinearMap.range (Matrix.mulVecLin N.transpose) ≤
      LinearMap.range (Matrix.mulVecLin M.transpose) := by
    rintro v ⟨x, rfl⟩
    refine ⟨![x 0, x 1, 0], ?_⟩
    ext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    change M 0 k * x 0 + M 1 k * x 1 + M 2 k * 0 = N 0 k * x 0 + N 1 k * x 1
    simp [M, N]
  have hrange_eq : LinearMap.range (Matrix.mulVecLin N.transpose) =
      LinearMap.range (Matrix.mulVecLin M.transpose) :=
    Submodule.eq_of_le_of_finrank_eq hle hrankT.symm
  have hu_mem : u ∈ LinearMap.range (Matrix.mulVecLin M.transpose) := by
    refine ⟨![0, 0, 1], ?_⟩
    ext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    change M 0 k * 0 + M 1 k * 0 + M 2 k * 1 = u k
    simp [M]
  rw [← hrange_eq] at hu_mem
  rcases hu_mem with ⟨x, hx⟩
  have hu_eq : u = x 0 • a + x 1 • b := by
    ext k
    have hk := congrFun hx k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hk
    change N 0 k * x 0 + N 1 k * x 1 = u k at hk
    simp only [N, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [← hk]
    ring
  rcases zmod2_cases (x 0) with hx0 | hx0 <;> rcases zmod2_cases (x 1) with hx1 | hx1
  · rw [hx0, hx1, zero_smul, zero_smul, add_zero] at hu_eq
    exact h0 hu_eq
  · rw [hx0, hx1, zero_smul, one_smul, zero_add] at hu_eq
    exact hb hu_eq
  · rw [hx0, hx1, one_smul, zero_smul, add_zero] at hu_eq
    exact ha hu_eq
  · rw [hx0, hx1, one_smul, one_smul] at hu_eq
    exact hab hu_eq

private lemma exists_dotV_pair {q : ℕ} (a b : Fin q → ZMod 2)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (x y : ZMod 2) :
    ∃ z : Fin q → ZMod 2, dotV a z = x ∧ dotV b z = y := by
  rcases exists_dotV_zero_zero_one b b a ha hab hab (by rw [vec_add_self]; exact ha) with ⟨z₁, hz₁b, -, hz₁a⟩
  rcases exists_dotV_zero_zero_one a a b hb hab.symm hab.symm (by rw [vec_add_self]; exact hb) with ⟨z₂, hz₂a, -, hz₂b⟩
  refine ⟨x • z₁ + y • z₂, ?_, ?_⟩
  · rw [dotV_add_right, dotV_smul_right, dotV_smul_right, hz₁a, hz₂a]
    ring
  · rw [dotV_add_right, dotV_smul_right, dotV_smul_right, hz₁b, hz₂b]
    ring

private lemma two_mul_card_dotV_eq_one {q : ℕ} (u : Fin q → ZMod 2) (hu : u ≠ 0) :
    2 * (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 1)).card = 2 ^ q := by
  rcases exists_dotV_eq_one u hu with ⟨z₀, hz₀⟩
  have hbij : (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 0)).card =
      (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 1)).card := by
    refine Finset.card_bij (fun z _ => z + z₀) ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [dotV_add_right, hz.2, hz₀, zero_add]
    · intro z₁ _ z₂ _ h
      exact add_right_cancel h
    · intro z hz
      rw [Finset.mem_filter] at hz
      refine ⟨z + z₀, ?_, vec_add_cancel_right z z₀⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [dotV_add_right, hz.2, hz₀]
      decide
  have hsum : (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 0)).card +
      (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 1)).card = 2 ^ q := by
    rw [← Finset.card_union_of_disjoint]
    · have huniv : Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 0) ∪
          Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV u z = 1) = Finset.univ := by
        ext z
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact zmod2_cases (dotV u z)
      rw [huniv]
      simp [Fintype.card_pi]
    · rw [Finset.disjoint_left]
      intro z h0 h1
      rw [Finset.mem_filter] at h0 h1
      have : (0 : ZMod 2) = 1 := h0.2.symm.trans h1.2
      exact absurd this (by decide)
  omega

private lemma four_mul_card_dotV_pair_zero {q : ℕ} (a b : Fin q → ZMod 2)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    4 * (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV a z = 0 ∧ dotV b z = 0)).card = 2 ^ q := by
  have hfib : ∀ x y : ZMod 2,
      (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV a z = x ∧ dotV b z = y)).card =
      (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV a z = 0 ∧ dotV b z = 0)).card := by
    intro x y
    rcases exists_dotV_pair a b ha hb hab x y with ⟨z₀, hz₀a, hz₀b⟩
    symm
    refine Finset.card_bij (fun z _ => z + z₀) ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [dotV_add_right, hz.2.1, hz₀a, zero_add]
      · rw [dotV_add_right, hz.2.2, hz₀b, zero_add]
    · intro z₁ _ z₂ _ h
      exact add_right_cancel h
    · intro z hz
      rw [Finset.mem_filter] at hz
      refine ⟨z + z₀, ?_, vec_add_cancel_right z z₀⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [dotV_add_right, hz.2.1, hz₀a]
        exact zmod2_add_self x
      · rw [dotV_add_right, hz.2.2, hz₀b]
        exact zmod2_add_self y
  have htot : (2 ^ q : ℕ) = ∑ p : ZMod 2 × ZMod 2,
      (Finset.univ.filter (fun z : Fin q → ZMod 2 => dotV a z = p.1 ∧ dotV b z = p.2)).card := by
    have hcard : (Finset.univ : Finset (Fin q → ZMod 2)).card = 2 ^ q := by
      simp [Fintype.card_pi]
    rw [← hcard]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun z : Fin q → ZMod 2 => (dotV a z, dotV b z))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
  rw [htot]
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
  simp [ZMod.card]

private lemma rank_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rintro v ⟨x, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.mulVecLin A)) (LinearMap.range (Matrix.mulVecLin B))
  change Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (A + B))) ≤
    Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin A)) +
    Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin B))
  omega

private lemma rank_sum_le {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (f : α → Matrix ι ι (ZMod 2)) :
    (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (rank_add_le _ _) (Nat.add_le_add_left ih _)

private lemma range_le_of_rank_add_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (ZMod 2)) (h : (A + B).rank = A.rank + B.rank) :
    LinearMap.range (Matrix.mulVecLin A) ≤ LinearMap.range (Matrix.mulVecLin (A + B)) := by
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rintro v ⟨x, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.mulVecLin A)) (LinearMap.range (Matrix.mulVecLin B))
  have hfin : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (A + B))) =
      Module.finrank (ZMod 2)
        ↥(LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B)) := by
    have h1 := Submodule.finrank_mono hle
    change Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (A + B))) =
      Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin A)) +
      Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin B)) at h
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  rw [heq]
  exact @le_sup_left (Submodule (ZMod 2) (ι → ZMod 2)) _ _ _

private lemma rank_blockDiagonal' {l : ℕ} {s : Fin l → ℕ}
    (D : (i : Fin l) → Matrix (Fin (2 * s i)) (Fin (2 * s i)) (ZMod 2)) :
    (Matrix.blockDiagonal' D).rank = ∑ i : Fin l, (D i).rank := by
  let e : LinearMap.range (Matrix.mulVecLin (Matrix.blockDiagonal' D)) ≃ₗ[ZMod 2]
      Π i : Fin l, LinearMap.range (Matrix.mulVecLin (D i)) :=
    { toFun := fun v i => ⟨fun k => v.1 ⟨i, k⟩, by
        rcases v.2 with ⟨x, hx⟩
        refine ⟨fun k => x ⟨i, k⟩, ?_⟩
        ext k
        have hkx := congrFun hx ⟨i, k⟩
        rw [← hkx]
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.blockDiagonal'_apply]
        symm
        rw [Fintype.sum_sigma, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji.symm]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim⟩
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl
      invFun := fun f => ⟨fun p => (f p.1).1 p.2, by
        choose x hx using fun i => (f i).2
        refine ⟨fun p => x p.1 p.2, ?_⟩
        ext ⟨i, k⟩
        have hix := congrFun (hx i) k
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
          Matrix.blockDiagonal'_apply] at hix ⊢
        rw [← hix, Fintype.sum_sigma, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji.symm]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim⟩
      left_inv := fun v => by
        ext ⟨i, k⟩
        rfl
      right_inv := fun f => by
        ext i k
        rfl }
  change Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (Matrix.blockDiagonal' D))) =
    ∑ i : Fin l, Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (D i)))
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype]

private lemma rank_smul_zmod2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ZMod 2) (A : Matrix ι ι (ZMod 2)) :
    (c • A).rank = if c = 0 then 0 else A.rank := by
  rcases zmod2_cases c with rfl | rfl
  · simp
  · simp

private lemma rank_sum_eq_forces_range_le {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (s : Finset α) (f : α → Matrix ι ι (ZMod 2))
    (heq : (∑ a ∈ s, f a).rank = ∑ a ∈ s, (f a).rank) {a : α} (ha : a ∈ s) :
    LinearMap.range (Matrix.mulVecLin (f a)) ≤ LinearMap.range (Matrix.mulVecLin (∑ b ∈ s, f b)) := by
  have hsplit : ∑ b ∈ s, f b = f a + ∑ b ∈ s.erase a, f b := by
    rw [← Finset.add_sum_erase s f ha]
  have hle1 : (f a + ∑ b ∈ s.erase a, f b).rank ≤ (f a).rank + (∑ b ∈ s.erase a, f b).rank :=
    rank_add_le _ _
  have hle2 : (∑ b ∈ s.erase a, f b).rank ≤ ∑ b ∈ s.erase a, (f b).rank :=
    rank_sum_le _ _
  have hsum : ∑ b ∈ s, (f b).rank = (f a).rank + ∑ b ∈ s.erase a, (f b).rank := by
    rw [← Finset.add_sum_erase s (fun b => (f b).rank) ha]
  have hr : (f a + ∑ b ∈ s.erase a, f b).rank = (f a).rank + (∑ b ∈ s.erase a, f b).rank := by
    rw [← hsplit, heq, hsum] at hle1 ⊢
    omega
  rw [hsplit]
  exact range_le_of_rank_add_eq _ _ hr

private lemma line_inter_unique {q : ℕ} (a₁ b₁ a₂ b₂ u w : Fin q → ZMod 2)
    (hne_line : ({a₁, b₁, a₁ + b₁} : Finset (Fin q → ZMod 2)) ≠ {a₂, b₂, a₂ + b₂})
    (hu₁ : u ∈ ({a₁, b₁, a₁ + b₁} : Finset (Fin q → ZMod 2)))
    (hu₂ : u ∈ ({a₂, b₂, a₂ + b₂} : Finset (Fin q → ZMod 2)))
    (hw₁ : w ∈ ({a₁, b₁, a₁ + b₁} : Finset (Fin q → ZMod 2)))
    (hw₂ : w ∈ ({a₂, b₂, a₂ + b₂} : Finset (Fin q → ZMod 2))) :
    w = u := by
  by_contra hwu
  have htriple : ∀ (x y p r : Fin q → ZMod 2),
      p ∈ ({x, y, x + y} : Finset (Fin q → ZMod 2)) →
      r ∈ ({x, y, x + y} : Finset (Fin q → ZMod 2)) →
      r ≠ p → ({x, y, x + y} : Finset (Fin q → ZMod 2)) = {p, r, p + r} := by
    intro x y p r hp hr hrp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr
    have hxxy : x + (x + y) = y := by rw [← add_assoc, vec_add_self, zero_add]
    have hyxy : y + (x + y) = x := by rw [add_comm x y, ← add_assoc, vec_add_self, zero_add]
    have hxyx : (x + y) + x = y := by rw [add_comm x y, add_assoc, vec_add_self, add_zero]
    have hxyy : (x + y) + y = x := by rw [add_assoc, vec_add_self, add_zero]
    rcases hp with hp | hp | hp <;> rcases hr with hr | hr | hr <;> rw [hp, hr] at hrp ⊢
    all_goals try exact (hrp rfl).elim
    all_goals
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton, hxxy, hyxy, hxyx, hxyy]
      try rw [add_comm y x]
      tauto
  have h1 := htriple a₁ b₁ u w hu₁ hw₁ hwu
  have h2 := htriple a₂ b₂ u w hu₂ hw₂ hwu
  exact hne_line (h1.trans h2.symm)

end PEqualNP.Outside.L_lib_1058_aux

theorem PEqualNP.Outside.L_lib_1058 :
let F := ZMod 2
∀ (q l : ℕ) (s : Fin l → ℕ),
  let V := Fin q → F
  let I := Σ i : Fin l, Fin (2*s i)
  let M := Matrix I I F
  let dot := fun (a z : V) => ∑ k, a k * z k
  ∀ (a b : Fin l → V), (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let line := fun i : Fin l => ({a i,b i,a i+b i} : Finset V)
    Function.Injective line →
    ∀ (U W : (i : Fin l) → Matrix (Fin (2*s i)) (Fin (2*s i)) F),
      (∀ i, (U i).rank = 2*s i ∧ (W i).rank = 2*s i ∧ (U i + W i).rank = 2*s i) →
      let K := fun (z : V) =>
        Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i)
      ∀ t : ℕ, 2*t = 3*(∑ i, s i) →
        ∀ (R : Fin t → M) (c : Fin t → V), (∀ j, (R j).rank ≤ 2) →
          (∀ z : V, K z = ∑ j, dot (c j) z • R j) →
          let group := fun u : V => ∑ j ∈ Finset.univ.filter (fun j => c j = u), R j
          (∀ j, c j ≠ 0 ∧ (R j).rank = 2) ∧
            ∀ u : V, (group u).rank = 2*(Finset.univ.filter (fun j => c j = u)).card ∧
              ∃ D : (i : Fin l) → Matrix (Fin (2*s i)) (Fin (2*s i)) F,
                group u = Matrix.blockDiagonal' D ∧
                ∀ i, (D i).rank = if u ∈ line i then s i else 0 := by
  dsimp only
  intro q l s a b hab hline U W hUW t ht R c hR hK
  let F := ZMod 2
  let V := Fin q → F
  let I := Σ i : Fin l, Fin (2 * s i)
  let M := Matrix I I F
  let dot : V → V → F := PEqualNP.Outside.L_lib_1058_aux.dotV
  let line := fun i : Fin l => ({a i, b i, a i + b i} : Finset V)
  let K := fun (z : V) =>
    Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i)
  let group := fun u : V => ∑ j ∈ Finset.univ.filter (fun j => c j = u), R j
  have hK_group : ∀ z : V, K z = ∑ u : V, dot u z • group u := by
    intro z
    change Matrix.blockDiagonal' (fun i => (∑ k, a i k * z k) • U i + (∑ k, b i k * z k) • W i) = _
    rw [hK z]
    have hpart : ∑ j : Fin t, dot (c j) z • R j =
        ∑ u : V, ∑ j ∈ Finset.univ.filter (fun j => c j = u), dot (c j) z • R j := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    change ∑ j : Fin t, dot (c j) z • R j = _
    rw [hpart]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_filter] at hj
    rw [hj.2]
  have hsumK : 2 * ∑ z : V, (K z).rank = 3 * 2 ^ q * ∑ i : Fin l, s i := by
    have hKz : ∀ z : V, (K z).rank =
        ∑ i : Fin l, (if dot (a i) z = 0 ∧ dot (b i) z = 0 then 0 else 2 * s i) := by
      intro z
      rw [PEqualNP.Outside.L_lib_1058_aux.rank_blockDiagonal']
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases PEqualNP.Outside.L_lib_1058_aux.zmod2_cases (dot (a i) z) with ha0 | ha1 <;>
        rcases PEqualNP.Outside.L_lib_1058_aux.zmod2_cases (dot (b i) z) with hb0 | hb1
      · simp [ha0, hb0]
      · simp [ha0, hb1, (hUW i).2.1]
      · simp [ha1, hb0, (hUW i).1]
      · simp [ha1, hb1, (hUW i).2.2]
    simp_rw [hKz]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcard_all : (Finset.univ : Finset V).card = 2 ^ q := by
      simp [V, F, Fintype.card_pi]
    have h4 := PEqualNP.Outside.L_lib_1058_aux.four_mul_card_dotV_pair_zero
      (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
    have hsum_i : ∑ z : V, (if dot (a i) z = 0 ∧ dot (b i) z = 0 then 0 else 2 * s i) =
        (Finset.univ.filter (fun z : V => ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0))).card * (2 * s i) := by
      have hf : ∀ z : V, (if dot (a i) z = 0 ∧ dot (b i) z = 0 then 0 else 2 * s i) =
          (if ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0) then 2 * s i else 0) := fun z => by
        by_cases h : dot (a i) z = 0 ∧ dot (b i) z = 0 <;> simp [h]
      simp_rw [hf]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hcomp : (Finset.univ.filter (fun z : V => dot (a i) z = 0 ∧ dot (b i) z = 0)).card +
        (Finset.univ.filter (fun z : V => ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0))).card = 2 ^ q := by
      rw [← Finset.card_union_of_disjoint]
      · have huniv : Finset.univ.filter (fun z : V => dot (a i) z = 0 ∧ dot (b i) z = 0) ∪
            Finset.univ.filter (fun z : V => ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0)) = Finset.univ := by
          ext z
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact em _
        rw [huniv, hcard_all]
      · rw [Finset.disjoint_left]
        intro z h1 h2
        rw [Finset.mem_filter] at h1 h2
        exact h2.2 h1.2
    rw [hsum_i]
    have h4' : 4 * (Finset.univ.filter (fun z : V => dot (a i) z = 0 ∧ dot (b i) z = 0)).card = 2 ^ q := h4
    have h3 : 4 * (Finset.univ.filter (fun z : V => ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0))).card = 3 * 2 ^ q := by
      omega
    have hmul : 2 * ((Finset.univ.filter (fun z : V => ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0))).card * (2 * s i)) =
        (4 * (Finset.univ.filter (fun z : V => ¬ (dot (a i) z = 0 ∧ dot (b i) z = 0))).card) * s i := by
      ring
    rw [hmul, h3]
  have hle_z : ∀ z : V, (K z).rank ≤ ∑ u : V, (if dot u z = 0 then 0 else (group u).rank) := by
    intro z
    rw [hK_group z]
    refine le_trans (PEqualNP.Outside.L_lib_1058_aux.rank_sum_le _ _) ?_
    refine Finset.sum_le_sum fun u _ => ?_
    rw [PEqualNP.Outside.L_lib_1058_aux.rank_smul_zmod2]
  have hle_u : ∀ u : V, (group u).rank ≤ ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank :=
    fun u => PEqualNP.Outside.L_lib_1058_aux.rank_sum_le _ _
  have hle_R : ∀ u : V, ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank ≤
      2 * (Finset.univ.filter (fun j => c j = u)).card := by
    intro u
    calc
      ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank
        ≤ ∑ _j ∈ Finset.univ.filter (fun j => c j = u), 2 := Finset.sum_le_sum fun j _ => hR j
      _ = 2 * (Finset.univ.filter (fun j => c j = u)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum_u_le : 2 * ∑ z : V, ∑ u : V, (if dot u z = 0 then 0 else (group u).rank) =
      2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0), (group u).rank := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    have hsplit : ∑ u : V, 2 * ∑ z : V, (if dot u z = 0 then 0 else (group u).rank) =
        ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * ∑ z : V, (if dot u z = 0 then 0 else (group u).rank) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_
      rw [Finset.mem_filter] at hu
      have hu0 : u = 0 := by
        by_contra hne
        exact hu ⟨Finset.mem_univ u, hne⟩
      subst hu0
      have hdot0 : ∀ z : V, dot 0 z = 0 := PEqualNP.Outside.L_lib_1058_aux.dotV_zero_left
      simp [hdot0]
    rw [hsplit]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_filter] at hu
    have h2u := PEqualNP.Outside.L_lib_1058_aux.two_mul_card_dotV_eq_one u hu.2
    have hsu : ∑ z : V, (if dot u z = 0 then 0 else (group u).rank) =
        (Finset.univ.filter (fun z : V => dot u z = 1)).card * (group u).rank := by
      have hf : ∀ z : V, (if dot u z = 0 then 0 else (group u).rank) =
          (if dot u z = 1 then (group u).rank else 0) := by
        intro z
        rcases PEqualNP.Outside.L_lib_1058_aux.zmod2_cases (dot u z) with h0 | h1
        · simp [h0]
        · simp [h1]
      simp_rw [hf]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [hsu, ← mul_assoc, h2u]
  have hchain1 : 2 * ∑ z : V, (K z).rank ≤
      2 * ∑ z : V, ∑ u : V, (if dot u z = 0 then 0 else (group u).rank) :=
    Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun z _ => hle_z z)
  have hchain2 : ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0), (group u).rank ≤
      ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
        ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank :=
    Finset.sum_le_sum fun u _ => hle_u u
  have hchain3 : ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
        ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank ≤
      ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
        2 * (Finset.univ.filter (fun j => c j = u)).card :=
    Finset.sum_le_sum fun u _ => hle_R u
  have hchain4 : ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
        2 * (Finset.univ.filter (fun j => c j = u)).card ≤
      ∑ u : V, 2 * (Finset.univ.filter (fun j => c j = u)).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have htot_cards : ∑ u : V, 2 * (Finset.univ.filter (fun j => c j = u)).card = 2 * t := by
    rw [← Finset.mul_sum]
    congr 1
    have := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simpa using this.symm
  have h2q_pos : 0 < 2 ^ q := Nat.pos_of_ne_zero (by positivity)
  have hall_eq :
      2 * ∑ z : V, (K z).rank =
        2 * ∑ z : V, ∑ u : V, (if dot u z = 0 then 0 else (group u).rank) ∧
      ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0), (group u).rank =
        ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank ∧
      ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank =
        ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * (Finset.univ.filter (fun j => c j = u)).card ∧
      ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * (Finset.univ.filter (fun j => c j = u)).card = 2 * t := by
    have htop : 2 ^ q * (2 * t) = 3 * 2 ^ q * ∑ i : Fin l, s i := by
      rw [ht]
      ring
    have h1 : 2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0), (group u).rank ≤
        2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank :=
      Nat.mul_le_mul_left _ hchain2
    have h2 : 2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank ≤
        2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * (Finset.univ.filter (fun j => c j = u)).card :=
      Nat.mul_le_mul_left _ hchain3
    have h3 : 2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * (Finset.univ.filter (fun j => c j = u)).card ≤ 2 ^ q * (2 * t) := by
      rw [← htot_cards]
      exact Nat.mul_le_mul_left _ hchain4
    rw [hsumK] at hchain1
    rw [hsum_u_le] at hchain1
    have he1 : 3 * 2 ^ q * ∑ i : Fin l, s i =
        2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0), (group u).rank := by omega
    have he2 : 2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0), (group u).rank =
        2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank := by omega
    have he3 : 2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank =
        2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * (Finset.univ.filter (fun j => c j = u)).card := by omega
    have he4 : 2 ^ q * ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
          2 * (Finset.univ.filter (fun j => c j = u)).card = 2 ^ q * (2 * t) := by omega
    refine ⟨?_, Nat.eq_of_mul_eq_mul_left h2q_pos he2,
      Nat.eq_of_mul_eq_mul_left h2q_pos he3, Nat.eq_of_mul_eq_mul_left h2q_pos he4⟩
    rw [hsumK, hsum_u_le]
    exact he1
  have hc_ne_zero : ∀ j : Fin t, c j ≠ 0 := by
    have hzero_card : (Finset.univ.filter (fun j : Fin t => c j = 0)).card = 0 := by
      have hsplit : ∑ u : V, 2 * (Finset.univ.filter (fun j => c j = u)).card =
          2 * (Finset.univ.filter (fun j => c j = 0)).card +
          ∑ u ∈ Finset.univ.filter (fun u : V => u ≠ 0),
            2 * (Finset.univ.filter (fun j => c j = u)).card := by
        have hfilt : Finset.univ.filter (fun u : V => u ≠ 0) = Finset.univ.erase 0 := by
          ext u
          simp
        rw [hfilt]
        exact (Finset.add_sum_erase Finset.univ
          (fun u => 2 * (Finset.univ.filter (fun j => c j = u)).card) (Finset.mem_univ (0 : V))).symm
      rw [htot_cards, hall_eq.2.2.2] at hsplit
      omega
    intro j hj
    have hmem : j ∈ Finset.univ.filter (fun j : Fin t => c j = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hpos := Finset.card_pos.mpr ⟨j, hmem⟩
    omega
  have hgroup_eq_sumR : ∀ u : V, (group u).rank =
      ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank := by
    intro u
    by_cases hu : u = 0
    · subst hu
      have hempty : Finset.univ.filter (fun j : Fin t => c j = 0) = ∅ := by
        ext j
        simp [hc_ne_zero j]
      simp [group, hempty]
    · have hu_mem : u ∈ Finset.univ.filter (fun u : V => u ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
      exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hle_u v)).mp hall_eq.2.1 u hu_mem
  have hsumR_eq_2card : ∀ u : V, ∑ j ∈ Finset.univ.filter (fun j => c j = u), (R j).rank =
      2 * (Finset.univ.filter (fun j => c j = u)).card := by
    intro u
    by_cases hu : u = 0
    · subst hu
      have hempty : Finset.univ.filter (fun j : Fin t => c j = 0) = ∅ := by
        ext j
        simp [hc_ne_zero j]
      simp [hempty]
    · have hu_mem : u ∈ Finset.univ.filter (fun u : V => u ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
      exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hle_R v)).mp hall_eq.2.2.1 u hu_mem
  have hR_eq_2 : ∀ j : Fin t, (R j).rank = 2 := by
    intro j
    have hu := hsumR_eq_2card (c j)
    have hsum2 : ∑ k ∈ Finset.univ.filter (fun k => c k = c j), (R k).rank =
        ∑ _k ∈ Finset.univ.filter (fun k => c k = c j), 2 := by
      rw [hu, Finset.sum_const, smul_eq_mul, mul_comm]
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hR k)).mp hsum2 j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)
  have hgroup_rank : ∀ u : V, (group u).rank = 2 * (Finset.univ.filter (fun j => c j = u)).card :=
    fun u => (hgroup_eq_sumR u).trans (hsumR_eq_2card u)
  have hKz_tight : ∀ z : V, (K z).rank = ∑ u : V, (dot u z • group u).rank := by
    intro z
    have h1 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hall_eq.1
    have h2 := (Finset.sum_eq_sum_iff_of_le (fun z' _ => hle_z z')).mp h1 z (Finset.mem_univ z)
    rw [h2]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [PEqualNP.Outside.L_lib_1058_aux.rank_smul_zmod2]
  have hzero_outside : ∀ (u : V) (i : Fin l), u ∉ line i →
      (∀ (x : Fin (2 * s i)) (p : I), group u ⟨i, x⟩ p = 0) ∧
      (∀ (p : I) (y : Fin (2 * s i)), group u p ⟨i, y⟩ = 0) := by
    intro u i hui
    by_cases hu0 : u = 0
    · subst hu0
      have hempty : Finset.univ.filter (fun j : Fin t => c j = 0) = ∅ := by
        ext j
        simp [hc_ne_zero j]
      simp [group, hempty]
    · have hua : u ≠ a i := fun h => hui (by simp [line, h])
      have hub : u ≠ b i := fun h => hui (by simp [line, h])
      have huab : u ≠ a i + b i := fun h => hui (by simp [line, h])
      rcases PEqualNP.Outside.L_lib_1058_aux.exists_dotV_zero_zero_one (a i) (b i) u
        hu0 hua hub huab with ⟨z, hza, hzb, hzu⟩
      have hzu' : dot u z = 1 := hzu
      have hKz_eq := hK_group z
      have htight := hKz_tight z
      rw [hKz_eq] at htight
      have hrange : LinearMap.range (Matrix.mulVecLin (group u)) ≤
          LinearMap.range (Matrix.mulVecLin (K z)) := by
        rw [hKz_eq]
        have hsub := PEqualNP.Outside.L_lib_1058_aux.rank_sum_eq_forces_range_le
          Finset.univ (fun w => dot w z • group w) htight (Finset.mem_univ u)
        rw [hzu', one_smul] at hsub
        exact hsub
      have htightT : (∑ w : V, (dot w z • group w).transpose).rank =
          ∑ w : V, (dot w z • group w).transpose.rank := by
        rw [← Matrix.transpose_sum, Matrix.rank_transpose]
        simp_rw [Matrix.rank_transpose]
        exact htight
      have hrangeT : LinearMap.range (Matrix.mulVecLin (group u).transpose) ≤
          LinearMap.range (Matrix.mulVecLin (K z).transpose) := by
        have hsumT : (K z).transpose = ∑ w : V, (dot w z • group w).transpose := by
          rw [hKz_eq, Matrix.transpose_sum]
        rw [hsumT]
        have hsub := PEqualNP.Outside.L_lib_1058_aux.rank_sum_eq_forces_range_le
          Finset.univ (fun w => (dot w z • group w).transpose) htightT (Finset.mem_univ u)
        rw [hzu', one_smul] at hsub
        exact hsub
      constructor
      · intro x p
        have hmem : (group u).mulVec (Pi.single p 1) ∈ LinearMap.range (Matrix.mulVecLin (K z)) :=
          hrange (LinearMap.mem_range_self _ (Pi.single p 1))
        rcases hmem with ⟨v, hv⟩
        have hvx := congrFun hv ⟨i, x⟩
        have hleft : (K z).mulVec v ⟨i, x⟩ = 0 := by
          simp only [K, Matrix.mulVec, dotProduct, Matrix.blockDiagonal'_apply]
          refine Finset.sum_eq_zero fun r _ => ?_
          rcases r with ⟨r₁, r₂⟩
          dsimp only
          split_ifs with hri
          · cases hri
            change (PEqualNP.Outside.L_lib_1058_aux.dotV (a i) z • U i +
              PEqualNP.Outside.L_lib_1058_aux.dotV (b i) z • W i) x _ * v _ = 0
            rw [hza, hzb]
            simp
          · simp
        have hright : (group u).mulVec (Pi.single p 1) ⟨i, x⟩ = group u ⟨i, x⟩ p := by
          simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single p]
          · simp
          · intro q _ hqp
            simp [Pi.single_eq_of_ne hqp]
          · intro hp
            exact (hp (Finset.mem_univ p)).elim
        rw [Matrix.mulVecLin_apply] at hvx
        rw [← hright, ← hvx, hleft]
      · intro p y
        have hmem : (group u).transpose.mulVec (Pi.single p 1) ∈
            LinearMap.range (Matrix.mulVecLin (K z).transpose) :=
          hrangeT (LinearMap.mem_range_self _ (Pi.single p 1))
        rcases hmem with ⟨v, hv⟩
        have hvy := congrFun hv ⟨i, y⟩
        have hleft : (K z).transpose.mulVec v ⟨i, y⟩ = 0 := by
          simp only [K, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.blockDiagonal'_apply]
          refine Finset.sum_eq_zero fun r _ => ?_
          rcases r with ⟨r₁, r₂⟩
          dsimp only
          split_ifs with hri
          · cases hri
            change (PEqualNP.Outside.L_lib_1058_aux.dotV (a i) z • U i +
              PEqualNP.Outside.L_lib_1058_aux.dotV (b i) z • W i) _ _ * v _ = 0
            rw [hza, hzb]
            simp
          · simp
        have hright : (group u).transpose.mulVec (Pi.single p 1) ⟨i, y⟩ = group u p ⟨i, y⟩ := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          rw [Finset.sum_eq_single p]
          · simp
          · intro q _ hqp
            simp [Pi.single_eq_of_ne hqp]
          · intro hp
            exact (hp (Finset.mem_univ p)).elim
        rw [Matrix.mulVecLin_apply] at hvy
        rw [← hright, ← hvy, hleft]
  have hoff_diag : ∀ (u : V) (i₁ i₂ : Fin l), i₁ ≠ i₂ →
      ∀ (x : Fin (2 * s i₁)) (y : Fin (2 * s i₂)), group u ⟨i₁, x⟩ ⟨i₂, y⟩ = 0 := by
    intro u i₁ i₂ hne x y
    by_cases h1 : u ∈ line i₁
    · by_cases h2 : u ∈ line i₂
      · have hu0 : u ≠ 0 := by
          intro h0
          subst h0
          simp only [line, Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with h | h | h
          · exact (hab i₁).1 h.symm
          · exact (hab i₁).2.1 h.symm
          · exact (hab i₁).2.2 (PEqualNP.Outside.L_lib_1058_aux.vec_add_eq_zero_iff.mp h.symm)
        rcases PEqualNP.Outside.L_lib_1058_aux.exists_dotV_eq_one u hu0 with ⟨z, hzu⟩
        have hzu' : dot u z = 1 := hzu
        have hKz := congrFun (congrFun (hK_group z) ⟨i₁, x⟩) ⟨i₂, y⟩
        have hleft : K z ⟨i₁, x⟩ ⟨i₂, y⟩ = 0 := by
          simp [K, Matrix.blockDiagonal'_apply, hne]
        rw [hleft] at hKz
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hKz
        rw [Finset.sum_eq_single u] at hKz
        · rw [hzu', one_mul] at hKz
          exact hKz.symm
        · intro w _ hwu
          have hnot : ¬ (w ∈ line i₁ ∧ w ∈ line i₂) := by
            intro ⟨hw1, hw2⟩
            exact hwu (PEqualNP.Outside.L_lib_1058_aux.line_inter_unique
              (a i₁) (b i₁) (a i₂) (b i₂) u w
              (fun heq => hne (hline heq)) h1 h2 hw1 hw2)
          by_cases hw1 : w ∈ line i₁
          · have hw2 : w ∉ line i₂ := fun h => hnot ⟨hw1, h⟩
            rw [(hzero_outside w i₂ hw2).2 ⟨i₁, x⟩ y, mul_zero]
          · rw [(hzero_outside w i₁ hw1).1 x ⟨i₂, y⟩, mul_zero]
        · intro hu'
          exact (hu' (Finset.mem_univ u)).elim
      · exact (hzero_outside u i₂ h2).2 ⟨i₁, x⟩ y
    · exact (hzero_outside u i₁ h1).1 x ⟨i₂, y⟩
  let D : V → (i : Fin l) → Matrix (Fin (2 * s i)) (Fin (2 * s i)) F :=
    fun u i x y => group u ⟨i, x⟩ ⟨i, y⟩
  have hgroup_bd : ∀ u : V, group u = Matrix.blockDiagonal' (D u) := by
    intro u
    ext ⟨i₁, x⟩ ⟨i₂, y⟩
    by_cases h : i₁ = i₂
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq]
    · simp [Matrix.blockDiagonal'_apply, h, hoff_diag u i₁ i₂ h x y]
  have hD_zero : ∀ (u : V) (i : Fin l), u ∉ line i → D u i = 0 := by
    intro u i hui
    ext x y
    exact (hzero_outside u i hui).1 x ⟨i, y⟩
  have hD_rank_tri : ∀ i : Fin l,
      2 * s i ≤ (D (a i) i).rank + (D (a i + b i) i).rank ∧
      2 * s i ≤ (D (b i) i).rank + (D (a i + b i) i).rank ∧
      2 * s i ≤ (D (a i) i).rank + (D (b i) i).rank := by
    intro i
    have hblock : ∀ z : V, dot (a i) z • U i + dot (b i) z • W i =
        dot (a i) z • D (a i) i + dot (b i) z • D (b i) i +
        dot (a i + b i) z • D (a i + b i) i := by
      intro z
      ext x y
      have hKz := congrFun (congrFun (hK_group z) ⟨i, x⟩) ⟨i, y⟩
      simp only [K, Matrix.blockDiagonal'_apply_eq, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul] at hKz
      rw [hKz]
      have hsub : ∑ u : V, dot u z * group u ⟨i, x⟩ ⟨i, y⟩ =
          ∑ u ∈ line i, dot u z * D u i x y := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun u _ hui => ?_
        rw [hD_zero u i hui]
        simp
      rw [hsub]
      have hne1 : a i ≠ b i := (hab i).2.2
      have hne2 : a i ≠ a i + b i := PEqualNP.Outside.L_lib_1058_aux.vec_ne_add_right (hab i).2.1
      have hne3 : b i ≠ a i + b i := PEqualNP.Outside.L_lib_1058_aux.vec_ne_add_left (hab i).1
      have hnot1 : a i ∉ ({b i, a i + b i} : Finset V) := by simp [hne1, hne2]
      have hnot2 : b i ∉ ({a i + b i} : Finset V) := by simp [hne3]
      change ∑ u ∈ ({a i, b i, a i + b i} : Finset V), dot u z * D u i x y = _
      rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_singleton]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rcases PEqualNP.Outside.L_lib_1058_aux.exists_dotV_pair (a i) (b i)
        (hab i).1 (hab i).2.1 (hab i).2.2 1 0 with ⟨z, hza, hzb⟩
      have hza' : dot (a i) z = 1 := hza
      have hzb' : dot (b i) z = 0 := hzb
      have hz := hblock z
      have hzab : dot (a i + b i) z = 1 := by
        change PEqualNP.Outside.L_lib_1058_aux.dotV (a i + b i) z = 1
        rw [PEqualNP.Outside.L_lib_1058_aux.dotV_add_left, hza, hzb, add_zero]
      rw [hza', hzb', hzab] at hz
      simp only [one_smul, zero_smul, add_zero] at hz
      calc
        2 * s i = (U i).rank := (hUW i).1.symm
        _ = (D (a i) i + D (a i + b i) i).rank := congrArg Matrix.rank hz
        _ ≤ (D (a i) i).rank + (D (a i + b i) i).rank :=
          PEqualNP.Outside.L_lib_1058_aux.rank_add_le _ _
    · rcases PEqualNP.Outside.L_lib_1058_aux.exists_dotV_pair (a i) (b i)
        (hab i).1 (hab i).2.1 (hab i).2.2 0 1 with ⟨z, hza, hzb⟩
      have hza' : dot (a i) z = 0 := hza
      have hzb' : dot (b i) z = 1 := hzb
      have hz := hblock z
      have hzab : dot (a i + b i) z = 1 := by
        change PEqualNP.Outside.L_lib_1058_aux.dotV (a i + b i) z = 1
        rw [PEqualNP.Outside.L_lib_1058_aux.dotV_add_left, hza, hzb, zero_add]
      rw [hza', hzb', hzab] at hz
      simp only [one_smul, zero_smul, zero_add] at hz
      calc
        2 * s i = (W i).rank := (hUW i).2.1.symm
        _ = (D (b i) i + D (a i + b i) i).rank := congrArg Matrix.rank hz
        _ ≤ (D (b i) i).rank + (D (a i + b i) i).rank :=
          PEqualNP.Outside.L_lib_1058_aux.rank_add_le _ _
    · rcases PEqualNP.Outside.L_lib_1058_aux.exists_dotV_pair (a i) (b i)
        (hab i).1 (hab i).2.1 (hab i).2.2 1 1 with ⟨z, hza, hzb⟩
      have hza' : dot (a i) z = 1 := hza
      have hzb' : dot (b i) z = 1 := hzb
      have hz := hblock z
      have hzab : dot (a i + b i) z = 0 := by
        change PEqualNP.Outside.L_lib_1058_aux.dotV (a i + b i) z = 0
        rw [PEqualNP.Outside.L_lib_1058_aux.dotV_add_left, hza, hzb]
        decide
      rw [hza', hzb', hzab] at hz
      simp only [one_smul, zero_smul, add_zero] at hz
      calc
        2 * s i = (U i + W i).rank := (hUW i).2.2.symm
        _ = (D (a i) i + D (b i) i).rank := congrArg Matrix.rank hz
        _ ≤ (D (a i) i).rank + (D (b i) i).rank :=
          PEqualNP.Outside.L_lib_1058_aux.rank_add_le _ _
  have hsum_D_le : ∀ i : Fin l, 3 * s i ≤ ∑ u ∈ line i, (D u i).rank := by
    intro i
    have hne1 : a i ≠ b i := (hab i).2.2
    have hne2 : a i ≠ a i + b i := PEqualNP.Outside.L_lib_1058_aux.vec_ne_add_right (hab i).2.1
    have hne3 : b i ≠ a i + b i := PEqualNP.Outside.L_lib_1058_aux.vec_ne_add_left (hab i).1
    have hnot1 : a i ∉ ({b i, a i + b i} : Finset V) := by simp [hne1, hne2]
    have hnot2 : b i ∉ ({a i + b i} : Finset V) := by simp [hne3]
    have hsum_line : ∑ u ∈ line i, (D u i).rank =
        (D (a i) i).rank + (D (b i) i).rank + (D (a i + b i) i).rank := by
      change ∑ u ∈ ({a i, b i, a i + b i} : Finset V), (D u i).rank = _
      rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_singleton]
      omega
    rw [hsum_line]
    have htri := hD_rank_tri i
    omega
  have hsum_total_D : ∑ i : Fin l, ∑ u ∈ line i, (D u i).rank = 3 * ∑ i : Fin l, s i := by
    have h1 : ∑ i : Fin l, ∑ u ∈ line i, (D u i).rank = ∑ i : Fin l, ∑ u : V, (D u i).rank := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_subset (Finset.subset_univ _) fun u _ hui => ?_
      rw [hD_zero u i hui]
      simp
    rw [h1, Finset.sum_comm]
    have h2 : ∑ u : V, ∑ i : Fin l, (D u i).rank = ∑ u : V, (group u).rank := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hgroup_bd u, PEqualNP.Outside.L_lib_1058_aux.rank_blockDiagonal']
    rw [h2]
    simp_rw [hgroup_rank]
    rw [htot_cards, ht]
  have hsum_D_eq : ∀ i : Fin l, ∑ u ∈ line i, (D u i).rank = 3 * s i := by
    intro i
    have htot : ∑ i : Fin l, 3 * s i = ∑ i : Fin l, ∑ u ∈ line i, (D u i).rank := by
      rw [← Finset.mul_sum, hsum_total_D]
    exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hsum_D_le j)).mp htot i (Finset.mem_univ i)).symm
  refine ⟨fun j => ⟨hc_ne_zero j, hR_eq_2 j⟩, fun u => ⟨hgroup_rank u, D u, hgroup_bd u, fun i => ?_⟩⟩
  split_ifs with hui
  · have hne1 : a i ≠ b i := (hab i).2.2
    have hne2 : a i ≠ a i + b i := PEqualNP.Outside.L_lib_1058_aux.vec_ne_add_right (hab i).2.1
    have hne3 : b i ≠ a i + b i := PEqualNP.Outside.L_lib_1058_aux.vec_ne_add_left (hab i).1
    have hnot1 : a i ∉ ({b i, a i + b i} : Finset V) := by simp [hne1, hne2]
    have hnot2 : b i ∉ ({a i + b i} : Finset V) := by simp [hne3]
    have hsum_line : (D (a i) i).rank + (D (b i) i).rank + (D (a i + b i) i).rank = 3 * s i := by
      have := hsum_D_eq i
      change ∑ u ∈ ({a i, b i, a i + b i} : Finset V), (D u i).rank = 3 * s i at this
      rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_singleton] at this
      omega
    have htri := hD_rank_tri i
    simp only [line, Finset.mem_insert, Finset.mem_singleton] at hui
    rcases hui with rfl | rfl | rfl <;> omega
  · rw [hD_zero u i hui]
    simp
