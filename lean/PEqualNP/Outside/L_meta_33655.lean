import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PEqualNP.Defs

open Module

namespace PEqualNP.Outside.L_meta_33655_aux.Rank

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def inversePair (D : LinearMap.BilinForm K V) (A G : V →ₗ[K] V) :
    LinearMap.BilinForm K A.range :=
  (D.compLeft G).restrict A.range

def nullOnImage (A M : V →ₗ[K] V) : Submodule K A.range :=
  M.ker.comap A.range.subtype

def lifted (A M : V →ₗ[K] V) : V →ₗ[K] A.range :=
  (A.comp M).codRestrict A.range (fun x => ⟨M x, rfl⟩)

theorem inversePair_symm (D : LinearMap.BilinForm K V) (A G : V →ₗ[K] V)
    (hs : D.IsSymm) (hA : ∀ x y, D (A x) y = D x (A y))
    (hAG : ∀ x : A.range, A (G x) = x) :
    (inversePair D A G).IsSymm := by
  constructor
  intro x y
  change D (G x) y = D (G y) x
  calc
    D (G x) y = D (G x) (A (G y)) := by rw [hAG]
    _ = D (A (G x)) (G y) := (hA _ _).symm
    _ = D x (G y) := by rw [hAG]
    _ = D (G y) x := hs.eq _ _

theorem inversePair_nondegenerate (D : LinearMap.BilinForm K V) (A G : V →ₗ[K] V)
    (hD : D.Nondegenerate) (hs : D.IsSymm) (hA : ∀ x y, D (A x) y = D x (A y))
    (hAG : ∀ x : A.range, A (G x) = x) :
    (inversePair D A G).Nondegenerate := by
  have hl : ∀ x : A.range, (∀ y : A.range, inversePair D A G x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    simp only [Submodule.coe_zero]
    apply hD.1
    intro y
    have v := hx ⟨A y, ⟨y, rfl⟩⟩
    change D (G x) (A y) = 0 at v
    rw [← hA, hAG] at v
    exact v
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl
  intro y
  rw [(inversePair_symm D A G hs hA hAG).eq x y]
  exact hx y

theorem inversePair_lifted (D : LinearMap.BilinForm K V) (A G M : V →ₗ[K] V)
    (hs : D.IsSymm) (hA : ∀ x y, D (A x) y = D x (A y))
    (hM : ∀ x y, D (M x) y = D x (M y))
    (hAG : ∀ x : A.range, A (G x) = x) (x : V) (y : A.range) :
    inversePair D A G (lifted A M x) y = D x (M y) := by
  rw [(inversePair_symm D A G hs hA hAG).eq (lifted A M x) y]
  change D (G y) (A (M x)) = D x (M y)
  rw [← hA, hAG, hs.eq y (M x), hM]

theorem rank_restriction [FiniteDimensional K V]
    (D : LinearMap.BilinForm K V) (A G M : V →ₗ[K] V)
    (hD : D.Nondegenerate) (hs : D.IsSymm)
    (hA : ∀ x y, D (A x) y = D x (A y))
    (hM : ∀ x y, D (M x) y = D x (M y))
    (hAG : ∀ x : A.range, A (G x) = x) :
    finrank K (M.comp (A.comp M)).range + finrank K (nullOnImage A M) +
      finrank K (nullOnImage A M ⊓ (inversePair D A G).orthogonal (nullOnImage A M) : Submodule K A.range) =
      finrank K A.range := by
  let B := inversePair D A G
  let f := lifted A M
  let P := f.range
  let T := nullOnImage A M
  have hO : B.orthogonal P = T := by
    ext y
    change (∀ z ∈ f.range, B z y = 0) ↔ M (y : V) = 0
    constructor
    · intro h
      apply hD.2
      intro x
      have eq := h (f x) ⟨x, rfl⟩
      rw [inversePair_lifted D A G M hs hA hM hAG] at eq
      exact eq
    · intro hy z hz
      obtain ⟨x, rfl⟩ := hz
      rw [inversePair_lifted D A G M hs hA hM hAG, hy, map_zero]
  have hNon := inversePair_nondegenerate D A G hD hs hA hAG
  have hRefl := (inversePair_symm D A G hs hA hAG).isRefl
  have hdim := B.finrank_add_finrank_orthogonal hRefl P
  rw [B.orthogonal_top_eq_bot hNon, inf_bot_eq, finrank_bot, add_zero, hO] at hdim
  have hP : B.orthogonal T = P := by
    rw [← hO, B.orthogonal_orthogonal hNon hRefl]
  let g : P →ₗ[K] V := M.comp (A.range.subtype.comp P.subtype)
  have hgRange : g.range = (M.comp (A.comp M)).range := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨v, rfl⟩ := hx
      exact ⟨v, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨f x, ⟨x, rfl⟩⟩, rfl⟩
  have hgKer : g.ker = (T ⊓ P).comap P.subtype := by
    ext ⟨x, hx⟩
    change M (x : V) = 0 ↔ M (x : V) = 0 ∧ x ∈ P
    exact ⟨fun h => ⟨h, hx⟩, And.left⟩
  have hkerDim : finrank K g.ker = finrank K (T ⊓ P : Submodule K A.range) := by
    rw [hgKer]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_right : T ⊓ P ≤ P)).finrank_eq
  have hgn := g.finrank_range_add_finrank_ker
  rw [hgRange, hkerDim] at hgn
  change _ + finrank K T + finrank K (T ⊓ B.orthogonal T : Submodule K A.range) = _
  rw [hP]
  omega
end

end PEqualNP.Outside.L_meta_33655_aux.Rank

open Module BigOperators


namespace PEqualNP.Outside.L_meta_33655_aux.Chart

universe u

abbrev F := ZMod 2
abbrev Coord (p r : ℕ) := (Fin p → F × F) × (Fin r → F)

def cross (x y : F × F) : F := x.1 * y.2 + x.2 * y.1

def zeroChart (r : ℕ) : (Fin r → F) ≃ₗ[F] Coord 0 r where
  toFun x := (0, x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := Prod.ext (Subsingleton.elim _ _) rfl
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def prepend (p r : ℕ) : ((F × F) × Coord p r) ≃ₗ[F] Coord (p+1) r where
  toFun x := (Fin.cons x.1 x.2.1, x.2.2)
  invFun x := (x.1 0, (fun i => x.1 i.succ, x.2))
  left_inv x := by
    refine Prod.ext (by simp) (Prod.ext ?_ rfl)
    funext i
    simp
  right_inv x := by
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_add' x y := by
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  map_smul' a x := by
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl

section
variable {V : Type u} [AddCommGroup V] [Module F V]

theorem symm_of_alt (B : LinearMap.BilinForm F V) (h : B.IsAlt) :
    B.IsSymm := by
  constructor
  intro x y
  have h1 := h (x + y)
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right, h x, h y, zero_add, add_zero] at h1
  exact (eq_neg_of_add_eq_zero_left h1).trans (ZMod.neg_eq_self_mod_two _)

def projection (B : LinearMap.BilinForm F V) (u v : V) : V →ₗ[F] F × F :=
  (B.flip v).prod (B.flip u)

def plane (u v : V) : (F × F) →ₗ[F] V :=
  (LinearMap.fst F F F).smulRight u + (LinearMap.snd F F F).smulRight v

theorem projection_plane (B : LinearMap.BilinForm F V) (h : B.IsAlt)
    {u v : V} (huv : B u v = 1) (a : F × F) :
    projection B u v (plane u v a) = a := by
  have hvu : B v u = 1 := (symm_of_alt B h).eq v u ▸ huv
  change (B (a.1 • u + a.2 • v) v, B (a.1 • u + a.2 • v) u) = a
  simp [h u, h v, huv, hvu]

def splitPlane (B : LinearMap.BilinForm F V) (h : B.IsAlt)
    {u v : V} (huv : B u v = 1) : V ≃ₗ[F] (F × F) × (projection B u v).ker := by
  let π := projection B u v
  let P := plane u v
  have hp (a : F × F) : π (P a) = a := projection_plane B h huv a
  let rem := (LinearMap.id - P.comp π).codRestrict π.ker (fun x => by
    change π (x - P (π x)) = 0
    rw [map_sub, hp, sub_self])
  let f := π.prod rem
  let j := (P.comp (LinearMap.fst F (F × F) π.ker)) +
    (π.ker.subtype.comp (LinearMap.snd F (F × F) π.ker))
  refine LinearEquiv.ofLinearMap f j ?_ ?_
  · apply LinearMap.ext
    intro a
    rcases a with ⟨a,r⟩
    have hr : π (r : V) = 0 := r.property
    have eq : π (P a + r) = a := by simp [hp, hr]
    change (π (P a + r), rem (P a + r)) = (a,r)
    refine Prod.ext eq ?_
    apply Subtype.ext
    change P a + r - P (π (P a + r)) = (r : V)
    rw [eq]
    abel
  · apply LinearMap.ext
    intro x
    change P (π x) + (x - P (π x)) = x
    abel
theorem splitPlane_formula (B : LinearMap.BilinForm F V) (h : B.IsAlt)
    {u v : V} (huv : B u v = 1) (x y : V) :
    let e := splitPlane B h huv
    B x y = cross (e x).1 (e y).1 + (B.restrict (projection B u v).ker) (e x).2 (e y).2 := by
  dsimp only
  let e := splitPlane B h huv
  let X := e x
  let Y := e y
  have hx : plane u v X.1 + (X.2 : V) = x := e.left_inv x
  have hy : plane u v Y.1 + (Y.2 : V) = y := e.left_inv y
  have hz (z : (projection B u v).ker) : B (z : V) u = 0 ∧ B (z : V) v = 0 := by
    have h := z.property
    change (B (z : V) v, B (z : V) u) = (0,0) at h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  have hvu : B v u = 1 := (symm_of_alt B h).eq v u ▸ huv
  have hs := symm_of_alt B h
  have hx0 := hz X.2
  have hy0 := hz Y.2
  have hyU : B u (Y.2 : V) = 0 := (hs.eq _ _).trans hy0.1
  have hyV : B v (Y.2 : V) = 0 := (hs.eq _ _).trans hy0.2
  change B x y = cross X.1 Y.1 + B (X.2 : V) (Y.2 : V)
  calc
    B x y = B (plane u v X.1 + (X.2 : V)) (plane u v Y.1 + (Y.2 : V)) :=
      congrArg₂ (fun x y => B x y) hx.symm hy.symm
    _ = _ := by
      change B (X.1.1 • u + X.1.2 • v + (X.2 : V))
        (Y.1.1 • u + Y.1.2 • v + (Y.2 : V)) = _
      simp [cross, LinearMap.BilinForm.add_right,
        h u, h v, huv, hvu,
        hx0.1, hx0.2, hyU, hyV]
end

theorem chart_by_dim (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      finrank F V = n → ∀ (B : LinearMap.BilinForm F V), B.IsAlt →
      ∃ (p r : ℕ) (E : V ≃ₗ[F] Coord p r), ∀ x y,
        B x y = ∑ i, cross ((E x).1 i) ((E y).1 i) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ _ hn B hAlt
    by_cases hz : B = 0
    · let E := (Module.finBasis F V).equivFun.trans (zeroChart _)
      exact ⟨0,finrank F V,E,by simp [hz]⟩
    have ex : ∃ u v, B u v ≠ 0 := by
      by_contra! h
      apply hz
      ext u v
      exact h u v
    obtain ⟨u,v,hnz⟩ := ex
    have huv : B u v = 1 := ((show ∀ a : F, a = 0 ∨ a = 1 by decide) _).resolve_left hnz
    let e := splitPlane B hAlt huv
    let W := (projection B u v).ker
    have dim : finrank F V = 2 + finrank F W := by
      have he := e.finrank_eq
      rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self] at he
      exact he
    have hlt : finrank F W < n := by omega
    obtain ⟨p,r,E,he⟩ := ih (finrank F W) hlt W rfl (B.restrict W) (fun z => hAlt z)
    let Q := (e.trans ((LinearEquiv.refl F (F × F)).prodCongr E)).trans (prepend p r)
    refine ⟨p+1,r,Q,?_⟩
    intro x y
    rw [Fin.sum_univ_succ]
    change B x y = cross (e x).1 (e y).1 + ∑ i : Fin p, cross ((E (e x).2).1 i) ((E (e y).2).1 i)
    rw [← he]
    exact splitPlane_formula B hAlt huv x y

end PEqualNP.Outside.L_meta_33655_aux.Chart

open Module BigOperators


namespace PEqualNP.Outside.L_meta_33655_aux.Normal

universe u
open PEqualNP.Outside.L_meta_33655_aux.Chart

section
variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

def pairedCoordinate {p r : ℕ} (E : V ≃ₗ[F] Coord p r) : V →ₗ[F] (Fin p → F × F) :=
  (LinearMap.fst F (Fin p → F × F) (Fin r → F)).comp E.toLinearMap

theorem cross_sum_zero {p : ℕ} (a : Fin p → F × F)
    (h : ∀ b : Fin p → F × F, (∑ i, cross (a i) (b i)) = 0) : a = 0 := by
  funext i
  have ev (w : F × F) : cross (a i) w = 0 := by
    have q := h (Pi.single i w)
    rw [Finset.sum_eq_single i] at q
    · simpa using q
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, cross]
    · simp
  exact Prod.ext (by simpa [cross] using ev (0,1)) (by simpa [cross] using ev (1,0))

theorem chart_rank (B : LinearMap.BilinForm F V) {p r : ℕ} (E : V ≃ₗ[F] Coord p r)
    (hE : ∀ x y, B x y = ∑ i, cross ((E x).1 i) ((E y).1 i)) :
    finrank F B.range = 2*p := by
  let f := pairedCoordinate E
  have hker : B.ker = f.ker := by
    ext x
    change B x = 0 ↔ (E x).1 = 0
    constructor
    · intro hx
      apply cross_sum_zero
      intro a
      let y := E.symm (a, 0)
      have h := DFunLike.congr_fun hx y
      simp only [LinearMap.zero_apply] at h
      rwa [hE, show E y = (a,0) from E.apply_symm_apply _] at h
    · intro hx
      ext y
      simp [hE, hx, cross]
  have hs : Function.Surjective f := fun a => ⟨E.symm (a,0), by simp [f, pairedCoordinate]⟩
  have hf := f.finrank_range_add_finrank_ker
  have hB := B.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hf
  rw [hker] at hB
  have hdim : finrank F (Fin p → F × F) = 2*p := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_prod, Nat.mul_comm]
  omega

omit [FiniteDimensional F V]
in
def unzip (p r : ℕ) : Coord p r ≃ₗ[F] (Fin p → F) × ((Fin p → F) × (Fin r → F)) where
  toFun x := (fun i => (x.1 i).1, (fun i => (x.1 i).2, x.2))
  invFun x := (fun i => (x.1 i, x.2.1 i), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def quadratic {p r : ℕ} (E : V ≃ₗ[F] Coord p r) (x : V) : F :=
  ∑ i, ((E x).1 i).1 * ((E x).1 i).2

omit [FiniteDimensional F V] in
theorem quadratic_zero {p r : ℕ} (E : V ≃ₗ[F] Coord p r) : quadratic E 0 = 0 := by
  simp [quadratic]

omit [FiniteDimensional F V] in
theorem quadratic_polar {p r : ℕ} (E : V ≃ₗ[F] Coord p r) (x y : V) :
    quadratic E (x + y) - quadratic E x - quadratic E y + quadratic E 0 =
      ∑ i, cross ((E x).1 i) ((E y).1 i) := by
  rw [quadratic_zero, add_zero]
  simp only [quadratic, map_add, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (((E x).1 i).1 + ((E y).1 i).1) * (((E x).1 i).2 + ((E y).1 i).2) -
      ((E x).1 i).1 * ((E x).1 i).2 - ((E y).1 i).1 * ((E y).1 i).2 = _
  unfold cross
  ring

omit [FiniteDimensional F V] in
theorem scalar_affine {p r : ℕ} (E : V ≃ₗ[F] Coord p r) (f : V → F)
    (h : ∀ x y, f (x+y) - f x - f y + f 0 = ∑ i, cross ((E x).1 i) ((E y).1 i)) :
    ∃ (l : V →ₗ[F] F) (c : F), ∀ x,
      f x = dotProduct ((E.trans (unzip p r)) x).1 ((E.trans (unzip p r)) x).2.1 + l x + c := by
  let residual (x : V) := f x - quadratic E x - f 0
  have hzero : residual 0 = 0 := by simp [residual, quadratic_zero]
  let l : V →ₗ[F] F := {
    toFun := residual
    map_add' := fun x y => by
      dsimp only [residual]
      calc
        f (x + y) - quadratic E (x + y) - f 0 =
            (f (x+y) - f x - f y + f 0) -
            (quadratic E (x+y) - quadratic E x - quadratic E y + quadratic E 0) +
            (f x - quadratic E x - f 0) + (f y - quadratic E y - f 0) := by
                rw [quadratic_zero]
                ring
        _ = _ := by rw [h, quadratic_polar, sub_self, zero_add]
    map_smul' := fun a x => by
      have ha := (show ∀ b : F, b = 0 ∨ b = 1 by decide) a
      rcases ha with rfl | rfl <;> simp [hzero] }
  refine ⟨l, f 0, fun x => ?_⟩
  change f x = quadratic E x + (f x - quadratic E x - f 0) + f 0
  ring

end

end PEqualNP.Outside.L_meta_33655_aux.Normal

open Module Matrix

namespace PEqualNP.Outside.L_meta_33655_aux.MatrixProof
open PEqualNP.Outside.L_meta_33655_aux.Chart
open PEqualNP.Outside.L_meta_33655_aux.Normal

abbrev W (k : ℕ) := Fin k → F

def dotB (k : ℕ) : LinearMap.BilinForm F (W k) := Matrix.toBilin' (1 : Matrix (Fin k) (Fin k) F)

@[simp] theorem dotB_eval {k} (x y : W k) : dotB k x y = dotProduct x y := by
  simp [dotB, Matrix.toBilin'_apply']

theorem dotB_symm (k : ℕ) : (dotB k).IsSymm :=
  ⟨fun x y => by simpa using dotProduct_comm x y⟩

theorem dotB_nondegenerate (k : ℕ) : (dotB k).Nondegenerate := by
  have hl (x : W k) (h : ∀ y, dotB k x y = 0) : x = 0 := by
    funext i
    simpa using h (Pi.single i 1)
  exact ⟨hl, fun x h => hl x (fun y => (dotB_symm k).eq x y ▸ h y)⟩

theorem matrixAdjoint {k} (A : Matrix (Fin k) (Fin k) F) (hA : Aᵀ = A) (x y : W k) :
    dotB k (A.mulVecLin x) y = dotB k x (A.mulVecLin y) := by
  simp only [dotB_eval, Matrix.mulVecLin_apply]
  rw [dotProduct_comm (A.mulVec x) y]
  simpa only [hA] using (Matrix.dotProduct_transpose_mulVec A x y).symm

theorem inverseOnRange {k} (A G : Matrix (Fin k) (Fin k) F) (h : A * G * A = A) :
    ∀ x : A.mulVecLin.range, A.mulVecLin (G.mulVecLin x) = x := by
  rintro ⟨x, v, rfl⟩
  change A.mulVec (G.mulVec (A.mulVec v)) = A.mulVec v
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem rank_compLeft {k} (G : W k →ₗ[F] W k) :
    finrank F ((dotB k).compLeft G).range = finrank F G.range := by
  have hk : ((dotB k).compLeft G).ker = G.ker := by
    ext x
    change (dotB k) (G x) = 0 ↔ G x = 0
    exact ⟨fun h => (dotB_nondegenerate k).1 _ (fun y => by simp [h]), fun h => by simp [h]⟩
  have hG := G.finrank_range_add_finrank_ker
  have hB := ((dotB k).compLeft G).finrank_range_add_finrank_ker
  rw [hk] at hB
  omega

theorem chart_of_polar {k} (H : W k →ₗ[F] W k) (rot : W k ≃ₗ[F] W k) (f : W k → F)
    (h : ∀ x y, f (x+y) - f x - f y + f 0 = dotProduct (H (rot x)) (rot y)) :
    ∃ (p r : ℕ) (E : W k ≃ₗ[F] (Fin p → F) × ((Fin p → F) × (Fin r → F)))
      (l : W k →ₗ[F] F) (c : F), finrank F H.range = 2*p ∧
      ∀ x, f x = dotProduct (E x).1 (E x).2.1 + l x + c := by
  let B := (dotB k).compLeft H
  have hh (x y : W k) : f (x+y) - f x - f y + f 0 = B (rot x) (rot y) := by
    change f (x+y) - f x - f y + f 0 = dotB k (H (rot x)) (rot y)
    rw [dotB_eval]
    exact h x y
  have alt : B.IsAlt := by
    intro x
    let u := rot.symm x
    have he : rot u = x := rot.apply_symm_apply _
    have bitSum : ∀ a : F, a+a=0 := by decide
    have hu : u+u=0 := funext (fun i => bitSum (u i))
    have hyp := hh u u
    rw [hu, he] at hyp
    rw [← hyp, ZModModule.sub_eq_add, ZModModule.sub_eq_add]
    calc
      f 0 + f u + f u + f 0 = (f 0 + f 0) + (f u + f u) := by ac_rfl
      _ = 0 := by simp [bitSum]
  obtain ⟨p,r,E,hE⟩ := chart_by_dim _ (W k) rfl B alt
  let E' := rot.trans E
  have hp := chart_rank B E hE
  have rankEq : finrank F H.range = 2*p := (rank_compLeft H).symm.trans hp
  have hx (x y : W k) : f (x+y) - f x - f y + f 0 = ∑ i, cross ((E' x).1 i) ((E' y).1 i) :=
    (hh x y).trans (hE _ _)
  obtain ⟨l,c,hl⟩ := scalar_affine E' f hx
  exact ⟨p,r,E'.trans (unzip p r),l,c,rankEq,hl⟩

theorem half_from_dimensions {j b t r : ℕ} (h : 2*j + t + r = 2*b) :
    j = b-(t+r)/2 := by omega

theorem eq_from_double {j b : ℕ} (h : 2*j = 2*b) : j=b := by omega

end PEqualNP.Outside.L_meta_33655_aux.MatrixProof

namespace PEqualNP.Outside.L_meta_33655_aux.Paths

abbrev F := ZMod 2

def forward (i j : Nat) : Prop := i < j ∧ i % 2 = 0 ∧ j % 2 = 1

instance (i j : Nat) : Decidable (forward i j) := by
  unfold forward
  infer_instance

def invEntry (n i j : Nat) : F :=
  if i < n ∧ j < n ∧ (forward i j ∨ forward j i) then 1 else 0

theorem invEntry_symm (n i j : Nat) : invEntry n i j = invEntry n j i := by
  have h : (i < n ∧ j < n ∧ (forward i j ∨ forward j i)) ↔
      (j < n ∧ i < n ∧ (forward j i ∨ forward i j)) :=
    ⟨fun ⟨hi, hj, h⟩ => ⟨hj, hi, h.symm⟩, fun ⟨hj, hi, h⟩ => ⟨hi, hj, h.symm⟩⟩
  simp only [invEntry, h]

theorem invEntry_add_neighbors (n i j : Nat) (hi : i < n) (hj : j < n) :
    (if 0 < i then invEntry n (i - 1) j else 0) + invEntry n (i + 1) j =
      (if i = j then 1 else 0) +
        (if i + 1 = n ∧ i % 2 = 0 ∧ j % 2 = 0 then 1 else 0) := by
  by_cases h : 0 < i
  · rw [ite_eq_left h]
    simp only [invEntry]
    split_ifs <;> simp only [forward] at * <;> first | omega | decide
  · rw [ite_eq_right h]
    simp only [invEntry]
    split_ifs <;> simp only [forward] at * <;> first | omega | decide

def pathA (n : Nat) : Matrix (Fin n) (Fin n) F :=
  fun i j => (if i.val + 1 = j.val then 1 else 0) + (if j.val + 1 = i.val then 1 else 0)

def pathG (n : Nat) : Matrix (Fin n) (Fin n) F :=
  fun i j => invEntry n i.val j.val

theorem pathG_eq (n : Nat) (i j : Fin n) :
    pathG n i j =
      if (min i.val j.val) % 2 = 0 ∧ (max i.val j.val) % 2 = 1 then 1 else 0 := by
  by_cases hij : i.val ≤ j.val
  · rw [min_eq_left hij, max_eq_right hij]
    simp only [pathG, invEntry, i.isLt, j.isLt, true_and, forward]
    split_ifs <;> first | omega | decide
  · have hji : j.val ≤ i.val := by omega
    rw [min_eq_right hji, max_eq_left hji]
    simp only [pathG, invEntry, i.isLt, j.isLt, true_and, forward]
    split_ifs <;> first | omega | decide

def lastEvenRow (n : Nat) : Matrix (Fin n) (Fin n) F :=
  fun i j => if i.val + 1 = n ∧ i.val % 2 = 0 ∧ j.val % 2 = 0 then 1 else 0

theorem pathA_mulVec_eq (n : Nat) (f : Nat → F) (hf : f n = 0) (i : Fin n) :
    (pathA n).mulVec (fun x => f x.val) i =
      (if 0 < i.val then f (i.val - 1) else 0) + f (i.val + 1) := by
  simp only [Matrix.mulVec, dotProduct, pathA, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul]
  have hright :
      (∑ x : Fin n, if i.val + 1 = x.val then f x.val else 0)
        = f (i.val + 1) := by
    by_cases h : i.val + 1 < n
    · let r : Fin n := ⟨i.val + 1, h⟩
      have heq (x : Fin n) : i.val + 1 = x.val ↔ r = x := by
        exact ⟨fun hx => Fin.ext hx, fun hx => congrArg Fin.val hx⟩
      simp_rw [heq]
      simp [r]
    · rw [show i.val + 1 = n by omega, hf]
      apply Finset.sum_eq_zero
      intro x hx
      split <;> try rfl
      omega
  have hleft :
      (∑ x : Fin n, if x.val + 1 = i.val then f x.val else 0)
        = if 0 < i.val then f (i.val - 1) else 0 := by
    split_ifs with h
    · let l : Fin n := ⟨i.val - 1, by omega⟩
      have heq (x : Fin n) : x.val + 1 = i.val ↔ x = l := by
        constructor
        · intro hx
          apply Fin.ext
          simp only [l]
          omega
        · rintro rfl
          simp only [l]
          omega
      simp_rw [heq]
      simp [l]
    · apply Finset.sum_eq_zero
      intro x hx
      split <;> try rfl
      omega
  rw [hright, hleft, add_comm]

theorem pathA_mul_pathG (n : Nat) : pathA n * pathG n = 1 + lastEvenRow n := by
  ext i j
  change (pathA n).mulVec (fun x => invEntry n x.val j.val) i = _
  rw [pathA_mulVec_eq n (fun a => invEntry n a j.val) (by simp [invEntry]) i]
  rw [invEntry_add_neighbors n i.val j.val i.isLt j.isLt]
  simp [lastEvenRow, Matrix.one_apply, Fin.ext_iff]

theorem pathA_mul_pathG_even {n : Nat} (hn : n % 2 = 0) :
    pathA n * pathG n = 1 := by
  rw [pathA_mul_pathG]
  have hzero : lastEvenRow n = 0 := by
    ext i j
    by_cases h : i.val + 1 = n ∧ i.val % 2 = 0 ∧ j.val % 2 = 0
    · omega
    · simp [lastEvenRow, h]
  rw [hzero, add_zero]

end PEqualNP.Outside.L_meta_33655_aux.Paths

namespace PEqualNP.Outside.L_meta_33655_aux.Paths

def successor {k : Nat} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

theorem successor_injective {k : Nat} (hk : 0 < k) :
    Function.Injective (successor hk) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [successor] at hval
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi' : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi'] at hval
    by_cases hj' : j.val + 1 < k
    · rw [Nat.mod_eq_of_lt hj'] at hval
      omega
    · have hj'' : j.val + 1 = k := by omega
      rw [hj'', Nat.mod_self] at hval
      omega
  · have hi'' : i.val + 1 = k := by omega
    rw [hi'', Nat.mod_self] at hval
    by_cases hj' : j.val + 1 < k
    · rw [Nat.mod_eq_of_lt hj'] at hval
      omega
    · omega

def selectionMax {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) : Nat :=
  (E.powerset.filter (fun M => ∀ i ∈ M, successor hk i ∉ M)).sup Finset.card

theorem card_le_half_of_independent {k : Nat} (hk : 0 < k) (M : Finset (Fin k))
    (h : ∀ i ∈ M, successor hk i ∉ M) : M.card ≤ k / 2 := by
  have hdisj : Disjoint M (M.image (successor hk)) := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha'
    exact h b hb ha
  have hcard := Finset.card_le_univ (M ∪ (M.image (successor hk)))
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective M (successor_injective hk),
    Fintype.card_fin] at hcard
  omega

theorem selectionMax_le_half {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) :
    selectionMax hk E ≤ k / 2 := by
  apply Finset.sup_le
  intro M hM
  exact card_le_half_of_independent hk M (Finset.mem_filter.mp hM).2

def pairedEven {k : Nat} (j : Fin (k / 2)) : Fin k :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

theorem selectionMax_eq_half_of_paired_even {k : Nat} (hk : 0 < k) (E : Finset (Fin k))
    (hE : ∀ j : Fin (k / 2), pairedEven j ∈ E) :
    selectionMax hk E = k / 2 := by
  apply le_antisymm (selectionMax_le_half hk E)
  let M : Finset (Fin k) := Finset.univ.image pairedEven
  have hsubset : M ⊆ E := by
    intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    exact hE j
  have hind : ∀ i ∈ M, successor hk i ∉ M := by
    intro i hi hi'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j', -, hj'⟩ := Finset.mem_image.mp hi'
    have hfit : 2 * j.val + 1 < k := by have := j.isLt; omega
    have hval := congrArg Fin.val hj'
    simp only [successor, pairedEven] at hval
    rw [Nat.mod_eq_of_lt hfit] at hval
    omega
  have hmem : M ∈ E.powerset.filter (fun M => ∀ i ∈ M, successor hk i ∉ M) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsubset, hind⟩
  have hcard : M.card = k / 2 := by
    have hinj : Function.Injective (@pairedEven k) := by
      intro j j' h
      apply Fin.ext
      have hval := congrArg Fin.val h
      simp only [pairedEven] at hval
      omega
    simp [M, Finset.card_image_of_injective _ hinj]
  simpa only [selectionMax, ← hcard] using (Finset.le_sup (f := Finset.card) hmem)

theorem selectionMax_univ {k : Nat} (hk : 0 < k) :
    selectionMax hk Finset.univ = k / 2 :=
  selectionMax_eq_half_of_paired_even hk _ (fun _ => Finset.mem_univ _)

theorem selectionMax_path {k : Nat} (hk : 0 < k) :
    selectionMax hk (Finset.univ.filter (fun i : Fin k => i.val + 1 < k)) = k / 2 := by
  apply selectionMax_eq_half_of_paired_even
  intro j
  have hj := j.isLt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairedEven]
  omega

theorem selectionMax_even {k : Nat} (hk : 0 < k) :
    selectionMax hk (Finset.univ.filter (fun i : Fin k => i.val % 2 = 0)) = k / 2 := by
  apply selectionMax_eq_half_of_paired_even
  intro j
  simp [pairedEven]

end PEqualNP.Outside.L_meta_33655_aux.Paths

namespace PEqualNP.Outside.L_meta_33655_aux.Paths

theorem range_zero_of_retained_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (keep : ι → Prop) (hA : A.transpose = A)
    (hker : ∀ i, ¬ keep i → ∃ u : ι → ZMod 2,
      A.mulVec u = 0 ∧ u i = 1 ∧ ∀ j, ¬ keep j → j ≠ i → u j = 0)
    (w : ι → ZMod 2) (hw : w ∈ LinearMap.range A.mulVecLin)
    (hz : ∀ i, keep i → w i = 0) : w = 0 := by
  funext i
  by_cases hi : keep i
  · exact hz i hi
  · obtain ⟨u, hu, hui, hur⟩ := hker i hi
    have ho : dotProduct u w = 0 := by
      obtain ⟨x, rfl⟩ := hw
      change dotProduct u (A.mulVec x) = 0
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, hu, zero_dotProduct]
    have hsum : dotProduct u w = w i := by
      unfold dotProduct
      rw [Fintype.sum_eq_single i]
      · rw [hui, one_mul]
      · intro j hji
        by_cases hj : keep j
        · rw [hz j hj, mul_zero]
        · rw [hur j hj hji, zero_mul]
    exact hsum.symm.trans ho

theorem rank_and_inverse_of_compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A G : Matrix ι ι (ZMod 2)) (keep : ι → Prop) [DecidablePred keep]
    (hA : A.transpose = A)
    (hAG : ∀ i, keep i → ∀ j, (A * G) i j = (1 : Matrix ι ι (ZMod 2)) i j)
    (hker : ∀ i, ¬ keep i → ∃ u : ι → ZMod 2,
      A.mulVec u = 0 ∧ u i = 1 ∧ ∀ j, ¬ keep j → j ≠ i → u j = 0) :
    A.rank = Fintype.card {i // keep i} ∧ A * G * A = A := by
  let V := LinearMap.range A.mulVecLin
  let proj : V →ₗ[ZMod 2] ({i // keep i} → ZMod 2) :=
    { toFun := fun w i => w.val i.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hproj (x : ι → ZMod 2) (i : ι) (hi : keep i) : A.mulVec (G.mulVec x) i = x i := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hAG i hi]
    simp [Matrix.one_apply]
  have hinj : Function.Injective proj := by
    apply (injective_iff_map_eq_zero proj).mpr
    intro w hw
    apply Subtype.ext
    exact range_zero_of_retained_zero A keep hA hker w.val w.property (fun i hi =>
      congrFun hw ⟨i, hi⟩)
  have hsurj : Function.Surjective proj := by
    intro w
    let x : ι → ZMod 2 := fun i => if hi : keep i then w ⟨i, hi⟩ else 0
    refine ⟨⟨A.mulVec (G.mulVec x), ⟨G.mulVec x, rfl⟩⟩, ?_⟩
    funext i
    change A.mulVec (G.mulVec x) i.val = w i
    rw [hproj x i.val i.property]
    simp [x, i.property]
  constructor
  · have h := (LinearEquiv.ofBijective proj ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_pi] at h
    exact h
  · apply Matrix.mulVec_injective
    funext x
    have hx : A.mulVec x ∈ V := ⟨x, rfl⟩
    have hGx : A.mulVec (G.mulVec (A.mulVec x)) ∈ V := ⟨G.mulVec (A.mulVec x), rfl⟩
    have heq : (⟨A.mulVec (G.mulVec (A.mulVec x)), hGx⟩ : V) = ⟨A.mulVec x, hx⟩ := by
      apply hinj
      funext i
      exact hproj _ i.val i.property
    have he := congrArg Subtype.val heq
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] using he

end PEqualNP.Outside.L_meta_33655_aux.Paths

namespace PEqualNP.Outside.L_meta_33655_aux.Paths

def markedBase {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) : Nat :=
  let miss := Finset.univ \ E
  if h : miss.Nonempty then (successor hk (miss.min' h)).val else 0

def markedPos (k base a : Nat) : Nat := (a + k - base) % k

def markedStart {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) (base u : Nat) : Nat :=
  ((Finset.range (u + 1)).filter (fun j =>
    j = 0 ∨ (⟨(base + (j - 1)) % k, Nat.mod_lt _ hk⟩ : Fin k) ∉ E)).sup id

def markedA {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) : Matrix (Fin k) (Fin k) F :=
  fun i j => (if i ∈ E ∧ successor hk i = j then 1 else 0) +
    (if j ∈ E ∧ successor hk j = i then 1 else 0)

def markedG {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) : Matrix (Fin k) (Fin k) F :=
  let base := markedBase hk E
  let pos := fun i : Fin k => markedPos k base i.val
  let start := markedStart hk E base
  let lim := if E = Finset.univ then k - (if k % 2 = 0 then 2 else 1) else k
  fun i j =>
    let u := min (pos i) (pos j)
    let v := max (pos i) (pos j)
    if v < lim ∧ start u = start v ∧ (u - start u) % 2 = 0 ∧ (v - start v) % 2 = 1
    then 1 else 0

def spanMarks (k : Nat) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => i.val + 1 < k)

def evenMarks (k : Nat) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => i.val % 2 = 0)

theorem markedStart_eq {k : Nat} (hk : 0 < k) (E : Finset (Fin k))
    (base u a : Nat) (ha : a ≤ u)
    (hac : a = 0 ∨ (⟨(base + (a - 1)) % k, Nat.mod_lt _ hk⟩ : Fin k) ∉ E)
    (had : ∀ j ≤ u, (j = 0 ∨ (⟨(base + (j - 1)) % k, Nat.mod_lt _ hk⟩ : Fin k) ∉ E) → j ≤ a) :
    markedStart hk E base u = a := by
  unfold markedStart
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    obtain ⟨hjr, hjc⟩ := Finset.mem_filter.mp hj
    exact had j (by simpa using hjr) hjc
  · apply Finset.le_sup (f := id)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hac⟩

theorem markedBase_lt {k : Nat} (hk : 0 < k) (E : Finset (Fin k)) :
    markedBase hk E < k := by
  simp only [markedBase]
  split
  · exact Fin.isLt _
  · exact hk

theorem markedPos_eq {k base a : Nat} (hb : base < k) (ha : a < k) :
    markedPos k base a = if base ≤ a then a - base else a + k - base := by
  unfold markedPos
  split_ifs with h
  · rw [show a + k - base = a - base + k by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.mod_eq_of_lt (by omega)

theorem markedPos_zero {k : Nat} (i : Fin k) : markedPos k 0 i.val = i.val := by
  simp [markedPos, Nat.mod_eq_of_lt i.isLt]

theorem spanMarks_ne_univ {k : Nat} (hk : 0 < k) : spanMarks k ≠ Finset.univ := by
  intro h
  let i : Fin k := ⟨k - 1, by omega⟩
  have hi : i ∈ spanMarks k := h.symm ▸ Finset.mem_univ i
  simp only [spanMarks, Finset.mem_filter, Finset.mem_univ, true_and, i] at hi
  omega

theorem markedBase_span {k : Nat} (hk : 0 < k) : markedBase hk (spanMarks k) = 0 := by
  simp only [markedBase]
  split
  next h =>
    let i := (Finset.univ \ spanMarks k).min' h
    have hi : i ∈ Finset.univ \ spanMarks k := Finset.min'_mem _ h
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, spanMarks, Finset.mem_filter] at hi
    have hlt := i.isLt
    have heq : i.val + 1 = k := by omega
    change (i.val + 1) % k = 0
    simp [heq]
  · rfl

theorem markedStart_span {k : Nat} (hk : 0 < k) (u : Nat) (hu : u < k) :
    markedStart hk (spanMarks k) 0 u = 0 := by
  apply markedStart_eq
  · omega
  · exact Or.inl rfl
  · intro j hj hjc
    by_cases hj0 : j = 0
    · omega
    · exfalso
      apply hjc.resolve_left hj0
      simp only [zero_add, spanMarks, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Nat.mod_eq_of_lt (show j - 1 < k by omega)]
      omega

theorem markedA_span {k : Nat} (hk : 0 < k) : markedA hk (spanMarks k) = pathA k := by
  ext i j
  have h (a b : Fin k) : a ∈ spanMarks k ∧ successor hk a = b ↔ a.val + 1 = b.val := by
    simp only [spanMarks, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, successor]
    constructor
    · rintro ⟨ha, hb⟩
      rwa [Nat.mod_eq_of_lt ha] at hb
    · intro hab
      have ha : a.val + 1 < k := hab ▸ b.isLt
      exact ⟨ha, (Nat.mod_eq_of_lt ha).trans hab⟩
  simp only [markedA, pathA, h]

theorem markedG_span {k : Nat} (hk : 0 < k) : markedG hk (spanMarks k) = pathG k := by
  ext i j
  rw [pathG_eq]
  have hmax : max i.val j.val < k := max_lt_iff.mpr ⟨i.isLt, j.isLt⟩
  have hmin : min i.val j.val < k := (min_le_left _ _).trans_lt i.isLt
  simp [markedG, markedBase_span hk, markedPos_zero, spanMarks_ne_univ hk,
    markedStart_span hk _ hmax, markedStart_span hk _ hmin]

theorem markedA_mul_G_span_even {k : Nat} (hk : 0 < k) (he : k % 2 = 0) :
    markedA hk (spanMarks k) * markedG hk (spanMarks k) = 1 := by
  rw [markedA_span, markedG_span, pathA_mul_pathG_even he]

theorem markedBase_even_parity {k : Nat} (hk : 0 < k) (he : k % 2 = 0) :
    markedBase hk (evenMarks k) % 2 = 0 := by
  simp only [markedBase]
  split
  next h =>
    let i := (Finset.univ \ evenMarks k).min' h
    have hi : i ∈ Finset.univ \ evenMarks k := Finset.min'_mem _ h
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, evenMarks, Finset.mem_filter] at hi
    have hdvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero he
    change ((i.val + 1) % k) % 2 = 0
    simp only [Nat.mod_mod_of_dvd _ hdvd]
    omega
  · rfl

theorem evenMarks_ne_univ {k : Nat} (hk : 0 < k) (he : k % 2 = 0) :
    evenMarks k ≠ Finset.univ := by
  intro h
  let i : Fin k := ⟨1, by omega⟩
  have hi : i ∈ evenMarks k := h.symm ▸ Finset.mem_univ i
  simp [evenMarks, i] at hi

theorem markedStart_even {k : Nat} (hk : 0 < k) (he : k % 2 = 0)
    (base : Nat) (hb : base % 2 = 0) (u : Nat) :
    markedStart hk (evenMarks k) base u = u - u % 2 := by
  have hdvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero he
  have hc (j : Nat) :
      (j = 0 ∨ (⟨(base + (j - 1)) % k, Nat.mod_lt _ hk⟩ : Fin k) ∉ evenMarks k)
        ↔ j % 2 = 0 := by
    simp only [evenMarks, Finset.mem_filter, Finset.mem_univ, true_and, Nat.mod_mod_of_dvd _ hdvd]
    omega
  apply markedStart_eq
  · omega
  · simpa only [hc] using (show (u - u % 2) % 2 = 0 by omega)
  · intro j hj hjc
    have := (hc j).mp hjc
    omega

theorem markedPos_even_parity {k base a : Nat} (he : k % 2 = 0) (hbe : base % 2 = 0)
    (hb : base < k) (ha : a < k) : markedPos k base a % 2 = a % 2 := by
  rw [markedPos_eq hb ha]
  split <;> omega

theorem markedPos_even_pair {k base a b : Nat} (he : k % 2 = 0) (hbe : base % 2 = 0)
    (hb : base < k) (ha : a < k) (hb' : b < k) :
    markedPos k base a / 2 = markedPos k base b / 2 ↔ a / 2 = b / 2 := by
  rw [markedPos_eq hb ha, markedPos_eq hb hb']
  split_ifs <;> omega

theorem markedG_even_apply {k : Nat} (hk : 0 < k) (he : k % 2 = 0) (i j : Fin k) :
    markedG hk (evenMarks k) i j =
      if i.val / 2 = j.val / 2 ∧ i.val % 2 ≠ j.val % 2 then 1 else 0 := by
  let base := markedBase hk (evenMarks k)
  let a := markedPos k base i.val
  let b := markedPos k base j.val
  have hbase := markedBase_lt hk (evenMarks k)
  have hbaseEven := markedBase_even_parity hk he
  have ha : a < k := Nat.mod_lt _ hk
  have hb : b < k := Nat.mod_lt _ hk
  have ha' : a % 2 = i.val % 2 := markedPos_even_parity he hbaseEven hbase i.isLt
  have hb' : b % 2 = j.val % 2 := markedPos_even_parity he hbaseEven hbase j.isLt
  have hp : a / 2 = b / 2 ↔ i.val / 2 = j.val / 2 :=
    markedPos_even_pair he hbaseEven hbase i.isLt j.isLt
  have heq :
      (max a b < k ∧ min a b - min a b % 2 = max a b - max a b % 2 ∧
        (min a b - (min a b - min a b % 2)) % 2 = 0 ∧
        (max a b - (max a b - max a b % 2)) % 2 = 1) ↔
        (i.val / 2 = j.val / 2 ∧ i.val % 2 ≠ j.val % 2) := by
    rw [← hp, ← ha', ← hb']
    by_cases hab : a ≤ b
    · rw [min_eq_left hab, max_eq_right hab]
      omega
    · have hba : b ≤ a := by omega
      rw [min_eq_right hba, max_eq_left hba]
      omega
  simp only [markedG, evenMarks_ne_univ hk he, ite_false,
    markedStart_even hk he _ hbaseEven]
  simp only [← heq, a, b, base]

theorem markedA_even_apply {k : Nat} (hk : 0 < k) (he : k % 2 = 0) (i j : Fin k) :
    markedA hk (evenMarks k) i j =
      if i.val / 2 = j.val / 2 ∧ i.val % 2 ≠ j.val % 2 then 1 else 0 := by
  have h (a b : Fin k) : a ∈ evenMarks k ∧ successor hk a = b ↔
      a.val % 2 = 0 ∧ a.val + 1 = b.val := by
    simp only [evenMarks, Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
    intro ha
    have hfit : a.val + 1 < k := by have := a.isLt; omega
    simp only [Fin.ext_iff, successor, Nat.mod_eq_of_lt hfit]
  simp only [markedA, h]
  split_ifs <;> first | omega | decide

def pairSwap {k : Nat} (he : k % 2 = 0) (i : Fin k) : Fin k :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have := i.isLt
    split <;> omega⟩

theorem pairSwap_eq_iff {k : Nat} (he : k % 2 = 0) (i j : Fin k) :
    pairSwap he i = j ↔ i.val / 2 = j.val / 2 ∧ i.val % 2 ≠ j.val % 2 := by
  simp only [Fin.ext_iff, pairSwap]
  split <;> omega

theorem pairSwap_involutive {k : Nat} (he : k % 2 = 0) : Function.Involutive (pairSwap he) := by
  intro i
  apply (pairSwap_eq_iff he (pairSwap he i) i).mpr
  have h := (pairSwap_eq_iff he i (pairSwap he i)).mp rfl
  exact ⟨h.1.symm, Ne.symm h.2⟩

theorem markedA_mul_G_evenMarks {k : Nat} (hk : 0 < k) (he : k % 2 = 0) :
    markedA hk (evenMarks k) * markedG hk (evenMarks k) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, markedA_even_apply hk he, markedG_even_apply hk he,
    ← pairSwap_eq_iff he, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [pairSwap_involutive he i]

end PEqualNP.Outside.L_meta_33655_aux.Paths

namespace PEqualNP.Outside.L_meta_33655_aux.Paths

private def cycleLimit (k : Nat) : Nat := k - (if k % 2 = 0 then 2 else 1)

private lemma cycleLimit_lt {k : Nat} (hk : 0 < k) : cycleLimit k < k := by
  unfold cycleLimit
  split <;> omega

private lemma cycleLimit_even (k : Nat) : cycleLimit k % 2 = 0 := by
  unfold cycleLimit
  split <;> omega

private def cyclePred {k : Nat} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨if i.val = 0 then k-1 else i.val-1, by have := i.isLt; split <;> omega⟩

private lemma successor_cyclePred {k : Nat} (hk : 0 < k) (i : Fin k) :
    successor hk (cyclePred hk i) = i := by
  apply Fin.ext
  change ((if i.val = 0 then k-1 else i.val-1) + 1) % k = i.val
  split_ifs with h
  · rw [show k-1+1 = k by omega, Nat.mod_self, h]
  · rw [show i.val-1+1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]

private lemma markedA_univ_mulVec {k : Nat} (hk : 0 < k) (x : Fin k → F) (i : Fin k) :
    (markedA hk Finset.univ).mulVec x i = x (successor hk i) + x (cyclePred hk i) := by
  have hp (j : Fin k) : successor hk j = i ↔ j = cyclePred hk i := by
    constructor
    · intro h
      exact successor_injective hk (h.trans (successor_cyclePred hk i).symm)
    · rintro rfl
      exact successor_cyclePred hk i
  simp only [Matrix.mulVec, dotProduct, markedA, Finset.mem_univ, true_and, hp, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp

private lemma markedG_univ_apply {k : Nat} (hk : 0 < k) (i j : Fin k) :
    markedG hk Finset.univ i j = invEntry (cycleLimit k) i.val j.val := by
  have hbase : markedBase hk (Finset.univ : Finset (Fin k)) = 0 := by
    simp [markedBase]
  have hstart (u : Nat) : markedStart hk Finset.univ 0 u = 0 := by
    apply markedStart_eq hk _ _ _ _ (Nat.zero_le _) (Or.inl rfl)
    intro j _ hj
    simpa using hj
  simp only [markedG, hbase, markedPos_zero, hstart, Nat.sub_zero, ite_true, cycleLimit,
    invEntry, forward, true_and]
  rcases le_total i.val j.val with h | h
  · simp only [min_eq_left h, max_eq_right h]
    split_ifs <;> first | omega | rfl
  · simp only [min_eq_right h, max_eq_left h]
    split_ifs <;> first | omega | rfl

private lemma markedAG_univ_kept {k : Nat} (hk : 0 < k) (i : Fin k) (hi : i.val < cycleLimit k)
    (j : Fin k) :
    (markedA hk Finset.univ * markedG hk Finset.univ) i j =
      (1 : Matrix (Fin k) (Fin k) F) i j := by
  let n := cycleLimit k
  have hn : n < k := cycleLimit_lt hk
  have hne : n % 2 = 0 := cycleLimit_even k
  change (markedA hk Finset.univ).mulVec (fun x => markedG hk Finset.univ x j) i = _
  rw [markedA_univ_mulVec, markedG_univ_apply, markedG_univ_apply]
  change invEntry n ((i.val+1)%k) j.val +
    invEntry n ((if i.val = 0 then k-1 else i.val-1)) j.val = _
  change i.val < n at hi
  rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < k)]
  have hprev : invEntry n (if i.val = 0 then k-1 else i.val-1) j.val =
      if 0 < i.val then invEntry n (i.val-1) j.val else 0 := by
    by_cases h : i.val = 0
    · have hn' : ¬ (k-1 < n) := by omega
      simp [invEntry, h, hn']
    · have hp : 0 < i.val := by omega
      simp [h, hp]
  rw [hprev, add_comm]
  by_cases hj : j.val < n
  · rw [invEntry_add_neighbors n i.val j.val hi hj]
    have hbad : ¬(i.val+1 = n ∧ i.val % 2 = 0 ∧ j.val % 2 = 0) := by omega
    simp [hbad, Matrix.one_apply, Fin.val_inj]
  · have hneq : i ≠ j := by
      intro h
      subst j
      exact hj hi
    simp [invEntry, hj, hneq]

private lemma markedA_univ_kernel_indicator {k : Nat} (hk : 0 < k) (i : Fin k)
    (hi : ¬ i.val < cycleLimit k) :
    ∃ u : Fin k → F, (markedA hk Finset.univ).mulVec u = 0 ∧ u i = 1 ∧
      ∀ j, ¬ j.val < cycleLimit k → j ≠ i → u j = 0 := by
  by_cases he : k % 2 = 0
  · let u : Fin k → F := fun j => if j.val % 2 = i.val % 2 then 1 else 0
    refine ⟨u, ?_, by simp [u], ?_⟩
    · funext j
      rw [markedA_univ_mulVec]
      have hp : (successor hk j).val % 2 = (cyclePred hk j).val % 2 := by
        have hm : 2 ∣ k := by omega
        change (j.val+1)%k % 2 = (if j.val = 0 then k-1 else j.val-1)%2
        rw [Nat.mod_mod_of_dvd _ hm]
        split <;> omega
      change (if (successor hk j).val % 2 = i.val % 2 then 1 else 0) +
        (if (cyclePred hk j).val % 2 = i.val % 2 then 1 else 0) = (0 : F)
      rw [hp]
      split <;> decide
    · intro j hj hji
      have hne : j.val ≠ i.val := Fin.val_ne_iff.mpr hji
      have hit := i.isLt
      have hjt := j.isLt
      simp only [cycleLimit, he, ite_true] at hi hj
      have hp : j.val % 2 ≠ i.val % 2 := by omega
      simp [u, hp]
  · refine ⟨fun _ => 1, ?_, rfl, ?_⟩
    · funext j
      rw [markedA_univ_mulVec]
      change (1 : F) + 1 = 0
      decide
    · intro j hj hji
      have hit := i.isLt
      have hjt := j.isLt
      simp only [cycleLimit, he, ite_false] at hi hj
      exact (hji (Fin.ext (by omega))).elim

theorem markedA_rank_and_inverse_univ {k : Nat} (hk : 0 < k) :
    (markedA hk Finset.univ).rank =
      2 * (if k % 2 = 0 then selectionMax hk Finset.univ - 1 else selectionMax hk Finset.univ) ∧
      markedA hk Finset.univ * markedG hk Finset.univ * markedA hk Finset.univ =
        markedA hk Finset.univ := by
  have hA : (markedA hk Finset.univ).transpose = markedA hk Finset.univ := by
    ext i j
    exact add_comm _ _
  obtain ⟨hRank, hInv⟩ := rank_and_inverse_of_compression (markedA hk Finset.univ)
    (markedG hk Finset.univ) (fun i => i.val < cycleLimit k) hA (markedAG_univ_kept hk) (markedA_univ_kernel_indicator hk)
  refine ⟨hRank.trans ?_, hInv⟩
  let e : {i : Fin k // i.val < cycleLimit k} ≃ Fin (cycleLimit k) :=
    { toFun := fun i => ⟨i.val.val, i.property⟩
      invFun := fun j => ⟨⟨j.val, j.isLt.trans (cycleLimit_lt hk)⟩, j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin, selectionMax_univ hk]
  unfold cycleLimit
  split <;> omega

end PEqualNP.Outside.L_meta_33655_aux.Paths

namespace PEqualNP.Outside.L_meta_33655_aux.Paths

section Line

variable (on : Nat → Prop) [DecidablePred on]

def lineStart (u : Nat) : Nat :=
  ((Finset.range (u + 1)).filter (fun j => j = 0 ∨ ¬on (j - 1))).sup id

theorem lineStart_le (u : Nat) : lineStart on u ≤ u := by
  apply Finset.sup_le
  intro j hj
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)

theorem lineStart_zero : lineStart on 0 = 0 := by
  exact Nat.le_zero.mp (lineStart_le on 0)

theorem lineStart_mono : Monotone (lineStart on) := by
  intro a b hab
  apply Finset.sup_le
  intro j hj
  apply Finset.le_sup (f := id)
  rcases Finset.mem_filter.mp hj with ⟨hj, hc⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hj
    omega), hc⟩

theorem lineStart_succ (u : Nat) :
    lineStart on (u + 1) = if on u then lineStart on u else u + 1 := by
  unfold lineStart
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hu : on u
  · simp [hu]
  · simp [hu, Finset.sup_insert]
    intro j hj _
    omega

theorem sameStart_le_of_end {i j : Nat} (hi : ¬on i)
    (h : lineStart on i = lineStart on j) : j ≤ i := by
  by_contra! hij
  have ho := lineStart_mono on (show i + 1 ≤ j by omega)
  simp only [lineStart_succ on i, hi, ite_false, ← h] at ho
  have := lineStart_le on i
  omega

theorem lineStart_pred_eq {i : Nat} (hi : 0 < i) (hm : on (i - 1)) :
    lineStart on (i - 1) = lineStart on i := by
  have h := lineStart_succ on (i - 1)
  rw [ite_eq_left hm, show i - 1 + 1 = i by omega] at h
  exact h.symm

def rel (i : Nat) : Nat := i - lineStart on i

theorem rel_eq_zero_iff (i : Nat) : rel on i = 0 ↔ ¬(0 < i ∧ on (i - 1)) := by
  by_cases hi : 0 < i
  · by_cases hm : on (i - 1)
    · have h := lineStart_pred_eq on hi hm
      have hle := lineStart_le on (i - 1)
      simp [rel, hi, hm]
      omega
    · have h := lineStart_succ on (i - 1)
      rw [ite_eq_right hm, show i - 1 + 1 = i by omega] at h
      simp [rel, h, hm]
  · have h : i = 0 := by omega
    subst i
    simp [rel]

theorem rel_succ {i : Nat} (hi : on i) : rel on (i + 1) = rel on i + 1 := by
  have hle := lineStart_le on i
  simp only [rel, lineStart_succ on i, ite_eq_left hi]
  omega

theorem rel_pred {i : Nat} (hi : 0 < i) (hm : on (i - 1)) :
    rel on (i - 1) + 1 = rel on i := by
  have h := rel_succ on hm
  rw [show i - 1 + 1 = i by omega] at h
  exact h.symm

def lineA (n : Nat) : Matrix (Fin n) (Fin n) F :=
  fun i j => (if on i.val ∧ i.val + 1 = j.val then 1 else 0) +
    (if on j.val ∧ j.val + 1 = i.val then 1 else 0)

def lineGAt (i j : Nat) : F :=
  if lineStart on i = lineStart on j ∧
    (forward (rel on i) (rel on j) ∨ forward (rel on j) (rel on i)) then 1 else 0

def lineG (n : Nat) : Matrix (Fin n) (Fin n) F :=
  fun i j => lineGAt on i.val j.val

theorem lineA_symmetric (n : Nat) : (lineA on n).transpose = lineA on n := by
  ext i j
  exact add_comm _ _

theorem lineG_eq_invEntry {n : Nat} (i j : Fin n) (m : Nat)
    (hi : rel on i.val < m) (hj : rel on j.val < m)
    (hs : lineStart on i.val = lineStart on j.val) :
    lineG on n i j = invEntry m (rel on i.val) (rel on j.val) := by
  simp [lineG, lineGAt, invEntry, hi, hj, hs]

theorem lineG_of_different_start {n : Nat} (i j : Fin n)
    (hs : lineStart on i.val ≠ lineStart on j.val) : lineG on n i j = 0 := by
  simp [lineG, lineGAt, hs]

def lineKeep (i : Nat) : Prop := on i ∨ rel on i % 2 = 1

instance (i : Nat) : Decidable (lineKeep on i) := by
  unfold lineKeep
  infer_instance

theorem lineA_mulVec_eq {n : Nat} (hlast : ¬on (n - 1)) (f : Nat → F) (i : Fin n) :
    (lineA on n).mulVec (fun x => f x.val) i =
      (if on i.val then f (i.val + 1) else 0) +
      (if 0 < i.val ∧ on (i.val - 1) then f (i.val - 1) else 0) := by
  simp only [Matrix.mulVec, dotProduct, lineA, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul]
  have hi := i.isLt
  have hr :
      (∑ x : Fin n, if on i.val ∧ i.val + 1 = x.val then f x.val else 0)
        = if on i.val then f (i.val + 1) else 0 := by
    by_cases hm : on i.val
    · have hlt : i.val + 1 < n := by
        by_contra! h
        have : i.val = n - 1 := by omega
        exact hlast (this ▸ hm)
      let x : Fin n := ⟨i.val + 1, hlt⟩
      have heq (y : Fin n) : i.val + 1 = y.val ↔ x = y :=
        ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp [hm, heq, x]
    · simp [hm]
  have hl :
      (∑ x : Fin n, if on x.val ∧ x.val + 1 = i.val then f x.val else 0)
        = if 0 < i.val ∧ on (i.val - 1) then f (i.val - 1) else 0 := by
    by_cases hp : 0 < i.val
    · let x : Fin n := ⟨i.val - 1, by omega⟩
      have heq (y : Fin n) : x.val + 1 = i.val := by dsimp [x]; omega
      have heq' (y : Fin n) : y.val + 1 = i.val ↔ y = x := by
        constructor
        · intro h
          apply Fin.ext
          dsimp [x]
          omega
        · rintro rfl
          exact heq x
      simp_rw [heq']
      simp only [hp, true_and]
      by_cases hm : on (i.val - 1)
      · rw [ite_eq_left hm, Fintype.sum_eq_single x]
        · simp [x, hm]
        · intro j hj
          simp [hj]
      · rw [ite_eq_right hm]
        apply Finset.sum_eq_zero
        intro y _
        by_cases he : y = x
        · subst y
          simp [x, hm]
        · simp [he]
    · rw [ite_eq_right (fun h => hp h.1)]
      apply Finset.sum_eq_zero
      intro x _
      have h : ¬x.val + 1 = i.val := by omega
      simp [h]
  rw [hr, hl]

theorem lineGAt_eq_invEntry {i j m : Nat}
    (hi : rel on i < m) (hj : rel on j < m)
    (hs : lineStart on i = lineStart on j) :
    lineGAt on i j = invEntry m (rel on i) (rel on j) := by
  simp [lineGAt, invEntry, hi, hj, hs]

theorem lineA_mul_G_of_keep {n : Nat} (hlast : ¬on (n - 1)) (i : Fin n)
    (hi : lineKeep on i.val) (j : Fin n) :
    (lineA on n * lineG on n) i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  change (lineA on n).mulVec (fun x => lineGAt on x.val j.val) i = _
  rw [lineA_mulVec_eq on hlast (fun x => lineGAt on x j.val) i]
  have hsR (ho : on i.val) : lineStart on (i.val + 1) = lineStart on i.val := by
    simp [lineStart_succ on i.val, ho]
  have hsL (ho : 0 < i.val ∧ on (i.val - 1)) :
      lineStart on (i.val - 1) = lineStart on i.val :=
    lineStart_pred_eq on ho.1 ho.2
  by_cases hs : lineStart on i.val = lineStart on j.val
  · let u := rel on i.val
    let v := rel on j.val
    let m := if on i.val then max (u + 2) (v + 1) else u + 1
    have hm (ho : ¬on i.val) : m = u + 1 := ite_eq_right ho
    have hmo (ho : on i.val) : m = max (u + 2) (v + 1) := ite_eq_left ho
    have hu : u < m := by
      by_cases ho : on i.val
      · rw [hmo ho]
        exact (show u < u + 2 by omega).trans_le (le_max_left _ _)
      · rw [hm ho]
        omega
    have hv : v < m := by
      by_cases ho : on i.val
      · rw [hmo ho]
        exact (show v < v + 1 by omega).trans_le (le_max_right _ _)
      · rw [hm ho]
        have hj := sameStart_le_of_end on ho hs
        dsimp [u, v, rel]
        omega
    have hR : (if on i.val then lineGAt on (i.val + 1) j.val else 0) =
        invEntry m (u + 1) v := by
      by_cases ho : on i.val
      · rw [ite_eq_left ho]
        have hrel : rel on (i.val + 1) = u + 1 := rel_succ on ho
        have hlt : rel on (i.val + 1) < m := by
          rw [hrel, hmo ho]
          exact (show u + 1 < u + 2 by omega).trans_le (le_max_left _ _)
        rw [lineGAt_eq_invEntry on hlt hv ((hsR ho).trans hs), hrel]
      · rw [ite_eq_right ho, hm ho]
        simp [invEntry]
    have hL : (if 0 < i.val ∧ on (i.val - 1) then lineGAt on (i.val - 1) j.val else 0) =
        if 0 < u then invEntry m (u - 1) v else 0 := by
      by_cases ho : 0 < i.val ∧ on (i.val - 1)
      · rw [ite_eq_left ho]
        have hr := rel_pred on ho.1 ho.2
        change rel on (i.val - 1) + 1 = u at hr
        have hlt : rel on (i.val - 1) < m := by omega
        rw [lineGAt_eq_invEntry on hlt hv ((hsL ho).trans hs),
          ite_eq_left (show 0 < u by omega)]
        congr 1
        omega
      · have he : u = 0 := (rel_eq_zero_iff on i.val).mpr ho
        simp [ho, he]
    have hlast' : ¬(u + 1 = m ∧ u % 2 = 0 ∧ v % 2 = 0) := by
      rintro ⟨hboundary, hpar, _⟩
      rcases hi with hmarked | hodd
      · have hle := le_max_left (u + 2) (v + 1)
        rw [hmo hmarked] at hboundary
        omega
      · change u % 2 = 1 at hodd
        omega
    have heq : (u = v) ↔ i = j := by
      rw [Fin.ext_iff]
      have hi' := lineStart_le on i.val
      have hj' := lineStart_le on j.val
      dsimp [u, v, rel]
      omega
    rw [hR, hL, add_comm, invEntry_add_neighbors m u v hu hv,
      ite_eq_right hlast', add_zero]
    simp [heq, Matrix.one_apply]
  · have hneq : i ≠ j := fun h => hs (congrArg (fun x : Fin n => lineStart on x.val) h)
    have hr : (if on i.val then lineGAt on (i.val + 1) j.val else 0) = 0 := by
      by_cases ho : on i.val
      · simp [ho, lineGAt, hsR ho, hs]
      · simp [ho]
    have hl : (if 0 < i.val ∧ on (i.val - 1) then lineGAt on (i.val - 1) j.val else 0) = 0 := by
      by_cases ho : 0 < i.val ∧ on (i.val - 1)
      · simp [ho, lineGAt, hsL ho, hs]
      · simp [ho]
    simp [hr, hl, hneq]

theorem lineKernel {n : Nat} (hlast : ¬on (n - 1)) (p : Fin n)
    (hp : ¬lineKeep on p.val) :
    ∃ v : Fin n → F, (lineA on n).mulVec v = 0 ∧ v p = 1 ∧
      ∀ j : Fin n, ¬lineKeep on j.val → j ≠ p → v j = 0 := by
  let f : Nat → F := fun j =>
    if lineStart on j = lineStart on p.val ∧ rel on j % 2 = 0 then 1 else 0
  have hpout : ¬on p.val := fun h => hp (.inl h)
  have hpar : rel on p.val % 2 = 0 := by
    have h : rel on p.val % 2 ≠ 1 := fun h => hp (.inr h)
    omega
  refine ⟨fun j => f j.val, ?_, by simp [f, hpar], ?_⟩
  · funext j
    change (lineA on n).mulVec (fun x => f x.val) j = 0
    rw [lineA_mulVec_eq on hlast f j]
    have hfR (ho : on j.val) :
        f (j.val + 1) =
          if lineStart on j.val = lineStart on p.val ∧ rel on j.val % 2 = 1
          then 1 else 0 := by
      have he : (rel on j.val + 1) % 2 = 0 ↔ rel on j.val % 2 = 1 := by omega
      simp [f, lineStart_succ on j.val, ho, rel_succ on ho, he]
    have hfL (ho : 0 < j.val ∧ on (j.val - 1)) :
        f (j.val - 1) =
          if lineStart on j.val = lineStart on p.val ∧ rel on j.val % 2 = 1
          then 1 else 0 := by
      have hrel := rel_pred on ho.1 ho.2
      have he : rel on (j.val - 1) % 2 = 0 ↔ rel on j.val % 2 = 1 := by omega
      simp [f, lineStart_pred_eq on ho.1 ho.2, he]
    by_cases hc : lineStart on j.val = lineStart on p.val ∧ rel on j.val % 2 = 1
    · have hin : 0 < j.val ∧ on (j.val - 1) := by
        by_contra hn
        have hz := (rel_eq_zero_iff on j.val).mpr hn
        omega
      have hout : on j.val := by
        by_contra hn
        have hpj := sameStart_le_of_end on hn hc.1
        have hjp := sameStart_le_of_end on hpout hc.1.symm
        have heq : p = j := Fin.ext (by omega)
        rw [heq] at hpar
        omega
      rw [ite_eq_left hout, ite_eq_left hin, hfR hout, hfL hin, ite_eq_left hc]
      decide
    · have hR : (if on j.val then f (j.val + 1) else 0) = 0 := by
        by_cases ho : on j.val
        · rw [ite_eq_left ho, hfR ho, ite_eq_right hc]
        · rw [ite_eq_right ho]
      have hL : (if 0 < j.val ∧ on (j.val - 1) then f (j.val - 1) else 0) = 0 := by
        by_cases ho : 0 < j.val ∧ on (j.val - 1)
        · rw [ite_eq_left ho, hfL ho, ite_eq_right hc]
        · rw [ite_eq_right ho]
      rw [hR, hL, add_zero]
  · intro j hj hne
    have hstart : lineStart on j.val ≠ lineStart on p.val := by
      intro h
      have hjout : ¬on j.val := fun h => hj (.inl h)
      have hpj := sameStart_le_of_end on hjout h
      have hjp := sameStart_le_of_end on hpout h.symm
      exact hne (Fin.ext (by omega))
    simp [f, hstart]

theorem line_rank_and_inverse {n : Nat} (hlast : ¬on (n - 1)) :
    (lineA on n).rank = Fintype.card {i : Fin n // lineKeep on i.val} ∧
      lineA on n * lineG on n * lineA on n = lineA on n := by
  exact rank_and_inverse_of_compression (lineA on n) (lineG on n) (fun i => lineKeep on i.val)
    (lineA_symmetric on n) (lineA_mul_G_of_keep on hlast) (lineKernel on hlast)

def lineMarks (n : Nat) : Finset (Fin n) := Finset.univ.filter (fun i => on i.val)

def lineCanon (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun i => on i.val ∧ rel on i.val % 2 = 0)

omit [DecidablePred on] in theorem successor_val_of_on {n : Nat} (hn : 0 < n) (hlast : ¬on (n - 1))
    {i : Fin n} (hi : on i.val) :
    (successor hn i).val = i.val + 1 := by
  have hlt := i.isLt
  have hlt' : i.val + 1 < n := by
    by_contra hn'
    have he : i.val = n - 1 := by omega
    exact hlast (he ▸ hi)
  exact Nat.mod_eq_of_lt hlt'

theorem lineCanon_independent {n : Nat} (hn : 0 < n) (hlast : ¬on (n - 1)) :
    ∀ i ∈ lineCanon on n, successor hn i ∉ lineCanon on n := by
  intro i hi hj
  simp only [lineCanon, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have h := successor_val_of_on on hn hlast hi.1
  rw [h, rel_succ on hi.1] at hj
  omega

theorem incoming_of_odd {i : Nat} (hi : rel on i % 2 = 1) : 0 < i ∧ on (i - 1) := by
  by_contra h
  have := (rel_eq_zero_iff on i).mpr h
  omega

def chooseCanon {n : Nat} (i : Fin n) : Fin n :=
  ⟨if rel on i.val % 2 = 0 then i.val else i.val - 1, by
    have := i.isLt
    split <;> omega⟩

theorem chooseCanon_mem {n : Nat} {i : Fin n} (hi : on i.val) :
    chooseCanon on i ∈ lineCanon on n := by
  simp only [lineCanon, Finset.mem_filter, Finset.mem_univ, true_and, chooseCanon]
  split
  next he => exact ⟨hi, he⟩
  next he =>
    have ho : rel on i.val % 2 = 1 := by omega
    have hm := incoming_of_odd on ho
    have hs := rel_pred on hm.1 hm.2
    exact ⟨hm.2, by omega⟩

theorem line_selectionMax {n : Nat} (hn : 0 < n) (hlast : ¬on (n - 1)) :
    selectionMax hn (lineMarks on n) = (lineCanon on n).card := by
  apply le_antisymm
  · apply Finset.sup_le
    intro M hM
    obtain ⟨hsub, hind⟩ := Finset.mem_filter.mp hM
    have hm (i : Fin n) (hi : i ∈ M) : on i.val := by
      simpa [lineMarks] using (Finset.mem_powerset.mp hsub) hi
    apply Finset.card_le_card_of_injOn (chooseCanon on)
    · intro i hi
      exact chooseCanon_mem on (hm i hi)
    · intro i hi j hj he
      by_contra hij
      have h₁ := successor_val_of_on on hn hlast (hm i hi)
      have h₂ := successor_val_of_on on hn hlast (hm j hj)
      have he' := congrArg Fin.val he
      simp only [chooseCanon] at he'
      have hne : i.val ≠ j.val := by simpa [Fin.ext_iff] using hij
      have hfit : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
        split_ifs at he' <;> omega
      rcases hfit with hab | hba
      · exact hind i hi ((Fin.ext (h₁.trans hab)).symm ▸ hj)
      · exact hind j hj ((Fin.ext (h₂.trans hba)).symm ▸ hi)
  · have hsub : lineCanon on n ⊆ lineMarks on n := by
      intro i hi
      simp only [lineCanon, lineMarks, Finset.mem_filter, Finset.mem_univ, true_and] at *
      exact hi.1
    apply Finset.le_sup (f := Finset.card)
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, lineCanon_independent on hn hlast⟩

theorem line_keep_card {n : Nat} (hn : 0 < n) (hlast : ¬on (n - 1)) :
    Fintype.card {i : Fin n // lineKeep on i.val} = 2 * (lineCanon on n).card := by
  rw [Fintype.card_subtype]
  let C := lineCanon on n
  have hdisj : Disjoint C (C.image (successor hn)) := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha'
    exact lineCanon_independent on hn hlast i hi ha
  have hsets : Finset.univ.filter (fun i : Fin n => lineKeep on i.val) =
      C ∪ C.image (successor hn) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hkeep
      by_cases he : rel on i.val % 2 = 0
      · left
        have ho : on i.val := hkeep.resolve_right (by omega)
        simp [C, lineCanon, ho, he]
      · right
        have ho : rel on i.val % 2 = 1 := by omega
        have hi := incoming_of_odd on ho
        let j : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hj : on j.val := hi.2
        have hr : rel on j.val + 1 = rel on i.val := rel_pred on hi.1 hi.2
        have heq : successor hn j = i := Fin.ext (by
          rw [successor_val_of_on on hn hlast hj]
          dsimp [j]
          omega)
        exact Finset.mem_image.mpr ⟨j, by simp [C, lineCanon, hj, show rel on j.val % 2 = 0 by omega], heq⟩
    · rintro (hi | hi)
      · left
        exact (by simpa [C, lineCanon] using hi : on i.val ∧ rel on i.val % 2 = 0).1
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        have hj' : on j.val ∧ rel on j.val % 2 = 0 := by simpa [C, lineCanon] using hj
        right
        rw [successor_val_of_on on hn hlast hj'.1, rel_succ on hj'.1]
        omega
  rw [hsets, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective C (successor_injective hn)]
  change C.card + C.card = 2 * C.card
  omega

theorem line_rank_selectionMax {n : Nat} (hn : 0 < n) (hlast : ¬on (n - 1)) :
    (lineA on n).rank = 2 * selectionMax hn (lineMarks on n) := by
  rw [(line_rank_and_inverse on hlast).1, line_keep_card on hn hlast, line_selectionMax on hn hlast]

theorem lineGAt_minmax (i j : Nat) :
    lineGAt on i j =
      if lineStart on (min i j) = lineStart on (max i j) ∧
          (min i j - lineStart on (min i j)) % 2 = 0 ∧
          (max i j - lineStart on (max i j)) % 2 = 1
      then 1 else 0 := by
  by_cases hij : i ≤ j
  · rw [min_eq_left hij, max_eq_right hij]
    by_cases hs : lineStart on i = lineStart on j
    · have hi := lineStart_le on i
      have hj := lineStart_le on j
      simp only [lineGAt, hs, true_and]
      split_ifs <;> simp only [forward, rel] at * <;> omega
    · simp [lineGAt, hs]
  · have hji : j ≤ i := by omega
    rw [min_eq_right hji, max_eq_left hji]
    by_cases hs : lineStart on i = lineStart on j
    · have hi := lineStart_le on i
      have hj := lineStart_le on j
      simp only [lineGAt, hs, true_and]
      split_ifs <;> simp only [forward, rel] at * <;> omega
    · simp [lineGAt, hs, Ne.symm hs]

end Line

section Rotation

def cycleRotate {k : Nat} (hk : 0 < k) (base i : Nat) : Fin k :=
  ⟨(base + i) % k, Nat.mod_lt _ hk⟩

def cycleUnrotate {k : Nat} (hk : 0 < k) (base : Nat) (i : Fin k) : Fin k :=
  ⟨markedPos k base i.val, Nat.mod_lt _ hk⟩

theorem cycleRotate_right_inv {k base : Nat} (hk : 0 < k) (hb : base < k) :
    Function.RightInverse (cycleUnrotate hk base) (fun i : Fin k => cycleRotate hk base i.val) := by
  intro i
  apply Fin.ext
  change (base + (i.val + k - base) % k) % k = i.val
  rw [Nat.add_mod_mod, show base + (i.val + k - base) = i.val + k by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

def cycleRotateEquiv {k base : Nat} (hk : 0 < k) (hb : base < k) : Fin k ≃ Fin k where
  toFun := fun i => cycleRotate hk base i.val
  invFun := cycleUnrotate hk base
  right_inv := cycleRotate_right_inv hk hb
  left_inv := by
    have hr := cycleRotate_right_inv hk hb
    exact hr.leftInverse_of_injective (Finite.injective_iff_surjective.mpr hr.surjective)

theorem cycleRotate_succ {k : Nat} (hk : 0 < k) (base : Nat) (i : Fin k) :
    cycleRotate hk base (successor hk i).val = successor hk (cycleRotate hk base i.val) := by
  apply Fin.ext
  change (base + (i.val + 1) % k) % k = ((base + i.val) % k + 1) % k
  rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem selectionMax_le_of_rotation {k : Nat} (hk : 0 < k) (E E' : Finset (Fin k))
    (e : Fin k ≃ Fin k) (he : ∀ i ∈ E, e i ∈ E')
    (hcomm : ∀ i, e (successor hk i) = successor hk (e i)) :
    selectionMax hk E ≤ selectionMax hk E' := by
  apply Finset.sup_le
  intro M hM
  obtain ⟨hm, hi⟩ := Finset.mem_filter.mp hM
  let N := M.map e.toEmbedding
  have hN' : N ⊆ E' := by
    intro a ha
    obtain ⟨i, h, rfl⟩ := Finset.mem_map.mp ha
    exact he i ((Finset.mem_powerset.mp hm) h)
  have hn : ∀ a ∈ N, successor hk a ∉ N := by
    intro a ha hb
    obtain ⟨i, hii, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hjj, h⟩ := Finset.mem_map.mp hb
    have h' : j = successor hk i := e.injective (h.trans (hcomm i).symm)
    exact hi i hii (h' ▸ hjj)
  have hN : N ∈ E'.powerset.filter (fun M => ∀ i ∈ M, successor hk i ∉ M) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hN', hn⟩
  have hle := Finset.le_sup (f := Finset.card) hN
  simpa [selectionMax, N] using hle

theorem selectionMax_eq_of_rotation {k : Nat} (hk : 0 < k) (E E' : Finset (Fin k))
    (e : Fin k ≃ Fin k) (he : ∀ i, i ∈ E ↔ e i ∈ E')
    (hcomm : ∀ i, e (successor hk i) = successor hk (e i)) :
    selectionMax hk E = selectionMax hk E' := by
  refine le_antisymm (selectionMax_le_of_rotation hk E E' e (fun i => (he i).mp) hcomm) ?_
  apply selectionMax_le_of_rotation hk E' E e.symm
  · intro j hj
    apply (he (e.symm j)).mpr
    simpa using hj
  · intro j
    apply e.injective
    rw [e.apply_symm_apply, hcomm, e.apply_symm_apply]

theorem rotate_last_unmarked {k : Nat} (hk : 0 < k) (E : Finset (Fin k))
    (hE : E ≠ Finset.univ) : cycleRotate hk (markedBase hk E) (k - 1) ∉ E := by
  have hmiss : (Finset.univ \ E).Nonempty := Finset.sdiff_nonempty.mpr
    (fun h => hE (Finset.Subset.antisymm (Finset.subset_univ E) h))
  let i := (Finset.univ \ E).min' hmiss
  have hn : i ∉ E := (Finset.mem_sdiff.mp (Finset.min'_mem _ hmiss)).2
  have hb : markedBase hk E = (successor hk i).val := by
    simp [markedBase, hmiss, i]
  let last : Fin k := ⟨k - 1, by omega⟩
  have hl : (successor hk last).val = 0 := by
    change (k - 1 + 1) % k = 0
    rw [show k - 1 + 1 = k by omega, Nat.mod_self]
  have he : successor hk (cycleRotate hk (markedBase hk E) last.val) = successor hk i := by
    rw [← cycleRotate_succ, hl]
    apply Fin.ext
    change (markedBase hk E + 0) % k = (successor hk i).val
    rw [Nat.add_zero, Nat.mod_eq_of_lt (markedBase_lt hk E), hb]
  exact (successor_injective hk he).symm ▸ hn

theorem proper_marked_rank_and_inverse {k : Nat} (hk : 0 < k) (E : Finset (Fin k))
    (hE : E ≠ Finset.univ) :
    (markedA hk E).rank = 2 * selectionMax hk E ∧
      markedA hk E * markedG hk E * markedA hk E = markedA hk E := by
  let base := markedBase hk E
  let e := cycleRotateEquiv hk (markedBase_lt hk E)
  let on := fun u : Nat => cycleRotate hk base u ∈ E
  let : DecidablePred on := fun _ => inferInstanceAs (Decidable (_ ∈ E))
  have hlast : ¬on (k - 1) := rotate_last_unmarked hk E hE
  have hcomm (i : Fin k) : e (successor hk i) = successor hk (e i) := cycleRotate_succ hk base i
  have hA : (markedA hk E).submatrix e e = lineA on k := by
    ext i j
    have h (a b : Fin k) : e a ∈ E ∧ successor hk (e a) = e b ↔ on a.val ∧ a.val + 1 = b.val := by
      change on a.val ∧ successor hk (e a) = e b ↔ _
      rw [← hcomm a, e.injective.eq_iff, and_congr_right_iff]
      intro hoa
      rw [Fin.ext_iff, successor_val_of_on on hk hlast hoa]
    simp only [Matrix.submatrix_apply, markedA, lineA, h]
  have hG : (markedG hk E).submatrix e e = lineG on k := by
    ext i j
    have hpos (a : Fin k) : markedPos k (markedBase hk E) (e a).val = a.val :=
      congrArg Fin.val (e.symm_apply_apply a)
    have hmax : max i.val j.val < k := max_lt_iff.mpr ⟨i.isLt, j.isLt⟩
    have hstart (u : Nat) : markedStart hk E (markedBase hk E) u = lineStart on u := rfl
    change markedG hk E (e i) (e j) = lineG on k i j
    simp only [markedG, hE, ite_false, hpos, hmax, true_and, hstart, lineG, lineGAt_minmax]
  constructor
  · calc
      (markedA hk E).rank = ((markedA hk E).submatrix e e).rank := (Matrix.rank_submatrix _ e e).symm
      _ = 2 * selectionMax hk (lineMarks on k) := hA ▸ line_rank_selectionMax on hk hlast
      _ = 2 * selectionMax hk E := congrArg (fun z => 2 * z)
        (selectionMax_eq_of_rotation hk (lineMarks on k) E e (fun i => by
          change i ∈ (Finset.univ.filter fun i : Fin k => on i.val) ↔ on i.val
          simp) hcomm)
  · apply Matrix.submatrix_injective e.surjective e.surjective
    change (markedA hk E * markedG hk E * markedA hk E).submatrix e e = (markedA hk E).submatrix e e
    rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e, hA, hG]
    exact (line_rank_and_inverse on hlast).2

end Rotation

end PEqualNP.Outside.L_meta_33655_aux.Paths

namespace PEqualNP.Outside.L_meta_33655_aux.Mixer
private def kernelIx {k : ℕ} (hk : 0 < k) (a : ℕ) : Fin k :=
  ⟨a % k, Nat.mod_lt a hk⟩

private lemma kernelIx_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    kernelIx hk ((kernelIx hk a).val + b) = kernelIx hk (a + b) :=
  Fin.ext (Nat.mod_add_mod ..)

private lemma kernelIx_self {k : ℕ} (hk : 0 < k) (j : Fin k) :
    kernelIx hk j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)

private lemma kernelIx_forward_back {k : ℕ} (hk : 0 < k) (j : Fin k) (s : ℕ) :
    kernelIx hk ((kernelIx hk (j.val + s)).val + k - s % k) = j := by
  have hlt := Nat.mod_lt s hk
  have hdiv := Nat.mod_add_div s k
  have heq : j.val + s + (k - s % k) = j.val + ((s / k + 1) * k) := by
    rw [Nat.add_mul, one_mul, mul_comm (s / k) k]
    omega
  apply Fin.ext
  change (((j.val + s) % k + k - s % k) % k) = j.val
  rw [show (j.val + s) % k + k - s % k = (j.val + s) % k + (k - s % k) by omega,
    Nat.mod_add_mod, heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]

private lemma kernelIx_back_forward {k : ℕ} (hk : 0 < k) (j : Fin k) (s : ℕ) :
    kernelIx hk ((kernelIx hk (j.val + k - s % k)).val + s) = j := by
  have hlt := Nat.mod_lt s hk
  have hdiv := Nat.mod_add_div s k
  have heq : j.val + k - s % k + s = j.val + ((s / k + 1) * k) := by
    rw [Nat.add_mul, one_mul, mul_comm (s / k) k]
    omega
  apply Fin.ext
  change (((j.val + k - s % k) % k + s) % k) = j.val
  rw [Nat.mod_add_mod, heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]

private def kernelMixer {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x j := x j + x (kernelIx hk (j.val + s)) + x (kernelIx hk (j.val + k - s % k))
  map_add' _ _ := by funext j; dsimp only [Pi.add_apply]; ring
  map_smul' _ _ := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private lemma kernelMixer_mem {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) :
    x ∈ (kernelMixer hk s).ker ↔
      ∀ j : Fin k, x j + x (kernelIx hk (j.val + s)) + x (kernelIx hk (j.val + 2 * s)) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j
    have hh := congrFun h (kernelIx hk (j.val + s))
    change x (kernelIx hk (j.val + s)) + x (kernelIx hk ((kernelIx hk (j.val + s)).val + s)) +
      x (kernelIx hk ((kernelIx hk (j.val + s)).val + k - s % k)) = 0 at hh
    rw [kernelIx_add, kernelIx_forward_back, show j.val + s + s = j.val + 2 * s by omega] at hh
    simpa only [add_comm, add_left_comm, add_assoc] using hh
  · intro h
    funext j
    let b := kernelIx hk (j.val + k - s % k)
    have hh := h b
    have hb : kernelIx hk (b.val + s) = j := kernelIx_back_forward hk j s
    have hb₂ : kernelIx hk (b.val + 2 * s) = kernelIx hk (j.val + s) := by
      rw [show b.val + 2 * s = b.val + s + s by omega, ← kernelIx_add, hb]
    rw [hb, hb₂] at hh
    change x j + x (kernelIx hk (j.val + s)) + x b = 0
    simpa only [add_comm, add_left_comm, add_assoc] using hh

private lemma kernelOrbit_injective {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Function.Injective (fun p : Fin (Nat.gcd k s) × Fin (k / Nat.gcd k s) =>
      kernelIx hk (p.1.val + p.2.val * s)) := by
  rintro ⟨r, i⟩ ⟨t, j⟩ h
  have hh : r.val + i.val * s ≡ t.val + j.val * s [MOD k] := congrArg Fin.val h
  have hr := hh.of_dvd (Nat.gcd_dvd_left k s)
  have hs : s ≡ 0 [MOD Nat.gcd k s] := Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_right k s)
  have hr' : r.val ≡ t.val [MOD Nat.gcd k s] := by
    have hri : r.val + i.val * s ≡ r.val [MOD Nat.gcd k s] := by
      simpa using (hs.mul_left i.val).add_left r.val
    have htj : t.val + j.val * s ≡ t.val [MOD Nat.gcd k s] := by
      simpa using (hs.mul_left j.val).add_left t.val
    exact hri.symm.trans (hr.trans htj)
  have hrt : r = t := Fin.ext (hr'.eq_of_lt_of_lt r.isLt t.isLt)
  subst t
  have hij := (hh.add_left_cancel' r.val).cancel_right_div_gcd hk
  have hij' : i = j := Fin.ext (hij.eq_of_lt_of_lt i.isLt j.isLt)
  subst j
  rfl

private noncomputable def kernelOrbit {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Fin (Nat.gcd k s) × Fin (k / Nat.gcd k s) ≃ Fin k :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨kernelOrbit_injective hk s, by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm (Nat.gcd k s)]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left k s)⟩)

private lemma kernelOrbit_nat {k : ℕ} (hk : 0 < k) (s : ℕ)
    (hn : 0 < k / Nat.gcd k s) (r : Fin (Nat.gcd k s)) (m : ℕ) :
    kernelOrbit hk s (r, kernelIx hn m) = kernelIx hk (r.val + m * s) := by
  let n := k / Nat.gcd k s
  have hmul : k ∣ n * s := by
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right k s
    refine ⟨t, ?_⟩
    rw [ht, ← Nat.mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left k s)]
  have hmod : (m % n) * s ≡ m * s [MOD k] :=
    ((Nat.mod_modEq m n).mul_right' s).of_dvd hmul
  apply Fin.ext
  change (r.val + (m % n) * s) % k = (r.val + m * s) % k
  exact hmod.add_left r.val

private lemma kernelMixer_cycles {k : ℕ} (hk : 0 < k) (s : ℕ)
    (hn : 0 < k / Nat.gcd k s) (x : Fin k → ZMod 2) :
    x ∈ (kernelMixer hk s).ker ↔
      ∀ (r : Fin (Nat.gcd k s)) (m : ℕ),
        x (kernelOrbit hk s (r, kernelIx hn m)) +
          x (kernelOrbit hk s (r, kernelIx hn (m + 1))) +
          x (kernelOrbit hk s (r, kernelIx hn (m + 2))) = 0 := by
  rw [kernelMixer_mem]
  have h₁ (r : Fin (Nat.gcd k s)) (m : ℕ) :
      kernelOrbit hk s (r, kernelIx hn (m + 1)) =
        kernelIx hk ((kernelOrbit hk s (r, kernelIx hn m)).val + s) := by
    rw [kernelOrbit_nat, kernelOrbit_nat, kernelIx_add]
    congr 1
    ring
  have h₂ (r : Fin (Nat.gcd k s)) (m : ℕ) :
      kernelOrbit hk s (r, kernelIx hn (m + 2)) =
        kernelIx hk ((kernelOrbit hk s (r, kernelIx hn m)).val + 2 * s) := by
    rw [kernelOrbit_nat, kernelOrbit_nat, kernelIx_add]
    congr 1
    ring
  constructor
  · intro h r m
    rw [h₁, h₂]
    exact h _
  · intro h j
    obtain ⟨⟨r, m⟩, rfl⟩ := (kernelOrbit hk s).surjective j
    specialize h r m.val
    rw [h₁, h₂, kernelIx_self] at h
    exact h

private lemma kernelBit_add_self (a : ZMod 2) : a + a = 0 := by
  have ha : a = 0 ∨ a = 1 := by
    rcases a with ⟨a, ha⟩
    interval_cases a
    · left; rfl
    · right; rfl
  rcases ha with rfl | rfl <;> decide

private def kernelPattern (v : ZMod 2 × ZMod 2) (m : ℕ) : ZMod 2 :=
  if m % 3 = 0 then v.1 else if m % 3 = 1 then v.2 else v.1 + v.2

private lemma kernelPattern_triple (v : ZMod 2 × ZMod 2) (m : ℕ) :
    kernelPattern v m + kernelPattern v (m + 1) + kernelPattern v (m + 2) = 0 := by
  have hz : v.1 + v.2 + (v.1 + v.2) = 0 := kernelBit_add_self _
  have h₁ : (m + 1) % 3 = (m % 3 + 1) % 3 := by omega
  have h₂ : (m + 2) % 3 = (m % 3 + 2) % 3 := by omega
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;>
    rw [hm] at h₁ h₂ <;>
    simp only [kernelPattern, hm, h₁, h₂] <;> norm_num <;>
    simpa only [add_comm, add_left_comm, add_assoc] using hz

private lemma kernelPattern_of_recurrence (f : ℕ → ZMod 2)
    (h : ∀ m, f m + f (m + 1) + f (m + 2) = 0) (m : ℕ) :
    f m = kernelPattern (f 0, f 1) m := by
  have hstep (a : ℕ) : f (a + 3) = f a := by
    have h₁ := h a
    have h₂ : f (a + 1) + f (a + 2) + f (a + 3) = 0 := h (a + 1)
    linear_combination h₂ - h₁
  have hmod : f m = f (m % 3) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm : m < 3
      · rw [Nat.mod_eq_of_lt hm]
      calc
        f m = f (m - 3) := by
          have hEq : m - 3 + 3 = m := by omega
          simpa only [hEq] using hstep (m - 3)
        _ = f ((m - 3) % 3) := ih _ (by omega)
        _ = f (m % 3) := by congr 1; omega
  have htwo : f 2 = f 0 + f 1 := by
    have hzero : f 0 + f 1 + f 2 = 0 := h 0
    have hself := kernelBit_add_self (f 0 + f 1)
    linear_combination hzero - hself
  rw [hmod]
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> simp [kernelPattern, hm, htwo]

private lemma kernelPattern_zero_of_period (f : ℕ → ZMod 2) {n : ℕ}
    (h : ∀ m, f m + f (m + 1) + f (m + 2) = 0)
    (hp : ∀ m, f (n + m) = f m) (hn : ¬ 3 ∣ n) (m : ℕ) : f m = 0 := by
  have hn' : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have h₀ := (kernelPattern_of_recurrence f h (n + 0)).symm.trans (hp 0)
  have h₁ := (kernelPattern_of_recurrence f h (n + 1)).symm.trans (hp 1)
  have hab : f 0 = 0 ∧ f 1 = 0 := by
    rcases hn' with hn' | hn'
    · have hn₁ : (n + 1) % 3 = 2 := by omega
      simp [kernelPattern, hn'] at h₀
      simp [kernelPattern, hn₁] at h₁
      exact ⟨h₁, h₀.trans h₁⟩
    · have hn₁ : (n + 1) % 3 = 0 := by omega
      simp [kernelPattern, hn'] at h₀
      simp [kernelPattern, hn₁] at h₁
      exact ⟨h₁.trans h₀, h₀⟩
  rw [kernelPattern_of_recurrence f h m]
  simp [kernelPattern, hab.1, hab.2]

private theorem kernelMixer_card {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Nat.card (kernelMixer hk s).ker = 2 ^ (if 3 ∣ k / Nat.gcd k s then 2 * Nat.gcd k s else 0) := by
  classical
  let g := Nat.gcd k s
  let n := k / g
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh : n * g = k := Nat.div_mul_cancel (Nat.gcd_dvd_left k s)
    rw [hz, zero_mul] at hh
    exact (Nat.ne_of_gt hk) hh.symm
  let e := kernelOrbit hk s
  by_cases h3 : 3 ∣ n
  · rw [ite_eq_left h3]
    let encode : (kernelMixer hk s).ker → (Fin g → ZMod 2 × ZMod 2) :=
      fun x r => (x.val (e (r, kernelIx hn 0)), x.val (e (r, kernelIx hn 1)))
    have value (x : (kernelMixer hk s).ker) (r : Fin g) (m : ℕ) :
        x.val (e (r, kernelIx hn m)) = kernelPattern (encode x r) m :=
      kernelPattern_of_recurrence _ ((kernelMixer_cycles hk s hn x.val).mp x.property r) m
    have hinj : Function.Injective encode := by
      intro x y hxy
      apply Subtype.ext
      funext j
      obtain ⟨⟨r, m⟩, rfl⟩ := e.surjective j
      rw [← kernelIx_self hn m, value, value, hxy]
    have hsurj : Function.Surjective encode := by
      intro v
      let x : Fin k → ZMod 2 := fun j => kernelPattern (v (e.symm j).1) (e.symm j).2.val
      have hx (r : Fin g) (m : ℕ) : x (e (r, kernelIx hn m)) = kernelPattern (v r) m := by
        dsimp only [x]
        rw [e.symm_apply_apply]
        change kernelPattern (v r) (m % n) = kernelPattern (v r) m
        have hm : (m % n) % 3 = m % 3 := (Nat.mod_modEq m n).of_dvd h3
        simp [kernelPattern, hm]
      have hxker : x ∈ (kernelMixer hk s).ker := by
        apply (kernelMixer_cycles hk s hn x).mpr
        intro r m
        rw [hx, hx, hx]
        exact kernelPattern_triple (v r) m
      refine ⟨⟨x, hxker⟩, ?_⟩
      funext r
      change (x (e (r, kernelIx hn 0)), x (e (r, kernelIx hn 1))) = v r
      rw [hx, hx]
      simp [kernelPattern]
    rw [Nat.card_congr (Equiv.ofBijective encode ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, ZMod.card]
    rw [pow_mul]
    rfl
  · rw [ite_eq_right h3, pow_zero]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨0, ?_⟩
    intro x
    apply Subtype.ext
    funext j
    obtain ⟨⟨r, m⟩, rfl⟩ := e.surjective j
    rw [← kernelIx_self hn m]
    let f : ℕ → ZMod 2 := fun a => x.val (e (r, kernelIx hn a))
    have hf := (kernelMixer_cycles hk s hn x.val).mp x.property r
    have hp (a : ℕ) : f (n + a) = f a := by
      have hm : (n + a) % n = a % n := by simp
      exact congrArg (fun i => x.val (e (r, i))) (Fin.ext hm)
    exact kernelPattern_zero_of_period f hf hp h3 m.val

private def kernelWord {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin (Nat.gcd k s) → ZMod 2 × ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun v i :=
    kernelPattern (v (kernelIx (Nat.gcd_pos_of_pos_left s hk) i.val)) (i.val / Nat.gcd k s)
  map_add' v w := by
    funext i
    dsimp only [kernelPattern, Pi.add_apply, Prod.fst_add, Prod.snd_add]
    split
    · rfl
    · split
      · rfl
      · ring
  map_smul' c v := by
    funext i
    dsimp only [kernelPattern, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
      smul_eq_mul]
    split
    · rfl
    · split
      · rfl
      · ring

private lemma kernelWord_div_phase {k g : ℕ} (hg : g ∣ k)
    (h3 : 3 ∣ k / g) (n : ℕ) :
    (n % k / g) % 3 = (n / g) % 3 := by
  have hk : g * (k / g) = k := Nat.mul_div_cancel' hg
  have hm := Nat.mod_mul_right_div_self n g (k / g)
  rw [hk] at hm
  rw [hm]
  exact (Nat.mod_modEq (n / g) (k / g)).of_dvd h3

private lemma kernelPattern_stride_triple (v : ZMod 2 × ZMod 2) (a d : ℕ)
    (hd : ¬ 3 ∣ d) :
    kernelPattern v a + kernelPattern v (a+d) + kernelPattern v (a+2*d) = 0 := by
  have h₁ : (a + d) % 3 = (a % 3 + d % 3) % 3 := Nat.add_mod _ _ _
  have h₂ : (a + 2*d) % 3 = (a % 3 + 2*(d % 3)) % 3 := by omega
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hd' : d % 3 = 1 ∨ d % 3 = 2 := by omega
  have hz : v.1 + v.2 + (v.1 + v.2) = 0 := kernelBit_add_self _
  rcases ha with ha | ha | ha <;> rcases hd' with hd' | hd' <;>
    rw [ha, hd'] at h₁ h₂ <;>
    simp only [kernelPattern, ha, h₁, h₂] <;> norm_num <;>
    simpa only [add_comm, add_left_comm, add_assoc] using hz

private lemma kernelWord_mem {k : ℕ} (hk : 0 < k) (s : ℕ)
    (h3 : 3 ∣ k / Nat.gcd k s) (v : Fin (Nat.gcd k s) → ZMod 2 × ZMod 2) :
    kernelWord hk s v ∈ (kernelMixer hk s).ker := by
  let g := Nat.gcd k s
  let d := s / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left s hk
  have hkg : g ∣ k := Nat.gcd_dvd_left k s
  have hsg : g * d = s := Nat.mul_div_cancel' (Nat.gcd_dvd_right k s)
  have hc : Nat.Coprime (k/g) d := Nat.coprime_div_gcd_div_gcd hg
  have hd : ¬ 3 ∣ d := by
    intro h
    have hg' : 3 ∣ Nat.gcd (k/g) d := Nat.dvd_gcd h3 h
    rw [hc.gcd_eq_one] at hg'
    norm_num at hg'
  apply (kernelMixer_mem hk s _).mpr
  intro j
  let r := v (kernelIx hg j.val)
  have hpoint (m : ℕ) :
      kernelWord hk s v (kernelIx hk (j.val + m*s)) =
        kernelPattern r (j.val/g + m*d) := by
    change kernelPattern (v (kernelIx hg ((j.val + m*s) % k))) ((j.val + m*s) % k / g) = _
    have hr : ((j.val + m*s) % k) % g = j.val % g := by
      have hmod := (Nat.mod_modEq (j.val + m*s) k).of_dvd hkg
      change ((j.val + m*s) % k) % g = (j.val + m*s) % g at hmod
      rw [hmod, ← hsg, show m * (g * d) = (m*d)*g by ring, Nat.add_mul_mod_self_right]
    have hp := kernelWord_div_phase hkg h3 (j.val + m*s)
    have he : (j.val + m*s) / g = j.val/g + m*d := by
      rw [← hsg, show m * (g * d) = (m*d)*g by ring, Nat.add_mul_div_right _ _ hg]
    have hj : kernelIx hg ((j.val + m*s) % k) = kernelIx hg j.val := Fin.ext hr
    rw [hj, kernelPattern, kernelPattern, hp, he]
  have h0 := hpoint 0
  have h1 := hpoint 1
  have h2 := hpoint 2
  simp only [zero_mul, add_zero, kernelIx_self] at h0
  simp only [one_mul] at h1
  rw [h0, h1, h2]
  exact kernelPattern_stride_triple r _ d hd

private lemma kernelWord_injective {k : ℕ} (hk : 0 < k) (s : ℕ)
    (h3 : 3 ∣ k / Nat.gcd k s) : Function.Injective (kernelWord hk s) := by
  let g := Nat.gcd k s
  have hg : 0 < g := Nat.gcd_pos_of_pos_left s hk
  have hkq : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k s)
  have hq : 3 ≤ k / g := by
    rcases h3 with ⟨n, h⟩
    change k / g = 3*n at h
    have hn : n ≠ 0 := by
      intro he
      rw [he, mul_zero] at h
      rw [h, mul_zero] at hkq
      omega
    omega
  have h2g : 2*g ≤ k := calc
    2*g ≤ g * (k/g) := by rw [mul_comm 2 g]; exact Nat.mul_le_mul_left g (by omega)
    _ = k := hkq
  intro v w h
  funext r
  let i₀ : Fin k := ⟨r.val, by have := r.isLt; change r.val < g at this; omega⟩
  let i₁ : Fin k := ⟨r.val+g, by have := r.isLt; change r.val < g at this; omega⟩
  have hdiv₀ : r.val / g = 0 := Nat.div_eq_of_lt r.isLt
  have hdiv₁ : (r.val + g) / g = 1 := by
    simpa [hdiv₀] using Nat.add_mul_div_left r.val 1 hg
  have hi₀ : kernelIx hg i₀.val = r := kernelIx_self hg r
  have hi₁ : kernelIx hg i₁.val = r := by
    apply Fin.ext
    change (r.val + g) % g = r.val
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
  apply Prod.ext
  · have h₀ := congrFun h i₀
    change kernelPattern (v (kernelIx hg i₀.val)) (r.val/g) =
      kernelPattern (w (kernelIx hg i₀.val)) (r.val/g) at h₀
    simpa [hi₀, hdiv₀, kernelPattern] using h₀
  · have h₁ := congrFun h i₁
    change kernelPattern (v (kernelIx hg i₁.val)) ((r.val+g)/g) =
      kernelPattern (w (kernelIx hg i₁.val)) ((r.val+g)/g) at h₁
    simpa [hi₁, hdiv₁, kernelPattern] using h₁

private noncomputable def kernelWordEquiv {k : ℕ} (hk : 0 < k) (s : ℕ)
    (h3 : 3 ∣ k / Nat.gcd k s) :
    (Fin (Nat.gcd k s) → ZMod 2 × ZMod 2) ≃ₗ[ZMod 2] (kernelMixer hk s).ker := by
  classical
  let lin := (kernelWord hk s).codRestrict (kernelMixer hk s).ker (kernelWord_mem hk s h3)
  have hi : Function.Injective lin := fun _ _ h =>
    kernelWord_injective hk s h3 (congrArg Subtype.val h)
  apply LinearEquiv.ofBijective lin
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, ?_⟩
  rw [← Nat.card_eq_fintype_card (α := (kernelMixer hk s).ker), kernelMixer_card hk s,
    ite_eq_left h3, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, ZMod.card, pow_mul]
  rfl

private lemma kernelWordEquiv_apply {k : ℕ} (hk : 0 < k) (s : ℕ)
    (h3 : 3 ∣ k / Nat.gcd k s) (v : Fin (Nat.gcd k s) → ZMod 2 × ZMod 2) :
    (kernelWordEquiv hk s h3 v).val = kernelWord hk s v := rfl

private lemma kernelMixer_ker_eq_bot {k : ℕ} (hk : 0 < k) (s : ℕ)
    (h3 : ¬ 3 ∣ k / Nat.gcd k s) : (kernelMixer hk s).ker = ⊥ := by
  have h := kernelMixer_card hk s
  rw [ite_eq_right h3, pow_zero] at h
  have hsub := (Nat.card_eq_one_iff_unique.mp h).1
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  exact
    congrArg Subtype.val (@Subsingleton.elim _ hsub (⟨x, hx⟩ : (kernelMixer hk s).ker) 0)



private lemma kernelMixer_dot_eq {k : ℕ} (hk : 0 < k) (s : ℕ)
    (x y : Fin k → ZMod 2) :
    dotProduct (kernelMixer hk s x) y = dotProduct x (kernelMixer hk s y) := by
  let e : Fin k ≃ Fin k :=
    { toFun := fun i => kernelIx hk (i.val+s)
      invFun := fun i => kernelIx hk (i.val+k-s%k)
      left_inv := fun i => kernelIx_forward_back hk i s
      right_inv := fun i => kernelIx_back_forward hk i s }
  have hf : (∑ i : Fin k, x (e i) * y i) = ∑ j : Fin k, x j * y (e.symm j) :=
    Fintype.sum_equiv e _ _ (fun i => by rw [e.symm_apply_apply])
  have hb : (∑ i : Fin k, x (e.symm i) * y i) = ∑ j : Fin k, x j * y (e j) :=
    Fintype.sum_equiv e.symm _ _ (fun i => by rw [e.apply_symm_apply])
  change (∑ i : Fin k, (x i + x (e i) + x (e.symm i)) * y i) =
    ∑ j : Fin k, x j * (y j + y (e j) + y (e.symm j))
  simp only [add_mul, mul_add, Finset.sum_add_distrib, hf, hb]
  ac_rfl
private def mixerPathEntry (a b : ℕ) : ZMod 2 :=
  if min a b % 2 = 0 ∧ max a b % 2 = 1 then 1 else 0

private def mixerMatchEntry (a b : ℕ) : ZMod 2 :=
  if a / 2 = b / 2 ∧ a % 2 ≠ b % 2 then 1 else 0

private def mixerAlt (u v : ZMod 2 × ZMod 2) : ZMod 2 :=
  u.1 * v.2 + u.2 * v.1

private lemma pattern_period_six (v : ZMod 2 × ZMod 2) (a i : ℕ) :
    kernelPattern v (i + 6*a) = kernelPattern v i := by
  have h : (i + 6*a) % 3 = i % 3 := by omega
  simp [kernelPattern, h]

private def mixerParity (p : ℕ) (v : ZMod 2 × ZMod 2) (i : Fin 6) : ZMod 2 :=
  if i.val % 2 = p then kernelPattern v i.val else 0

private lemma mixerParity_sum_zero (p : ℕ) (v : ZMod 2 × ZMod 2)
    (hp : p = 0 ∨ p = 1) : ∑ i : Fin 6, mixerParity p v i = 0 := by
  rcases v with ⟨a,b⟩
  rcases hp with rfl | rfl <;> fin_cases a <;> fin_cases b <;> decide

private lemma mixerPath_local (u v : ZMod 2 × ZMod 2) :
    (∑ i : Fin 6, ∑ j : Fin 6,
        mixerPathEntry i.val j.val * kernelPattern u j.val * kernelPattern v i.val) = 0 := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private lemma mixerMatch_local (u v : ZMod 2 × ZMod 2) :
    (∑ i : Fin 6, ∑ j : Fin 6,
        mixerMatchEntry i.val j.val * kernelPattern u j.val * kernelPattern v i.val) =
      mixerAlt u v := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private lemma mixerPath_block (u v : ZMod 2 × ZMod 2) (a b : ℕ) :
    (∑ i : Fin 6, ∑ j : Fin 6, mixerPathEntry (i.val+6*a) (j.val+6*b) *
        kernelPattern u j.val * kernelPattern v i.val) = 0 := by
  rcases lt_trichotomy a b with h | rfl | h
  · have hf (i j : Fin 6) :
        mixerPathEntry (i.val+6*a) (j.val+6*b) * kernelPattern u j.val *
          kernelPattern v i.val = mixerParity 0 v i * mixerParity 1 u j := by
      have hle : i.val+6*a ≤ j.val+6*b := by have := i.isLt; omega
      have hi : (i.val+6*a)%2 = i.val % 2 := by omega
      have hj : (j.val+6*b)%2 = j.val % 2 := by omega
      simp only [mixerPathEntry, min_eq_left hle, max_eq_right hle, hi, hj, mixerParity]
      by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 1 <;>
        simp [hi, hj, mul_comm]
    simp_rw [hf, ← Finset.mul_sum, mixerParity_sum_zero 1 u (Or.inr rfl), mul_zero,
      Finset.sum_const_zero]
  · have hf (i j : Fin 6) :
        mixerPathEntry (i.val+6*a) (j.val+6*a) = mixerPathEntry i.val j.val := by
      unfold mixerPathEntry
      have hm : min (i.val+6*a) (j.val+6*a) = min i.val j.val + 6*a := by omega
      have hM : max (i.val+6*a) (j.val+6*a) = max i.val j.val + 6*a := by omega
      have hi : (min i.val j.val+6*a)%2 = min i.val j.val % 2 := by omega
      have hj : (max i.val j.val+6*a)%2 = max i.val j.val % 2 := by omega
      rw [hm,hM,hi,hj]
    simp_rw [hf]
    exact mixerPath_local u v
  · have hf (i j : Fin 6) :
        mixerPathEntry (i.val+6*a) (j.val+6*b) * kernelPattern u j.val *
          kernelPattern v i.val = mixerParity 1 v i * mixerParity 0 u j := by
      have hle : j.val+6*b ≤ i.val+6*a := by have := j.isLt; omega
      have hi : (i.val+6*a)%2 = i.val % 2 := by omega
      have hj : (j.val+6*b)%2 = j.val % 2 := by omega
      simp only [mixerPathEntry, min_eq_right hle, max_eq_left hle, hi, hj, mixerParity]
      by_cases hi : i.val % 2 = 1 <;> by_cases hj : j.val % 2 = 0 <;>
        simp [hi, hj, mul_comm]
    simp_rw [hf, ← Finset.mul_sum, mixerParity_sum_zero 0 u (Or.inl rfl), mul_zero,
      Finset.sum_const_zero]

private lemma mixerMatch_block (u v : ZMod 2 × ZMod 2) (a b : ℕ) :
    (∑ i : Fin 6, ∑ j : Fin 6, mixerMatchEntry (i.val+6*a) (j.val+6*b) *
        kernelPattern u j.val * kernelPattern v i.val) =
      if a = b then mixerAlt u v else 0 := by
  by_cases hab : a = b
  · subst b
    have hf (i j : Fin 6) :
        mixerMatchEntry (i.val+6*a) (j.val+6*a) = mixerMatchEntry i.val j.val := by
      unfold mixerMatchEntry
      have hi : (i.val+6*a)%2 = i.val % 2 := by omega
      have hj : (j.val+6*a)%2 = j.val % 2 := by omega
      have hdiv : (i.val+6*a)/2 = (j.val+6*a)/2 ↔ i.val/2 = j.val/2 := by omega
      simp only [hi,hj,hdiv]
    simp only [hf]
    exact mixerMatch_local u v
  · have hf (i j : Fin 6) :
        mixerMatchEntry (i.val+6*a) (j.val+6*b) = 0 := by
      have hdiv : (i.val+6*a)/2 ≠ (j.val+6*b)/2 := by
        have := i.isLt
        have := j.isLt
        omega
      simp [mixerMatchEntry, hdiv]
    simp [hf, hab]

private lemma mixerPair_by_blocks {k : ℕ} (h6 : 6 ∣ k) (G : Matrix (Fin k) (Fin k) (ZMod 2))
    (entry : ℕ → ℕ → ZMod 2) (hG : ∀ i j, G i j = entry i.val j.val)
    (u v : ZMod 2 × ZMod 2) :
    dotProduct (G.mulVec (fun i => kernelPattern u i.val)) (fun i => kernelPattern v i.val) =
      ∑ a : Fin (k/6), ∑ b : Fin (k/6), ∑ i : Fin 6, ∑ j : Fin 6,
        entry (i.val+6*a.val) (j.val+6*b.val) * kernelPattern u j.val * kernelPattern v i.val := by
  let e : Fin (k/6) × Fin 6 ≃ Fin k :=
    finProdFinEquiv.trans (finCongr (Nat.div_mul_cancel h6))
  have he (a : Fin (k/6)) (i : Fin 6) : (e (a,i)).val = i.val + 6*a.val := rfl
  have reindex (f : Fin k → ZMod 2) :
      (∑ i : Fin k, f i) = ∑ a : Fin (k/6), ∑ i : Fin 6, f (e (a,i)) := by
    calc
      (∑ i : Fin k, f i) = ∑ p : Fin (k/6) × Fin 6, f (e p) := (e.sum_comp f).symm
      _ = _ := Fintype.sum_prod_type (fun p => f (e p))
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, hG]
  rw [reindex]
  simp_rw [reindex, he, pattern_period_six]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

private lemma mixerPath_pair {k : ℕ} (h6 : 6 ∣ k) (G : Matrix (Fin k) (Fin k) (ZMod 2))
    (hG : ∀ i j, G i j = mixerPathEntry i.val j.val) (u v : ZMod 2 × ZMod 2) :
    dotProduct (G.mulVec (fun i => kernelPattern u i.val)) (fun i => kernelPattern v i.val) = 0 := by
  rw [mixerPair_by_blocks h6 G _ hG]
  simp only [mixerPath_block, Finset.sum_const_zero]

private lemma mixerMatch_pair {k : ℕ} (h6 : 6 ∣ k) (G : Matrix (Fin k) (Fin k) (ZMod 2))
    (hG : ∀ i j, G i j = mixerMatchEntry i.val j.val) (u v : ZMod 2 × ZMod 2) :
    dotProduct (G.mulVec (fun i => kernelPattern u i.val)) (fun i => kernelPattern v i.val) =
      (↑(k/6) : ZMod 2) * mixerAlt u v := by
  rw [mixerPair_by_blocks h6 G _ hG]
  simp only [mixerMatch_block, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma kernelWord_of_coprime {k : ℕ} (hk : 0 < k) (s : ℕ)
    (hc : Nat.Coprime k s) (u : Fin (Nat.gcd k s) → ZMod 2 × ZMod 2) :
    kernelWord hk s u = fun i => kernelPattern (u ⟨0,Nat.gcd_pos_of_pos_left s hk⟩) i.val := by
  funext i
  let h := Nat.gcd_pos_of_pos_left s hk
  have hi : kernelIx h i.val = ⟨0,h⟩ := Fin.ext (by
    change i.val % Nat.gcd k s = 0
    simp [hc.gcd_eq_one, Nat.mod_one])
  have hdiv : i.val / Nat.gcd k s = i.val := by simp [hc.gcd_eq_one]
  change kernelPattern (u (kernelIx h i.val)) (i.val/Nat.gcd k s) = _
  rw [hi,hdiv]



private def mixerCorrection {k : ℕ} (hk : 0 < k) (s : ℕ)
    (A G : Matrix (Fin k) (Fin k) (ZMod 2)) : ℕ :=
  let T := Finset.univ.filter (fun u =>
    A.mulVec (G.mulVec (kernelWord hk s u)) = kernelWord hk s u)
  let R := T.filter (fun u => ∀ v ∈ T, dotProduct (G.mulVec (kernelWord hk s u)) (kernelWord hk s v) = 0)
  if 3 ∣ k / Nat.gcd k s then Nat.log2 (T.card * R.card) / 2 else 0

private lemma mixerCase_p {k : ℕ} (hk : 0 < k) (s : ℕ) (h6 : 6 ∣ k) (hc : Nat.Coprime k s)
    (A G : Matrix (Fin k) (Fin k) (ZMod 2))
    (hAG : ∀ x, A.mulVec (G.mulVec x) = x)
    (matching : Bool)
    (hG : ∀ i j, G i j =
      if matching then mixerMatchEntry i.val j.val else mixerPathEntry i.val j.val) :
    k/2 - mixerCorrection hk s A G = k/2 - 2 + (if matching then (k/6)%2 else 0) := by
  let g := Nat.gcd k s
  let U := Fin g → ZMod 2 × ZMod 2
  let q : Fin g := ⟨0,Nat.gcd_pos_of_pos_left s hk⟩
  have h3 : 3 ∣ k / Nat.gcd k s := by
    rw [hc.gcd_eq_one, Nat.div_one]
    exact dvd_trans (by decide : (3 : ℕ) ∣ 6) h6
  have hT : ((Finset.univ : Finset U).filter
      (fun u => A.mulVec (G.mulVec (kernelWord hk s u)) = kernelWord hk s u)) = Finset.univ := by
    simp [hAG]
  have hcard : (Finset.univ : Finset U).card = 4 := by
    have hg : g = 1 := hc.gcd_eq_one
    simp [U, Finset.card_univ, Fintype.card_prod, ZMod.card, hg]
  have hsmall : 6 ≤ k := Nat.le_of_dvd hk h6
  unfold mixerCorrection
  rw [ite_eq_left h3, hT, hcard]
  cases matching
  · have hPair (u v : U) :
        dotProduct (G.mulVec (kernelWord hk s u)) (kernelWord hk s v) = 0 := by
      rw [kernelWord_of_coprime hk s hc u, kernelWord_of_coprime hk s hc v]
      exact mixerPath_pair h6 G (fun i j => by simpa using hG i j) (u q) (v q)
    simp only [hPair, implies_true, Finset.filter_true_of_mem, hcard]
    simp
  · have hPair (u v : U) :
        dotProduct (G.mulVec (kernelWord hk s u)) (kernelWord hk s v) =
          (↑(k/6) : ZMod 2) * mixerAlt (u q) (v q) := by
      rw [kernelWord_of_coprime hk s hc u, kernelWord_of_coprime hk s hc v]
      exact mixerMatch_pair h6 G (fun i j => by simpa using hG i j) (u q) (v q)
    simp only [hPair, ite_true]
    have hpar : (k/6)%2 = 0 ∨ (k/6)%2 = 1 := by omega
    rcases hpar with hpar | hpar
    · have hc0 : (↑(k/6) : ZMod 2) = 0 := by rw [← ZMod.natCast_mod (k/6) 2, hpar, Nat.cast_zero]
      simp only [hc0, zero_mul, implies_true, Finset.filter_true_of_mem, hcard, hpar, add_zero]
      have he : Nat.log2 (4*4) / 2 = 2 := by decide
      rw [he]
    · have hc1 : (↑(k/6) : ZMod 2) = 1 := by rw [← ZMod.natCast_mod (k/6) 2, hpar, Nat.cast_one]
      have hR : ((Finset.univ : Finset U).filter
          (fun u => ∀ v ∈ (Finset.univ : Finset U), (↑(k/6) : ZMod 2) * mixerAlt (u q) (v q) = 0)) = {0} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hc1, one_mul]
        constructor
        · intro h
          have hf := h (fun _ => (0,1))
          have hs := h (fun _ => (1,0))
          have hzero : u q = 0 := by
            apply Prod.ext
            · simpa [mixerAlt] using hf
            · simpa [mixerAlt] using hs
          funext i
          have hi : i = q := Fin.ext (by
            have hlt := i.isLt
            change i.val < Nat.gcd k s at hlt
            rw [hc.gcd_eq_one] at hlt
            change i.val = 0
            omega)
          rw [hi]
          exact hzero
        · rintro rfl v _
          change (0 : ZMod 2) * (v q).2 + (0 : ZMod 2) * (v q).1 = 0
          simp
      rw [hR, Finset.card_singleton, Nat.mul_one, hpar]
      have he : Nat.log2 4 / 2 = 1 := by decide
      rw [he]
      omega



private def rotateLinear {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x i := x (kernelIx hk (i.val+k-s%k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rotateLinearEquiv {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) where
  __ := rotateLinear hk s
  invFun x i := x (kernelIx hk (i.val+s))
  left_inv x := by
    funext i
    change x (kernelIx hk ((kernelIx hk (i.val+s)).val+k-s%k)) = x i
    rw [kernelIx_forward_back]
  right_inv x := by
    funext i
    change x (kernelIx hk ((kernelIx hk (i.val+k-s%k)).val+s)) = x i
    rw [kernelIx_back_forward]

private lemma rotateLinearEquiv_apply {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) :
    rotateLinearEquiv hk s x = rotateLinear hk s x := rfl

private def mixerSucc {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k := kernelIx hk (i.val+1)

private def mixerAdj {k : ℕ} (hk : 0 < k) (E : Finset (Fin k)) :
    Matrix (Fin k) (Fin k) (ZMod 2) := fun i j =>
  (if i ∈ E ∧ mixerSucc hk i = j then 1 else 0) + (if j ∈ E ∧ mixerSucc hk j = i then 1 else 0)

private def mixerOut {k : ℕ} (hk : 0 < k) (spacing s t : ℕ) (name constant raw : Fin k → ZMod 2)
    (site : Fin k) : ZMod 2 :=
  let old := rotateLinear hk s raw + name
  let y := kernelMixer hk spacing old
  y site + (1+y (mixerSucc hk site))*y (kernelIx hk (site.val+2)) + rotateLinear hk t raw site + constant site

private lemma mixerOut_polar_at {k : ℕ} (hk : 0 < k) (spacing s t : ℕ)
    (name constant x y : Fin k → ZMod 2) (i : Fin k) :
    let O := mixerOut hk spacing s t name constant
    let P := (kernelMixer hk spacing).comp (rotateLinear hk s)
    let a := mixerSucc hk i
    let b := mixerSucc hk a
    O (x+y) i - O x i - O y i + O 0 i = P x b * P y a + P x a * P y b := by
  have hnext : mixerSucc hk (mixerSucc hk i) = kernelIx hk (i.val+2) := by
    unfold mixerSucc
    rw [kernelIx_add]
  dsimp only
  rw [hnext]
  simp only [mixerOut, LinearMap.comp_apply, map_add, map_zero, Pi.add_apply, Pi.zero_apply]
  ring

private lemma mixerAdj_pair {k : ℕ} (hk : 0 < k) (E : Finset (Fin k)) (x y : Fin k → ZMod 2) :
    dotProduct ((mixerAdj hk E).mulVec x) y =
      ∑ i ∈ E, (x (mixerSucc hk i) * y i + x i * y (mixerSucc hk i)) := by
  let e := mixerSucc hk
  have h₁ (i : Fin k) :
      (∑ j : Fin k, (if i ∈ E ∧ e i = j then 1 else 0) * x j * y i) =
        if i ∈ E then x (e i) * y i else 0 := by
    by_cases hi : i ∈ E
    · rw [ite_eq_left hi, Finset.sum_eq_single (e i)]
      · simp [hi]
      · intro j _ hj
        simp [hi, Ne.symm hj]
      · simp
    · simp [hi]
  have h₂ (i : Fin k) :
      (∑ j : Fin k, (if i ∈ E ∧ e i = j then 1 else 0) * x i * y j) =
        if i ∈ E then x i * y (e i) else 0 := by
    by_cases hi : i ∈ E
    · rw [ite_eq_left hi, Finset.sum_eq_single (e i)]
      · simp [hi]
      · intro j _ hj
        simp [hi, Ne.symm hj]
      · simp
    · simp [hi]
  have hfilter (f : Fin k → ZMod 2) :
      (∑ i : Fin k, (if i ∈ E then f i else 0)) = ∑ i ∈ E, f i := by
    rw [← Finset.sum_filter]
    simp
  calc
    _ = (∑ i : Fin k, ∑ j : Fin k, (if i ∈ E ∧ e i = j then 1 else 0) * x j * y i) +
        (∑ j : Fin k, ∑ i : Fin k, (if j ∈ E ∧ e j = i then 1 else 0) * x j * y i) := by
      simp only [dotProduct, Matrix.mulVec, mixerAdj, Finset.sum_mul, add_mul, Finset.sum_add_distrib, e]
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      simp_rw [h₁, h₂, hfilter]
      exact (Finset.sum_add_distrib).symm

private lemma mixerSum_polar {k : ℕ} (hk : 0 < k) (spacing s t : ℕ)
    (name constant : Fin k → ZMod 2) (sites : Finset (Fin k)) (x y : Fin k → ZMod 2) :
    let f := fun u => ∑ i ∈ sites, mixerOut hk spacing s t name constant u i
    let E := sites.image (mixerSucc hk)
    let A := mixerAdj hk E
    let M := kernelMixer hk spacing
    let R := rotateLinearEquiv hk s
    f (x+y) - f x - f y + f 0 = dotProduct (M (A.mulVec (M (R x)))) (R y) := by
  dsimp only
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, kernelMixer_dot_eq]
  simp only [mixerOut_polar_at, LinearMap.comp_apply, rotateLinearEquiv_apply, mixerAdj_pair]
  rw [Finset.sum_image]
  intro a _ b _ h
  have hf := congrArg (fun j : Fin k => kernelIx hk (j.val+k-1%k)) h
  exact (kernelIx_forward_back hk a 1).symm.trans (hf.trans (kernelIx_forward_back hk b 1))

private def mixerPostedP {k : ℕ} (hk : 0 < k) (s : ℕ) (E : Finset (Fin k)) : ℕ :=
  let m := PEqualNP.Outside.L_meta_33655_aux.Paths.selectionMax hk E
  let b := if E = Finset.univ ∧ k % 2 = 0 then m - 1 else m
  b - mixerCorrection hk s (PEqualNP.Outside.L_meta_33655_aux.Paths.markedA hk E) (PEqualNP.Outside.L_meta_33655_aux.Paths.markedG hk E)

private lemma mixerPostedP_special {k : ℕ} (hk : 0 < k) (s : ℕ) (E : Finset (Fin k))
    (h6 : 6 ∣ k) (hc : Nat.Coprime k s) :
    (E = PEqualNP.Outside.L_meta_33655_aux.Paths.spanMarks k → mixerPostedP hk s E = k/2-2) ∧
    (E = PEqualNP.Outside.L_meta_33655_aux.Paths.evenMarks k → mixerPostedP hk s E = k/2-2+(k/6)%2) := by
  have he : k % 2 = 0 := by omega
  constructor
  · rintro rfl
    have hAG (x : Fin k → ZMod 2) :
        (PEqualNP.Outside.L_meta_33655_aux.Paths.markedA hk (PEqualNP.Outside.L_meta_33655_aux.Paths.spanMarks k)).mulVec
          ((PEqualNP.Outside.L_meta_33655_aux.Paths.markedG hk (PEqualNP.Outside.L_meta_33655_aux.Paths.spanMarks k)).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, PEqualNP.Outside.L_meta_33655_aux.Paths.markedA_mul_G_span_even hk he, Matrix.one_mulVec]
    have hG (i j : Fin k) :
        PEqualNP.Outside.L_meta_33655_aux.Paths.markedG hk (PEqualNP.Outside.L_meta_33655_aux.Paths.spanMarks k) i j = mixerPathEntry i.val j.val := by
      rw [PEqualNP.Outside.L_meta_33655_aux.Paths.markedG_span hk, PEqualNP.Outside.L_meta_33655_aux.Paths.pathG_eq]
      rfl
    have h := mixerCase_p hk s h6 hc _ _ hAG false hG
    have hm : PEqualNP.Outside.L_meta_33655_aux.Paths.selectionMax hk (PEqualNP.Outside.L_meta_33655_aux.Paths.spanMarks k) = k / 2 :=
      PEqualNP.Outside.L_meta_33655_aux.Paths.selectionMax_path hk
    simp only [mixerPostedP, PEqualNP.Outside.L_meta_33655_aux.Paths.spanMarks_ne_univ hk, false_and, ite_false, hm]
    simpa using h
  · rintro rfl
    have hAG (x : Fin k → ZMod 2) :
        (PEqualNP.Outside.L_meta_33655_aux.Paths.markedA hk (PEqualNP.Outside.L_meta_33655_aux.Paths.evenMarks k)).mulVec
          ((PEqualNP.Outside.L_meta_33655_aux.Paths.markedG hk (PEqualNP.Outside.L_meta_33655_aux.Paths.evenMarks k)).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, PEqualNP.Outside.L_meta_33655_aux.Paths.markedA_mul_G_evenMarks hk he, Matrix.one_mulVec]
    have hG (i j : Fin k) :
        PEqualNP.Outside.L_meta_33655_aux.Paths.markedG hk (PEqualNP.Outside.L_meta_33655_aux.Paths.evenMarks k) i j = mixerMatchEntry i.val j.val :=
      PEqualNP.Outside.L_meta_33655_aux.Paths.markedG_even_apply hk he i j
    have h := mixerCase_p hk s h6 hc _ _ hAG true hG
    have hm : PEqualNP.Outside.L_meta_33655_aux.Paths.selectionMax hk (PEqualNP.Outside.L_meta_33655_aux.Paths.evenMarks k) = k / 2 :=
      PEqualNP.Outside.L_meta_33655_aux.Paths.selectionMax_even hk
    simp only [mixerPostedP, PEqualNP.Outside.L_meta_33655_aux.Paths.evenMarks_ne_univ hk he, false_and, ite_false, hm]
    exact h

end PEqualNP.Outside.L_meta_33655_aux.Mixer

namespace PEqualNP.Outside.L_meta_33655_aux.Tree

open Finset
open scoped BigOperators

abbrev F := ZMod 2
abbrev Cube (n : ℕ) := Fin n → F
abbrev Chart (p r : ℕ) := Cube p × (Cube p × Cube r)
abbrev Hist := List Bool

def sign (a : F) : ℤ := if a = 0 then 1 else -1

lemma bit_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

@[simp] lemma sign_zero : sign 0 = 1 := rfl
@[simp] lemma sign_one : sign 1 = -1 := rfl
@[simp] lemma bit_add_self (a : F) : a + a = 0 := by rcases bit_cases a with rfl | rfl <;> decide

lemma sign_add (a b : F) : sign (a+b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide

lemma sign_le_one (a : F) : sign a ≤ 1 := by
  rcases bit_cases a with rfl | rfl <;> decide

lemma sign_sub_eq (a b : F) : a + b = 0 ↔ a = b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide

lemma cancel_character {V : Type*} [Fintype V] [AddGroup V] (f : V → F)
    (hf : ∀ a b, f (a+b) = f a + f b) (u : V) (hu : f u ≠ 0) :
    ∀ c : F, ∑ v, sign (f v+c) = 0 := by
  intro c
  have hu' : f u = 1 := (bit_cases _).resolve_left hu
  let e : V ≃ V := ⟨fun v => v+u, fun v => v-u,
    fun v => add_sub_cancel_right _ _, fun v => sub_add_cancel _ _⟩
  have h := e.sum_comp (fun v => sign (f v+c))
  change (∑ v, sign (f (v+u)+c)) = _ at h
  simp only [hf, hu', add_right_comm _ (1 : F), sign_add _ (1 : F), sign_one, mul_neg,
    mul_one, Finset.sum_neg_distrib] at h
  linarith

def quad {p r : ℕ} (x : Chart p r) : F := x.1 ⬝ᵥ x.2.1

lemma card_cube (n : ℕ) : Fintype.card (Cube n) = 2^n := by
  simp [Cube, F, ZMod.card]

lemma sum_chart {p r : ℕ} (f : Chart p r → ℤ) :
    (∑ x, f x) = ∑ a : Cube p, ∑ z : Cube r, ∑ b : Cube p, f (a,b,z) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma chart_bound {p r : ℕ} (l : Chart p r →ₗ[F] F) (c : F) :
    (∑ x, sign (quad x + l x + c)) ≤ (2 : ℤ)^(p+r) := by
  classical
  let q (a b : Cube p) : F := a ⬝ᵥ b + l (0,b,0)
  let s := (Finset.univ : Finset (Cube p)).filter (fun a => ∀ b, q a b = 0)
  have uq (a b : Cube p) (ha : a ∈ s) (hb : b ∈ s) : a = b := by
    funext i
    have ha' := (Finset.mem_filter.mp ha).2 (Pi.single i 1)
    have hb' := (Finset.mem_filter.mp hb).2 (Pi.single i 1)
    simp only [q, dotProduct_single_one, sign_sub_eq] at ha' hb'
    exact ha'.trans hb'.symm
  have hs : s.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => uq a b ha hb)
  have hsum (a : Cube p) (z : Cube r) :
      (∑ b : Cube p, sign (quad (a,b,z) + l (a,b,z) + c)) ≤
        if a ∈ s then (2 : ℤ)^p else 0 := by
    by_cases h : a ∈ s
    · rw [ite_eq_left h]
      calc
        _ ≤ ∑ _b : Cube p, (1 : ℤ) := Finset.sum_le_sum (fun _ _ => sign_le_one _)
        _ = _ := by simp
    · rw [ite_eq_right h]
      have hne : ∃ b, q a b ≠ 0 := by simpa [s, not_forall] using h
      obtain ⟨u, hu⟩ := hne
      have qadd (v w : Cube p) : q a (v+w) = q a v + q a w := by
        dsimp only [q]
        rw [show ((0, v+w, 0) : Chart p r) = (0,v,0) + (0,w,0) by simp,
          map_add, dotProduct_add]
        abel
      have hrewrite (b : Cube p) : quad (a,b,z) + l (a,b,z) + c = q a b + (l (a,0,z)+c) := by
        rw [show ((a,b,z) : Chart p r) = (a,0,z)+(0,b,0) by simp, map_add]
        simp only [quad, Prod.fst_add, Prod.snd_add, add_zero, zero_add, q]
        abel
      simp only [hrewrite, cancel_character (q a) qadd u hu, le_refl]
  rw [sum_chart]
  calc
    _ ≤ ∑ a : Cube p, ∑ _z : Cube r, if a ∈ s then (2 : ℤ)^p else 0 :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hsum _ _
    _ = (s.card : ℤ) * (2 : ℤ)^(p+r) := by
      simp only [Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, mul_ite, mul_zero, ← Finset.sum_filter]
      have hx : ({a : Cube p | a ∈ s} : Finset _) = s := by ext; simp
      rw [hx, pow_add, mul_comm ((2 : ℤ)^r)]
    _ ≤ _ := by
      exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hs)

section Tree

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module F V]

def branch (a : F) : Bool := decide (a ≠ 0)
def bit (a : Bool) : F := if a then 1 else 0

@[simp] lemma bit_branch (a : F) : bit (branch a) = a := by
  rcases bit_cases a with rfl | rfl <;> decide

@[simp] lemma branch_bit (a : Bool) : branch (bit a) = a := by cases a <;> decide

def Good (f : V → F) (B : ℤ) (P : Finset V) : Prop :=
  ∀ (l : V →ₗ[F] F) (c : F), (∑ x ∈ P, sign (f x + l x + c)) ≤ B

lemma twice_sign_branch (v a : F) (b : Bool) :
    2 * (if branch a = b then sign v else 0) = sign v + sign (v + a + bit b) := by
  cases b <;> rcases bit_cases v with rfl | rfl <;> rcases bit_cases a with rfl | rfl <;> decide

omit [Fintype V] in
lemma good_filter {f : V → F} {B : ℤ} {P : Finset V} (h : Good f B P)
    (ask : V →ₗ[F] F) (bias : F) (b : Bool) :
    Good f B (P.filter (fun x => branch (ask x+bias) = b)) := by
  intro l c
  have H (x : V) : sign (f x + l x + c + (ask x + bias) + bit b) =
      sign (f x + (l+ask) x + (c+bias+bit b)) := by
    congr 1
    simp only [LinearMap.add_apply]
    abel
  have he : 2 * (∑ x ∈ P.filter (fun x => branch (ask x+bias) = b), sign (f x + l x + c)) =
      (∑ x ∈ P, sign (f x + l x + c)) + (∑ x ∈ P, sign (f x + (l+ask) x + (c+bias+bit b))) := by
    simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib, twice_sign_branch, H]
  have h1 := h l c
  have h2 := h (l+ask) (c+bias+bit b)
  omega

private def runTree {A : Type*} (nodes : Finset Hist) (ask : Hist → A → Bool) (x : A) :
    ℕ → Hist → Hist
  | 0, h => h
  | m + 1, h => if h ∈ nodes then runTree nodes ask x m (h ++ [ask h x]) else h

private lemma runTree_fold {A : Type*} (nodes : Finset Hist) (ask : Hist → A → Bool)
    (x : A) (m : ℕ) (h : Hist) : runTree nodes ask x m h =
      (List.range m).foldl (fun q _ => if q ∈ nodes then q ++ [ask q x] else q) h := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    by_cases hh : h ∈ nodes
    · simpa only [runTree, ite_eq_left hh] using ih (h ++ [ask h x])
    · have hf (l : List ℕ) : l.foldl (fun q _ => if q ∈ nodes then q ++ [ask q x] else q) h = h := by
        induction l with
        | nil => rfl
        | cons _ l ih' => simpa only [List.foldl_cons, ite_eq_right hh] using ih'
      simp only [runTree, ite_eq_right hh, hf]

private def descendants (nodes : Finset Hist) (h : Hist) : Finset Hist :=
  nodes.filter (fun q => h <+: q)

private lemma descendants_child (nodes : Finset Hist) (h : Hist) (b : Bool) :
    descendants nodes (h ++ [b]) ⊆ descendants nodes h := by
  intro q hq
  obtain ⟨hqN, hqp⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hqN, (List.prefix_append _ _).trans hqp⟩

private lemma descendants_budget (nodes : Finset Hist) (h : Hist) (hh : h ∈ nodes) :
    (descendants nodes (h ++ [false])).card + (descendants nodes (h ++ [true])).card + 1 ≤
      (descendants nodes h).card := by
  let left := descendants nodes (h ++ [false])
  let right := descendants nodes (h ++ [true])
  have hd : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro q hl hr
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hl).2
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hr).2
    have he : h ++ (false :: l) = h ++ (true :: r) := by
      simpa only [List.append_assoc, List.singleton_append] using hl.trans hr.symm
    have hh' := List.append_cancel_left he
    simp at hh'
  have hnot : h ∉ left ∪ right := by
    intro H
    rcases Finset.mem_union.mp H with hL | hR
    · have := (Finset.mem_filter.mp hL).2.length_le
      simp at this
    · have := (Finset.mem_filter.mp hR).2.length_le
      simp at this
  have hsub : insert h (left ∪ right) ⊆ descendants nodes h := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hh, List.prefix_rfl⟩
    · rcases Finset.mem_union.mp hq with hl | hr
      · exact descendants_child nodes h false hl
      · exact descendants_child nodes h true hr
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hd] at hcard



def run (nodes : Finset Hist) (ask : Hist → V →ₗ[F] F) (bias : Hist → F) (x : V) : Hist :=
  (List.range nodes.card).foldl (fun h _ =>
    if h ∈ nodes then h ++ [branch (ask h x + bias h)] else h) []

def signed (f : V → F) (nodes : Finset Hist) (ask : Hist → V →ₗ[F] F) (bias : Hist → F)
    (pred : Hist → V →ₗ[F] F) (c : Hist → F) : ℤ :=
  ∑ x, sign (f x + pred (run nodes ask bias x) x + c (run nodes ask bias x))

lemma tree_upper {f : V → F} {B : ℤ} (hB : 0 ≤ B) (nodes : Finset Hist)
    (ask : Hist → V →ₗ[F] F) (bias : Hist → F)
    (pred : Hist → V →ₗ[F] F) (c : Hist → F) (hf : Good f B Finset.univ) :
    signed f nodes ask bias pred c ≤ (nodes.card + 1 : ℤ) * B := by
  classical
  let Q (h : Hist) (x : V) := branch (ask h x + bias h)
  let value (h : Hist) (x : V) := sign (f x + pred h x + c h)
  have H (m : ℕ) (h : Hist) (P : Finset V) (hP : Good f B P) :
      (∑ x ∈ P, value (runTree nodes Q x m h) x) ≤ ((descendants nodes h).card + 1 : ℤ) * B := by
    induction m generalizing h P with
    | zero =>
      simpa only [runTree] using (hP (pred h) (c h)).trans
        (le_mul_of_one_le_left hB (by omega : 1 ≤ ((descendants nodes h).card : ℤ) + 1))
    | succ m ih =>
      by_cases hn : h ∈ nodes
      · let P0 := P.filter (fun x => Q h x = false)
        let P1 := P.filter (fun x => Q h x = true)
        have h0 := ih (h ++ [false]) P0 (good_filter hP (ask h) (bias h) false)
        have h1 := ih (h ++ [true]) P1 (good_filter hP (ask h) (bias h) true)
        have hd : Disjoint P0 P1 := Finset.disjoint_left.mpr (by
          intro x hx hy
          exact Bool.false_ne_true ((Finset.mem_filter.mp hx).2.symm.trans
            (Finset.mem_filter.mp hy).2))
        have hp : P0 ∪ P1 = P := by
          ext x
          cases hx : Q h x <;> simp [P0, P1, hx]
        have hsum : (∑ x ∈ P, value (runTree nodes Q x (m+1) h) x) =
            (∑ x ∈ P0, value (runTree nodes Q x m (h++[false])) x) +
            (∑ x ∈ P1, value (runTree nodes Q x m (h++[true])) x) := by
          rw [← hp, Finset.sum_union hd]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx
          · simp [runTree, hn, (Finset.mem_filter.mp hx).2]
          · simp [runTree, hn, (Finset.mem_filter.mp hx).2]
        rw [hsum]
        apply (add_le_add h0 h1).trans
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ hB
        have hbudget := descendants_budget nodes h hn
        omega
      · simpa only [runTree, ite_eq_right hn] using (hP (pred h) (c h)).trans
          (le_mul_of_one_le_left hB (by omega : 1 ≤ ((descendants nodes h).card : ℤ) + 1))
  simpa only [signed, run, Q, value, runTree_fold, descendants, List.nil_prefix,
    Finset.filter_true_of_mem (fun _ _ => trivial)] using H nodes.card [] Finset.univ hf

noncomputable def hits (f : V → F) (nodes : Finset Hist) (ask : Hist → V →ₗ[F] F) (bias : Hist → F)
    (pred : Hist → V →ₗ[F] F) (c : Hist → F) : ℕ :=
  ((Finset.univ : Finset V).filter (fun x =>
    f x = pred (run nodes ask bias x) x + c (run nodes ask bias x))).card

lemma signed_hits (f : V → F) (nodes : Finset Hist) (ask : Hist → V →ₗ[F] F) (bias : Hist → F)
    (pred : Hist → V →ₗ[F] F) (c : Hist → F) :
    signed f nodes ask bias pred c = 2 * (hits f nodes ask bias pred c : ℤ) - (Fintype.card V : ℤ) := by
  have hpoint (x : V) : sign (f x + pred (run nodes ask bias x) x + c (run nodes ask bias x)) =
      (if f x = pred (run nodes ask bias x) x + c (run nodes ask bias x) then (2 : ℤ) else 0)-1 := by
    simp only [add_assoc, sign, sign_sub_eq]
    split <;> decide
  simp only [signed, hpoint, Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, hits, Finset.card_univ, mul_one, mul_comm _ (2 : ℤ)]

end Tree

private lemma sum_powers_two (d : ℕ) : (∑ p ∈ range d, 2 ^ p) + 1 = 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [sum_range_succ, pow_succ]; omega

private def histories (p : ℕ) : Finset Hist :=
  Finset.univ.image (List.ofFn : (Fin p → Bool) → Hist)

private lemma mem_histories (h : Hist) (p : ℕ) : h ∈ histories p ↔ h.length = p := by
  constructor
  · intro hh
    obtain ⟨bs, _, rfl⟩ := Finset.mem_image.mp hh
    exact List.length_ofFn
  · intro hh
    subst p
    exact Finset.mem_image.mpr ⟨h.get, Finset.mem_univ _, List.ofFn_get _⟩

private lemma card_histories (p : ℕ) : (histories p).card = 2^p := by
  rw [histories, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

private def belowDepth (d : ℕ) : Finset Hist := (Finset.range d).biUnion histories

private lemma mem_belowDepth (d : ℕ) (h : Hist) : h ∈ belowDepth d ↔ h.length < d := by
  simp [belowDepth, mem_histories]

private lemma card_belowDepth (d : ℕ) : (belowDepth d).card + 1 = 2^d := by
  unfold belowDepth
  rw [Finset.card_biUnion]
  · simpa only [card_histories] using sum_powers_two d
  · intro p _ q _ hne
    apply Finset.disjoint_left.mpr
    intro h hp hq
    exact hne (((mem_histories h p).mp hp).symm.trans ((mem_histories h q).mp hq))

private lemma runTree_hits_stop {A : Type*} (nodes : Finset Hist) (ask : Hist → A → Bool)
    (x : A) (H : ℕ → Hist) (q : ℕ)
    (hs : ∀ n, H (n+1) = H n ++ [ask (H n) x])
    (hnode : ∀ n < q, H n ∈ nodes) (hstop : H q ∉ nodes) :
    ∀ m p, p ≤ q → q ≤ p+m → runTree nodes ask x m (H p) = H q := by
  intro m
  induction m with
  | zero =>
    intro p hp hq
    have he : p = q := by omega
    subst p
    rfl
  | succ m ih =>
    intro p hp hq
    by_cases he : p = q
    · subst p
      simp [runTree, hstop]
    · have ha := hnode p (by omega)
      rw [runTree, ite_eq_left ha, ← hs]
      exact ih (p+1) (by omega) (by omega)

private def readA {p : ℕ} (a : Cube p) (i : ℕ) : F := if hi : i < p then a ⟨i,hi⟩ else 0

private def history {p : ℕ} (a : Cube p) (n : ℕ) : Hist :=
  List.ofFn (fun i : Fin n => branch (readA a i.val))

@[simp] private lemma history_length {p : ℕ} (a : Cube p) (n : ℕ) :
    (history a n).length = n := List.length_ofFn

private lemma history_succ {p : ℕ} (a : Cube p) (n : ℕ) :
    history a (n+1) = history a n ++ [branch (readA a n)] := by
  simpa only [history, List.concat_eq_append, Fin.val_castSucc, Fin.val_last] using
    List.ofFn_succ' (fun i : Fin (n+1) => branch (readA a i.val))

private def complete {p : ℕ} (h : Hist) : Cube p := fun i => bit (h.getD i.val false)

private lemma history_complete {p : ℕ} (h : Hist) (hp : h.length ≤ p) :
    history (complete (p:=p) h) h.length = h := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp [history, readA, complete, show i < p by omega]

private def coordAsk {p r : ℕ} (h : Hist) : Chart p r →ₗ[F] F :=
  if hh : h.length < p then
    (LinearMap.proj ⟨h.length,hh⟩).comp (LinearMap.fst F (Cube p) (Cube p × Cube r)) else 0

private lemma coordAsk_apply {p r : ℕ} (h : Hist) (x : Chart p r) :
    coordAsk h x = readA x.1 h.length := by
  by_cases hh : h.length < p <;> simp [coordAsk, readA, hh]

private lemma balanced_histories {p r m : ℕ} (hm : 0 < m) (hmp : m ≤ 2^p) :
    ∃ nodes leaves : Finset Hist, nodes.card + 1 = m ∧ leaves.card = m ∧
      (∀ (x : Chart p r), run nodes coordAsk (fun _ => 0) x ∈ leaves) ∧
      (∀ h ∈ leaves, run nodes coordAsk (fun _ => 0) ((complete h, 0, 0) : Chart p r) = h) := by
  classical
  let d := Nat.log2 m
  let A := m - 2^d
  have hMd : 2^d ≤ m := Nat.log2_self_le hm.ne'
  have hMd' : m < 2^(d+1) := (Nat.log2_lt hm.ne').mp (Nat.lt_succ_self _)
  have hdp : d ≤ p := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hMd.trans hmp)
  have hA : A ≤ (histories d).card := by
    rw [pow_succ] at hMd'
    rw [card_histories]
    dsimp only [A]
    omega
  obtain ⟨sel, hsel, hcard⟩ := Finset.exists_subset_card_eq hA
  let nodes := belowDepth d ∪ sel
  have hD : Disjoint (belowDepth d) sel := by
    apply Finset.disjoint_left.mpr
    intro h h₀ h₁
    have hh := (mem_histories h d).mp (hsel h₁)
    have hl := (mem_belowDepth d h).mp h₀
    omega
  have hN : nodes.card + 1 = m := by
    unfold nodes
    rw [Finset.card_union_of_disjoint hD, hcard, Nat.add_right_comm, card_belowDepth]
    exact Nat.add_sub_of_le hMd
  let kids (b : Bool) := sel.image (fun h => h ++ [b])
  let leaves := (histories d \ sel) ∪ (kids false ∪ kids true)
  have kids_length {b : Bool} {h : Hist} (hh : h ∈ kids b) : h.length = d+1 := by
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hh
    simp [(mem_histories g d).mp (hsel hg)]
  have kids_card (b : Bool) : (kids b).card = sel.card :=
    Finset.card_image_of_injective sel (fun _ _ he => List.append_cancel_right he)
  have hkdisj : Disjoint (kids false) (kids true) := Finset.disjoint_left.mpr (by
    intro h h0 h1
    obtain ⟨g,hg,h0⟩ := Finset.mem_image.mp h0
    obtain ⟨q,hq,h1⟩ := Finset.mem_image.mp h1
    have hh := List.append_inj (h0.trans h1.symm) (show g.length = q.length by
      rw [(mem_histories _ _).mp (hsel hg), (mem_histories _ _).mp (hsel hq)])
    simp at hh)
  have hldisj : Disjoint (histories d \ sel) (kids false ∪ kids true) := Finset.disjoint_left.mpr (by
    intro h h0 h1
    have hl := (mem_histories _ _).mp (Finset.mem_sdiff.mp h0).1
    rcases Finset.mem_union.mp h1 with h1 | h1 <;> have := kids_length h1 <;> omega)
  have hL : leaves.card = m := by
    unfold leaves
    rw [Finset.card_union_of_disjoint hldisj, Finset.card_union_of_disjoint hkdisj,
      kids_card false, kids_card true, Finset.card_sdiff_of_subset hsel, card_histories, hcard]
    dsimp only [A]
    omega
  let Q (h : Hist) (x : Chart p r) := branch (readA x.1 h.length)
  have hrun (x : Chart p r) :
      let q := if history x.1 d ∈ sel then d+1 else d
      run nodes coordAsk (fun _ => 0) x = history x.1 q := by
    dsimp only
    let q := if history x.1 d ∈ sel then d+1 else d
    have hs (n : ℕ) : history x.1 (n+1) = history x.1 n ++ [Q (history x.1 n) x] := by
      simp only [Q, history_length, history_succ]
    have hn : ∀ n < q, history x.1 n ∈ nodes := by
      intro n hn
      by_cases hd : n < d
      · exact Finset.mem_union.mpr (Or.inl ((mem_belowDepth _ _).mpr (by simpa)))
      · by_cases hx : history x.1 d ∈ sel
        · have he : n = d := by simp only [q, hx, ite_true] at hn; omega
          subst n
          exact Finset.mem_union.mpr (Or.inr hx)
        · simp only [q, hx, ite_false] at hn
          contradiction
    have hstop : history x.1 q ∉ nodes := by
      intro hh
      rcases Finset.mem_union.mp hh with hlow | hh
      · have h := (mem_belowDepth _ _).mp hlow
        rw [history_length] at h
        by_cases hx : history x.1 d ∈ sel <;> simp [q,hx] at h
      · have h := (mem_histories _ _).mp (hsel hh)
        rw [history_length] at h
        by_cases hx : history x.1 d ∈ sel
        · simp [q,hx] at h
        · exact hx (h ▸ hh)
    have hq : q ≤ nodes.card := by
      have hpow : d < 2^d := Nat.lt_two_pow_self
      by_cases hx : history x.1 d ∈ sel
      · have hApos : 0 < A := hcard ▸ Finset.card_pos.mpr ⟨_,hx⟩
        have he : q = d+1 := by simp [q,hx]
        dsimp only [A] at hApos
        omega
      · have he : q = d := by simp [q,hx]
        omega
    simpa only [run, add_zero, coordAsk_apply, runTree_fold, Q, show history x.1 0 = [] from rfl] using
      runTree_hits_stop nodes Q x (history x.1) q hs hn hstop nodes.card 0 (by omega) (by omega)
  refine ⟨nodes,leaves,hN,hL,?_,?_⟩
  · intro x
    rw [hrun]
    by_cases hx : history x.1 d ∈ sel
    · rw [ite_eq_left hx, history_succ]
      cases h : branch (readA x.1 d)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨_,hx,rfl⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨_,hx,rfl⟩))))
    · rw [ite_eq_right hx]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨(mem_histories _ _).mpr (history_length ..),hx⟩))
  · intro h hh
    rw [hrun]
    change history (complete h : Cube p) (if history (complete h : Cube p) d ∈ sel then d+1 else d) = h
    rcases Finset.mem_union.mp hh with h0 | h1
    · have hl := (mem_histories _ _).mp (Finset.mem_sdiff.mp h0).1
      have hx := history_complete (p:=p) h (hl ▸ hdp)
      rw [hl] at hx
      rw [hx, ite_eq_right (Finset.mem_sdiff.mp h0).2]
      exact hx
    · obtain ⟨b,g,hg,rfl⟩ : ∃ b : Bool, ∃ g ∈ sel, g ++ [b] = h := by
        rcases Finset.mem_union.mp h1 with h1 | h1
        · exact ⟨false,Finset.mem_image.mp h1⟩
        · exact ⟨true,Finset.mem_image.mp h1⟩
      have hl : (g ++ [b]).length = d+1 := by simp [(mem_histories _ _).mp (hsel hg)]
      have hApos : 0 < A := hcard ▸ Finset.card_pos.mpr ⟨_,hg⟩
      have hlt : d+1 ≤ p := by
        by_contra! h
        have he : d = p := by omega
        dsimp only [A] at hApos
        rw [he] at hApos
        omega
      have hx := history_complete (p:=p) (g ++ [b]) (hl ▸ hlt)
      rw [hl] at hx
      have hpref : history (complete (g ++ [b]) : Cube p) d = g := by
        rw [history_succ] at hx
        exact (List.append_inj hx (by simp [(mem_histories _ _).mp (hsel hg)])).1
      rw [hpref, ite_eq_left hg]
      exact hx

private def dotPred {p r : ℕ} (a : Cube p) : Chart p r →ₗ[F] F where
  toFun x := a ⬝ᵥ x.2.1
  map_add' _ _ := dotProduct_add ..
  map_smul' _ _ := dotProduct_smul ..

private lemma dot_corr {p : ℕ} (a a' : Cube p) :
    (∑ b : Cube p, sign ((a ⬝ᵥ b) + (a' ⬝ᵥ b))) = if a' = a then (2 : ℤ)^p else 0 := by
  classical
  by_cases he : a' = a
  · subst a'
    simp
  · rw [ite_eq_right he]
    have he' : ∃ i, a i ≠ a' i := by
      by_contra! hh
      exact he (funext fun i => (hh i).symm)
    obtain ⟨i, hii⟩ := he'
    simp only [← add_dotProduct]
    simpa only [add_zero] using cancel_character (fun b : Cube p => (a+a') ⬝ᵥ b)
      (fun _ _ => dotProduct_add ..) (Pi.single i 1)
      (fun hh => hii ((sign_sub_eq _ _).mp (by simpa only [dotProduct_single_one, Pi.add_apply] using hh))) 0

private lemma chart_lower {p r m : ℕ} (hm : 0 < m) (hmp : m ≤ 2^p) :
    ∃ (nodes : Finset Hist) (ask : Hist → Chart p r →ₗ[F] F) (bias : Hist → F)
      (pred : Hist → Chart p r →ₗ[F] F) (c : Hist → F),
      nodes.card + 1 = m ∧ signed quad nodes ask bias pred c = (m : ℤ) * (2 : ℤ)^(p+r) := by
  classical
  obtain ⟨nodes,leaves,hn,hc,hall,hcompl⟩ := balanced_histories (p:=p) (r:=r) hm hmp
  let leaf (a : Cube p) := run nodes coordAsk (fun _ => 0) ((a,0,0) : Chart p r)
  have hleaf (a b : Cube p) (z : Cube r) :
      run nodes coordAsk (fun _ => 0) ((a,b,z) : Chart p r) = leaf a := by
    simp only [run, add_zero, coordAsk_apply, leaf]
  let fixed := (Finset.univ : Finset (Cube p)).filter (fun a => complete (leaf a) = a)
  have hfixed : fixed = leaves.image complete := by
    ext a
    simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha
      exact ⟨leaf a, hall _, ha⟩
    · rintro ⟨h,hh,rfl⟩
      rw [show leaf (complete h) = h from hcompl h hh]
  have hfc : fixed.card = m := by
    rw [hfixed, Finset.card_image_of_injOn, hc]
    intro h hh g hg he
    exact (hcompl h hh).symm.trans ((congrArg leaf he).trans (hcompl g hg))
  refine ⟨nodes,coordAsk,fun _ => 0,fun h => dotPred (complete h),fun _ => 0, hn, ?_⟩
  rw [signed, sum_chart]
  simp only [add_zero, hleaf]
  change (∑ a : Cube p, ∑ _z : Cube r, ∑ b : Cube p,
    sign ((a ⬝ᵥ b) + (complete (leaf a) ⬝ᵥ b))) = _
  simp only [dot_corr, Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, mul_ite, mul_zero, ← Finset.sum_filter]
  change (fixed.card : ℤ) * ((2 : ℤ)^r * (2 : ℤ)^p) = _
  rw [hfc, pow_add, mul_comm ((2 : ℤ)^r)]

private lemma pullBound {k p r : ℕ} (e : Cube k ≃ₗ[F] Chart p r) (f : Cube k → F)
    (l : Cube k →ₗ[F] F) (c : F) (hf : ∀ x, f x = quad (e x) + l x + c) :
    Good f ((2 : ℤ)^(p+r)) Finset.univ := by
  intro a b
  let a' := (l+a).comp e.symm.toLinearMap
  have H (x : Cube k) : f x + a x + b = quad (e x) + a' (e x) + (c+b) := by
    rw [hf]
    simp only [a', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.add_apply]
    abel
  simp only [H]
  exact (e.toEquiv.sum_comp (fun x => sign (quad x + a' x + (c+b)))).trans_le (chart_bound a' (c+b))

private lemma pullLower {k p r m : ℕ} (e : Cube k ≃ₗ[F] Chart p r) (f : Cube k → F)
    (l : Cube k →ₗ[F] F) (c : F) (hf : ∀ x, f x = quad (e x) + l x + c)
    (hm : 0 < m) (hmp : m ≤ 2^p) :
    ∃ (nodes : Finset Hist) (ask : Hist → Cube k →ₗ[F] F) (bias : Hist → F)
      (pred : Hist → Cube k →ₗ[F] F) (b : Hist → F),
      nodes.card + 1 = m ∧ signed f nodes ask bias pred b = (m : ℤ) * (2 : ℤ)^(p+r) := by
  obtain ⟨nodes,ask,bias,pred,b,hn,hs⟩ := chart_lower (r:=r) hm hmp
  let ask' (h : Hist) := (ask h).comp e.toLinearMap
  let pred' (h : Hist) := (pred h).comp e.toLinearMap + l
  let b' (h : Hist) := b h + c
  have hr (x : Cube k) : run nodes ask' bias x = run nodes ask bias (e x) := rfl
  have H (x : Cube k) : f x + pred' (run nodes ask' bias x) x + b' (run nodes ask' bias x) =
      quad (e x) + pred (run nodes ask bias (e x)) (e x) + b (run nodes ask bias (e x)) := by
    simp only [hf, hr, pred', b', LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ∀ q t u v w : F, q+t+u+(v+t)+(w+u) = (q+v+w)+(t+t)+(u+u) by intros; abel]
    simp
  refine ⟨nodes,ask',bias,pred',b',hn,?_⟩
  simp only [signed, H]
  exact (e.toEquiv.sum_comp (fun y =>
    sign (quad y + pred (run nodes ask bias y) y + b (run nodes ask bias y)))).trans hs

theorem scalar_tree_optimum {k p r L : ℕ} (hL : 0 < L) (e : Cube k ≃ₗ[F] Chart p r)
    (f : Cube k → F) (l : Cube k →ₗ[F] F) (c : F)
    (hf : ∀ x, f x = quad (e x) + l x + c) :
    IsGreatest {z : ℕ | ∃ (nodes : Finset Hist) (ask : Hist → Cube k →ₗ[F] F) (bias : Hist → F)
      (pred : Hist → Cube k →ₗ[F] F) (b : Hist → F), nodes.card < L ∧
      hits f nodes ask bias pred b = z} ((2^k + min L (2^p) * 2^(k-p))/2) := by
  classical
  let M := min L (2^p)
  have hM : 0 < M := lt_min hL (by positivity)
  have hMP : M ≤ 2^p := min_le_right ..
  have hML : M ≤ L := min_le_left ..
  have hdim : k = p + (p+r) := by
    have he := Fintype.card_congr e.toEquiv
    simp only [Fintype.card_prod, card_cube, ← pow_add] at he
    have h₁ := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp he.le
    have h₂ := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp he.ge
    omega
  have hp : k-p = p+r := by omega
  have hcast : (M : ℤ) * (2 : ℤ)^(p+r) = ((M * 2^(k-p) : ℕ) : ℤ) := by
    rw [hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change IsGreatest _ ((2^k + M*2^(k-p))/2)
  constructor
  · obtain ⟨nodes,ask,bias,pred,b,hn,hs⟩ := pullLower e f l c hf hM hMP
    refine ⟨nodes,ask,bias,pred,b,by omega,?_⟩
    rw [signed_hits, card_cube, hcast] at hs
    omega
  · rintro z ⟨nodes,ask,bias,pred,b,hNL,rfl⟩
    have hs : signed f nodes ask bias pred b ≤ (M : ℤ) * (2 : ℤ)^(p+r) := by
      by_cases h : L ≤ 2^p
      · have hup := tree_upper (by positivity : 0 ≤ (2 : ℤ)^(p+r)) nodes ask bias pred b (pullBound e f l c hf)
        refine hup.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        dsimp only [M]
        rw [min_eq_left h]
        omega
      · have hpow : (M : ℤ) * (2 : ℤ)^(p+r) = (2 : ℤ)^k := by
          dsimp only [M]
          rw [min_eq_right (by omega), Nat.cast_pow, Nat.cast_ofNat, ← pow_add, ← hdim]
        rw [hpow, signed]
        calc
          _ ≤ ∑ _x : Cube k, (1 : ℤ) := Finset.sum_le_sum (fun _ _ => sign_le_one _)
          _ = _ := by simp
    rw [signed_hits, card_cube, hcast] at hs
    omega

end PEqualNP.Outside.L_meta_33655_aux.Tree

namespace PEqualNP.Outside.L_meta_33655_aux.Counts

open Rank

variable {K V U : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype U]

noncomputable def accepted (A G M : V →ₗ[K] V) (e : U ≃ M.ker) : Finset U := by
  classical
  exact Finset.univ.filter (fun u => A (G (e u)) = (e u : V))

noncomputable def acceptedOrthogonal (D : LinearMap.BilinForm K V) (A G M : V →ₗ[K] V)
    (e : U ≃ M.ker) : Finset U := by
  classical
  exact (accepted A G M e).filter (fun u => ∀ v ∈ accepted A G M e, D (G (e u)) (e v) = 0)

lemma mem_accepted (A G M : V →ₗ[K] V) (e : U ≃ M.ker) (u : U) :
    u ∈ accepted A G M e ↔ A (G (e u)) = (e u : V) := by
  classical
  simp [accepted]

lemma mem_acceptedOrthogonal (D : LinearMap.BilinForm K V) (A G M : V →ₗ[K] V)
    (e : U ≃ M.ker) (u : U) :
    u ∈ acceptedOrthogonal D A G M e ↔
      u ∈ accepted A G M e ∧ ∀ v ∈ accepted A G M e, D (G (e u)) (e v) = 0 := by
  classical
  simp [acceptedOrthogonal]

noncomputable def acceptedEquiv (A G M : V →ₗ[K] V) (e : U ≃ M.ker)
    (hAG : ∀ x : A.range, A (G x) = x) : accepted A G M e ≃ nullOnImage A M where
  toFun u := ⟨⟨(e u : V), ⟨G (e u), (mem_accepted A G M e u).mp u.property⟩⟩, (e u).property⟩
  invFun x := by
    let y : M.ker := ⟨((x : A.range) : V), x.property⟩
    refine ⟨e.symm y, (mem_accepted A G M e _).mpr ?_⟩
    rw [e.apply_symm_apply]
    exact hAG x
  left_inv u := by
    apply Subtype.ext
    exact e.symm_apply_apply u
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : M.ker => (y : V))
      (e.apply_symm_apply ⟨((x : A.range) : V), x.property⟩)

@[simp] lemma acceptedEquiv_val (A G M : V →ₗ[K] V) (e : U ≃ M.ker)
    (hAG : ∀ x : A.range, A (G x) = x) (u : accepted A G M e) :
    (((acceptedEquiv A G M e hAG u : nullOnImage A M) : A.range) : V) = (e u : V) := rfl

noncomputable def acceptedOrthogonalEquiv (D : LinearMap.BilinForm K V) (A G M : V →ₗ[K] V)
    (e : U ≃ M.ker) (hD : D.IsSymm) (hA : ∀ x y, D (A x) y = D x (A y))
    (hAG : ∀ x : A.range, A (G x) = x) : acceptedOrthogonal D A G M e ≃
      (nullOnImage A M ⊓ (inversePair D A G).orthogonal (nullOnImage A M) : Submodule K A.range) := by
  let T := nullOnImage A M
  let B := inversePair D A G
  let et := acceptedEquiv A G M e hAG
  have hsym := inversePair_symm D A G hD hA hAG
  have hmem (u : accepted A G M e) : (u : U) ∈ acceptedOrthogonal D A G M e ↔
      (et u : A.range) ∈ B.orthogonal T := by
    rw [mem_acceptedOrthogonal, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨_, hu⟩ v hv
      let w := et.symm ⟨v, hv⟩
      have he : (et w : A.range) = v := congrArg Subtype.val (et.apply_symm_apply ⟨v, hv⟩)
      rw [hsym.eq, ← he]
      exact hu w w.property
    · intro hu
      refine ⟨u.property, fun v hv => ?_⟩
      let w : accepted A G M e := ⟨v, hv⟩
      rw [← show B (et u) (et w) = D (G (e u)) (e v) from rfl, hsym.eq]
      exact hu (et w) (et w).property
  refine {
    toFun := fun u => ?_
    invFun := fun x => ?_
    left_inv := ?_
    right_inv := ?_
  }
  · have hu := (mem_acceptedOrthogonal D A G M e u).mp u.property
    let w : accepted A G M e := ⟨u, hu.1⟩
    exact ⟨et w, (et w).property, (hmem w).mp u.property⟩
  · let t : T := ⟨x, x.property.1⟩
    let w := et.symm t
    have hw : (et w : A.range) ∈ B.orthogonal T := by
      change (et (et.symm t) : A.range) ∈ B.orthogonal T
      rw [et.apply_symm_apply]
      exact x.property.2
    exact ⟨w, (hmem w).mpr hw⟩
  · intro u
    apply Subtype.ext
    exact congrArg (fun y : accepted A G M e => (y : U)) (et.symm_apply_apply
      ⟨u, ((mem_acceptedOrthogonal D A G M e u).mp u.property).1⟩)
  · intro x
    apply Subtype.ext
    exact congrArg (fun y : T => (y : A.range)) (et.apply_symm_apply (⟨x, x.property.1⟩ : T))

theorem accepted_card (A G M : V →ₗ[K] V) (e : U ≃ M.ker)
    (hAG : ∀ x : A.range, A (G x) = x) :
    (accepted A G M e).card = Nat.card (nullOnImage A M) := by
  rw [← Nat.card_congr (acceptedEquiv A G M e hAG), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem acceptedOrthogonal_card (D : LinearMap.BilinForm K V) (A G M : V →ₗ[K] V)
    (e : U ≃ M.ker) (hD : D.IsSymm) (hA : ∀ x y, D (A x) y = D x (A y))
    (hAG : ∀ x : A.range, A (G x) = x) :
    (acceptedOrthogonal D A G M e).card = Nat.card
      (nullOnImage A M ⊓ (inversePair D A G).orthogonal (nullOnImage A M) : Submodule K A.range) := by
  rw [← Nat.card_congr (acceptedOrthogonalEquiv D A G M e hD hA hAG),
    Nat.card_eq_fintype_card, Fintype.card_coe]

theorem log2_counts {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (D : LinearMap.BilinForm (ZMod 2) W) (A G M : W →ₗ[ZMod 2] W)
    (e : U ≃ M.ker) (hD : D.IsSymm) (hA : ∀ x y, D (A x) y = D x (A y))
    (hAG : ∀ x : A.range, A (G x) = x) :
    Nat.log2 ((accepted A G M e).card * (acceptedOrthogonal D A G M e).card) =
      Module.finrank (ZMod 2) (nullOnImage A M) + Module.finrank (ZMod 2)
        (nullOnImage A M ⊓ (inversePair D A G).orthogonal (nullOnImage A M) : Submodule (ZMod 2) A.range) := by
  rw [accepted_card A G M e hAG, acceptedOrthogonal_card D A G M e hD hA hAG,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := nullOnImage A M),
    Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := (nullOnImage A M ⊓ (inversePair D A G).orthogonal (nullOnImage A M) : Submodule (ZMod 2) A.range)),
    Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card, ← pow_add, Nat.log2_two_pow]

end PEqualNP.Outside.L_meta_33655_aux.Counts

open PEqualNP.Outside.L_meta_33655_aux in
theorem PEqualNP.Outside.L_meta_33655 : (∀ (k : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  ∀ (spacing s t : Nat) (name constant : W),
    let out := fun (raw : W) (site : Fin k) =>
      let old := rot s raw + name
      let y := fun u : Fin k =>
        old u + old (ix (u.val+spacing)) + old (ix (u.val+k-spacing % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) + rot t raw site + constant site
    ∀ (sites : Finset (Fin k)) (L : Nat), 0 < L →
      let E := sites.image (fun i => ix (i.val+1))
      let nxt := fun i : Fin k => ix (i.val+1)
      let miss := Finset.univ \ E
      let base := if h : miss.Nonempty then (nxt (miss.min' h)).val else 0
      let pos := fun i : Fin k => (i.val+k-base) % k
      let start := fun u : Nat => ((Finset.range (u+1)).filter (fun j =>
        j = 0 ∨ ix (base+(j-1)) ∉ E)).sup id
      let lim := if E = Finset.univ then k - (if k % 2 = 0 then 2 else 1) else k
      let A : Matrix (Fin k) (Fin k) F := fun i j =>
        (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
      let G : Matrix (Fin k) (Fin k) F := fun i j =>
        let u := min (pos i) (pos j)
        let v := max (pos i) (pos j)
        if v < lim ∧ start u = start v ∧ (u-start u) % 2 = 0 ∧ (v-start v) % 2 = 1 then 1 else 0
      let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
      let b := if E = Finset.univ ∧ k % 2 = 0 then m-1 else m
      let g := Nat.gcd k spacing
      let q := k/g
      let word := fun (ab : Fin g → F × F) (i : Fin k) =>
        let j : Fin g := ⟨i.val % g, Nat.mod_lt _ (Nat.gcd_pos_of_pos_left _ hk)⟩
        let z := ab j
        if (i.val/g) % 3 = 0 then z.1 else if (i.val/g) % 3 = 1 then z.2 else z.1+z.2
      let T := (Finset.univ : Finset (Fin g → F × F)).filter (fun u =>
        A.mulVec (G.mulVec (word u)) = word u)
      let R := T.filter (fun u => ∀ v ∈ T, dotProduct (G.mulVec (word u)) (word v) = 0)
      let p := b - (if 3 ∣ q then Nat.log2 (T.card*R.card)/2 else 0)
      let H := List Bool
      let D := W →ₗ[F] F
      let run := fun (nodes : Finset H) (ask : H → D) (bias : H → F) (x : W) =>
        (List.range nodes.card).foldl (fun h _ =>
          if h ∈ nodes then h ++ [decide (ask h x + bias h ≠ 0)] else h) []
      let hits := fun (nodes : Finset H) (ask : H → D) (bias : H → F)
          (pred : H → D) (c : H → F) =>
        ((Finset.univ : Finset W).filter (fun x =>
          let h := run nodes ask bias x
          (∑ i ∈ sites, out x i) = pred h x + c h)).card
      ((6 ∣ k ∧ Nat.Coprime k spacing) →
        (E = Finset.univ.filter (fun i : Fin k => i.val+1 < k) → p = k/2-2) ∧
        (E = Finset.univ.filter (fun i : Fin k => i.val % 2 = 0) → p = k/2-2+(k/6) % 2)) ∧
        IsGreatest {z : Nat | ∃ (nodes : Finset H) (ask : H → D) (bias : H → F) (pred : H → D) (c : H → F), nodes.card < L ∧
          hits nodes ask bias pred c = z} ((2^k + min L (2^p)*2^(k-p))/2)) := by
  classical
  intro k hk F W ix rot spacing s t name constant out sites L hL E nxt miss base pos start lim A G m b g q word
    T R p H D run hits
  let C := A.mulVecLin
  let I := G.mulVecLin
  let M := Mixer.kernelMixer hk spacing
  let rho := Mixer.rotateLinearEquiv hk s
  let f : W → F := fun x => ∑ i ∈ sites, out x i
  let raw := M.comp (C.comp M)
  have graph : A.rank = 2*b ∧ A*G*A = A := by
    change (Paths.markedA hk E).rank =
        2*(if E = Finset.univ ∧ k % 2 = 0 then Paths.selectionMax hk E-1 else Paths.selectionMax hk E) ∧
      Paths.markedA hk E * Paths.markedG hk E * Paths.markedA hk E = Paths.markedA hk E
    by_cases hE : E = Finset.univ
    · rw [hE]
      simpa only [true_and] using Paths.markedA_rank_and_inverse_univ hk
    · simpa only [hE, false_and, ite_false] using Paths.proper_marked_rank_and_inverse hk E hE
  have hArank : finrank F C.range = 2*b := graph.1
  have hAG : ∀ x : C.range, C (I x) = x :=
    MatrixProof.inverseOnRange A G graph.2
  have symA : Aᵀ = A := by
    apply Matrix.ext
    intro i j
    exact add_comm _ _
  have adjA := MatrixProof.matrixAdjoint A symA
  have adjM (x y : W) : MatrixProof.dotB k (M x) y = MatrixProof.dotB k x (M y) := by
    simp only [MatrixProof.dotB_eval]
    exact Mixer.kernelMixer_dot_eq hk spacing x y
  have hpolar (x y : W) :
      f (x+y) - f x - f y + f 0 = dotProduct (raw (rho x)) (rho y) :=
    Mixer.mixerSum_polar hk spacing s t name constant sites x y
  obtain ⟨j, r, chart, l, c, hRaw, hf⟩ := MatrixProof.chart_of_polar raw rho f hpolar

  let S := Rank.nullOnImage C M
  let orthogonal := (Rank.inversePair (MatrixProof.dotB k) C I).orthogonal S
  let td := finrank (ZMod 2) S
  let rd := finrank (ZMod 2) (S ⊓ orthogonal : Submodule (ZMod 2) C.range)
  have rankSum : finrank (ZMod 2) raw.range + td + rd = finrank (ZMod 2) C.range :=
    Rank.rank_restriction (MatrixProof.dotB k) C I M
      (MatrixProof.dotB_nondegenerate k) (MatrixProof.dotB_symm k) adjA adjM hAG
  have hdim : 2*j + td + rd = 2*b := by
    calc
      2*j + td + rd = finrank (ZMod 2) C.range := by simpa only [hRaw] using rankSum
      _ = 2*b := hArank
  have hp : j = p := by
    change j = b - (if 3 ∣ q then Nat.log2 (T.card*R.card)/2 else 0)
    by_cases h3 : 3 ∣ q
    · let equiv := (Mixer.kernelWordEquiv hk spacing h3).toEquiv
      have hw (u : Fin g → F × F) : (equiv u : W) = word u :=
        Mixer.kernelWordEquiv_apply hk spacing h3 u
      have hT : T = Counts.accepted C I M equiv := by
        ext u
        simp only [T, Counts.accepted, Finset.mem_filter, Finset.mem_univ, true_and, hw]
        rfl
      have hR : R = Counts.acceptedOrthogonal (MatrixProof.dotB k) C I M equiv := by
        ext u
        simp only [R, Counts.acceptedOrthogonal, Finset.mem_filter, hw, MatrixProof.dotB_eval]
        rw [hT]
        rfl
      have hlog : Nat.log2 (T.card*R.card) = td + rd := by
        rw [hT,hR]
        exact Counts.log2_counts (MatrixProof.dotB k) C I M equiv
          (MatrixProof.dotB_symm k) adjA hAG
      rw [ite_eq_left h3, hlog]
      exact MatrixProof.half_from_dimensions hdim
    · have hk0 : M.ker = ⊥ := Mixer.kernelMixer_ker_eq_bot hk spacing h3
      have h0 : S = ⊥ := by simp [S, Rank.nullOnImage, hk0]
      have ht : td = 0 := by simp [td, h0]
      have hr : rd = 0 := by simp [rd, h0]
      rw [ite_eq_right h3, Nat.sub_zero]
      apply MatrixProof.eq_from_double
      simpa only [ht,hr,add_zero] using hdim
  constructor
  · intro hc
    have postedP : p = Mixer.mixerPostedP hk spacing E := rfl
    rw [postedP]
    exact Mixer.mixerPostedP_special hk spacing E hc.1 hc.2
  · rw [← hp]
    exact Tree.scalar_tree_optimum hL chart f l c hf
