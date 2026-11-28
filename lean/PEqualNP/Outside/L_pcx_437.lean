import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_pcx_437_aux

open Finset MvPolynomial

/-- The zero-pin query matrix of a split `A` at a price vector `z`. -/
noncomputable def qmat {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A : Finset (Fin t)) :
    Matrix (Finset (Fin t)) (Finset (Fin t)) ℚ :=
  fun P Q => ∑ x : Bool × Fin n → Bool, if (∀ j ∈ A ∩ P, x (pin j) = false) ∧
      (∀ j ∈ Q, j ∉ A → x (pin j) = false) then
    ∏ e : Fin 3 × Fin n, (if x (false,e.2) = x (true,dest e) then 1 else z e) else 0

lemma qmat_row {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A P Q : Finset (Fin t)) :
    qmat dest pin z A P Q = qmat dest pin z A (A ∩ P) Q := by
  unfold qmat
  rw [← Finset.inter_assoc, Finset.inter_self]

lemma qmat_col {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A P Q : Finset (Fin t)) :
    qmat dest pin z A P Q = qmat dest pin z A P (Q \ A) := by
  unfold qmat
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj hA => h2 j (Finset.mem_sdiff.1 hj).1 hA⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj hA => h2 j (Finset.mem_sdiff.2 ⟨hj, hA⟩) hA⟩

lemma rank_le_rows {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A : Finset (Fin t)) :
    (qmat dest pin z A).rank ≤ 2 ^ A.card := by
  classical
  let L : Matrix (Finset (Fin t)) A.powerset ℚ := fun P S => if A ∩ P = S.1 then 1 else 0
  let K : Matrix A.powerset (Finset (Fin t)) ℚ := fun S Q => qmat dest pin z A S.1 Q
  have hLK : qmat dest pin z A = L * K := by
    ext P Q
    rw [Matrix.mul_apply, Finset.sum_eq_single
      ⟨A ∩ P, Finset.mem_powerset.2 Finset.inter_subset_left⟩]
    · simp only [L, K, if_pos rfl, one_mul]
      exact qmat_row dest pin z A P Q
    · intro S _ hS
      simp only [L]
      rw [if_neg, zero_mul]
      intro h
      exact hS (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hLK]
  calc (L * K).rank ≤ L.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card A.powerset := Matrix.rank_le_card_width _
    _ = 2 ^ A.card := by rw [Fintype.card_coe, Finset.card_powerset]

lemma rank_le_cols {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A : Finset (Fin t)) :
    (qmat dest pin z A).rank ≤ 2 ^ (t - A.card) := by
  classical
  let K : Matrix (Finset (Fin t)) (Aᶜ).powerset ℚ := fun P S => qmat dest pin z A P S.1
  let R : Matrix (Aᶜ).powerset (Finset (Fin t)) ℚ := fun S Q => if Q \ A = S.1 then 1 else 0
  have hsub : ∀ Q : Finset (Fin t), Q \ A ∈ (Aᶜ).powerset := fun Q =>
    Finset.mem_powerset.2 (fun j hj => Finset.mem_compl.2 (Finset.mem_sdiff.1 hj).2)
  have hKR : qmat dest pin z A = K * R := by
    ext P Q
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨Q \ A, hsub Q⟩]
    · simp only [K, R, if_pos rfl, mul_one]
      exact qmat_col dest pin z A P Q
    · intro S _ hS
      simp only [R]
      rw [if_neg, mul_zero]
      intro h
      exact hS (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hKR]
  calc (K * R).rank ≤ R.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card (Aᶜ).powerset := Matrix.rank_le_card_height _
    _ = 2 ^ (t - A.card) := by
      rw [Fintype.card_coe, Finset.card_powerset, Finset.card_compl, Fintype.card_fin]

lemma rank_le {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A : Finset (Fin t)) :
    (qmat dest pin z A).rank ≤ 2 ^ (min A.card (t - A.card)) := by
  rcases le_total A.card (t - A.card) with h | h
  · rw [min_eq_left h]; exact rank_le_rows dest pin z A
  · rw [min_eq_right h]; exact rank_le_cols dest pin z A

/-- Terminals selected by a Boolean vector through an injection. -/
def selS {t m : ℕ} (a : Fin m → Fin t) (y : Fin m → Bool) : Finset (Fin t) :=
  (Finset.univ.filter (fun i => y i = true)).image a

lemma rank_ge {n t m : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A : Finset (Fin t)) (a b : Fin m → Fin t)
    (hdet : (Matrix.of fun y r : Fin m → Bool =>
      qmat dest pin z A (selS a y) (selS b r)).det ≠ 0) :
    2 ^ m ≤ (qmat dest pin z A).rank := by
  classical
  have h1 := Matrix.rank_submatrix_le (qmat dest pin z A) (selS a) (selS b)
  have h2 : ((qmat dest pin z A).submatrix (selS a) (selS b)).rank = 2 ^ m := by
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      exact hdet
  omega

/-- The query matrix entries as polynomials in the prices. -/
noncomputable def qpoly {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (A P Q : Finset (Fin t)) : MvPolynomial (Fin 3 × Fin n) ℚ :=
  ∑ x : Bool × Fin n → Bool, if (∀ j ∈ A ∩ P, x (pin j) = false) ∧
      (∀ j ∈ Q, j ∉ A → x (pin j) = false) then
    ∏ e : Fin 3 × Fin n, (if x (false,e.2) = x (true,dest e) then 1 else X e) else 0

lemma eval_qpoly {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A P Q : Finset (Fin t)) :
    eval z (qpoly dest pin A P Q) = qmat dest pin z A P Q := by
  unfold qpoly qmat
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · rw [map_prod]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    split_ifs <;> simp
  · simp

noncomputable def dpoly {n t m : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (A : Finset (Fin t)) (a b : Fin m → Fin t) : MvPolynomial (Fin 3 × Fin n) ℚ :=
  (Matrix.of fun y r : Fin m → Bool => qpoly dest pin A (selS a y) (selS b r)).det

lemma eval_dpoly {n t m : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (z : Fin 3 × Fin n → ℚ) (A : Finset (Fin t)) (a b : Fin m → Fin t) :
    eval z (dpoly dest pin A a b) = (Matrix.of fun y r : Fin m → Bool =>
      qmat dest pin z A (selS a y) (selS b r)).det := by
  unfold dpoly
  rw [RingHom.map_det]
  congr 1
  ext y r
  simp [eval_qpoly]

lemma degreeOf_qpoly_le {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (A P Q : Finset (Fin t)) (e : Fin 3 × Fin n) :
    degreeOf e (qpoly dest pin A P Q) ≤ 1 := by
  classical
  unfold qpoly
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun x _ => ?_)
  split_ifs
  · refine (degreeOf_prod_le _ _ _).trans ?_
    calc ∑ e' ∈ univ, degreeOf e (if x (false,e'.2) = x (true,dest e') then 1 else
          (X e' : MvPolynomial (Fin 3 × Fin n) ℚ))
        ≤ ∑ e' ∈ univ, (if e = e' then 1 else 0) := Finset.sum_le_sum fun e' _ => ?_
      _ = 1 := by simp
    split_ifs <;> simp_all [degreeOf_one, degreeOf_X]
  · simp [degreeOf_zero]

lemma degreeOf_det_le {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℚ)) (e : σ) (D : ℕ)
    (h : ∀ i j, degreeOf e (M i j) ≤ D) : degreeOf e M.det ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun p _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h0 : degreeOf e (((Equiv.Perm.sign p : ℤ) : MvPolynomial σ ℚ)) = 0 := by
    rw [← map_intCast (C : ℚ →+* MvPolynomial σ ℚ)]
    exact degreeOf_C _ _
  rw [h0, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ i ∈ univ, degreeOf e (M (p i) i) ≤ ∑ _i ∈ univ, D := Finset.sum_le_sum fun i _ => h _ _
    _ = Fintype.card ι * D := by simp

lemma exists_prices {n : ℕ} (ι : Type*) [Fintype ι] (D : ι → MvPolynomial (Fin 3 × Fin n) ℚ)
    (B N : ℕ) (hD : ∀ i, D i ≠ 0) (hdeg : ∀ i e, degreeOf e (D i) ≤ B)
    (hN : Fintype.card ι * B + 2 ≤ N) :
    ∃ z : Fin 3 × Fin n → ℕ, (∀ e, 2 ≤ z e ∧ z e ≤ N) ∧
      ∀ i, eval (fun e => (z e : ℚ)) (D i) ≠ 0 := by
  classical
  have hQ : (∏ i, D i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hD i
  let S : Fin 3 × Fin n → Finset ℚ := fun _ => (Finset.Icc 2 N).image (Nat.cast)
  have hS : ∀ e, #(S e) = N + 1 - 2 := by
    intro e
    simp only [S]
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
  have hdegQ : ∀ e, degreeOf e (∏ i, D i) < #(S e) := by
    intro e
    rw [hS e]
    have := (degreeOf_prod_le e univ D).trans (Finset.sum_le_sum fun i _ => hdeg i e)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    omega
  by_contra hcon
  push_neg at hcon
  apply hQ
  apply eq_zero_of_eval_zero_at_prod_finset _ S hdegQ
  intro x hx
  have : ∀ e, ∃ m : ℕ, (2 ≤ m ∧ m ≤ N) ∧ (m : ℚ) = x e := fun e => by
    obtain ⟨m, hm, hm'⟩ := Finset.mem_image.1 (hx e)
    exact ⟨m, Finset.mem_Icc.1 hm, hm'⟩
  choose z hz hzx using this
  obtain ⟨i, hi⟩ := hcon z hz
  have hx' : x = fun e => (z e : ℚ) := funext fun e => (hzx e).symm
  rw [hx', map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi


def gg (a b : Bool) : ℚ := if (a || b) then 1 else 2

def hh (a b : Bool) : ℚ := if a = b then (if a then 2 else 1) else -1

lemma gg_hh (a c : Bool) : ∑ b : Bool, gg a b * hh b c = if a = c then 1 else 0 := by
  cases a <;> cases c <;> simp [gg, hh, Fintype.sum_bool] <;> norm_num

lemma tensor_det_ne (m : ℕ) :
    (Matrix.of fun y r : Fin m → Bool => ∏ i, gg (y i) (r i)).det ≠ 0 := by
  classical
  let G : Matrix (Fin m → Bool) (Fin m → Bool) ℚ := Matrix.of fun y r => ∏ i, gg (y i) (r i)
  let H : Matrix (Fin m → Bool) (Fin m → Bool) ℚ := Matrix.of fun r u => ∏ i, hh (r i) (u i)
  have hGH : G * H = 1 := by
    ext y u
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [G, H, Matrix.of_apply]
    have e1 : (∑ r : Fin m → Bool, (∏ i, gg (y i) (r i)) * ∏ i, hh (r i) (u i)) =
        ∑ r : Fin m → Bool, ∏ i, (gg (y i) (r i) * hh (r i) (u i)) :=
      Finset.sum_congr rfl fun r _ => Finset.prod_mul_distrib.symm
    have e2 : (∑ r : Fin m → Bool, ∏ i, (gg (y i) (r i) * hh (r i) (u i))) =
        ∏ i, ∑ b : Bool, gg (y i) b * hh b (u i) :=
      (Fintype.prod_sum (fun i b => gg (y i) b * hh b (u i))).symm
    rw [e1, e2]
    simp only [gg_hh]
    by_cases hyu : y = u
    · subst hyu; simp
    · rw [if_neg hyu]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hyu
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have := congrArg Matrix.det hGH
  rw [Matrix.det_mul, Matrix.det_one] at this
  intro h0
  change G.det = 0 at h0
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- Extend values on classes and on the unclassed vertices to all vertices. -/
def extd {α : Type*} {m : ℕ} (cls : α → Option (Fin m)) (y : Fin m → Bool)
    (w : {v // cls v = none} → Bool) (v : α) : Bool :=
  match h : cls v with
  | some i => y i
  | none => w ⟨v, h⟩

lemma extd_some {α : Type*} {m : ℕ} (cls : α → Option (Fin m)) (y : Fin m → Bool)
    (w : {v // cls v = none} → Bool) (v : α) (i : Fin m) (h : cls v = some i) :
    extd cls y w v = y i := by
  unfold extd
  split <;> simp_all

lemma extd_none {α : Type*} {m : ℕ} (cls : α → Option (Fin m)) (y : Fin m → Bool)
    (w : {v // cls v = none} → Bool) (v : α) (h : cls v = none) :
    extd cls y w v = w ⟨v, h⟩ := by
  unfold extd
  split <;> simp_all

lemma special_entry {n t m : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n)
    (A : Finset (Fin t)) (a b : Fin m → Fin t)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∉ A)
    (cls : Bool × Fin n → Option (Fin m)) (F : Finset (Fin 3 × Fin n))
    (h1 : ∀ i, cls (pin (a i)) = some i) (h2 : ∀ i, cls (pin (b i)) = some i)
    (h3 : ∀ e ∈ F, ∃ i, cls (false,e.2) = some i ∧ cls (true, dest e) = some i)
    (h4 : ∀ x : Bool × Fin n → Bool, (∀ e ∈ F, x (false,e.2) = x (true,dest e)) →
      ∀ v w i, cls v = some i → cls w = some i → x v = x w)
    (y r : Fin m → Bool) :
    qmat dest pin (fun e => if e ∈ F then 0 else 1) A (selS a y) (selS b r) =
      (2 : ℚ) ^ Fintype.card {v : Bool × Fin n // cls v = none} * ∏ i, gg (y i) (r i) := by
  classical
  let cc : (Bool × Fin n → Bool) → Prop := fun x =>
    ∀ v w i, cls v = some i → cls w = some i → x v = x w
  let pins : (Bool × Fin n → Bool) → Prop := fun x =>
    (∀ j ∈ A ∩ selS a y, x (pin j) = false) ∧ (∀ j ∈ selS b r, j ∉ A → x (pin j) = false)
  have hw : ∀ x : Bool × Fin n → Bool,
      (∏ e : Fin 3 × Fin n, (if x (false,e.2) = x (true,dest e) then 1 else
        (if e ∈ F then (0:ℚ) else 1))) = if cc x then 1 else 0 := by
    intro x
    by_cases hx : cc x
    · rw [if_pos hx]
      refine Finset.prod_eq_one fun e _ => ?_
      by_cases hag : x (false,e.2) = x (true,dest e)
      · rw [if_pos hag]
      · rw [if_neg hag]
        by_cases heF : e ∈ F
        · obtain ⟨i, hi1, hi2⟩ := h3 e heF
          exact absurd (hx _ _ i hi1 hi2) hag
        · rw [if_neg heF]
    · rw [if_neg hx]
      have : ¬ ∀ e ∈ F, x (false,e.2) = x (true,dest e) := fun h => hx (h4 x h)
      push_neg at this
      obtain ⟨e, heF, hne⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by rw [if_neg hne, if_pos heF])
  have step1 : qmat dest pin (fun e => if e ∈ F then 0 else 1) A (selS a y) (selS b r) =
      ∑ x ∈ Finset.univ.filter cc, (if pins x then (1:ℚ) else 0) := by
    unfold qmat
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hw x]
    by_cases hp : (∀ j ∈ A ∩ selS a y, x (pin j) = false) ∧
        (∀ j ∈ selS b r, j ∉ A → x (pin j) = false) <;> by_cases hc : cc x
    · have hp' : pins x := hp
      have hc' : ∀ (v w : Bool × Fin n) (i : Fin m), cls v = some i → cls w = some i →
          x v = x w := hc
      simp only [if_pos hp, if_pos hc, if_pos hp', if_pos hc']
    · have hc' : ¬ ∀ (v w : Bool × Fin n) (i : Fin m), cls v = some i → cls w = some i →
          x v = x w := hc
      simp only [if_pos hp, if_neg hc, if_neg hc']
    · have hp' : ¬ pins x := hp
      have hc' : ∀ (v w : Bool × Fin n) (i : Fin m), cls v = some i → cls w = some i →
          x v = x w := hc
      simp only [if_neg hp, if_pos hc, if_neg hp', if_pos hc']
    · have hc' : ¬ ∀ (v w : Bool × Fin n) (i : Fin m), cls v = some i → cls w = some i →
          x v = x w := hc
      simp only [if_neg hp, if_neg hc, if_neg hc']
  let Φ : (Fin m → Bool) × ({v // cls v = none} → Bool) → (Bool × Fin n → Bool) :=
    fun p => extd cls p.1 p.2
  let Ψ : (Bool × Fin n → Bool) → (Fin m → Bool) × ({v // cls v = none} → Bool) :=
    fun x => (fun i => x (pin (a i)), fun v => x v.1)
  have hΦc : ∀ p, cc (Φ p) := by
    intro p v w i hv hw'
    simp only [Φ]
    rw [extd_some cls p.1 p.2 v i hv, extd_some cls p.1 p.2 w i hw']
  have hΦΨ : ∀ x, cc x → Φ (Ψ x) = x := by
    intro x hx
    funext v
    simp only [Φ, Ψ]
    cases hv : cls v with
    | none => rw [extd_none cls _ _ v hv]
    | some i => rw [extd_some cls _ _ v i hv]; exact hx _ _ i (h1 i) hv
  have hΨΦ : ∀ p, Ψ (Φ p) = p := by
    intro p
    obtain ⟨y', w'⟩ := p
    simp only [Φ, Ψ, Prod.mk.injEq]
    constructor
    · funext i; exact extd_some cls y' w' _ i (h1 i)
    · funext v; exact extd_none cls y' w' v.1 v.2
  have step2 : ∑ x ∈ Finset.univ.filter cc, (if pins x then (1:ℚ) else 0) =
      ∑ p : (Fin m → Bool) × ({v // cls v = none} → Bool), (if pins (Φ p) then (1:ℚ) else 0) := by
    refine Finset.sum_bij' (fun x _ => Ψ x) (fun p _ => Φ p) (fun _ _ => Finset.mem_univ _)
      (fun p _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, hΦc p⟩)
      (fun x hx => hΦΨ x (Finset.mem_filter.1 hx).2) (fun p _ => hΨΦ p) ?_
    intro x hx
    rw [hΦΨ x (Finset.mem_filter.1 hx).2]
  have hpins : ∀ p : (Fin m → Bool) × ({v // cls v = none} → Bool),
      pins (Φ p) ↔ ∀ i, (y i = true ∨ r i = true) → p.1 i = false := by
    intro p
    have hA : ∀ i, Φ p (pin (a i)) = p.1 i := fun i => extd_some cls _ _ _ i (h1 i)
    have hB : ∀ i, Φ p (pin (b i)) = p.1 i := fun i => extd_some cls _ _ _ i (h2 i)
    simp only [pins, selS, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hP, hQ⟩ i (hi | hi)
      · rw [← hA i]; exact hP _ ⟨ha i, i, hi, rfl⟩
      · rw [← hB i]; exact hQ _ ⟨i, hi, rfl⟩ (hb i)
    · intro h
      refine ⟨?_, ?_⟩
      · rintro j ⟨_, i, hi, rfl⟩; rw [hA i]; exact h i (Or.inl hi)
      · rintro j ⟨i, hi, rfl⟩ _; rw [hB i]; exact h i (Or.inr hi)
  have step3 : ∑ p : (Fin m → Bool) × ({v // cls v = none} → Bool),
      (if pins (Φ p) then (1:ℚ) else 0) =
      ∑ p : (Fin m → Bool) × ({v // cls v = none} → Bool),
      ∏ i, (if (y i || r i) && p.1 i then (0:ℚ) else 1) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : pins (Φ p)
    · rw [if_pos hp]
      refine (Finset.prod_eq_one fun i _ => ?_).symm
      have := (hpins p).1 hp i
      rw [if_neg]
      intro hc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      rw [this hc.1] at hc
      exact Bool.false_ne_true hc.2
    · rw [if_neg hp]
      have : ¬ ∀ i, (y i = true ∨ r i = true) → p.1 i = false := fun h => hp ((hpins p).2 h)
      push_neg at this
      obtain ⟨i, hi, hpi⟩ := this
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [if_pos]
      simp only [Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨hi, by simpa using hpi⟩
  have step4 : ∑ p : (Fin m → Bool) × ({v // cls v = none} → Bool),
      ∏ i, (if (y i || r i) && p.1 i then (0:ℚ) else 1) =
      (2 : ℚ) ^ Fintype.card {v : Bool × Fin n // cls v = none} * ∏ i, gg (y i) (r i) := by
    have hc : ∀ x : Fin m → Bool, (∑ _w : {v // cls v = none} → Bool,
        ∏ i, (if (y i || r i) && x i then (0:ℚ) else 1)) =
        (2:ℚ) ^ Fintype.card {v // cls v = none} *
          ∏ i, (if (y i || r i) && x i then (0:ℚ) else 1) := by
      intro x
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_bool,
        Nat.cast_pow, Nat.cast_ofNat]
    simp only [Fintype.sum_prod_type]
    simp only [hc]
    rw [← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i b => if (y i || r i) && b then (0:ℚ) else 1)]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> cases r i <;> simp [gg, Fintype.sum_bool] <;> norm_num
  rw [step1, step2, step3, step4]


theorem framework {n t : ℕ} (dest : Fin 3 × Fin n → Fin n) (pin : Fin t → Bool × Fin n) (N : ℕ)
    (hN : 2 ^ t * 2 ^ t + 2 ≤ N)
    (cert : ∀ A : Finset (Fin t), ∃ (a b : Fin (min A.card (t - A.card)) → Fin t)
      (cls : Bool × Fin n → Option (Fin (min A.card (t - A.card)))) (F : Finset (Fin 3 × Fin n)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∉ A) ∧ (∀ i, cls (pin (a i)) = some i) ∧
      (∀ i, cls (pin (b i)) = some i) ∧
      (∀ e ∈ F, ∃ i, cls (false,e.2) = some i ∧ cls (true, dest e) = some i) ∧
      (∀ x : Bool × Fin n → Bool, (∀ e ∈ F, x (false,e.2) = x (true,dest e)) →
        ∀ v w i, cls v = some i → cls w = some i → x v = x w)) :
    ∃ z : Fin 3 × Fin n → ℕ, (∀ e, 2 ≤ z e ∧ z e ≤ N) ∧
      ∀ A, (qmat dest pin (fun e => (z e : ℚ)) A).rank = 2 ^ (min A.card (t - A.card)) := by
  classical
  choose a b cls F ha hb h1 h2 h3 h4 using cert
  let D : Finset (Fin t) → MvPolynomial (Fin 3 × Fin n) ℚ := fun A => dpoly dest pin A (a A) (b A)
  have hD : ∀ A, D A ≠ 0 := by
    intro A h0
    have hev := eval_dpoly dest pin (fun e => if e ∈ F A then 0 else 1) A (a A) (b A)
    have h0' : dpoly dest pin A (a A) (b A) = 0 := h0
    rw [h0', map_zero] at hev
    have hmat : (Matrix.of fun y r : Fin (min A.card (t - A.card)) → Bool =>
        qmat dest pin (fun e => if e ∈ F A then 0 else 1) A (selS (a A) y) (selS (b A) r)) =
        ((2 : ℚ) ^ Fintype.card {v : Bool × Fin n // cls A v = none}) •
          Matrix.of fun y r : Fin (min A.card (t - A.card)) → Bool => ∏ i, gg (y i) (r i) := by
      ext y r
      rw [Matrix.of_apply, special_entry dest pin A (a A) (b A) (ha A) (hb A) (cls A) (F A)
        (h1 A) (h2 A) (h3 A) (h4 A) y r]
      simp
    rw [hmat, Matrix.det_smul] at hev
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) (tensor_det_ne _) hev.symm
  have hdeg : ∀ A e, degreeOf e (D A) ≤ 2 ^ t := by
    intro A e
    refine (degreeOf_det_le _ e 1 fun y r => degreeOf_qpoly_le dest pin A _ _ e).trans ?_
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, mul_one]
    exact Nat.pow_le_pow_right (by norm_num) ((min_le_right _ _).trans (Nat.sub_le _ _))
  obtain ⟨z, hz, hz'⟩ := exists_prices (Finset (Fin t)) D (2 ^ t) N hD hdeg
    (by rw [Fintype.card_finset, Fintype.card_fin]; exact hN)
  refine ⟨z, hz, fun A => le_antisymm (rank_le dest pin _ A) (rank_ge dest pin _ A (a A) (b A) ?_)⟩
  rw [← eval_dpoly]
  exact hz' A


/-! ## The concrete drawing -/


lemma fin4_cases (d : Fin 4) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by fin_cases d <;> simp
lemma fin3_cases (d : Fin 3) : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp

abbrev Port (k : ℕ) := Fin (2*k) × Fin (2*k) × Fin 4

def cnext {k : ℕ} (c : Fin (2*k)) : Fin (2*k) :=
  if h : c.val + 1 < 2*k then ⟨c.val+1, h⟩ else ⟨0, by have := c.isLt; omega⟩

def cprev {k : ℕ} (c : Fin (2*k)) : Fin (2*k) :=
  if h : c.val = 0 then ⟨2*k-1, by have := c.isLt; omega⟩
  else ⟨c.val - 1, by have := c.isLt; omega⟩

def cpair {k : ℕ} (c : Fin (2*k)) : Fin (2*k) :=
  if h : c.val % 2 = 0 then ⟨c.val + 1, by have := c.isLt; omega⟩
  else ⟨c.val - 1, by have := c.isLt; omega⟩

lemma cnext_val {k : ℕ} (c : Fin (2*k)) :
    (cnext c).val = if c.val + 1 < 2*k then c.val + 1 else 0 := by
  unfold cnext; split_ifs <;> rfl

lemma cprev_val {k : ℕ} (c : Fin (2*k)) :
    (cprev c).val = if c.val = 0 then 2*k-1 else c.val - 1 := by
  unfold cprev; split_ifs <;> rfl

lemma cpair_val {k : ℕ} (c : Fin (2*k)) :
    (cpair c).val = if c.val % 2 = 0 then c.val + 1 else c.val - 1 := by
  unfold cpair; split_ifs <;> rfl

lemma cprev_cnext {k : ℕ} (c : Fin (2*k)) : cprev (cnext c) = c := by
  apply Fin.ext; have := c.isLt
  by_cases h : c.val + 1 < 2*k
  · rw [cprev_val, cnext_val, if_pos h, if_neg (by omega)]; omega
  · rw [cprev_val, cnext_val, if_neg h, if_pos rfl]; omega

lemma cnext_cprev {k : ℕ} (c : Fin (2*k)) : cnext (cprev c) = c := by
  apply Fin.ext; rw [cnext_val, cprev_val]; have := c.isLt; split_ifs <;> omega

lemma cpair_cpair {k : ℕ} (c : Fin (2*k)) : cpair (cpair c) = c := by
  apply Fin.ext; rw [cpair_val, cpair_val]; have := c.isLt; split_ifs <;> omega

def facing {k : ℕ} (p : Port k) : Port k :=
  if p.2.2 = 0 then
    (if h : p.1.val + 1 < 2*k then (⟨p.1.val+1, h⟩, p.2.1, 2) else (p.1, cpair p.2.1, 0))
  else if p.2.2 = 2 then
    (if h : p.1.val = 0 then (p.1, cpair p.2.1, 2)
     else (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2.1, 0))
  else if p.2.2 = 1 then (p.1, cnext p.2.1, 3)
  else (p.1, cprev p.2.1, 1)

lemma facing_N {k : ℕ} (r c : Fin (2*k)) (h : r.val + 1 < 2*k) :
    facing (r, c, 0) = (⟨r.val+1, h⟩, c, 2) := by
  simp [facing, h]
lemma facing_Ntop {k : ℕ} (r c : Fin (2*k)) (h : ¬ r.val + 1 < 2*k) :
    facing (r, c, 0) = (r, cpair c, 0) := by
  simp [facing, h]
lemma facing_S {k : ℕ} (r c : Fin (2*k)) (h : r.val ≠ 0) :
    facing (r, c, 2) = (⟨r.val-1, by have := r.isLt; omega⟩, c, 0) := by
  simp [facing, h]
lemma facing_Sbot {k : ℕ} (r c : Fin (2*k)) (h : r.val = 0) :
    facing (r, c, 2) = (r, cpair c, 2) := by
  simp [facing, h]
lemma facing_E {k : ℕ} (r c : Fin (2*k)) : facing (r, c, 1) = (r, cnext c, 3) := by
  simp [facing]
lemma facing_W {k : ℕ} (r c : Fin (2*k)) : facing (r, c, 3) = (r, cprev c, 1) := by
  simp [facing]

lemma facing_facing {k : ℕ} (p : Port k) : facing (facing p) = p := by
  obtain ⟨r, c, d⟩ := p
  rcases fin4_cases d with rfl | rfl | rfl | rfl
  · by_cases h : r.val + 1 < 2*k
    · rw [facing_N r c h, facing_S _ c (by simp)]; simp
    · rw [facing_Ntop r c h, facing_Ntop r _ h, cpair_cpair]
  · rw [facing_E, facing_W, cprev_cnext]
  · by_cases h : r.val = 0
    · rw [facing_Sbot r c h, facing_Sbot r _ h, cpair_cpair]
    · rw [facing_S r c h, facing_N _ c (by simp; have := r.isLt; omega)]
      simp only [Prod.mk.injEq, and_true]; ext; simp; omega
  · rw [facing_W, facing_E, cnext_cprev]

/-- parity value of a port: the port is on the `true` side iff it is odd -/
def pval {k : ℕ} (p : Port k) : ℕ := p.2.2.val + p.1.val + p.2.1.val

def vside {k : ℕ} (p : Port k) : Bool := pval p % 2 == 1

lemma bool_flip (a b : ℕ) (h : a % 2 ≠ b % 2) : (a % 2 == 1) = !(b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all

lemma pval_facing {k : ℕ} (p : Port k) : pval (facing p) % 2 ≠ pval p % 2 := by
  obtain ⟨r, c, d⟩ := p
  have hc := c.isLt
  rcases fin4_cases d with rfl | rfl | rfl | rfl
  · by_cases h : r.val + 1 < 2*k
    · rw [facing_N r c h]; simp [pval]; omega
    · rw [facing_Ntop r c h]; simp only [pval, cpair_val]; split_ifs <;> simp <;> omega
  · rw [facing_E]; simp only [pval, cnext_val]; split_ifs <;> simp <;> omega
  · by_cases h : r.val = 0
    · rw [facing_Sbot r c h]; simp only [pval, cpair_val]; split_ifs <;> simp <;> omega
    · rw [facing_S r c h]; simp [pval]; omega
  · rw [facing_W]; simp only [pval, cprev_val]; split_ifs <;> simp <;> omega

lemma vside_facing {k : ℕ} (p : Port k) : vside (facing p) = !vside p :=
  bool_flip _ _ (pval_facing p)

abbrev XX (k : ℕ) := Fin (2*k) × Fin (2*k) × Fin 2

def vslot {k : ℕ} (p : Port k) : Fin 2 :=
  ⟨((p.2.2.val + 4 - (p.1.val + p.2.1.val) % 2) % 4) / 2, by omega⟩

def xOf {k : ℕ} (p : Port k) : XX k := (p.1, p.2.1, vslot p)

def portOf {k : ℕ} (b : Bool) (x : XX k) : Port k :=
  (x.1, x.2.1, ⟨((x.1.val + x.2.1.val) % 2 + 2 * x.2.2.val + (if b then 1 else 0)) % 4, by omega⟩)

lemma portOf_xOf {k : ℕ} (p : Port k) : portOf (vside p) (xOf p) = p := by
  obtain ⟨r, c, d⟩ := p
  have hd := d.isLt
  simp only [portOf, xOf, vslot, vside, pval, Prod.mk.injEq, true_and]
  ext
  simp only
  by_cases h : (d.val + r.val + c.val) % 2 = 1
  · simp [h]; omega
  · have h' : (d.val + r.val + c.val) % 2 = 0 := by omega
    simp [h']; omega

lemma vside_portOf {k : ℕ} (b : Bool) (x : XX k) : vside (portOf b x) = b := by
  obtain ⟨r, c, s⟩ := x
  have hs := s.isLt
  cases b <;> simp [portOf, vside, pval] <;> omega

lemma xOf_portOf {k : ℕ} (b : Bool) (x : XX k) : xOf (portOf b x) = x := by
  obtain ⟨r, c, s⟩ := x
  have hs := s.isLt
  simp only [portOf, xOf, vslot, Prod.mk.injEq, true_and]
  ext
  cases b <;> simp <;> omega

def eX (k : ℕ) : XX k ≃ Fin (8*k^2) :=
  ((Equiv.refl (Fin (2*k))).prodCongr finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

def vertexOf {k : ℕ} (p : Port k) : Bool × Fin (8*k^2) := (vside p, eX k (xOf p))

lemma vertexOf_injective {k : ℕ} : Function.Injective (vertexOf (k := k)) := by
  intro p q h
  simp only [vertexOf, Prod.mk.injEq] at h
  rw [← portOf_xOf p, ← portOf_xOf q, h.1, (eX k).injective h.2]

lemma vertexOf_surjective {k : ℕ} : Function.Surjective (vertexOf (k := k)) := by
  intro v
  refine ⟨portOf v.1 ((eX k).symm v.2), ?_⟩
  simp [vertexOf, vside_portOf, xOf_portOf]

def sX {k : ℕ} : Equiv.Perm (XX k) where
  toFun x := (x.1, x.2.1, ⟨1 - x.2.2.val, by omega⟩)
  invFun x := (x.1, x.2.1, ⟨1 - x.2.2.val, by omega⟩)
  left_inv x := by
    obtain ⟨a, b, s⟩ := x; have := s.isLt
    simp only [Prod.mk.injEq, true_and]; ext; simp; omega
  right_inv x := by
    obtain ⟨a, b, s⟩ := x; have := s.isLt
    simp only [Prod.mk.injEq, true_and]; ext; simp; omega

lemma facing_portOf_side {k : ℕ} (b : Bool) (x : XX k) :
    portOf (!b) (xOf (facing (portOf b x))) = facing (portOf b x) := by
  have h := portOf_xOf (facing (portOf b x))
  rw [vside_facing, vside_portOf] at h
  exact h

def tX {k : ℕ} : Equiv.Perm (XX k) where
  toFun x := xOf (facing (portOf false x))
  invFun y := xOf (facing (portOf true y))
  left_inv x := by
    show xOf (facing (portOf true (xOf (facing (portOf false x))))) = x
    have h := facing_portOf_side false x
    simp only [Bool.not_false] at h
    rw [h, facing_facing, xOf_portOf]
  right_inv y := by
    show xOf (facing (portOf false (xOf (facing (portOf true y))))) = y
    have h := facing_portOf_side true y
    simp only [Bool.not_true] at h
    rw [h, facing_facing, xOf_portOf]

/-- the three neighbours of a port: clockwise, counterclockwise in its cell, and facing -/
def nb {k : ℕ} (p : Port k) (κ : Fin 3) : Port k :=
  if κ = 0 then (p.1, p.2.1, p.2.2 + 1) else if κ = 1 then (p.1, p.2.1, p.2.2 - 1) else facing p

def sw (κ : Fin 3) : Fin 3 := if κ = 0 then 1 else if κ = 1 then 0 else 2

lemma nb_nb {k : ℕ} (p : Port k) (κ : Fin 3) : nb (nb p κ) (sw κ) = p := by
  rcases fin3_cases κ with rfl | rfl | rfl <;> simp [nb, sw, facing_facing]

lemma vside_nb {k : ℕ} (p : Port k) (κ : Fin 3) : vside (nb p κ) = !vside p := by
  rcases fin3_cases κ with rfl | rfl | rfl
  · simp only [nb, ite_true]
    apply bool_flip
    obtain ⟨r, c, d⟩ := p
    rcases fin4_cases d with rfl | rfl | rfl | rfl <;> simp [pval] <;> omega
  · simp only [nb]; simp only [show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true]
    apply bool_flip
    obtain ⟨r, c, d⟩ := p
    rcases fin4_cases d with rfl | rfl | rfl | rfl <;> simp [pval] <;> omega
  · simp only [nb]; simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ite_false]
    exact vside_facing p

/-- false ports: their three neighbours as `true` ports of the three matchings -/
lemma nb0_false {k : ℕ} (p : Port k) (h : vside p = false) : portOf true (xOf p) = nb p 0 := by
  obtain ⟨r, c, d⟩ := p
  simp only [vside, pval, beq_eq_false_iff_ne, ne_eq] at h
  simp only [portOf, xOf, vslot, nb, ite_true, Prod.mk.injEq, true_and]
  rcases fin4_cases d with rfl | rfl | rfl | rfl <;> (ext; simp at h ⊢; omega)

lemma nb1_false {k : ℕ} (p : Port k) (h : vside p = false) :
    portOf true (sX (xOf p)) = nb p 1 := by
  obtain ⟨r, c, d⟩ := p
  simp only [vside, pval, beq_eq_false_iff_ne, ne_eq] at h
  have e1 : nb (r, c, d) 1 = (r, c, d - 1) := by simp [nb]
  rw [e1]
  refine Prod.ext rfl (Prod.ext rfl (Fin.ext ?_))
  simp only [portOf, xOf, vslot, sX, Equiv.coe_fn_mk, ite_true]
  rcases fin4_cases d with rfl | rfl | rfl | rfl <;> simp at h ⊢ <;> omega

lemma nb2_false {k : ℕ} (p : Port k) (h : vside p = false) :
    portOf true (tX (xOf p)) = nb p 2 := by
  have h1 : portOf false (xOf p) = p := by rw [← h]; exact portOf_xOf p
  have h2 := facing_portOf_side false (xOf p)
  simp only [Bool.not_false, h1] at h2
  simp only [nb, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false]
  show portOf true (xOf (facing (portOf false (xOf p)))) = facing p
  rw [h1, h2]

/-! ## Darts of the drawing with the apex -/

abbrev Dt (k : ℕ) := (Port k × Fin 3) ⊕ (Fin (2*k) ⊕ Fin (2*k))

def pinDir {k : ℕ} (c : Fin (2*k)) : Fin 4 := if c.val % 2 = 0 then 3 else 0
def topR {k : ℕ} (c : Fin (2*k)) : Fin (2*k) := ⟨2*k-1, by have := c.isLt; omega⟩
def pinPort {k : ℕ} (c : Fin (2*k)) : Port k := (topR c, c, pinDir c)
def isPinB {k : ℕ} (p : Port k) : Bool :=
  decide (p.1.val + 1 = 2*k) && decide (p.2.2 = pinDir p.2.1)

lemma isPinB_iff {k : ℕ} (p : Port k) : isPinB p = true ↔ pinPort p.2.1 = p := by
  obtain ⟨r, c, d⟩ := p
  have := r.isLt
  simp only [isPinB, pinPort, topR, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h2]; congr 1; ext; simp; omega
  · intro h
    have h1 := congrArg (fun p : Port k => p.1.val) h
    have h2 := congrArg (fun p : Port k => p.2.2) h
    simp at h1 h2
    exact ⟨by omega, h2.symm⟩

@[simp] lemma pinPort_snd {k : ℕ} (c : Fin (2*k)) : (pinPort c).2.1 = c := rfl

lemma isPinB_pinPort {k : ℕ} (c : Fin (2*k)) : isPinB (pinPort c) = true :=
  (isPinB_iff _).2 rfl

lemma pinPort_inj {k : ℕ} {c c' : Fin (2*k)} (h : pinPort c = pinPort c') : c = c' :=
  congrArg (fun p : Port k => p.2.1) h

lemma isPinB_row {k : ℕ} (p : Port k) (h : p.1.val + 1 ≠ 2*k) : isPinB p = false := by
  simp [isPinB, h]

lemma isPinB_dir {k : ℕ} (p : Port k) (h1 : p.2.2 ≠ 0) (h2 : p.2.2 ≠ 3) : isPinB p = false := by
  simp only [isPinB, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; unfold pinDir; split_ifs <;> simp_all

def drev {k : ℕ} : Dt k → Dt k
  | .inl (p, κ) => .inl (nb p κ, sw κ)
  | .inr (.inl c) => .inr (.inr c)
  | .inr (.inr c) => .inr (.inl c)

lemma drev_drev {k : ℕ} (d : Dt k) : drev (drev d) = d := by
  rcases d with ⟨p, κ⟩ | c | c
  · simp only [drev, nb_nb]; rcases fin3_cases κ with rfl | rfl | rfl <;> rfl
  · rfl
  · rfl

def drot {k : ℕ} : Dt k → Dt k
  | .inl (p, κ) => if κ = 2 then (if isPinB p then .inr (.inl p.2.1) else .inl (p, 0))
      else .inl (p, κ + 1)
  | .inr (.inl c) => .inl (pinPort c, 0)
  | .inr (.inr c) => .inr (.inr (cprev c))

def drotInv {k : ℕ} : Dt k → Dt k
  | .inl (p, κ) => if κ = 0 then (if isPinB p then .inr (.inl p.2.1) else .inl (p, 2))
      else .inl (p, κ - 1)
  | .inr (.inl c) => .inl (pinPort c, 2)
  | .inr (.inr c) => .inr (.inr (cnext c))

lemma drotInv_drot {k : ℕ} (d : Dt k) : drotInv (drot d) = d := by
  rcases d with ⟨p, κ⟩ | c | c
  · rcases fin3_cases κ with rfl | rfl | rfl
    · simp [drot, drotInv]
    · simp [drot, drotInv]
    · by_cases hp : isPinB p = true
      · simp [drot, drotInv, hp, (isPinB_iff p).1 hp]
      · simp [drot, drotInv, hp]
  · simp [drot, drotInv, isPinB_pinPort, pinPort_snd]
  · simp [drot, drotInv, cnext_cprev]

noncomputable def rotP (k : ℕ) : Equiv.Perm (Dt k) :=
  Equiv.ofBijective drot (Finite.injective_iff_bijective.mp
    (Function.LeftInverse.injective drotInv_drot))

def revP (k : ℕ) : Equiv.Perm (Dt k) := Function.Involutive.toPerm drev drev_drev

def dsrc {k : ℕ} : Dt k → Option (Bool × Fin (8*k^2))
  | .inl (p, _) => some (vertexOf p)
  | .inr (.inl c) => some (vertexOf (pinPort c))
  | .inr (.inr _) => none

def sig (k : ℕ) : Equiv.Perm (Fin (8*k^2)) := (eX k).permCongr sX
def tau (k : ℕ) : Equiv.Perm (Fin (8*k^2)) := (eX k).permCongr tX
def pinV {k : ℕ} (c : Fin (2*k)) : Bool × Fin (8*k^2) := vertexOf (pinPort c)

def arcB {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (a b : Bool × Fin n) : Bool :=
  !a.1 && b.1 && (decide (a.2 = b.2) || decide (σ a.2 = b.2) || decide (τ a.2 = b.2))
def linkB {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (a b : Bool × Fin n) : Bool :=
  arcB σ τ a b || arcB σ τ b a
def rimB {n t : ℕ} (pin : Fin t → Bool × Fin n) (a : Bool × Fin n) : Bool :=
  decide (∃ j, pin j = a)
def incB {n t : ℕ} (σ τ : Equiv.Perm (Fin n)) (pin : Fin t → Bool × Fin n)
    (x y : Option (Bool × Fin n)) : Bool :=
  x.elim (y.elim false (rimB pin)) (fun a => y.elim (rimB pin a) (linkB σ τ a))

lemma sig_eX {k : ℕ} (x : XX k) : sig k (eX k x) = eX k (sX x) := by simp [sig]
lemma tau_eX {k : ℕ} (x : XX k) : tau k (eX k x) = eX k (tX x) := by simp [tau]

lemma arc_vertexOf {k : ℕ} (p q : Port k) :
    arcB (sig k) (tau k) (vertexOf p) (vertexOf q) = true ↔
      vside p = false ∧ ∃ κ, q = nb p κ := by
  simp only [arcB, vertexOf, sig_eX, tau_eX, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true, decide_eq_true_eq, (eX k).injective.eq_iff]
  constructor
  · rintro ⟨⟨hp, hq⟩, h⟩
    refine ⟨hp, ?_⟩
    have hq' : q = portOf true (xOf q) := by rw [← hq]; exact (portOf_xOf q).symm
    rcases h with (h | h) | h
    · exact ⟨0, by rw [hq', ← h, nb0_false p hp]⟩
    · exact ⟨1, by rw [hq', ← h, nb1_false p hp]⟩
    · exact ⟨2, by rw [hq', ← h, nb2_false p hp]⟩
  · rintro ⟨hp, κ, rfl⟩
    refine ⟨⟨hp, by rw [vside_nb, hp]; rfl⟩, ?_⟩
    rcases fin3_cases κ with rfl | rfl | rfl
    · left; left; rw [← nb0_false p hp, xOf_portOf]
    · left; right; rw [← nb1_false p hp, xOf_portOf]
    · right; rw [← nb2_false p hp, xOf_portOf]

lemma link_vertexOf {k : ℕ} (p q : Port k) :
    linkB (sig k) (tau k) (vertexOf p) (vertexOf q) = true ↔ ∃ κ, q = nb p κ := by
  simp only [linkB, Bool.or_eq_true, arc_vertexOf]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, κ, rfl⟩)
    · exact h
    · exact ⟨sw κ, (nb_nb q κ).symm⟩
  · rintro ⟨κ, rfl⟩
    cases hp : vside p
    · exact Or.inl ⟨rfl, κ, rfl⟩
    · exact Or.inr ⟨by rw [vside_nb, hp]; rfl, sw κ, (nb_nb p κ).symm⟩

lemma inc_iff {k : ℕ} (a b : Option (Bool × Fin (8*k^2))) :
    incB (sig k) (tau k) pinV a b = true ↔ ∃ d : Dt k, dsrc d = a ∧ dsrc (drev d) = b := by
  rcases a with _ | a <;> rcases b with _ | b
  · simp only [incB, Option.elim]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨d, h1, h2⟩
      rcases d with ⟨p, κ⟩ | c | c <;> simp [dsrc, drev] at h1 h2
  · simp only [incB, Option.elim, rimB, decide_eq_true_eq]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨.inr (.inr j), rfl, rfl⟩
    · rintro ⟨d, h1, h2⟩
      rcases d with ⟨p, κ⟩ | c | c <;> simp [dsrc, drev] at h1 h2
      exact ⟨c, h2⟩
  · simp only [incB, Option.elim, rimB, decide_eq_true_eq]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨.inr (.inl j), rfl, rfl⟩
    · rintro ⟨d, h1, h2⟩
      rcases d with ⟨p, κ⟩ | c | c <;> simp [dsrc, drev] at h1 h2
      exact ⟨c, h1⟩
  · simp only [incB, Option.elim]
    obtain ⟨p, rfl⟩ := vertexOf_surjective a
    obtain ⟨q, rfl⟩ := vertexOf_surjective b
    rw [link_vertexOf]
    constructor
    · rintro ⟨κ, rfl⟩; exact ⟨.inl (p, κ), rfl, rfl⟩
    · rintro ⟨d, h1, h2⟩
      rcases d with ⟨p', κ⟩ | c | c <;> simp [dsrc, drev] at h1 h2
      have e := vertexOf_injective h1
      subst e
      exact ⟨κ, (vertexOf_injective h2).symm⟩

lemma facing_dir {k : ℕ} (p : Port k) : (facing p).2.2 = p.2.2 ∨ (facing p).2.2 = p.2.2 + 2 := by
  obtain ⟨r, c, d⟩ := p
  rcases fin4_cases d with rfl | rfl | rfl | rfl
  · by_cases h : r.val + 1 < 2*k
    · rw [facing_N r c h]; right; rfl
    · rw [facing_Ntop r c h]; left; rfl
  · rw [facing_E]; right; rfl
  · by_cases h : r.val = 0
    · rw [facing_Sbot r c h]; left; rfl
    · rw [facing_S r c h]; right; rfl
  · rw [facing_W]; right; rfl

lemma nb_inj {k : ℕ} (p : Port k) (κ κ' : Fin 3) (h : nb p κ = nb p κ') : κ = κ' := by
  have hd := congrArg (fun x : Port k => x.2.2) h
  have hf := facing_dir p
  obtain ⟨r, c, d⟩ := p
  simp only at hf
  rcases fin3_cases κ with rfl | rfl | rfl <;> rcases fin3_cases κ' with rfl | rfl | rfl <;>
    simp only [nb, ite_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, ite_false] at hd <;>
    first
    | rfl
    | (rcases fin4_cases d with rfl | rfl | rfl | rfl <;> revert hd <;> decide)
    | (rcases fin4_cases d with rfl | rfl | rfl | rfl <;> rcases hf with hf | hf <;>
        rw [hf] at hd <;> revert hd <;> decide)

lemma src_dst_inj {k : ℕ} : Function.Injective (fun d : Dt k => (dsrc d, dsrc (drev d))) := by
  intro d d' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases d with ⟨p, κ⟩ | c | c <;> rcases d' with ⟨p', κ'⟩ | c' | c' <;>
    simp [dsrc, drev] at h1 h2 ⊢
  · have hp := vertexOf_injective h1
    subst hp
    exact ⟨rfl, nb_inj p κ κ' (vertexOf_injective h2)⟩
  · exact pinPort_inj (vertexOf_injective h1)
  · exact pinPort_inj (vertexOf_injective h2)

/-! ## Rotation is transitive at every vertex -/

lemma rot_pow {k : ℕ} (j : ℕ) (d : Dt k) : (rotP k ^ j) d = drot^[j] d := by
  rw [Equiv.Perm.coe_pow]; rfl

lemma cprev_iter {k : ℕ} (c : Fin (2*k)) (j : ℕ) (hj : j ≤ c.val) :
    (cprev^[j] c).val = c.val - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', cprev_val, ih (by omega)]
    split_ifs <;> omega

lemma cprev_reach {k : ℕ} (c c' : Fin (2*k)) : ∃ j, cprev^[j] c = c' := by
  have hc := c.isLt; have hc' := c'.isLt
  by_cases h : c'.val ≤ c.val
  · exact ⟨c.val - c'.val, Fin.ext (by rw [cprev_iter c _ (by omega)]; omega)⟩
  · refine ⟨(2*k-1-c'.val) + (c.val + 1), Fin.ext ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_succ_apply']
    have h0 : (cprev^[c.val] c).val = 0 := by rw [cprev_iter c _ le_rfl]; omega
    have h1 : (cprev (cprev^[c.val] c)).val = 2*k-1 := by rw [cprev_val, if_pos h0]
    rw [cprev_iter _ _ (by omega), h1]; omega

lemma drot_iter_apex {k : ℕ} (c : Fin (2*k)) (j : ℕ) :
    drot^[j] (.inr (.inr c) : Dt k) = .inr (.inr (cprev^[j] c)) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

lemma rot_trans {k : ℕ} (a b : Dt k) (h : dsrc a = dsrc b) : ∃ j : ℕ, (rotP k ^ j) a = b := by
  simp only [rot_pow]
  rcases a with ⟨p, κ⟩ | c | c <;> rcases b with ⟨p', κ'⟩ | c' | c' <;> simp [dsrc] at h
  · have e := vertexOf_injective h
    subst e
    by_cases hp : isPinB p = true
    · rcases fin3_cases κ with rfl | rfl | rfl <;> rcases fin3_cases κ' with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simp [drot]⟩
      · exact ⟨2, by simp [drot]⟩
      · exact ⟨3, by simp [drot, hp, (isPinB_iff p).1 hp]⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simp [drot]⟩
      · exact ⟨2, by simp [drot, hp, (isPinB_iff p).1 hp]⟩
      · exact ⟨3, by simp [drot, hp, (isPinB_iff p).1 hp]⟩
      · exact ⟨0, rfl⟩
    · simp only [Bool.not_eq_true] at hp
      rcases fin3_cases κ with rfl | rfl | rfl <;> rcases fin3_cases κ' with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simp [drot]⟩
      · exact ⟨2, by simp [drot]⟩
      · exact ⟨2, by simp [drot, hp]⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simp [drot]⟩
      · exact ⟨1, by simp [drot, hp]⟩
      · exact ⟨2, by simp [drot, hp]⟩
      · exact ⟨0, rfl⟩
  · have e := vertexOf_injective h
    subst e
    have hp := isPinB_pinPort c'
    rcases fin3_cases κ with rfl | rfl | rfl
    · exact ⟨3, by simp [drot, hp]⟩
    · exact ⟨2, by simp [drot, hp]⟩
    · exact ⟨1, by simp [drot, hp]⟩
  · have e := vertexOf_injective h
    subst e
    rcases fin3_cases κ' with rfl | rfl | rfl
    · exact ⟨1, by simp [drot]⟩
    · exact ⟨2, by simp [drot]⟩
    · exact ⟨3, by simp [drot]⟩
  · exact ⟨0, by rw [pinPort_inj (vertexOf_injective h)]; rfl⟩
  · obtain ⟨j, hj⟩ := cprev_reach c c'
    exact ⟨j, by rw [drot_iter_apex, hj]⟩

lemma src_rot {k : ℕ} (d : Dt k) : dsrc (drot d) = dsrc d := by
  rcases d with ⟨p, κ⟩ | c | c
  · rcases fin3_cases κ with rfl | rfl | rfl
    · simp [drot, dsrc]
    · simp [drot, dsrc]
    · by_cases hp : isPinB p = true
      · simp [drot, dsrc, hp, (isPinB_iff p).1 hp]
      · simp [drot, dsrc, hp]
  · rfl
  · rfl

/-! ## The faces of the drawing -/

def walkF {k : ℕ} (d : Dt k) : Dt k := drot (drev d)

lemma walk_k1 {k : ℕ} (r c : Fin (2*k)) (d : Fin 4) :
    walkF (.inl ((r, c, d), 1)) = .inl ((r, c, d - 1), 1) := by
  simp [walkF, drev, drot, nb, sw]
lemma walk_k0 {k : ℕ} (r c : Fin (2*k)) (d : Fin 4) :
    walkF (.inl ((r, c, d), 0)) = .inl ((r, c, d + 1), 2) := by
  simp [walkF, drev, drot, nb, sw]
lemma walk_k2 {k : ℕ} (p : Port k) :
    walkF (.inl (p, 2)) = if isPinB (facing p) then .inr (.inl (facing p).2.1)
      else .inl (facing p, 0) := by
  simp [walkF, drev, drot, nb, sw]
lemma walk_k2' {k : ℕ} (p : Port k) (h : isPinB (facing p) = false) :
    walkF (.inl (p, 2)) = .inl (facing p, 0) := by
  rw [walk_k2, h]; rfl
lemma walk_pa {k : ℕ} (c : Fin (2*k)) : walkF (.inr (.inl c) : Dt k) = .inr (.inr (cprev c)) :=
  rfl
lemma walk_ap {k : ℕ} (c : Fin (2*k)) : walkF (.inr (.inr c) : Dt k) = .inl (pinPort c, 0) :=
  rfl

def cellDart {k : ℕ} (r c : Fin (2*k)) (t : ℕ) : Dt k :=
  .inl ((r, c, ⟨(4 - t % 4) % 4, by omega⟩), 1)

def oR0 {k : ℕ} (r : Fin (2*k-1)) : Fin (2*k) := ⟨r.val, by have := r.isLt; omega⟩
def oR1 {k : ℕ} (r : Fin (2*k-1)) : Fin (2*k) := ⟨r.val + 1, by have := r.isLt; omega⟩

def octDart {k : ℕ} (r : Fin (2*k-1)) (c : Fin (2*k)) : ℕ → Dt k
  | 0 => .inl ((oR0 r, c, 0), 0)
  | 1 => .inl ((oR0 r, c, 1), 2)
  | 2 => .inl ((oR0 r, cnext c, 3), 0)
  | 3 => .inl ((oR0 r, cnext c, 0), 2)
  | 4 => .inl ((oR1 r, cnext c, 2), 0)
  | 5 => .inl ((oR1 r, cnext c, 3), 2)
  | 6 => .inl ((oR1 r, c, 1), 0)
  | _ => .inl ((oR1 r, c, 2), 2)

def tc0 {k : ℕ} (j : Fin k) : Fin (2*k) := ⟨2*j.val, by have := j.isLt; omega⟩
def tc1 {k : ℕ} (j : Fin k) : Fin (2*k) := ⟨2*j.val+1, by have := j.isLt; omega⟩
def tT {k : ℕ} (j : Fin k) : Fin (2*k) := ⟨2*k-1, by have := j.isLt; omega⟩
def tB {k : ℕ} (j : Fin k) : Fin (2*k) := ⟨0, by have := j.isLt; omega⟩

def topDart {k : ℕ} (j : Fin k) : ℕ → Dt k
  | 0 => .inl ((tT j, tc1 j, 3), 0)
  | 1 => .inl ((tT j, tc1 j, 0), 2)
  | 2 => .inl ((tT j, tc0 j, 0), 0)
  | _ => .inl ((tT j, tc0 j, 1), 2)

def botDart {k : ℕ} (j : Fin k) : ℕ → Dt k
  | 0 => .inl ((tB j, tc0 j, 1), 0)
  | 1 => .inl ((tB j, tc0 j, 2), 2)
  | 2 => .inl ((tB j, tc1 j, 2), 0)
  | _ => .inl ((tB j, tc1 j, 3), 2)

def blkDart {k : ℕ} (j : Fin k) : ℕ → Dt k
  | 0 => .inl ((tB j, tc1 j, 1), 0)
  | 1 => .inl ((tB j, tc1 j, 2), 2)
  | 2 => .inl ((tB j, tc0 j, 2), 0)
  | _ => .inl ((tB j, tc0 j, 3), 2)

def apexDart {k : ℕ} (c : Fin (2*k)) : ℕ → Dt k
  | 0 => .inr (.inr c)
  | 1 => .inl (pinPort c, 0)
  | 2 => .inl ((topR c, c, pinDir c + 1), 2)
  | _ => .inr (.inl (cnext c))

def innerBlk {k : ℕ} (m : Fin (4*k)) : Fin k := ⟨k - 1 - m.val / 4, by have := m.isLt; omega⟩

def innerDart {k : ℕ} (m : Fin (4*k)) : Dt k := blkDart (innerBlk m) (m.val % 4)

abbrev FLab (k : ℕ) := (Fin (2*k) × Fin (2*k)) ⊕ ((Fin (2*k-1) × Fin (2*k)) ⊕
  (Fin k ⊕ (Fin (2*k) ⊕ (Fin k ⊕ Unit))))

def flen {k : ℕ} : FLab k → ℕ
  | .inl _ => 4
  | .inr (.inl _) => 8
  | .inr (.inr (.inl _)) => 4
  | .inr (.inr (.inr (.inl _))) => 4
  | .inr (.inr (.inr (.inr (.inl _)))) => 4
  | .inr (.inr (.inr (.inr (.inr _)))) => 4*k

def fdart {k : ℕ} : (Σ i : FLab k, Fin (flen i)) → Dt k
  | ⟨.inl (r, c), t⟩ => cellDart r c t.val
  | ⟨.inr (.inl (r, c)), t⟩ => octDart r c t.val
  | ⟨.inr (.inr (.inl j)), t⟩ => topDart j t.val
  | ⟨.inr (.inr (.inr (.inl c))), t⟩ => apexDart c t.val
  | ⟨.inr (.inr (.inr (.inr (.inl j)))), t⟩ => botDart j t.val
  | ⟨.inr (.inr (.inr (.inr (.inr _)))), t⟩ => innerDart t

lemma cell_step {k : ℕ} (r c : Fin (2*k)) (t : ℕ) (ht : t < 4) :
    walkF (cellDart r c t) = cellDart r c ((t+1) % 4) := by
  unfold cellDart; rw [walk_k1]
  interval_cases t <;> rfl

lemma oct_step {k : ℕ} (r : Fin (2*k-1)) (c : Fin (2*k)) (t : ℕ) (ht : t < 8) :
    walkF (octDart r c t) = octDart r c ((t+1) % 8) := by
  have hr := r.isLt
  have hr0 : (oR0 r).val + 1 ≠ 2*k := by simp [oR0]; omega
  have hr1 : (oR0 r).val + 1 < 2*k := by simp [oR0]; omega
  have hr2 : (oR1 r).val ≠ 0 := by simp [oR1]
  have hr3 : (oR0 r).val + 1 ≠ 2*k := hr0
  have e10 : (⟨(oR1 r).val - 1, by omega⟩ : Fin (2*k)) = oR0 r := by ext; simp [oR0, oR1]
  interval_cases t
  · exact walk_k0 _ _ _
  · show walkF (.inl ((oR0 r, c, 1), 2)) = .inl ((oR0 r, cnext c, 3), 0)
    rw [walk_k2' (oR0 r, c, 1) (by rw [facing_E]; exact isPinB_row _ hr0), facing_E]
  · exact walk_k0 _ _ _
  · show walkF (.inl ((oR0 r, cnext c, 0), 2)) = .inl ((oR1 r, cnext c, 2), 0)
    rw [walk_k2' (oR0 r, cnext c, 0)
      (by rw [facing_N _ _ hr1]; exact isPinB_dir _ (by simp) (by simp)), facing_N _ _ hr1]
    rfl
  · exact walk_k0 _ _ _
  · show walkF (.inl ((oR1 r, cnext c, 3), 2)) = .inl ((oR1 r, c, 1), 0)
    rw [walk_k2' (oR1 r, cnext c, 3)
      (by rw [facing_W]; exact isPinB_dir _ (by simp) (by simp)), facing_W, cprev_cnext]
  · exact walk_k0 _ _ _
  · show walkF (.inl ((oR1 r, c, 2), 2)) = .inl ((oR0 r, c, 0), 0)
    rw [walk_k2' (oR1 r, c, 2)
      (by rw [facing_S _ _ hr2]; exact isPinB_row _ (by simp [oR1]; omega)), facing_S _ _ hr2, e10]

lemma top_step {k : ℕ} (j : Fin k) (t : ℕ) (ht : t < 4) :
    walkF (topDart j t) = topDart j ((t+1) % 4) := by
  have hj := j.isLt
  have hT : ¬ (tT j).val + 1 < 2*k := by simp [tT]; omega
  have hp1 : cpair (tc1 j) = tc0 j := by ext; simp [cpair_val, tc1, tc0] <;> omega
  have hn0 : cnext (tc0 j) = tc1 j := by ext; simp [cnext_val, tc1, tc0] <;> omega
  have hd0 : pinDir (tc0 j) = 3 := by simp [pinDir, tc0]
  have hd1 : pinDir (tc1 j) = 0 := by simp [pinDir, tc1] <;> omega
  interval_cases t
  · exact walk_k0 _ _ _
  · show walkF (.inl ((tT j, tc1 j, 0), 2)) = .inl ((tT j, tc0 j, 0), 0)
    rw [walk_k2' (tT j, tc1 j, 0) (by rw [facing_Ntop _ _ hT, hp1]; simp [isPinB, hd0]),
      facing_Ntop _ _ hT, hp1]
  · exact walk_k0 _ _ _
  · show walkF (.inl ((tT j, tc0 j, 1), 2)) = .inl ((tT j, tc1 j, 3), 0)
    rw [walk_k2' (tT j, tc0 j, 1) (by rw [facing_E, hn0]; simp [isPinB, hd1]), facing_E, hn0]

lemma bot_step {k : ℕ} (j : Fin k) (t : ℕ) (ht : t < 4) :
    walkF (botDart j t) = botDart j ((t+1) % 4) := by
  have hj := j.isLt
  have hB : (tB j).val = 0 := rfl
  have hp0 : cpair (tc0 j) = tc1 j := by ext; simp [cpair_val, tc1, tc0]
  have hq1 : cprev (tc1 j) = tc0 j := by ext; simp [cprev_val, tc1, tc0]
  interval_cases t
  · exact walk_k0 _ _ _
  · show walkF (.inl ((tB j, tc0 j, 2), 2)) = .inl ((tB j, tc1 j, 2), 0)
    rw [walk_k2' (tB j, tc0 j, 2)
      (by rw [facing_Sbot _ _ hB]; exact isPinB_dir _ (by simp) (by simp)),
      facing_Sbot _ _ hB, hp0]
  · exact walk_k0 _ _ _
  · show walkF (.inl ((tB j, tc1 j, 3), 2)) = .inl ((tB j, tc0 j, 1), 0)
    rw [walk_k2' (tB j, tc1 j, 3)
      (by rw [facing_W]; exact isPinB_dir _ (by simp) (by simp)), facing_W, hq1]

lemma facing_pin_next {k : ℕ} (c : Fin (2*k)) :
    facing (topR c, c, pinDir c + 1) = pinPort (cnext c) := by
  have hc := c.isLt
  have hT : ¬ (topR c).val + 1 < 2*k := by simp [topR]; omega
  by_cases h : c.val % 2 = 0
  · have hd : pinDir c = 3 := by simp [pinDir, h]
    have hn : (cnext c).val = c.val + 1 := by rw [cnext_val, if_pos (by omega)]
    have hd' : pinDir (cnext c) = 0 := by simp only [pinDir, hn]; rw [if_neg (by omega)]
    rw [hd, show (3 : Fin 4) + 1 = 0 from rfl, facing_Ntop _ _ hT]
    refine Prod.ext rfl (Prod.ext (Fin.ext ?_) hd'.symm)
    rw [cpair_val, if_pos h, pinPort_snd, hn]
  · have hd : pinDir c = 0 := by simp [pinDir, h]
    have hd' : pinDir (cnext c) = 3 := by
      simp only [pinDir, cnext_val]; split_ifs <;> first | rfl | omega
    rw [hd, show (0 : Fin 4) + 1 = 1 from rfl, facing_E]
    exact Prod.ext rfl (Prod.ext rfl hd'.symm)

lemma apex_step {k : ℕ} (c : Fin (2*k)) (t : ℕ) (ht : t < 4) :
    walkF (apexDart c t) = apexDart c ((t+1) % 4) := by
  interval_cases t
  · exact walk_ap c
  · exact walk_k0 (topR c) c (pinDir c)
  · show walkF (.inl ((topR c, c, pinDir c + 1), 2)) = .inr (.inl (cnext c))
    rw [walk_k2, facing_pin_next, isPinB_pinPort] <;> rfl
  · show walkF (.inr (.inl (cnext c))) = .inr (.inr c)
    rw [walk_pa, cprev_cnext]

lemma innerBlk_val {k : ℕ} (m : Fin (4*k)) : (innerBlk m).val = k - 1 - m.val / 4 := rfl

lemma inner_step {k : ℕ} (m : Fin (4*k)) :
    walkF (innerDart m) = innerDart ⟨(m.val + 1) % (4*k), Nat.mod_lt _ (by have := m.isLt; omega)⟩ := by
  have hm := m.isLt
  set m' : Fin (4*k) := ⟨(m.val + 1) % (4*k), Nat.mod_lt _ (by omega)⟩ with hm'
  have e2 : m'.val = if m.val + 1 < 4*k then m.val + 1 else 0 := by
    simp only [hm']
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [show m.val + 1 = 4*k by omega, Nat.mod_self]
  unfold innerDart
  have hm4 : m.val % 4 = 0 ∨ m.val % 4 = 1 ∨ m.val % 4 = 2 ∨ m.val % 4 = 3 := by omega
  rcases hm4 with h | h | h | h
  · have e1 : m'.val = m.val + 1 := by rw [e2, if_pos (by omega)]
    have hb : innerBlk m' = innerBlk m := by ext; simp only [innerBlk_val, e1]; omega
    rw [hb, h, show m'.val % 4 = 1 by omega]
    exact walk_k0 _ _ _
  · have e1 : m'.val = m.val + 1 := by rw [e2, if_pos (by omega)]
    have hb : innerBlk m' = innerBlk m := by ext; simp only [innerBlk_val, e1]; omega
    rw [hb, h, show m'.val % 4 = 2 by omega]
    have hB : (tB (innerBlk m)).val = 0 := rfl
    have hp1 : cpair (tc1 (innerBlk m)) = tc0 (innerBlk m) := by
      ext; simp [cpair_val, tc1, tc0] <;> omega
    show walkF (.inl ((tB (innerBlk m), tc1 (innerBlk m), 2), 2)) =
      .inl ((tB (innerBlk m), tc0 (innerBlk m), 2), 0)
    rw [walk_k2' (tB (innerBlk m), tc1 (innerBlk m), 2)
      (by rw [facing_Sbot _ _ hB]; exact isPinB_dir _ (by simp) (by simp)),
      facing_Sbot _ _ hB, hp1]
  · have e1 : m'.val = m.val + 1 := by rw [e2, if_pos (by omega)]
    have hb : innerBlk m' = innerBlk m := by ext; simp only [innerBlk_val, e1]; omega
    rw [hb, h, show m'.val % 4 = 3 by omega]
    exact walk_k0 _ _ _
  · have h0 : m'.val % 4 = 0 := by rw [e2]; split_ifs <;> omega
    have hb : tc1 (innerBlk m') = cprev (tc0 (innerBlk m)) := by
      ext
      simp only [tc1, tc0, innerBlk_val, cprev_val, e2]
      split_ifs <;> omega
    rw [h, h0]
    show walkF (.inl ((tB (innerBlk m), tc0 (innerBlk m), 3), 2)) =
      .inl ((tB (innerBlk m'), tc1 (innerBlk m'), 1), 0)
    rw [walk_k2' (tB (innerBlk m), tc0 (innerBlk m), 3)
      (by rw [facing_W]; exact isPinB_dir _ (by simp) (by simp)), facing_W, hb]
    rfl

lemma fdart_step {k : ℕ} (i : FLab k) (t : Fin (flen i)) :
    walkF (fdart ⟨i, t⟩) = fdart ⟨i, ⟨(t.val + 1) % flen i, Nat.mod_lt _ (by have := t.isLt; omega)⟩⟩ := by
  rcases i with ⟨r, c⟩ | ⟨r, c⟩ | j | c | j | u
  · exact cell_step r c t.val t.isLt
  · exact oct_step r c t.val t.isLt
  · exact top_step j t.val t.isLt
  · exact apex_step c t.val t.isLt
  · exact bot_step j t.val t.isLt
  · exact inner_step t

lemma pd_eq {k : ℕ} {r r' c c' : Fin (2*k)} {e e' : Fin 4} {κ : Fin 3}
    (h1 : r.val = r'.val) (h2 : c.val = c'.val) (h3 : e = e') :
    (Sum.inl ((r, c, e), κ) : Dt k) = Sum.inl ((r', c', e'), κ) := by
  rw [Fin.ext h1, Fin.ext h2, h3]

lemma innerDart_mk' {k : ℕ} (jv : ℕ) (hj : jv < k) (t : ℕ) (ht : t < 4)
    (h : 4*(k-1-jv)+t < 4*k) : innerDart ⟨4*(k-1-jv)+t, h⟩ = blkDart ⟨jv, hj⟩ t := by
  unfold innerDart
  rw [show (4*(k-1-jv)+t) % 4 = t by omega]
  congr 1
  ext; simp only [innerBlk_val]; omega

lemma pinDir_odd {k : ℕ} (c : Fin (2*k)) (h : ¬ c.val % 2 = 0) : pinDir c = 0 := by
  simp [pinDir, h]
lemma pinDir_even {k : ℕ} (c : Fin (2*k)) (h : c.val % 2 = 0) : pinDir c = 3 := by
  simp [pinDir, h]

lemma fdart_surj {k : ℕ} : Function.Surjective (fdart (k := k)) := by
  intro d
  rcases d with ⟨⟨r, c, e⟩, κ⟩ | c | c
  · have hr := r.isLt; have hc := c.isLt
    rcases fin3_cases κ with rfl | rfl | rfl
    · rcases fin4_cases e with rfl | rfl | rfl | rfl
      · by_cases h : r.val + 1 < 2*k
        · exact ⟨⟨.inr (.inl (⟨r.val, by omega⟩, c)), ⟨0, by simp [flen]⟩⟩, by rfl⟩
        · by_cases h2 : c.val % 2 = 0
          · exact ⟨⟨.inr (.inr (.inl ⟨c.val/2, by omega⟩)), ⟨2, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tT]; omega) (by simp [tc0]; omega) rfl⟩
          · exact ⟨⟨.inr (.inr (.inr (.inl c))), ⟨1, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [topR]; omega) rfl (pinDir_odd c h2)⟩
      · by_cases h : r.val = 0
        · by_cases h2 : c.val % 2 = 0
          · exact ⟨⟨.inr (.inr (.inr (.inr (.inl ⟨c.val/2, by omega⟩)))), ⟨0, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tB]; omega) (by simp [tc0]; omega) rfl⟩
          · refine ⟨⟨.inr (.inr (.inr (.inr (.inr ())))),
              ⟨4*(k-1-(c.val-1)/2)+0, by simp only [flen]; omega⟩⟩, ?_⟩
            show innerDart _ = _
            refine (innerDart_mk' (k := k) ((c.val-1)/2) (by omega) 0 (by omega) _).trans ?_
            dsimp only [blkDart]; exact pd_eq (by simp [tB]; omega) (by simp [tc1]; omega) rfl
        · exact ⟨⟨.inr (.inl (⟨r.val - 1, by omega⟩, c)), ⟨6, by simp [flen]⟩⟩, by
            dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [oR1]; omega) rfl rfl⟩
      · by_cases h : r.val = 0
        · by_cases h2 : c.val % 2 = 0
          · refine ⟨⟨.inr (.inr (.inr (.inr (.inr ())))),
              ⟨4*(k-1-c.val/2)+2, by simp only [flen]; omega⟩⟩, ?_⟩
            show innerDart _ = _
            refine (innerDart_mk' (k := k) (c.val/2) (by omega) 2 (by omega) _).trans ?_
            dsimp only [blkDart]; exact pd_eq (by simp [tB]; omega) (by simp [tc0]; omega) rfl
          · exact ⟨⟨.inr (.inr (.inr (.inr (.inl ⟨c.val/2, by omega⟩)))), ⟨2, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tB]; omega) (by simp [tc1]; omega) rfl⟩
        · exact ⟨⟨.inr (.inl (⟨r.val - 1, by omega⟩, cprev c)), ⟨4, by simp [flen]⟩⟩, by
            dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [oR1]; omega) (by rw [cnext_cprev]) rfl⟩
      · by_cases h : r.val + 1 < 2*k
        · exact ⟨⟨.inr (.inl (⟨r.val, by omega⟩, cprev c)), ⟨2, by simp [flen]⟩⟩, by
            dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq rfl (by rw [cnext_cprev]) rfl⟩
        · by_cases h2 : c.val % 2 = 0
          · exact ⟨⟨.inr (.inr (.inr (.inl c))), ⟨1, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [topR]; omega) rfl (pinDir_even c h2)⟩
          · exact ⟨⟨.inr (.inr (.inl ⟨c.val/2, by omega⟩)), ⟨0, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tT]; omega) (by simp [tc1]; omega) rfl⟩
    · rcases fin4_cases e with rfl | rfl | rfl | rfl
      · exact ⟨⟨.inl (r, c), ⟨0, by simp [flen]⟩⟩, by
          show Sum.inl ((r, c, _), 1) = _; exact pd_eq rfl rfl (Fin.ext (by simp))⟩
      · exact ⟨⟨.inl (r, c), ⟨3, by simp [flen]⟩⟩, by
          show Sum.inl ((r, c, _), 1) = _; exact pd_eq rfl rfl (Fin.ext (by simp))⟩
      · exact ⟨⟨.inl (r, c), ⟨2, by simp [flen]⟩⟩, by
          show Sum.inl ((r, c, _), 1) = _; exact pd_eq rfl rfl (Fin.ext (by simp))⟩
      · exact ⟨⟨.inl (r, c), ⟨1, by simp [flen]⟩⟩, by
          show Sum.inl ((r, c, _), 1) = _; exact pd_eq rfl rfl (Fin.ext (by simp))⟩
    · rcases fin4_cases e with rfl | rfl | rfl | rfl
      · by_cases h : r.val + 1 < 2*k
        · exact ⟨⟨.inr (.inl (⟨r.val, by omega⟩, cprev c)), ⟨3, by simp [flen]⟩⟩, by
            dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq rfl (by rw [cnext_cprev]) rfl⟩
        · by_cases h2 : c.val % 2 = 0
          · exact ⟨⟨.inr (.inr (.inr (.inl c))), ⟨2, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [topR]; omega) rfl (by rw [pinDir_even c h2]; rfl)⟩
          · exact ⟨⟨.inr (.inr (.inl ⟨c.val/2, by omega⟩)), ⟨1, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tT]; omega) (by simp [tc1]; omega) rfl⟩
      · by_cases h : r.val + 1 < 2*k
        · exact ⟨⟨.inr (.inl (⟨r.val, by omega⟩, c)), ⟨1, by simp [flen]⟩⟩, by rfl⟩
        · by_cases h2 : c.val % 2 = 0
          · exact ⟨⟨.inr (.inr (.inl ⟨c.val/2, by omega⟩)), ⟨3, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tT]; omega) (by simp [tc0]; omega) rfl⟩
          · exact ⟨⟨.inr (.inr (.inr (.inl c))), ⟨2, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [topR]; omega) rfl (by rw [pinDir_odd c h2]; rfl)⟩
      · by_cases h : r.val = 0
        · by_cases h2 : c.val % 2 = 0
          · exact ⟨⟨.inr (.inr (.inr (.inr (.inl ⟨c.val/2, by omega⟩)))), ⟨1, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tB]; omega) (by simp [tc0]; omega) rfl⟩
          · refine ⟨⟨.inr (.inr (.inr (.inr (.inr ())))),
              ⟨4*(k-1-(c.val-1)/2)+1, by simp only [flen]; omega⟩⟩, ?_⟩
            show innerDart _ = _
            refine (innerDart_mk' (k := k) ((c.val-1)/2) (by omega) 1 (by omega) _).trans ?_
            dsimp only [blkDart]; exact pd_eq (by simp [tB]; omega) (by simp [tc1]; omega) rfl
        · exact ⟨⟨.inr (.inl (⟨r.val - 1, by omega⟩, c)), ⟨7, by simp [flen]⟩⟩, by
            dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [oR1]; omega) rfl rfl⟩
      · by_cases h : r.val = 0
        · by_cases h2 : c.val % 2 = 0
          · refine ⟨⟨.inr (.inr (.inr (.inr (.inr ())))),
              ⟨4*(k-1-c.val/2)+3, by simp only [flen]; omega⟩⟩, ?_⟩
            show innerDart _ = _
            refine (innerDart_mk' (k := k) (c.val/2) (by omega) 3 (by omega) _).trans ?_
            dsimp only [blkDart]; exact pd_eq (by simp [tB]; omega) (by simp [tc0]; omega) rfl
          · exact ⟨⟨.inr (.inr (.inr (.inr (.inl ⟨c.val/2, by omega⟩)))), ⟨3, by simp [flen]⟩⟩, by
              dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [tB]; omega) (by simp [tc1]; omega) rfl⟩
        · exact ⟨⟨.inr (.inl (⟨r.val - 1, by omega⟩, cprev c)), ⟨5, by simp [flen]⟩⟩, by
            dsimp only [fdart, topDart, botDart, octDart, apexDart, pinPort]; exact pd_eq (by simp [oR1]; omega) (by rw [cnext_cprev]) rfl⟩
  · exact ⟨⟨.inr (.inr (.inr (.inl (cprev c)))), ⟨3, by simp [flen]⟩⟩,
      by show Sum.inr (Sum.inl (cnext (cprev c))) = _; rw [cnext_cprev]⟩
  · exact ⟨⟨.inr (.inr (.inr (.inl c))), ⟨0, by simp [flen]⟩⟩, by rfl⟩

lemma card_Dt {k : ℕ} : Fintype.card (Dt k) = 48*k^2 + 4*k := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; ring

lemma card_FLab {k : ℕ} (hk : 0 < k) : Fintype.card (FLab k) = 8*k^2 + 2*k + 1 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (k'+1) - 1 = 2*k'+1 by omega]; ring

lemma card_sig {k : ℕ} (hk : 0 < k) :
    Fintype.card (Σ i : FLab k, Fin (flen i)) = 48*k^2 + 4*k := by
  rw [Fintype.card_sigma]
  have hc : ∀ i : FLab k, Fintype.card (Fin (flen i)) = flen i := fun i => Fintype.card_fin _
  rw [Finset.sum_congr rfl (fun i _ => hc i)]
  simp only [Fintype.sum_sum_type, flen, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, smul_eq_mul]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (k'+1) - 1 = 2*k'+1 by omega]; ring



lemma card_image_eq_of_fibers {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (g : α → β) (h : α → γ) (hgh : ∀ a b, g a = g b ↔ h a = h b) :
    (Finset.univ.image g).card = (Finset.univ.image h).card := by
  classical
  have e1 : Finset.univ.image g = (Finset.univ.image (fun a => (g a, h a))).image Prod.fst := by
    rw [Finset.image_image]; rfl
  have e2 : Finset.univ.image h = (Finset.univ.image (fun a => (g a, h a))).image Prod.snd := by
    rw [Finset.image_image]; rfl
  have c1 : ((Finset.univ.image (fun a => (g a, h a))).image Prod.fst).card =
      (Finset.univ.image (fun a => (g a, h a))).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    simp only at hxy
    simp [hxy, (hgh a b).1 hxy]
  have c2 : ((Finset.univ.image (fun a => (g a, h a))).image Prod.snd).card =
      (Finset.univ.image (fun a => (g a, h a))).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    simp only at hxy
    simp [hxy, (hgh a b).2 hxy]
  rw [e1, e2, c1, c2]

lemma sameCycle_iff_lt {D : Type*} [Fintype D] [DecidableEq D] (w : Equiv.Perm D) (x y : D) :
    (∃ j < Fintype.card D, (w ^ j) x = y) ↔ w.SameCycle x y := by
  constructor
  · rintro ⟨j, _, rfl⟩; exact ⟨j, by simp [zpow_natCast]⟩
  · intro h
    by_cases hx : x ∈ w.support
    · obtain ⟨i, hi, hxy⟩ := h.exists_pow_eq_of_mem_support hx
      exact ⟨i, lt_of_lt_of_le hi (Finset.card_le_univ _), hxy⟩
    · rw [Equiv.Perm.notMem_support] at hx
      obtain ⟨i, hi⟩ := h
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx] at hi
      exact ⟨0, Fintype.card_pos_iff.2 ⟨x⟩, by simp [hi]⟩

lemma orb_eq_iff {D : Type*} [Fintype D] [DecidableEq D] (w : Equiv.Perm D) (x y : D) :
    (Finset.range (Fintype.card D)).image (fun j => (w ^ j) x) =
      (Finset.range (Fintype.card D)).image (fun j => (w ^ j) y) ↔ w.SameCycle x y := by
  have mem : ∀ a z : D, z ∈ (Finset.range (Fintype.card D)).image (fun j => (w ^ j) a) ↔
      w.SameCycle a z := by
    intro a z
    rw [← sameCycle_iff_lt]
    simp
  constructor
  · intro h
    have : y ∈ (Finset.range (Fintype.card D)).image (fun j => (w ^ j) x) := by
      rw [h, mem]
    exact (mem x y).1 this
  · intro h
    ext z
    rw [mem, mem]
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem planar_of {G D : Type} [DecidableEq G] [Fintype D] [DecidableEq D]
    (src : D → G) (rev rot : Equiv.Perm D) (inc : G → G → Bool) (N0 : ℕ)
    (hinj : Function.Injective (fun d => (src d, src (rev d))))
    (hinc : ∀ a b, inc a b = true ↔ ∃ d, src d = a ∧ src (rev d) = b)
    (hrev : ∀ d, rev (rev d) = d)
    (hrot : ∀ d, src (rot d) = src d)
    (htr : ∀ a b, src a = src b → ∃ j : ℕ, (rot^j) a = b)
    (ι : Type) [Fintype ι] (len : ι → ℕ) (hlen : ∀ i, 0 < len i)
    (f : (Σ i, Fin (len i)) → D)
    (hsurj : Function.Surjective f) (hcard : Fintype.card (Σ i, Fin (len i)) = Fintype.card D)
    (hstep : ∀ i (t : Fin (len i)), rot (rev (f ⟨i, t⟩)) =
      f ⟨i, ⟨(t.val + 1) % len i, Nat.mod_lt _ (hlen i)⟩⟩)
    (heuler : N0 + 2 * Fintype.card ι = 4 + Fintype.card D) :
    ∃ (l : ℕ) (src' dst' : Fin l → G) (rot' rev' : Equiv.Perm (Fin l)),
      Function.Injective (fun d => (src' d, dst' d)) ∧
      (∀ a b : G, inc a b = true ↔ ∃ d, src' d = a ∧ dst' d = b) ∧
      (∀ d, src' (rev' d) = dst' d ∧ dst' (rev' d) = src' d ∧ src' (rot' d) = src' d) ∧
      (∀ a b, src' a = src' b → ∃ j : ℕ, (rot'^j) a = b) ∧
      let walk := fun a : Fin l => rot' (rev' a)
      let faces := (Finset.univ : Finset (Fin l)).image (fun a =>
        (Finset.range l).image (fun j => walk^[j] a))
      N0 + 2*faces.card = 4+l := by
  classical
  set e := Fintype.equivFin D with he
  have hpow : ∀ (p : Equiv.Perm D) (j : ℕ) (a : Fin (Fintype.card D)),
      ((e.permCongr p) ^ j) a = e ((p ^ j) (e.symm a)) := by
    intro p j
    induction j with
    | zero => intro a; simp
    | succ j ih => intro a; rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ',
        Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine ⟨Fintype.card D, src ∘ e.symm, src ∘ rev ∘ e.symm, e.permCongr rot,
    e.permCongr rev, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact e.symm.injective (hinj h)
  · intro a b
    rw [hinc]
    constructor
    · rintro ⟨d, h1, h2⟩; exact ⟨e d, by simp [h1], by simp [h2]⟩
    · rintro ⟨d, h1, h2⟩; exact ⟨e.symm d, h1, h2⟩
  · intro d
    simp [Equiv.permCongr_apply, hrev, hrot]
  · intro a b h
    obtain ⟨j, hj⟩ := htr (e.symm a) (e.symm b) h
    exact ⟨j, by rw [hpow, hj]; simp⟩
  · -- the face count
    intro walk faces
    let w : Equiv.Perm D := rot * rev
    have hwalk : ∀ j a, walk^[j] a = e ((w ^ j) (e.symm a)) := by
      intro j
      induction j with
      | zero => intro a; simp
      | succ j ih =>
        intro a
        rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply]
        simp [walk, w, Equiv.permCongr_apply]
    have hbij : Function.Bijective f := (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcard⟩
    let lab : D → ι := fun d => ((Equiv.ofBijective f hbij).symm d).1
    have hlab : ∀ i t, lab (f ⟨i, t⟩) = i := by
      intro i t
      simp only [lab]
      rw [show f ⟨i, t⟩ = Equiv.ofBijective f hbij ⟨i, t⟩ from rfl, Equiv.symm_apply_apply]
    have hfiter : ∀ (j : ℕ) i (t : Fin (len i)), (w ^ j) (f ⟨i, t⟩) =
        f ⟨i, ⟨(t.val + j) % len i, Nat.mod_lt _ (hlen i)⟩⟩ := by
      intro j
      induction j with
      | zero => intro i t; simp [Nat.mod_eq_of_lt t.isLt]
      | succ j ih =>
        intro i t
        rw [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.Perm.mul_apply, hstep]
        have : ((t.val + j) % len i + 1) % len i = (t.val + (j + 1)) % len i := by
          rw [Nat.mod_add_mod, Nat.add_assoc]
        exact congrArg (fun s => f ⟨i, s⟩) (Fin.ext this)
    have hlabw : ∀ (j : ℕ) d, lab ((w ^ j) d) = lab d := by
      intro j d
      obtain ⟨⟨i, t⟩, rfl⟩ := hsurj d
      rw [hfiter, hlab, hlab]
    have hfib : ∀ x y : D, w.SameCycle x y ↔ lab x = lab y := by
      intro x y
      constructor
      · intro h
        obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
        rw [← hj, hlabw]
      · intro h
        obtain ⟨⟨i, t⟩, rfl⟩ := hsurj x
        obtain ⟨⟨i', t'⟩, rfl⟩ := hsurj y
        rw [hlab, hlab] at h
        subst h
        refine ⟨((t'.val + len i - t.val : ℕ) : ℤ), ?_⟩
        rw [zpow_natCast, hfiter]
        congr 2
        ext
        simp only
        have := t.isLt; have := t'.isLt
        rw [show t.val + (t'.val + len i - t.val) = t'.val + len i by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt t'.isLt]
    have horb : ∀ a : Fin (Fintype.card D), (Finset.range (Fintype.card D)).image
        (fun j => walk^[j] a) = ((Finset.range (Fintype.card D)).image
          (fun j => (w ^ j) (e.symm a))).map e.toEmbedding := by
      intro a
      rw [Finset.map_eq_image, Finset.image_image]
      apply Finset.image_congr
      intro j _
      simp [hwalk]
    have hcardF : faces.card = Fintype.card ι := by
      show ((Finset.univ : Finset (Fin (Fintype.card D))).image (fun a =>
        (Finset.range (Fintype.card D)).image (fun j => walk^[j] a))).card = Fintype.card ι
      rw [card_image_eq_of_fibers _ (fun a => lab (e.symm a))]
      · have himg : (Finset.univ : Finset (Fin (Fintype.card D))).image
            (fun a => lab (e.symm a)) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro i
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨e (f ⟨i, ⟨0, hlen i⟩⟩), by simp [hlab]⟩
        rw [himg, Finset.card_univ]
      · intro a b
        rw [horb, horb, Finset.map_inj, orb_eq_iff, hfib]
    rw [hcardF]
    exact heuler


/-! ## Connectivity -/

lemma nb_zero {k : ℕ} (p : Port k) : nb p 0 = (p.1, p.2.1, p.2.2 + 1) := by simp [nb]
lemma nb_two {k : ℕ} (p : Port k) : nb p 2 = facing p := by simp [nb]

abbrev LR (k : ℕ) := fun a b : Bool × Fin (8*k^2) => linkB (sig k) (tau k) a b = true

lemma link_nb {k : ℕ} (p : Port k) (κ : Fin 3) : LR k (vertexOf p) (vertexOf (nb p κ)) :=
  (link_vertexOf p _).2 ⟨κ, rfl⟩

lemma LR_symm {k : ℕ} : Symmetric (LR k) := by
  intro a b h
  simp only [LR, linkB, Bool.or_eq_true] at h ⊢
  tauto

lemma rtg_symm {k : ℕ} {a b : Bool × Fin (8*k^2)} (h : Relation.ReflTransGen (LR k) a b) :
    Relation.ReflTransGen (LR k) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (LR_symm hbc)).trans ih

lemma reach_step {k : ℕ} (p : Port k) : Relation.ReflTransGen (LR k) (vertexOf p)
    (vertexOf (p.1, p.2.1, p.2.2 + 1)) := by
  have := link_nb p 0
  rw [nb_zero] at this
  exact Relation.ReflTransGen.single this

lemma reach_cell {k : ℕ} (r c : Fin (2*k)) (d : Fin 4) :
    Relation.ReflTransGen (LR k) (vertexOf (r, c, 0)) (vertexOf (r, c, d)) := by
  rcases fin4_cases d with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact reach_step (r, c, 0)
  · exact (reach_step (r, c, 0)).trans (reach_step (r, c, 1))
  · exact ((reach_step (r, c, 0)).trans (reach_step (r, c, 1))).trans (reach_step (r, c, 2))

lemma reach_row {k : ℕ} (r : Fin (2*k)) (n : ℕ) (hn : n < 2*k) :
    Relation.ReflTransGen (LR k) (vertexOf (r, ⟨0, by omega⟩, 0)) (vertexOf (r, ⟨n, hn⟩, 0)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine ((ih (by omega)).trans (reach_cell r ⟨n, by omega⟩ 1)).trans ?_
    have h1 : facing (r, (⟨n, by omega⟩ : Fin (2*k)), 1) = (r, ⟨n+1, hn⟩, 3) := by
      rw [facing_E]; congr 2; ext; rw [cnext_val, if_pos hn]
    have e1 := link_nb (r, (⟨n, by omega⟩ : Fin (2*k)), 1) 2
    rw [nb_two, h1] at e1
    exact (Relation.ReflTransGen.single e1).trans (reach_step (r, ⟨n+1, hn⟩, 3))

lemma reach_col {k : ℕ} (n : ℕ) (hn : n < 2*k) :
    Relation.ReflTransGen (LR k) (vertexOf (⟨0, by omega⟩, ⟨0, by omega⟩, 0))
      (vertexOf (⟨n, hn⟩, ⟨0, by omega⟩, 0)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine (ih (by omega)).trans ?_
    have e1 := link_nb ((⟨n, by omega⟩ : Fin (2*k)), (⟨0, by omega⟩ : Fin (2*k)), 0) 2
    rw [nb_two, facing_N _ _ hn] at e1
    exact ((Relation.ReflTransGen.single e1).trans
      (reach_step (⟨n+1, hn⟩, ⟨0, by omega⟩, 2))).trans (reach_step (⟨n+1, hn⟩, ⟨0, by omega⟩, 3))

lemma conn_part (k : ℕ) (hk : 0 < k) :
    ∀ i j : Bool × Fin (8*k^2), Relation.ReflTransGen (LR k) i j := by
  have base : ∀ p : Port k, Relation.ReflTransGen (LR k)
      (vertexOf (⟨0, by omega⟩, ⟨0, by omega⟩, 0)) (vertexOf p) := by
    rintro ⟨r, c, d⟩
    exact ((reach_col r.val r.isLt).trans (reach_row r c.val c.isLt)).trans (reach_cell r c d)
  intro i j
  obtain ⟨p, rfl⟩ := vertexOf_surjective i
  obtain ⟨q, rfl⟩ := vertexOf_surjective j
  exact (rtg_symm (base p)).trans (base q)

theorem planar_part (k : ℕ) (hk : 0 < k) :
    ∃ (l : ℕ) (src dst : Fin l → Option (Bool × Fin (8*k^2))) (rot rev : Equiv.Perm (Fin l)),
      Function.Injective (fun d => (src d, dst d)) ∧
      (∀ a b, incB (sig k) (tau k) pinV a b = true ↔ ∃ d, src d = a ∧ dst d = b) ∧
      (∀ d, src (rev d) = dst d ∧ dst (rev d) = src d ∧ src (rot d) = src d) ∧
      (∀ a b, src a = src b → ∃ j : ℕ, (rot^j) a = b) ∧
      let walk := fun a : Fin l => rot (rev a)
      let faces := (Finset.univ : Finset (Fin l)).image (fun a =>
        (Finset.range l).image (fun j => walk^[j] a))
      2*(2*(8*k^2)+1) + 2*faces.card = 4+l :=
  planar_of dsrc (revP k) (rotP k) (incB (sig k) (tau k) pinV) (2*(2*(8*k^2)+1))
    src_dst_inj inc_iff drev_drev src_rot rot_trans (FLab k) flen
    (by intro i; rcases i with _ | _ | _ | _ | _ | _ <;> simp [flen] <;> omega) fdart fdart_surj
    (by rw [card_sig hk, card_Dt]) (fun i t => fdart_step i t)
    (by rw [card_FLab hk, card_Dt]; ring)


/-! ## Routing certificates -/

lemma exists_matching {N : ℕ} (A : Finset (Fin N)) (S : Finset (Fin N)) :
    ∃ M : Finset (Fin N × Fin N),
      (∀ e ∈ M, e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S ∧ (e.1 ∈ A ↔ e.2 ∉ A)) ∧
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
      (∀ e ∈ M, ∀ e' ∈ M, ¬ (e.1 < e'.1 ∧ e'.1 < e.2 ∧ e.2 < e'.2)) ∧
      M.card = min (S ∩ A).card (S \ A).card := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hc : (S ∩ A).card = 0 ∨ (S \ A).card = 0
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      rw [Finset.card_empty]; omega
    have hc1 : (S ∩ A).card ≠ 0 := fun h => hc (Or.inl h)
    have hc2 : (S \ A).card ≠ 0 := fun h => hc (Or.inr h)
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hc1)
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hc2)
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_sdiff] at hy
    let C := (S ×ˢ S).filter (fun pq : Fin N × Fin N => pq.1 < pq.2 ∧ (pq.1 ∈ A ↔ pq.2 ∉ A))
    have hCne : C.Nonempty := by
      have hxy : x ≠ y := by rintro rfl; exact hy.2 hx.2
      rcases lt_or_gt_of_ne hxy with hxy | hxy
      · exact ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx.1, hy.1⟩, hxy, by tauto⟩⟩
      · exact ⟨(y, x), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hy.1, hx.1⟩, hxy, by tauto⟩⟩
    obtain ⟨⟨p, q⟩, hpqC, hmin⟩ := Finset.exists_min_image C (fun pq => pq.2.val - pq.1.val) hCne
    obtain ⟨hpqS, hpq, hpqA⟩ := Finset.mem_filter.1 hpqC
    obtain ⟨hpS, hqS⟩ := Finset.mem_product.1 hpqS
    simp only at hpS hqS hpq hpqA
    have hpq' : p.val < q.val := hpq
    have hgap : ∀ s ∈ S, ¬ (p.val < s.val ∧ s.val < q.val) := by
      rintro s hs ⟨h1, h2⟩
      by_cases hsA : (s ∈ A ↔ p ∈ A)
      · have := hmin (s, q) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs, hqS⟩, h2, by tauto⟩)
        simp only at this; omega
      · have := hmin (p, s) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hpS, hs⟩, h1, by tauto⟩)
        simp only at this; omega
    have memS' : ∀ z, z ∈ (S.erase p).erase q ↔ z ∈ S ∧ z ≠ p ∧ z ≠ q := by
      intro z; simp only [Finset.mem_erase]; tauto
    have hsub : (S.erase p).erase q ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨fun z hz => ((memS' z).1 hz).1, fun h => ?_⟩
      have : p ∈ (S.erase p).erase q := by rw [h]; exact hpS
      exact ((memS' p).1 this).2.1 rfl
    obtain ⟨M', hM1, hM2, hM3, hM4⟩ := ih _ hsub
    have hpM : (p, q) ∉ M' := fun h => ((memS' p).1 (hM1 _ h).2.1).2.1 rfl
    refine ⟨insert (p, q) M', ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact ⟨hpq, hpS, hqS, hpqA⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hM1 e he
        exact ⟨h1, ((memS' _).1 h2).1, ((memS' _).1 h3).1, h4⟩
    · intro e he e' he' hne
      rcases Finset.mem_insert.1 he with rfl | he <;> rcases Finset.mem_insert.1 he' with rfl | he'
      · exact absurd rfl hne
      · obtain ⟨_, h2, h3, _⟩ := hM1 e' he'
        rw [memS'] at h2 h3
        exact ⟨fun h => h2.2.1 h.symm, fun h => h3.2.1 h.symm, fun h => h2.2.2 h.symm,
          fun h => h3.2.2 h.symm⟩
      · obtain ⟨_, h2, h3, _⟩ := hM1 e he
        rw [memS'] at h2 h3
        exact ⟨h2.2.1, h2.2.2, h3.2.1, h3.2.2⟩
      · exact hM2 e he e' he' hne
    · intro e he e' he'
      rcases Finset.mem_insert.1 he with rfl | he <;> rcases Finset.mem_insert.1 he' with rfl | he'
      · rintro ⟨h1, -, -⟩; exact lt_irrefl _ h1
      · rintro ⟨h1, h2, -⟩
        exact hgap e'.1 ((memS' _).1 (hM1 e' he').2.1).1 ⟨h1, h2⟩
      · rintro ⟨-, h2, h3⟩
        exact hgap e.2 ((memS' _).1 (hM1 e he).2.2.1).1 ⟨h2, h3⟩
      · exact hM3 e he e' he'
    · rw [Finset.card_insert_of_notMem hpM, hM4]
      by_cases hpA : p ∈ A
      · have hqA : q ∉ A := hpqA.1 hpA
        have e1 : (S.erase p).erase q ∩ A = (S ∩ A).erase p := by
          ext z; simp only [Finset.mem_inter, Finset.mem_erase]; constructor
          · rintro ⟨⟨_, hzp, hzS⟩, hzA⟩; exact ⟨hzp, hzS, hzA⟩
          · rintro ⟨hzp, hzS, hzA⟩; exact ⟨⟨fun h => hqA (h ▸ hzA), hzp, hzS⟩, hzA⟩
        have e2 : (S.erase p).erase q \ A = (S \ A).erase q := by
          ext z; simp only [Finset.mem_sdiff, Finset.mem_erase]; constructor
          · rintro ⟨⟨hzq, _, hzS⟩, hzA⟩; exact ⟨hzq, hzS, hzA⟩
          · rintro ⟨hzq, hzS, hzA⟩; exact ⟨⟨hzq, fun h => hzA (h ▸ hpA), hzS⟩, hzA⟩
        rw [e1, e2, Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨hpS, hpA⟩),
          Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hqS, hqA⟩)]
        omega
      · have hqA : q ∈ A := by by_contra h; exact hpA (hpqA.2 h)
        have e1 : (S.erase p).erase q ∩ A = (S ∩ A).erase q := by
          ext z; simp only [Finset.mem_inter, Finset.mem_erase]; constructor
          · rintro ⟨⟨hzq, _, hzS⟩, hzA⟩; exact ⟨hzq, hzS, hzA⟩
          · rintro ⟨hzq, hzS, hzA⟩; exact ⟨⟨hzq, fun h => hpA (h ▸ hzA), hzS⟩, hzA⟩
        have e2 : (S.erase p).erase q \ A = (S \ A).erase p := by
          ext z; simp only [Finset.mem_sdiff, Finset.mem_erase]; constructor
          · rintro ⟨⟨_, hzp, hzS⟩, hzA⟩; exact ⟨hzp, hzS, hzA⟩
          · rintro ⟨hzp, hzS, hzA⟩; exact ⟨⟨fun h => hzA (h ▸ hqA), hzp, hzS⟩, hzA⟩
        rw [e1, e2, Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨hqS, hqA⟩),
          Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hpS, hpA⟩)]
        omega

def onRoute (K l r ρ γ : ℕ) : Prop :=
  ((γ = l ∨ γ = r) ∧ K - 1 - (r - l) ≤ ρ) ∨ (ρ = K - 1 - (r - l) ∧ l ≤ γ ∧ γ ≤ r)

lemma route_disj (K l r l' r' ρ γ : ℕ) (hl : l < r) (hl' : l' < r') (hr : r < K) (hr' : r' < K)
    (h1 : l ≠ l') (h2 : l ≠ r') (h3 : r ≠ l') (h4 : r ≠ r')
    (hc1 : ¬ (l < l' ∧ l' < r ∧ r < r')) (hc2 : ¬ (l' < l ∧ l < r' ∧ r' < r))
    (ha : onRoute K l r ρ γ) (hb : onRoute K l' r' ρ γ) : False := by
  unfold onRoute at ha hb
  omega

def portOfV {k : ℕ} (v : Bool × Fin (8*k^2)) : Port k := portOf v.1 ((eX k).symm v.2)

lemma portOfV_vertexOf {k : ℕ} (p : Port k) : portOfV (vertexOf p) = p := by
  simp [portOfV, vertexOf, portOf_xOf]

lemma edge_of_link {k : ℕ} (u v : Bool × Fin (8*k^2)) (h : linkB (sig k) (tau k) u v = true) :
    ∃ e : Fin 3 × Fin (8*k^2),
      ((false, e.2) = u ∧
        (true, (if e.1 = 0 then e.2 else if e.1 = 1 then sig k e.2 else tau k e.2)) = v) ∨
      ((false, e.2) = v ∧
        (true, (if e.1 = 0 then e.2 else if e.1 = 1 then sig k e.2 else tau k e.2)) = u) := by
  have key : ∀ a b : Bool × Fin (8*k^2), arcB (sig k) (tau k) a b = true →
      ∃ e : Fin 3 × Fin (8*k^2), (false, e.2) = a ∧
        (true, (if e.1 = 0 then e.2 else if e.1 = 1 then sig k e.2 else tau k e.2)) = b := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
    simp only [arcB, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
      decide_eq_true_eq] at hab
    obtain ⟨⟨rfl, rfl⟩, h⟩ := hab
    rcases h with (h | h) | h
    · exact ⟨(0, a2), rfl, by simp [h]⟩
    · exact ⟨(1, a2), rfl, by simp [h]⟩
    · exact ⟨(2, a2), rfl, by simp [h]⟩
  simp only [linkB, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨e, h1, h2⟩ := key u v h; exact ⟨e, Or.inl ⟨h1, h2⟩⟩
  · obtain ⟨e, h1, h2⟩ := key v u h; exact ⟨e, Or.inr ⟨h1, h2⟩⟩

theorem cert_part (k : ℕ) (hk : 0 < k) :
    ∀ A : Finset (Fin (2*k)), ∃ (a b : Fin (min A.card (2*k - A.card)) → Fin (2*k))
      (cls : Bool × Fin (8*k^2) → Option (Fin (min A.card (2*k - A.card))))
      (F : Finset (Fin 3 × Fin (8*k^2))),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∉ A) ∧ (∀ i, cls (pinV (a i)) = some i) ∧
      (∀ i, cls (pinV (b i)) = some i) ∧
      (∀ e ∈ F, ∃ i, cls (false,e.2) = some i ∧
        cls (true, (if e.1 = 0 then e.2 else if e.1 = 1 then sig k e.2 else tau k e.2)) = some i) ∧
      (∀ x : Bool × Fin (8*k^2) → Bool, (∀ e ∈ F, x (false,e.2) =
          x (true, (if e.1 = 0 then e.2 else if e.1 = 1 then sig k e.2 else tau k e.2))) →
        ∀ v w i, cls v = some i → cls w = some i → x v = x w) := by
  classical
  intro A
  obtain ⟨M, hM1, hM2, hM3, hM4⟩ := exists_matching A Finset.univ
  have hMc : M.card = min A.card (2*k - A.card) := by
    rw [hM4, Finset.univ_inter, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  let eM : M ≃ Fin (min A.card (2*k - A.card)) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hMc)
  let arc : Fin (min A.card (2*k - A.card)) → Fin (2*k) × Fin (2*k) := fun i => (eM.symm i).1
  have harcM : ∀ i, arc i ∈ M := fun i => (eM.symm i).2
  have harc_inj : ∀ i j, arc i = arc j → i = j := fun i j h => eM.symm.injective (Subtype.ext h)
  let R : Fin (min A.card (2*k - A.card)) → ℕ → ℕ → Prop :=
    fun i ρ γ => onRoute (2*k) (arc i).1.val (arc i).2.val ρ γ
  have hdisj : ∀ i j ρ γ, R i ρ γ → R j ρ γ → i = j := by
    intro i j ρ γ hi hj
    by_contra hij
    have hne : arc i ≠ arc j := fun h => hij (harc_inj i j h)
    obtain ⟨a1, -, -, -⟩ := hM1 _ (harcM i)
    obtain ⟨b1, -, -, -⟩ := hM1 _ (harcM j)
    obtain ⟨d1, d2, d3, d4⟩ := hM2 _ (harcM i) _ (harcM j) hne
    exact route_disj (2*k) _ _ _ _ ρ γ a1 b1 (arc i).2.isLt (arc j).2.isLt
      (fun h => d1 (Fin.ext h)) (fun h => d2 (Fin.ext h)) (fun h => d3 (Fin.ext h))
      (fun h => d4 (Fin.ext h))
      (hM3 _ (harcM i) _ (harcM j)) (hM3 _ (harcM j) _ (harcM i)) hi hj
  let cls : Bool × Fin (8*k^2) → Option (Fin (min A.card (2*k - A.card))) := fun v =>
    if h : ∃ i, R i (portOfV v).1.val (portOfV v).2.1.val then some (Classical.choose h) else none
  have hcls : ∀ v i, cls v = some i ↔ R i (portOfV v).1.val (portOfV v).2.1.val := by
    intro v i
    simp only [cls]
    split_ifs with h
    · constructor
      · intro hh; rw [← Option.some.inj hh]; exact Classical.choose_spec h
      · intro hi; rw [hdisj _ _ _ _ (Classical.choose_spec h) hi]
    · constructor
      · intro hh; cases hh
      · intro hi; exact absurd ⟨i, hi⟩ h
  have hclsP : ∀ p i, cls (vertexOf p) = some i ↔ R i p.1.val p.2.1.val := by
    intro p i; rw [hcls, portOfV_vertexOf]
  have hiff : ∀ i, ((arc i).1 ∈ A ↔ (arc i).2 ∉ A) := fun i => (hM1 _ (harcM i)).2.2.2
  have hpinR : ∀ i (c : Fin (2*k)), (c = (arc i).1 ∨ c = (arc i).2) → cls (pinV c) = some i := by
    intro i c hc
    rw [pinV, hclsP]
    simp only [R, onRoute, pinPort, topR]
    left
    refine ⟨?_, by omega⟩
    rcases hc with rfl | rfl <;> simp
  refine ⟨fun i => if (arc i).1 ∈ A then (arc i).1 else (arc i).2,
    fun i => if (arc i).1 ∈ A then (arc i).2 else (arc i).1, cls,
    Finset.univ.filter (fun e : Fin 3 × Fin (8*k^2) => ∃ i, cls (false, e.2) = some i ∧
      cls (true, (if e.1 = 0 then e.2 else if e.1 = 1 then sig k e.2 else tau k e.2)) = some i),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only
    split_ifs with h
    · exact h
    · by_contra h'; exact h ((hiff i).2 h')
  · intro i
    simp only
    split_ifs with h
    · exact (hiff i).1 h
    · exact h
  · intro i; apply hpinR; simp only; split_ifs <;> simp
  · intro i; apply hpinR; simp only; split_ifs <;> simp
  · intro e he; exact (Finset.mem_filter.1 he).2
  · intro x hx v w i hv hw
    have adj : ∀ p κ, R i p.1.val p.2.1.val → R i (nb p κ).1.val (nb p κ).2.1.val →
        x (vertexOf p) = x (vertexOf (nb p κ)) := by
      intro p κ h1 h2
      rw [← hclsP] at h1 h2
      obtain ⟨e, he | he⟩ := edge_of_link _ _ ((link_vertexOf p _).2 ⟨κ, rfl⟩)
      · have := hx e (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, by rw [he.1]; exact h1,
          by rw [he.2]; exact h2⟩)
        rw [he.1, he.2] at this; exact this
      · have := hx e (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, by rw [he.1]; exact h2,
          by rw [he.2]; exact h1⟩)
        rw [he.1, he.2] at this; exact this.symm
    -- all ports of a route cell carry the same value
    have hcell : ∀ (r c : Fin (2*k)) (d : Fin 4), R i r.val c.val →
        x (vertexOf (r, c, d)) = x (vertexOf (r, c, 0)) := by
      intro r c d h
      have s : ∀ e : Fin 4, x (vertexOf (r, c, e)) = x (vertexOf (r, c, e + 1)) := by
        intro e
        have := adj (r, c, e) 0 h (by rw [nb_zero]; exact h)
        rwa [nb_zero] at this
      rcases fin4_cases d with rfl | rfl | rfl | rfl
      · rfl
      · exact (s 0).symm
      · exact ((s 0).trans (s 1)).symm
      · exact (((s 0).trans (s 1)).trans (s 2)).symm
    let cv : ℕ → ℕ → Bool := fun ρ γ =>
      if h : ρ < 2*k ∧ γ < 2*k then x (vertexOf (⟨ρ, h.1⟩, ⟨γ, h.2⟩, 0)) else false
    have hcv : ∀ (r c : Fin (2*k)), cv r.val c.val = x (vertexOf (r, c, 0)) := by
      intro r c; simp only [cv]; rw [dif_pos ⟨r.isLt, c.isLt⟩]
    have vert : ∀ ρ γ, ρ + 1 < 2*k → γ < 2*k → R i ρ γ → R i (ρ+1) γ → cv ρ γ = cv (ρ+1) γ := by
      intro ρ γ h1 h2 hR hR'
      have := adj (⟨ρ, by omega⟩, ⟨γ, h2⟩, 0) 2 hR (by rw [nb_two, facing_N _ _ h1]; exact hR')
      rw [nb_two, facing_N _ _ h1] at this
      rw [hcv ⟨ρ, by omega⟩ ⟨γ, h2⟩, hcv ⟨ρ+1, h1⟩ ⟨γ, h2⟩, this, hcell _ _ _ hR']
    have horz : ∀ ρ γ, ρ < 2*k → γ + 1 < 2*k → R i ρ γ → R i ρ (γ+1) → cv ρ γ = cv ρ (γ+1) := by
      intro ρ γ h1 h2 hR hR'
      have hn : cnext (⟨γ, by omega⟩ : Fin (2*k)) = ⟨γ+1, h2⟩ := by
        ext; rw [cnext_val, if_pos h2]
      have := adj (⟨ρ, h1⟩, ⟨γ, by omega⟩, 1) 2 hR (by rw [nb_two, facing_E, hn]; exact hR')
      rw [nb_two, facing_E, hn] at this
      rw [hcv ⟨ρ, h1⟩ ⟨γ, by omega⟩, hcv ⟨ρ, h1⟩ ⟨γ+1, h2⟩, ← hcell _ _ 1 hR, this,
        hcell _ _ _ hR']
    set l := (arc i).1.val with hl
    set r := (arc i).2.val with hr
    have hlr : l < r := (hM1 _ (harcM i)).1
    have hrK : r < 2*k := (arc i).2.isLt
    have vchain : ∀ γ, (γ = l ∨ γ = r) → ∀ j ρ, ρ + j < 2*k → 2*k-1-(r-l) ≤ ρ →
        cv ρ γ = cv (ρ + j) γ := by
      intro γ hγ j
      induction j with
      | zero => intro ρ _ _; rfl
      | succ j ih =>
        intro ρ h1 h2
        rw [ih ρ (by omega) h2]
        apply vert _ _ (by omega) (by omega)
        · simp only [R, onRoute]; left; exact ⟨hγ, by omega⟩
        · simp only [R, onRoute]; left; exact ⟨hγ, by omega⟩
    have hchain : ∀ j γ, γ + j ≤ r → l ≤ γ → cv (2*k-1-(r-l)) γ = cv (2*k-1-(r-l)) (γ + j) := by
      intro j
      induction j with
      | zero => intro γ _ _; rfl
      | succ j ih =>
        intro γ h1 h2
        rw [ih γ (by omega) h2]
        apply horz _ _ (by omega) (by omega)
        · simp only [R, onRoute]; right; exact ⟨rfl, by omega, by omega⟩
        · simp only [R, onRoute]; right; exact ⟨rfl, by omega, by omega⟩
    have hall : ∀ ρ γ, ρ < 2*k → γ < 2*k → R i ρ γ → cv ρ γ = cv (2*k-1) l := by
      intro ρ γ hρ hγ hR
      have hbase : cv (2*k-1-(r-l)) l = cv (2*k-1) l := by
        have := vchain l (Or.inl rfl) (r - l) (2*k-1-(r-l)) (by omega) le_rfl
        rw [this, show 2*k-1-(r-l) + (r-l) = 2*k-1 by omega]
      simp only [R, onRoute] at hR
      rcases hR with ⟨hγ' | hγ', hρ'⟩ | ⟨hρ', h1, h2⟩
      · subst hγ'
        have := vchain l (Or.inl rfl) (2*k-1-ρ) ρ (by omega) hρ'
        rw [this, show ρ + (2*k-1-ρ) = 2*k-1 by omega]
      · subst hγ'
        have e1 := vchain r (Or.inr rfl) (ρ - (2*k-1-(r-l))) (2*k-1-(r-l)) (by omega) le_rfl
        rw [show 2*k-1-(r-l) + (ρ - (2*k-1-(r-l))) = ρ by omega] at e1
        have e2 := hchain (r - l) l (by omega) le_rfl
        rw [show l + (r - l) = r by omega] at e2
        rw [← e1, ← e2, hbase]
      · subst hρ'
        have e2 := hchain (γ - l) l (by omega) le_rfl
        rw [show l + (γ - l) = γ by omega] at e2
        rw [← e2, hbase]
    have hval : ∀ u, cls u = some i → x u = cv (2*k-1) l := by
      intro u hu
      obtain ⟨p, rfl⟩ := vertexOf_surjective u
      rw [hclsP] at hu
      obtain ⟨r0, c0, d0⟩ := p
      rw [hcell r0 c0 d0 hu, ← hcv]
      exact hall _ _ r0.isLt c0.isLt hu
    rw [hval v hv, hval w hw]

/-- The explicit planar cylinder of four-port cells with its routing certificates. -/
theorem construction (k : ℕ) (hk : 0 < k) :
  ∃ (σ τ : Equiv.Perm (Fin (8*k^2))) (pin : Fin (2*k) → Bool × Fin (8*k^2)),
    let n := 8*k^2
    let I := Fin n
    let V := Bool × I
    let G := Option V
    let dest := fun e : Fin 3 × I => if e.1 = 0 then e.2 else if e.1 = 1 then σ e.2 else τ e.2
    let arc := fun (a b : V) => !a.1 && b.1 &&
      (decide (a.2 = b.2) || decide (σ a.2 = b.2) || decide (τ a.2 = b.2))
    let link := fun a b => arc a b || arc b a
    let rim := fun a : V => decide (∃ j, pin j = a)
    let inc := fun (x y : G) => x.elim (y.elim false rim) (fun a => y.elim (rim a) (link a))
    Function.Injective pin ∧ (∀ i j : V, Relation.ReflTransGen (fun a b => link a b = true) i j) ∧
    (∃ (l : ℕ) (src dst : Fin l → G) (rot rev : Equiv.Perm (Fin l)),
      Function.Injective (fun d => (src d,dst d)) ∧
      (∀ a b : G, inc a b = true ↔ ∃ d, src d = a ∧ dst d = b) ∧
      (∀ d, src (rev d) = dst d ∧ dst (rev d) = src d ∧ src (rot d) = src d) ∧
      (∀ a b, src a = src b → ∃ j : ℕ, (rot^j) a = b) ∧
      let walk := fun a : Fin l => rot (rev a)
      let faces := (Finset.univ : Finset (Fin l)).image (fun a =>
        (Finset.range l).image (fun j => walk^[j] a))
      2*(2*n+1) + 2*faces.card = 4+l) ∧
    (∀ A : Finset (Fin (2*k)), ∃ (a b : Fin (min A.card (2*k - A.card)) → Fin (2*k))
      (cls : V → Option (Fin (min A.card (2*k - A.card)))) (F : Finset (Fin 3 × I)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∉ A) ∧ (∀ i, cls (pin (a i)) = some i) ∧
      (∀ i, cls (pin (b i)) = some i) ∧
      (∀ e ∈ F, ∃ i, cls (false,e.2) = some i ∧ cls (true, dest e) = some i) ∧
      (∀ x : V → Bool, (∀ e ∈ F, x (false,e.2) = x (true,dest e)) →
        ∀ v w i, cls v = some i → cls w = some i → x v = x w)) := by
  refine ⟨sig k, tau k, pinV, ?_⟩
  intros
  exact ⟨fun a b h => pinPort_inj (vertexOf_injective h), conn_part k hk, planar_part k hk,
    cert_part k hk⟩

lemma bound_ok (k : ℕ) : 2 ^ (2*k) * 2 ^ (2*k) + 2 ≤ (3*(8*k^2)+1)*8^(2*k+1) := by
  have h1 : 2 ^ (2*k) * 2 ^ (2*k) ≤ 8 ^ (2*k) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) _
  have h2 : 1 ≤ 8 ^ (2*k) := Nat.one_le_pow _ _ (by norm_num)
  have h3 : 8 ^ (2*k+1) = 8 * 8 ^ (2*k) := by rw [pow_succ]; ring
  have h4 : 8 ^ (2*k+1) ≤ (3*(8*k^2)+1)*8^(2*k+1) := Nat.le_mul_of_pos_left _ (by positivity)
  omega

end PEqualNP.Outside.L_pcx_437_aux

theorem PEqualNP.Outside.L_pcx_437 : ∀ k : ℕ, 0 < k →
  let n := 8*k^2
  let I := Fin n
  let V := Bool × I
  let T := Fin (2*k)
  let E := Fin 3 × I
  ∃ (σ τ : Equiv.Perm I) (pin : T → V) (z : E → ℕ),
    let dest := fun e : E => if e.1 = 0 then e.2 else if e.1 = 1 then σ e.2 else τ e.2
    let arc := fun (a b : V) => !a.1 && b.1 &&
      (decide (a.2 = b.2) || decide (σ a.2 = b.2) || decide (τ a.2 = b.2))
    let link := fun a b => arc a b || arc b a
    let G := Option V
    let rim := fun a : V => decide (∃ j, pin j = a)
    let inc := fun (x y : G) => x.elim (y.elim false rim) (fun a => y.elim (rim a) (link a))
    Function.Injective pin ∧ (∀ i j : V, Relation.ReflTransGen (fun a b => link a b = true) i j) ∧
    (∃ (l : ℕ) (src dst : Fin l → G) (rot rev : Equiv.Perm (Fin l)),
      Function.Injective (fun d => (src d,dst d)) ∧
      (∀ a b : G, inc a b = true ↔ ∃ d, src d = a ∧ dst d = b) ∧
      (∀ d, src (rev d) = dst d ∧ dst (rev d) = src d ∧ src (rot d) = src d) ∧
      (∀ a b, src a = src b → ∃ j : ℕ, (rot^j) a = b) ∧
      let walk := fun a : Fin l => rot (rev a)
      let faces := (Finset.univ : Finset (Fin l)).image (fun a =>
        (Finset.range l).image (fun j => walk^[j] a))
      2*(2*n+1) + 2*faces.card = 4+l) ∧
    (∀ e, 2 ≤ z e ∧ z e ≤ (3*n+1)*8^(2*k+1)) ∧
    ∀ A : Finset T,
      let mat : Matrix (Finset T) (Finset T) ℚ := fun P Q =>
        ∑ x : V → Bool, if (∀ j ∈ A ∩ P, x (pin j) = false) ∧
            (∀ j ∈ Q, j ∉ A → x (pin j) = false) then
          ∏ e : E, (if x (false,e.2) = x (true,dest e) then 1 else (z e : ℚ)) else 0
      Matrix.rank mat = 2^(min A.card (2*k-A.card)) := by
  intro k hk
  obtain ⟨σ, τ, pin, hinj, hconn, hplan, hcert⟩ := PEqualNP.Outside.L_pcx_437_aux.construction k hk
  obtain ⟨z, hz, hrank⟩ := PEqualNP.Outside.L_pcx_437_aux.framework
    (fun e : Fin 3 × Fin (8*k^2) => if e.1 = 0 then e.2 else if e.1 = 1 then σ e.2 else τ e.2)
    pin ((3*(8*k^2)+1)*8^(2*k+1)) (PEqualNP.Outside.L_pcx_437_aux.bound_ok k) hcert
  exact ⟨σ, τ, pin, z, hinj, hconn, hplan, hz, fun A => hrank A⟩
