import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_709

open Finset

section Iter

variable {α : Type*}

def iterN (f : ℕ → α → α) : ℕ → α → α
  | 0, s => s
  | k + 1, s => f k (iterN f k s)

theorem iterN_succ (f : ℕ → α → α) (k : ℕ) (s : α) : iterN f (k + 1) s = f k (iterN f k s) := rfl

theorem iterN_add (f : ℕ → α → α) (a c : ℕ) (s : α) :
    iterN f (a + c) s = iterN (fun k => f (a + k)) c (iterN f a s) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show f (a + c) (iterN f (a + c) s) = f (a + c) (iterN (fun k => f (a + k)) c (iterN f a s))
    rw [ih]

theorem iterN_congr (f f' : ℕ → α → α) (N : ℕ) (h : ∀ k < N, f k = f' k) (s : α) :
    iterN f N s = iterN f' N s := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show f N (iterN f N s) = f' N (iterN f' N s)
    rw [ih (fun k hk => h k (by omega)), h N (by omega)]

theorem foldl_range (f : ℕ → α → α) (N : ℕ) (s : α) :
    (List.range N).foldl (fun s k => f k s) s = iterN f N s := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem foldl_finRange {N : ℕ} (f : Fin N → α → α) (s : α) :
    (List.finRange N).foldl (fun s i => f i s) s =
      iterN (fun k s => if h : k < N then f ⟨k, h⟩ s else s) N s := by
  rw [← foldl_range, ← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext t i
  simp [i.2]

theorem iterN_lin {K M : Type} [Field K] [AddCommGroup M] [Module K M] (F : ℕ → M →ₗ[K] M)
    (N : ℕ) : ∃ L : M →ₗ[K] M, ∀ v, iterN (fun k v => F k v) N v = L v := by
  induction N with
  | zero => exact ⟨LinearMap.id, fun v => rfl⟩
  | succ N ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨F N ∘ₗ L, fun v => by rw [iterN_succ, hL]; rfl⟩

end Iter

section Cyc

variable {b a : ℕ}

abbrev Ctrl (b : ℕ) := (Fin b → ZMod 2) × ZMod 2

def row (c : Ctrl b) (s : Fin (b + 1) → ZMod 2) : Fin (b + 1) → ZMod 2 :=
  Fin.snoc (α := fun _ : Fin (b + 1) => ZMod 2) (fun j : Fin b => s j.succ)
    (s 0 + c.2 + ∑ j : Fin b, c.1 j * s j.succ)

theorem row_cs (c : Ctrl b) (s : Fin (b + 1) → ZMod 2) (j : Fin b) :
    row c s (Fin.castSucc j) = s j.succ := by
  simp [row]

theorem row_last (c : Ctrl b) (s : Fin (b + 1) → ZMod 2) :
    row c s (Fin.last b) = s 0 + c.2 + ∑ j : Fin b, c.1 j * s j.succ := by
  simp [row]

def gC (C : Fin (a + 1) → Ctrl b) (k : ℕ) : (Fin (b + 1) → ZMod 2) → (Fin (b + 1) → ZMod 2) :=
  row (C (Fin.ofNat (a + 1) k))

def sol (C : Fin (a + 1) → Ctrl b) : Finset (Fin (a + 1) → ZMod 2) :=
  (Finset.univ : Finset (Fin (a + 1) → ZMod 2)).filter (fun x =>
    ∀ i : Fin (a + 1), x (Fin.ofNat (a + 1) (i.val + (b + 1))) = x i + (C i).2 +
      ∑ j : Fin b, (C i).1 j * x (Fin.ofNat (a + 1) (i.val + 1 + j.val)))

def fixS (C : Fin (a + 1) → Ctrl b) : Finset (Fin (b + 1) → ZMod 2) :=
  (Finset.univ : Finset (Fin (b + 1) → ZMod 2)).filter (fun s => iterN (gC C) (a + 1) s = s)

def stt (b : ℕ) (y : ℕ → ZMod 2) (k : ℕ) : Fin (b + 1) → ZMod 2 := fun j => y (k + j.val)

theorem of_mod_add (k t : ℕ) :
    Fin.ofNat (a + 1) ((Fin.ofNat (a + 1) k).val + t) = Fin.ofNat (a + 1) (k + t) :=
  Fin.ext (by simp only [Fin.val_ofNat, Nat.mod_add_mod])

theorem of_mod_add2 (k t : ℕ) :
    Fin.ofNat (a + 1) ((Fin.ofNat (a + 1) k).val + 1 + t) = Fin.ofNat (a + 1) (k + 1 + t) :=
  Fin.ext (by
    simp only [Fin.val_ofNat]
    rw [Nat.add_assoc (k % (a + 1)), Nat.add_assoc k, Nat.mod_add_mod])

theorem of_add_period (k : ℕ) : Fin.ofNat (a + 1) (a + 1 + k) = Fin.ofNat (a + 1) k :=
  Fin.ext (by simp only [Fin.val_ofNat, Nat.add_mod_left])

theorem of_lt (k : ℕ) (h : k < a + 1) : Fin.ofNat (a + 1) k = ⟨k, h⟩ :=
  Fin.ext (by simp only [Fin.val_ofNat, Nat.mod_eq_of_lt h])

theorem sol_rec (C : Fin (a + 1) → Ctrl b) (x : Fin (a + 1) → ZMod 2) (hx : x ∈ sol C) (k : ℕ) :
    x (Fin.ofNat (a + 1) (k + (b + 1))) = x (Fin.ofNat (a + 1) k) + (C (Fin.ofNat (a + 1) k)).2 +
      ∑ j : Fin b, (C (Fin.ofNat (a + 1) k)).1 j * x (Fin.ofNat (a + 1) (k + 1 + j.val)) := by
  have h := (Finset.mem_filter.mp hx).2 (Fin.ofNat (a + 1) k)
  simp only [of_mod_add, of_mod_add2] at h
  exact h

theorem row_stt (C : Fin (a + 1) → Ctrl b) (y : ℕ → ZMod 2) (k : ℕ)
    (h : y (k + (b + 1)) = y k + (C (Fin.ofNat (a + 1) k)).2 +
      ∑ j : Fin b, (C (Fin.ofNat (a + 1) k)).1 j * y (k + 1 + j.val)) :
    gC C k (stt b y k) = stt b y (k + 1) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    show row (C (Fin.ofNat (a + 1) k)) (stt b y k) (Fin.last b) = stt b y (k + 1) (Fin.last b)
    rw [row_last]
    simp only [stt, Fin.val_zero, Fin.val_succ, Fin.val_last, Nat.add_zero]
    rw [show k + 1 + b = k + (b + 1) by omega, h]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show k + (j.val + 1) = k + 1 + j.val by omega]
  | cast j =>
    show row (C (Fin.ofNat (a + 1) k)) (stt b y k) (Fin.castSucc j) =
      stt b y (k + 1) (Fin.castSucc j)
    rw [row_cs]
    simp only [stt, Fin.val_succ, Fin.val_castSucc]
    rw [show k + (j.val + 1) = k + 1 + j.val by omega]

theorem iter_stt (C : Fin (a + 1) → Ctrl b) (x : Fin (a + 1) → ZMod 2) (hx : x ∈ sol C) (k : ℕ) :
    iterN (gC C) k (stt b (fun t => x (Fin.ofNat (a + 1) t)) 0) =
      stt b (fun t => x (Fin.ofNat (a + 1) t)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterN_succ, ih]
    exact row_stt C _ k (sol_rec C x hx k)

theorem zp (C : Fin (a + 1) → Ctrl b) (s : Fin (b + 1) → ZMod 2) (hs : iterN (gC C) (a + 1) s = s)
    (k : ℕ) : iterN (gC C) (a + 1 + k) s = iterN (gC C) k s := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    show gC C (a + 1 + k) (iterN (gC C) (a + 1 + k) s) = gC C k (iterN (gC C) k s)
    rw [ih]
    simp only [gC, of_add_period]

theorem zs (C : Fin (a + 1) → Ctrl b) (s : Fin (b + 1) → ZMod 2) (t : ℕ) :
    ∀ (k : ℕ) (j : Fin (b + 1)), j.val = t → iterN (gC C) k s j = iterN (gC C) (k + t) s 0 := by
  induction t with
  | zero =>
    intro k j hj
    have : j = 0 := Fin.ext (by simpa using hj)
    subst this
    rfl
  | succ t ih =>
    intro k j hj
    have ht : t < b := by have := j.2; omega
    have hj' : j = Fin.succ ⟨t, ht⟩ := Fin.ext (by simp [hj])
    subst hj'
    have e : iterN (gC C) k s (Fin.succ ⟨t, ht⟩) =
        iterN (gC C) (k + 1) s (Fin.castSucc ⟨t, ht⟩) := (row_cs _ _ _).symm
    rw [e, ih (k + 1) _ (by simp), show k + 1 + t = k + (t + 1) by omega]

theorem Ymod (C : Fin (a + 1) → Ctrl b) (s : Fin (b + 1) → ZMod 2)
    (hs : iterN (gC C) (a + 1) s = s) (k : ℕ) :
    iterN (gC C) (Fin.ofNat (a + 1) k).val s 0 = iterN (gC C) k s 0 := by
  have Yp : ∀ q r, iterN (gC C) (r + (a + 1) * q) s 0 = iterN (gC C) r s 0 := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show r + (a + 1) * (q + 1) = a + 1 + (r + (a + 1) * q) by ring, zp C s hs, ih]
  have := Yp (k / (a + 1)) (k % (a + 1))
  rw [Nat.mod_add_div] at this
  rw [Fin.val_ofNat]
  exact this.symm

theorem card_sol (C : Fin (a + 1) → Ctrl b) : (sol C).card = (fixS C).card := by
  refine Finset.card_bij' (fun x _ => stt b (fun t => x (Fin.ofNat (a + 1) t)) 0)
    (fun s _ => fun i : Fin (a + 1) => iterN (gC C) i.val s 0) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [fixS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [iter_stt C x hx]
    funext j
    simp only [stt, of_add_period, Nat.zero_add]
  · intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    simp only [Ymod C s hs']
    rw [show i.val + (b + 1) = i.val + 1 + b by omega,
      ← zs C s b (i.val + 1) (Fin.last b) (by simp)]
    have e1 : iterN (gC C) (i.val + 1) s (Fin.last b) = iterN (gC C) i.val s 0 + (C i).2 +
        ∑ j : Fin b, (C i).1 j * iterN (gC C) i.val s j.succ := by
      show row (C (Fin.ofNat (a + 1) i.val)) (iterN (gC C) i.val s) (Fin.last b) = _
      rw [row_last, Fin.ofNat_val_eq_self]
    rw [e1]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [zs C s (j.val + 1) i.val j.succ (by simp),
      show i.val + (j.val + 1) = i.val + 1 + j.val by omega]
  · intro x hx
    funext i
    show iterN (gC C) i.val (stt b (fun t => x (Fin.ofNat (a + 1) t)) 0) 0 = x i
    rw [iter_stt C x hx]
    simp only [stt, Fin.val_zero, Nat.add_zero, Fin.ofNat_val_eq_self]
  · intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    funext j
    simp only [stt]
    rw [Ymod C s hs', ← zs C s j.val 0 j rfl]
    rfl

end Cyc

section Aff

variable {b : ℕ}

abbrev Vb (b : ℕ) := Fin (b + 1) → ZMod 2
abbrev Pb (b : ℕ) := (Vb b ≃ₗ[ZMod 2] Vb b) × Vb b

def fixedC (p r : Pb b) : ℕ :=
  ((Finset.univ : Finset (Vb b)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card

def comp (r p : Pb b) : Pb b := (p.1.trans r.1, r.1 p.2 + r.2)

theorem comp_app (r p : Pb b) (x : Vb b) :
    (comp r p).1 x + (comp r p).2 = r.1 (p.1 x + p.2) + r.2 := by
  simp only [comp, LinearEquiv.trans_apply, map_add, add_assoc]

def idP : Pb b := (LinearEquiv.refl _ _, 0)

theorem idP_app (y : Vb b) : (idP : Pb b).1 y + (idP : Pb b).2 = y := by
  simp [idP]

def rowLin (tap : Fin b → ZMod 2) : Vb b →ₗ[ZMod 2] Vb b where
  toFun s := Fin.snoc (α := fun _ : Fin (b + 1) => ZMod 2) (fun j : Fin b => s j.succ)
    (s 0 + ∑ j : Fin b, tap j * s j.succ)
  map_add' s t := by
    funext k
    induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring
    | cast j => simp only [Fin.snoc_castSucc, Pi.add_apply]
  map_smul' c s := by
    funext k
    induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    | cast j => simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem rowLin_inj (tap : Fin b → ZMod 2) : Function.Injective (rowLin tap) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  have h1 : ∀ j : Fin b, s j.succ = 0 := fun j => by
    have := congrFun hs (Fin.castSucc j)
    simpa [rowLin] using this
  have h0 : s 0 = 0 := by
    have := congrFun hs (Fin.last b)
    simpa [rowLin, h1] using this
  funext k
  induction k using Fin.cases with
  | zero => exact h0
  | succ j => exact h1 j

noncomputable def rowP (c : Ctrl b) : Pb b :=
  (LinearEquiv.ofInjectiveEndo (rowLin c.1) (rowLin_inj c.1),
    Fin.snoc (α := fun _ : Fin (b + 1) => ZMod 2) (0 : Fin b → ZMod 2) c.2)

theorem rowP_app (c : Ctrl b) (s : Vb b) : (rowP c).1 s + (rowP c).2 = row c s := by
  funext k
  induction k using Fin.lastCases with
  | last =>
    simp [rowP, rowLin, row]
    try ring
  | cast j => simp [rowP, rowLin, row]

end Aff

theorem embed {K M : Type} [Field K] [AddCommGroup M] [Module K M] (W : Submodule K M)
    [FiniteDimensional K W] (m : ℕ) (hk : Module.finrank K W ≤ m) :
    ∃ (Ψ : M →ₗ[K] (Fin m → K)) (Ψ' : (Fin m → K) →ₗ[K] M), ∀ f ∈ W, Ψ' (Ψ f) = f := by
  obtain ⟨g0, hg0⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  let e := (Module.finBasis K W).equivFun
  let ι : (Fin (Module.finrank K W) → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun v j => if h : j.val < Module.finrank K W then v ⟨j.val, h⟩ else 0
      map_add' := fun v v' => by
        funext j
        by_cases h : j.val < Module.finrank K W <;> simp [h]
      map_smul' := fun c v => by
        funext j
        by_cases h : j.val < Module.finrank K W <;> simp [h] }
  let π : (Fin m → K) →ₗ[K] (Fin (Module.finrank K W) → K) := LinearMap.funLeft K K (Fin.castLE hk)
  have hπ : ∀ v, π (ι v) = v := fun v => by
    funext i
    simp [π, ι, LinearMap.funLeft_apply, i.2]
  refine ⟨ι ∘ₗ e.toLinearMap ∘ₗ g0, W.subtype ∘ₗ e.symm.toLinearMap ∘ₗ π, fun f hf => ?_⟩
  have hg : g0 f = ⟨f, hf⟩ := by
    have := LinearMap.congr_fun hg0 ⟨f, hf⟩
    simpa using this
  simp [hg, hπ]

theorem upper (K : Type) [Field K] (b a m d : ℕ)
    (hF : ∃ A B : Pb b → Fin d → K, ∀ p r, (fixedC p r : K) = ∑ j, A p j * B r j)
    (hm : d ≤ m) :
    ∃ (s : Fin m → K) (step : Fin (a + 1) → Ctrl b → (Fin m → K) →ₗ[K] (Fin m → K))
      (out : (Fin m → K) →ₗ[K] K), ∀ C : Fin (a + 1) → Ctrl b,
        out ((List.finRange (a + 1)).foldl (fun v i => step i (C i) v) s) = ((sol C).card : K) := by
  obtain ⟨A, B, hAB⟩ := hF
  let φ : Pb b → (Pb b → K) := fun p r => (fixedC p r : K)
  let W := Submodule.span K (Set.range (fun j : Fin d => fun r : Pb b => B r j))
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hW : Module.finrank K W ≤ m :=
    (finrank_range_le_card (R := K) (fun j : Fin d => fun r : Pb b => B r j)).trans
      (by simpa using hm)
  have hφ : ∀ p, φ p ∈ W := fun p => by
    have : φ p = ∑ j, A p j • (fun r : Pb b => B r j) := by
      funext r
      simp [φ, hAB, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  obtain ⟨Ψ, Ψ', hΨ⟩ := embed W m hW
  let pre : Pb b → (Pb b → K) →ₗ[K] (Pb b → K) := fun R => LinearMap.funLeft K K (fun r => comp r R)
  have hpre : ∀ R q, pre R (φ q) = φ (comp R q) := fun R q => by
    funext r
    simp only [pre, φ, LinearMap.funLeft_apply, fixedC, comp_app]
  let step : Fin (a + 1) → Ctrl b → (Fin m → K) →ₗ[K] (Fin m → K) :=
    fun _ c => Ψ ∘ₗ pre (rowP c) ∘ₗ Ψ'
  refine ⟨Ψ (φ idP), step, (LinearMap.proj (R := K) (φ := fun _ : Pb b => K) idP) ∘ₗ Ψ',
    fun C => ?_⟩
  rw [foldl_finRange]
  let Fp : ℕ → Pb b → Pb b := fun k q => if h : k < a + 1 then comp (rowP (C ⟨k, h⟩)) q else q
  have inv : ∀ N, N ≤ a + 1 →
      iterN (fun k v => if h : k < a + 1 then step ⟨k, h⟩ (C ⟨k, h⟩) v else v) N (Ψ (φ idP)) =
        Ψ (φ (iterN Fp N idP)) := by
    intro N
    induction N with
    | zero => intro _; rfl
    | succ N ih =>
      intro hN
      have hN' : N < a + 1 := by omega
      rw [iterN_succ, iterN_succ, ih (by omega)]
      simp only [Fp, dif_pos hN', step, LinearMap.comp_apply]
      rw [hΨ _ (hφ _), hpre]
  have appQ : ∀ N, N ≤ a + 1 → ∀ x,
      (iterN Fp N idP).1 x + (iterN Fp N idP).2 = iterN (gC C) N x := by
    intro N
    induction N with
    | zero => intro _ x; exact idP_app x
    | succ N ih =>
      intro hN x
      have hN' : N < a + 1 := by omega
      rw [iterN_succ, iterN_succ, ← ih (by omega) x]
      simp only [Fp, dif_pos hN', comp_app]
      rw [rowP_app]
      simp only [gC, of_lt N hN']
  rw [inv (a + 1) le_rfl]
  simp only [LinearMap.comp_apply]
  rw [hΨ _ (hφ _)]
  simp only [LinearMap.proj_apply, φ]
  rw [card_sol]
  congr 1
  unfold fixedC fixS
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => by
    simp only [idP_app, appQ (a + 1) le_rfl]))

theorem lower (K : Type) [Field K] (b a m d : ℕ)
    (hR : ∀ L : ℕ, (∀ (g : Vb b ≃ₗ[ZMod 2] Vb b) (v : Vb b),
      ∃ (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2), ∀ x : Vb b,
        (List.finRange L).foldl (fun (s : Vb b) i => row (tap i, bias i) s) x = g x + v) ↔
          2 * (b + 1) - 1 ≤ L)
    (hF : (∃ A B : Pb b → Fin m → K, ∀ p r, (fixedC p r : K) = ∑ j, A p j * B r j) → d ≤ m)
    (hn : 2 * (2 * (b + 1) - 1) ≤ a + 1)
    (hadm : ∃ (s : Fin m → K) (step : Fin (a + 1) → Ctrl b → (Fin m → K) →ₗ[K] (Fin m → K))
      (out : (Fin m → K) →ₗ[K] K), ∀ C : Fin (a + 1) → Ctrl b,
        out ((List.finRange (a + 1)).foldl (fun v i => step i (C i) v) s) = ((sol C).card : K)) :
    d ≤ m := by
  obtain ⟨s, step, out, hs⟩ := hadm
  obtain ⟨L1, hL1⟩ : ∃ L1, L1 = 2 * (b + 1) - 1 := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2, L2 = a + 1 - L1 := ⟨_, rfl⟩
  have hn' : a + 1 = L1 + L2 := by omega
  have h1 := (hR L1).mpr (by omega)
  have h2 := (hR L2).mpr (by omega)
  choose t1 b1 e1 using h1
  choose t2 b2 e2 using h2
  let c1 : Pb b → ℕ → Ctrl b := fun p k =>
    if h : k < L1 then (t1 p.1 p.2 ⟨k, h⟩, b1 p.1 p.2 ⟨k, h⟩) else (0, 0)
  let c2 : Pb b → ℕ → Ctrl b := fun r k =>
    if h : k < L2 then (t2 r.1 r.2 ⟨k, h⟩, b2 r.1 r.2 ⟨k, h⟩) else (0, 0)
  let cc : Pb b → Pb b → ℕ → Ctrl b := fun p r k => if k < L1 then c1 p k else c2 r (k - L1)
  have key : ∀ p r x, iterN (gC (fun i : Fin (a + 1) => cc p r i.val)) (a + 1) x =
      r.1 (p.1 x + p.2) + r.2 := by
    intro p r x
    have E1 := e1 p.1 p.2 x
    have E2 := e2 r.1 r.2 (p.1 x + p.2)
    rw [foldl_finRange] at E1 E2
    have s1 : iterN (gC (fun i : Fin (a + 1) => cc p r i.val)) (a + 1) x =
        iterN (fun k => row (cc p r k)) (a + 1) x :=
      iterN_congr _ _ _ (fun k hk => by
        show row (cc p r (Fin.ofNat (a + 1) k).val) = row (cc p r k)
        rw [Fin.val_ofNat, Nat.mod_eq_of_lt hk]) x
    have s2 : iterN (fun k => row (cc p r k)) (a + 1) x =
        iterN (fun j => row (cc p r (L1 + j))) L2 (iterN (fun k => row (cc p r k)) L1 x) := by
      rw [hn']
      exact iterN_add _ L1 L2 x
    have s3 : iterN (fun k => row (cc p r k)) L1 x = iterN (fun k s =>
        if h : k < L1 then row (t1 p.1 p.2 ⟨k, h⟩, b1 p.1 p.2 ⟨k, h⟩) s else s) L1 x :=
      iterN_congr _ _ _ (fun k hk => by
        funext s
        simp only [cc, c1, if_pos hk, dif_pos hk]) x
    have s4 : iterN (fun j => row (cc p r (L1 + j))) L2 (p.1 x + p.2) = iterN (fun k s =>
        if h : k < L2 then row (t2 r.1 r.2 ⟨k, h⟩, b2 r.1 r.2 ⟨k, h⟩) s else s) L2
          (p.1 x + p.2) :=
      iterN_congr _ _ _ (fun k hk => by
        funext s
        simp only [cc, c2, if_neg (show ¬ (L1 + k < L1) by omega), Nat.add_sub_cancel_left,
          dif_pos hk]) _
    rw [s1, s2, s3, E1, s4, E2]
  have fixed_eq : ∀ p r, fixedC p r = (sol (fun i : Fin (a + 1) => cc p r i.val)).card := by
    intro p r
    rw [card_sol]
    unfold fixedC fixS
    exact congrArg Finset.card (Finset.filter_congr (fun x _ => by simp only [key]))
  let SL : Pb b → Pb b → ℕ → (Fin m → K) →ₗ[K] (Fin m → K) := fun p r k =>
    if h : k < a + 1 then step ⟨k, h⟩ (cc p r k) else LinearMap.id
  have hpre : ∀ p r, iterN (fun k v => SL p r k v) L1 s = iterN (fun k v => SL p idP k v) L1 s :=
    fun p r => iterN_congr _ _ _ (fun k hk => by
      funext v
      simp only [SL, cc, if_pos hk]) s
  have hsuf : ∀ p r v, iterN (fun j v => SL p r (L1 + j) v) L2 v =
      iterN (fun j v => SL idP r (L1 + j) v) L2 v :=
    fun p r v => iterN_congr _ _ _ (fun k hk => by
      funext v
      simp only [SL, cc, if_neg (show ¬ (L1 + k < L1) by omega)]) v
  have hsplit : ∀ F : ℕ → (Fin m → K) → (Fin m → K),
      iterN F (a + 1) s = iterN (fun j => F (L1 + j)) L2 (iterN F L1 s) := fun F => by
    rw [hn']
    exact iterN_add F L1 L2 s
  choose Lr hLr using fun r => iterN_lin (fun j => SL idP r (L1 + j)) L2
  apply hF
  refine ⟨fun p => iterN (fun k v => SL p idP k v) L1 s,
    fun r j => (out ∘ₗ Lr r) (fun j' => if j = j' then 1 else 0), fun p r => ?_⟩
  have hfin : out (Lr r (iterN (fun k v => SL p idP k v) L1 s)) =
      ((sol (fun i : Fin (a + 1) => cc p r i.val)).card : K) := by
    rw [← hs (fun i => cc p r i.val), foldl_finRange]
    congr 1
    calc Lr r (iterN (fun k v => SL p idP k v) L1 s)
        = iterN (fun j v => SL idP r (L1 + j) v) L2 (iterN (fun k v => SL p idP k v) L1 s) :=
          (hLr r _).symm
      _ = iterN (fun j v => SL p r (L1 + j) v) L2 (iterN (fun k v => SL p r k v) L1 s) := by
          rw [hpre p r, hsuf p r]
      _ = iterN (fun k v => SL p r k v) (a + 1) s := (hsplit (fun k v => SL p r k v)).symm
      _ = _ := iterN_congr _ _ _ (fun k hk => by
          funext v
          show (if h : k < a + 1 then step ⟨k, h⟩ (cc p r k) else LinearMap.id) v = _
          rw [dif_pos hk, dif_pos hk]) s
  rw [fixed_eq p r, ← hfin]
  exact (LinearMap.pi_apply_eq_sum_univ (out ∘ₗ Lr r) _).trans (by simp only [smul_eq_mul])

end PEqualNP.Outside.L_lib_709

open PEqualNP.Outside.L_lib_709 in
theorem PEqualNP.Outside.L_lib_709 : let affineRouting : Prop :=
  ∀ (b L : ℕ),
    let w := b + 1
    let V := Fin w → ZMod 2
    (∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      ∃ (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2),
        ∀ x : V, (List.finRange L).foldl (fun (s : V) i =>
          let tail := fun j : Fin b => s j.succ
          Fin.snoc (α := fun _ : Fin w => ZMod 2) tail
            (s 0 + bias i + ∑ j : Fin b, tap i j * tail j)) x = g x + v) ↔
      2 * w - 1 ≤ L
let fixedPointRank : Prop :=
  ∀ (K : Type) [Field K] [CharP K 2] (b d : ℕ),
    let w := b + 1
    let V := Fin w → ZMod 2
    let P := (V ≃ₗ[ZMod 2] V) × V
    let fixed := fun (p r : P) =>
      ((Finset.univ : Finset V).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card
    (∃ (A B : P → Fin d → K),
      ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
      Nat.choose (2 * w) w - 2 ≤ d
let conclusion : Prop :=
  ∀ (K : Type) [Field K] [CharP K 2] (b a m : ℕ),
    let w := b + 1
    let n := a + 1
    let Control := (Fin b → ZMod 2) × ZMod 2
    let cost := Nat.choose (2 * w) w - 2
    let atSite := fun k => Fin.ofNat (a + 1) k
    let count := fun (C : Fin n → Control) =>
      ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x =>
        ∀ i : Fin n, x (atSite (i.val + w)) = x i + (C i).2 +
          ∑ j : Fin b, (C i).1 j * x (atSite (i.val + 1 + j.val)))).card
    let admits :=
      ∃ (s : Fin m → K) (step : Fin n → Control → (Fin m → K) →ₗ[K] (Fin m → K))
        (out : (Fin m → K) →ₗ[K] K),
        ∀ C : Fin n → Control,
          out ((List.finRange n).foldl (fun v i => step i (C i) v) s) = (count C : K)
    (cost ≤ m → admits) ∧ (2 * (2 * w - 1) ≤ n → admits → cost ≤ m)
affineRouting → fixedPointRank → conclusion := by
  intro aR fR concl hR hF K _ _ b a m w n Control cost atSite count admits
  exact ⟨fun hm => upper K b a m _ ((hF K b _).mpr le_rfl) hm,
    fun hn hadm => lower K b a m _ (fun L => hR b L) (hF K b m).mp hn hadm⟩
