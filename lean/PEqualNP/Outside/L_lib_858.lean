import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_858

open Finset

theorem zmod2_eq_one {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

theorem add_self_zero {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) : y + y = 0 := by
  have h2 : (2 : K) = 0 := by
    have : (algebraMap (ZMod 2) K) 2 = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, map_zero]
    rwa [map_ofNat] at this
  rw [← two_mul, h2, zero_mul]

theorem nsmul_even {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) {n : ℕ} (h : Even n) :
    n • y = 0 := by
  obtain ⟨m, rfl⟩ := h
  rw [add_nsmul, add_self_zero]

theorem nsmul_odd {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) {n : ℕ} (h : ¬ Even n) :
    n • y = y := by
  obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp h
  rw [add_nsmul, two_mul, add_nsmul, add_self_zero, zero_add, one_nsmul]

theorem rank_full {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (f : K →ₗ[ZMod 2] K) (c : K) (hc : c ≠ 0) (hf : ∀ x, f x = c * x) :
    Module.finrank (ZMod 2) (LinearMap.range f) = Module.finrank (ZMod 2) K := by
  have : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨c⁻¹ * y, by rw [hf, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [this, finrank_top]

theorem sets_eq {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module (ZMod 2) V]
    (v : ι → V) (hv : LinearIndependent (ZMod 2) v) (S S' : Finset ι)
    (h : ∑ i ∈ S, v i = ∑ i ∈ S', v i) : S = S' := by
  have key : ∀ T : Finset ι, ∑ i, (if i ∈ T then (1 : ZMod 2) else 0) • v i = ∑ i ∈ T, v i := by
    intro T
    simp [ite_smul]
  have hz := Fintype.linearIndependent_iff.mp hv
    (fun i => (if i ∈ S then (1 : ZMod 2) else 0) - (if i ∈ S' then (1 : ZMod 2) else 0))
    (by simp only [sub_smul, Finset.sum_sub_distrib, key, h, sub_self])
  ext i
  have := hz i
  by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp_all

theorem sumform {K : Type} [Field K] [Algebra (ZMod 2) K] {k : ℕ}
    (D : Fin (k+1) → (K →ₗ[ZMod 2] K)) (a : Fin k → K)
    (ha : ∀ (i : Fin k) (x : K), D i.succ x = D 0 x + a i * x) (S : Finset (Fin (k+1))) (x : K) :
    ∑ j ∈ S, D j x = S.card • D 0 x + (∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j) * x := by
  have hj : ∀ j : Fin (k+1), D j x = D 0 x + (Fin.cons 0 a : Fin (k+1) → K) j * x := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp [ha]
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_mul]

theorem struct {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (k : ℕ) (hk : 0 < k) (hK : Module.finrank (ZMod 2) K = k)
    (D : Fin (k+1) → (K →ₗ[ZMod 2] K))
    (hD : ∀ i, Module.finrank (ZMod 2) (LinearMap.range (D i)) < k)
    (hc : ∀ z : K, ∃ S : Finset (Fin (k+1)), ∀ x : K, ∑ i ∈ S, D i x = z * x) :
    LinearIndependent (ZMod 2) D ∧ ∃ a : Fin k → K, LinearIndependent (ZMod 2) a ∧
          ∀ (i : Fin k) (x : K), D i.succ x = D 0 x + a i * x := by
  classical
  set μ := LinearMap.mul (ZMod 2) K with hμ
  set M := LinearMap.range μ with hM
  set V := Submodule.span (ZMod 2) (Set.range D) with hV
  have hμinj : Function.Injective μ := by
    intro c d h
    have := LinearMap.congr_fun h 1
    simpa [hμ] using this
  have hMr : Module.finrank (ZMod 2) M = k := by
    rw [hM, LinearMap.finrank_range_of_inj hμinj, hK]
  have hsing : ∀ f ∈ M, Module.finrank (ZMod 2) (LinearMap.range f) < k → f = 0 := by
    rintro f ⟨c, rfl⟩ hf
    by_cases h0 : c = 0
    · rw [h0, map_zero]
    · exfalso
      have := rank_full (μ c) c h0 (fun x => by simp [hμ])
      omega
  have hMV : M ≤ V := by
    rintro f ⟨c, rfl⟩
    obtain ⟨S, hS⟩ := hc c
    have : μ c = ∑ i ∈ S, D i := by
      ext x
      rw [LinearMap.sum_apply, hS]
      simp [hμ]
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)
  have eV : Set.finrank (ZMod 2) (Set.range D) = Module.finrank (ZMod 2) V := rfl
  have hVle : Module.finrank (ZMod 2) V ≤ k + 1 := by
    have := finrank_range_le_card (R := ZMod 2) D
    rw [eV, Fintype.card_fin] at this
    exact this
  have hli : LinearIndependent (ZMod 2) D := by
    by_contra hn
    have h1 : Module.finrank (ZMod 2) V ≤ k := by
      have : Fintype.card (Fin (k+1)) ≠ Module.finrank (ZMod 2) V :=
        fun h => hn (linearIndependent_iff_card_eq_finrank_span.mpr (h.trans eV.symm))
      rw [Fintype.card_fin] at this
      omega
    have hMeq : M = V := Submodule.eq_of_le_of_finrank_le hMV (by omega)
    have hz : ∀ i, D i = 0 := fun i =>
      hsing _ (hMeq ▸ Submodule.subset_span ⟨i, rfl⟩) (hD i)
    have hbot : V = ⊥ := by
      rw [hV, Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact hz i
    rw [hMeq, hbot, finrank_bot] at hMr
    omega
  have hVr : Module.finrank (ZMod 2) V = k + 1 := by
    have := linearIndependent_iff_card_eq_finrank_span.mp hli
    rw [eV, Fintype.card_fin] at this
    exact this.symm
  have hnotM : ∀ i, D i ∉ M := fun i h => hli.ne_zero i (hsing _ h (hD i))
  set W := M ⊔ Submodule.span (ZMod 2) {D 0} with hW
  have hD0W : D 0 ∈ W := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hMW : M < W := IsConcreteLE.lt_iff_le_and_exists.mpr ⟨le_sup_left, D 0, hD0W, hnotM 0⟩
  have hWV : W ≤ V := sup_le hMV (Submodule.span_le.mpr
    (Set.singleton_subset_iff.mpr (Submodule.subset_span ⟨0, rfl⟩)))
  have hWr := Submodule.finrank_lt_finrank_of_lt hMW
  have hWeq : W = V := Submodule.eq_of_le_of_finrank_le hWV (by omega)
  have hdiff : ∀ i, ∃ a : K, ∀ x, D i x = D 0 x + a * x := by
    intro i
    have hi : D i ∈ W := hWeq ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hi
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    by_cases hc0 : c = 0
    · exfalso
      apply hnotM i
      rw [← hyz, hc0, zero_smul, add_zero]
      exact hy
    · rw [zmod2_eq_one hc0, one_smul] at hyz
      obtain ⟨a, rfl⟩ := hy
      refine ⟨a, fun x => ?_⟩
      rw [← hyz, LinearMap.add_apply, add_comm]
      simp [hμ]
  choose a ha using hdiff
  refine ⟨hli, fun i => a i.succ, ?_, fun i x => ha i.succ x⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := Fintype.linearIndependent_iff.mp hli
    (Fin.cons (-(∑ j, g j)) g : Fin (k+1) → ZMod 2) (by
      ext x
      rw [LinearMap.sum_apply, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.smul_apply, LinearMap.zero_apply]
      have e : ∀ j : Fin k, g j • D j.succ x = g j • D 0 x + (g j • a j.succ) * x := by
        intro j
        rw [ha j.succ x, smul_add, smul_mul_assoc]
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, ← Finset.sum_mul, hg,
        zero_mul, add_zero, ← Finset.sum_smul, neg_smul, neg_add_cancel])
  have := h0 i.succ
  simpa using this

end PEqualNP.Outside.L_lib_858

open PEqualNP.Outside.L_lib_858 in
theorem PEqualNP.Outside.L_lib_858 :
let F := ZMod 2
∀ (k : ℕ), 0 < k →
  ∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
    Module.finrank F K = k →
    ∀ (D : Fin (k+1) → (K →ₗ[F] K)),
      (∀ i, Module.finrank F (LinearMap.range (D i)) < k) →
      let hit := fun (S : Finset (Fin (k+1))) (z : K) =>
        ∀ x : K, ∑ i ∈ S, D i x = z*x
      ((∀ z : K, ∃ S, hit S z) ↔
        ∃ a : Fin k → K, LinearIndependent F a ∧
          ∀ (i : Fin k) (x : K), D i.succ x = D 0 x + a i*x) ∧
      ((∀ z : K, ∃ S, hit S z) →
        (∀ S, (∃ z : K, hit S z) ↔ Even S.card) ∧
        (∀ z : K, ∃! S, hit S z)) := by
  intro F k hk K _ _ _ hK D hD hit
  classical
  refine ⟨⟨fun hc => (struct k hk hK D hD hc).2, ?_⟩, ?_⟩
  · rintro ⟨a, hai, ha⟩ z
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have hspan := hai.span_eq_top_of_card_eq_finrank (by simpa using hK.symm)
    have hz : z ∈ Submodule.span (ZMod 2) (Set.range a) := by rw [hspan]; trivial
    obtain ⟨c, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hz
    set T := Finset.univ.filter (fun i => c i = 1) with hT
    have hTs : ∑ i ∈ T, a i = z := by
      rw [← hcz, hT, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : c i = 1
      · rw [if_pos h, h, one_smul]
      · have h0 : c i = 0 := by
          by_contra h0
          exact h (zmod2_eq_one h0)
        rw [if_neg h, h0, zero_smul]
    set S0 := T.map (Fin.succEmb k) with hS0
    have hS0s : ∑ j ∈ S0, (Fin.cons 0 a : Fin (k+1) → K) j = z := by
      rw [hS0, Finset.sum_map]
      simpa using hTs
    have h0n : (0 : Fin (k+1)) ∉ S0 := by
      rw [hS0, Finset.mem_map]
      rintro ⟨i, _, hi⟩
      exact Fin.succ_ne_zero i hi
    by_cases hev : Even S0.card
    · refine ⟨S0, fun x => ?_⟩
      rw [sumform D a ha, nsmul_even _ hev, zero_add, hS0s]
    · refine ⟨insert 0 S0, fun x => ?_⟩
      have hev' : Even (insert 0 S0).card := by
        rw [Finset.card_insert_of_notMem h0n]
        exact (Nat.even_add_one).mpr hev
      rw [sumform D a ha, nsmul_even _ hev', zero_add, Finset.sum_insert h0n, hS0s]
      simp
  · intro hc
    obtain ⟨hli, a, hai, ha⟩ := struct k hk hK D hD hc
    refine ⟨fun S => ⟨?_, ?_⟩, fun z => ?_⟩
    · rintro ⟨z, hz⟩
      by_contra hev
      have hD0 : ∀ x, D 0 x = (z - ∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j) * x := by
        intro x
        have := hz x
        rw [sumform D a ha, nsmul_odd _ hev] at this
        rw [sub_mul, ← this, add_sub_cancel_right]
      by_cases h0 : z - ∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j = 0
      · have i0 : Fin k := ⟨0, hk⟩
        have hr := rank_full (D i0.succ) (a i0) (hai.ne_zero i0)
          (fun x => by rw [ha, hD0, h0, zero_mul, zero_add])
        have h2 : Module.finrank (ZMod 2) (LinearMap.range (D i0.succ)) < k := hD i0.succ
        have hK' : Module.finrank (ZMod 2) K = k := hK
        omega
      · have hr := rank_full (D 0) _ h0 hD0
        have h2 : Module.finrank (ZMod 2) (LinearMap.range (D 0)) < k := hD 0
        have hK' : Module.finrank (ZMod 2) K = k := hK
        omega
    · intro hev
      exact ⟨∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j, fun x => by
        rw [sumform D a ha, nsmul_even _ hev, zero_add]⟩
    · obtain ⟨S, hS⟩ := hc z
      refine ⟨S, hS, fun S' hS' => ?_⟩
      apply sets_eq D hli
      ext x
      rw [LinearMap.sum_apply, LinearMap.sum_apply, hS, hS']
