import Mathlib
import PEqualNP.Defs

-- L-pcx-383. The helper blocks in the namespace PEqualNP.Outside.L_pcx_383_aux are copied
-- (comments removed) from upstream main: PEqualNP.ProofComplexity.L043, L049 and their helper
-- files, Helpers.BoolVanish, and PEqualNP.Outside.L_pcx_382 (Apache-2.0), with credit to
-- their authors. The new part is in the namespace PEqualNP.Outside.L_pcx_383.

open PEqualNP.ProofComplexity

-- inlined from PEqualNP.ProofComplexity.Helpers.ExpanderGraph (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open PEqualNP.Expanders

def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)

def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial

def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.ExpanderDet (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open PEqualNP.Expanders

theorem permGraph_leftDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.LeftDegLe (permGraph σ) b := by
  intro i
  have hsub : (permGraph σ i).map Fin.castSuccEmb ⊆ Finset.univ.image (fun k => σ k i) := by
    intro x hx
    simp only [Finset.mem_map, permGraph, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_castSuccEmb] at hx
    obtain ⟨j, ⟨k, hk⟩, rfl⟩ := hx
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
  calc (permGraph σ i).card = ((permGraph σ i).map Fin.castSuccEmb).card := (Finset.card_map _).symm
    _ ≤ (Finset.univ.image (fun k => σ k i)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp

theorem permGraph_rightDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.RightDegLe (permGraph σ) b := by
  intro j
  have hsub : rightNbrs (permGraph σ) j ⊆
      Finset.univ.image (fun k => (σ k).symm j.castSucc) := by
    intro i hi
    simp only [rightNbrs, permGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hk⟩ := hi
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [← hk]; simp⟩
  calc (rightNbrs (permGraph σ) j).card
      ≤ (Finset.univ.image (fun k => (σ k).symm j.castSucc)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp

theorem permGraph_trap {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1)))
    (hT : 5 * T.card ≤ n + 1)
    (hbad : (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card) :
    ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y := by
  set G := permGraph σ with hG
  set N := T.biUnion G with hN
  set U := uniqueNbrs G T with hU

  have he : ∑ i ∈ T, (G i).card = ∑ j ∈ N, (T.filter (fun i => j ∈ G i)).card := by
    have h1 : ∀ i ∈ T, (G i).card = ∑ j ∈ N, if j ∈ G i then 1 else 0 := by
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, hN, Finset.mem_biUnion]
      exact ⟨fun h => ⟨⟨i, hi, h⟩, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  have hle8 : ∑ i ∈ T, (G i).card ≤ 8 * T.card := by
    have := Finset.sum_le_card_nsmul T (fun i => (G i).card) 8
      (fun i _ => permGraph_leftDegLe σ i)
    simpa [mul_comm] using this
  have hpt : ∀ j ∈ N, 2 ≤ (T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0 := by
    intro j hj
    have hpos : 0 < (T.filter (fun i => j ∈ G i)).card := by
      rw [hN, Finset.mem_biUnion] at hj
      obtain ⟨i, hi, hji⟩ := hj
      exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hji⟩⟩
    by_cases h1 : (T.filter (fun i => j ∈ G i)).card = 1
    · have : j ∈ U := by
        simp only [hU, uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      simp [this, h1]
    · split_ifs <;> omega
  have hsum : 2 * N.card ≤ ∑ i ∈ T, (G i).card + U.card := by
    have h2 : ∑ j ∈ N, 2 ≤ ∑ j ∈ N,
        ((T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← he] at h2
    have h3 : (N.filter (fun j => j ∈ U)).card ≤ U.card :=
      Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hNc : N.card + 1 ≤ 5 * T.card := by omega
  set Y0 := N.map Fin.castSuccEmb ∪ {Fin.last n} with hY0
  have hY0c : Y0.card ≤ 5 * T.card := by
    calc Y0.card ≤ (N.map Fin.castSuccEmb).card + ({Fin.last n} : Finset _).card :=
          Finset.card_union_le _ _
      _ = N.card + 1 := by simp
      _ ≤ 5 * T.card := hNc
  obtain ⟨Y, hY0Y, hYc⟩ := Finset.exists_superset_card_eq hY0c (by simpa using hT)
  refine ⟨Y, hYc, fun k x hx => hY0Y ?_⟩
  induction h : σ k x using Fin.lastCases with
  | last => simp [hY0]
  | cast j =>
    have hj : j ∈ N := by
      rw [hN, Finset.mem_biUnion]
      refine ⟨x, hx, ?_⟩
      simp only [hG, permGraph, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, h⟩
    simp only [hY0, Finset.mem_union, Finset.mem_map, Fin.coe_castSuccEmb]
    exact Or.inl ⟨j, hj, rfl⟩

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.ExpanderPerm (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open Finset

theorem permCount : PermCountStmt := by
  intro α _ _ T Y
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y) with hS
  let f : Equiv.Perm α → (T → α) := fun σ x => σ x
  let t : Finset (T → α) :=
    Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ Y)
  have hmaps : ∀ σ ∈ S, f σ ∈ t := by
    intro σ hσ
    simp only [hS, mem_filter, mem_univ, true_and] at hσ
    simp only [t, mem_filter, mem_univ, true_and]
    refine ⟨?_, fun x => hσ x.1 x.2⟩
    intro a b hab
    exact Subtype.ext (σ.injective hab)

  have ht : #t ≤ Y.card.descFactorial T.card := by
    have hinj : Function.Injective
        (fun g : t => (⟨fun x => ⟨g.1 x, ((mem_filter.mp g.2).2.2 x)⟩,
          fun a b hab => (mem_filter.mp g.2).2.1 (congrArg Subtype.val hab)⟩ : T ↪ Y)) := by
      intro g h hgh
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq] at this
    simpa using this

  have hfib : ∀ g ∈ t, #{σ ∈ S | f σ = g} ≤ (Fintype.card α - T.card).factorial := by
    intro g _
    rcases Finset.eq_empty_or_nonempty {σ ∈ S | f σ = g} with h | ⟨σ₀, hσ₀⟩
    · rw [h]; simp
    have hσ₀g : f σ₀ = g := (mem_filter.mp hσ₀).2
    let P := {τ : Equiv.Perm α // ∀ a, ¬ (a ∉ T) → τ a = a}
    have hcardP : Fintype.card P = (Fintype.card α - T.card).factorial := by
      rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ T)),
        Fintype.card_perm]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    let F : {σ // σ ∈ ({σ ∈ S | f σ = g} : Finset _)} → P := fun σ =>
      ⟨σ₀⁻¹ * σ.1, by
        intro a ha
        have ha' : a ∈ T := not_not.mp ha
        have h1 : f σ.1 = g := (mem_filter.mp σ.2).2
        have h2 : σ.1 a = σ₀ a := by
          have e := congrFun (h1.trans hσ₀g.symm) ⟨a, ha'⟩
          simpa [f] using e
        simp [Equiv.Perm.mul_apply, h2]⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [F] using this
    have := Fintype.card_le_of_injective F hF
    rw [hcardP, Fintype.card_coe] at this
    exact this
  have := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  calc #S ≤ (Fintype.card α - T.card).factorial * #t := this
    _ ≤ (Fintype.card α - T.card).factorial * Y.card.descFactorial T.card :=
        Nat.mul_le_mul_left _ ht
    _ = _ := Nat.mul_comm _ _

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.ExpanderArith (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open Finset

lemma arith_choose_le (N r : ℕ) (hr : 0 < r) : (N.choose r : ℝ) ≤ (3 * N / r) ^ r := by
  have h1 : (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r N
  have h2 : (r : ℝ) ^ r / r.factorial ≤ Real.exp r :=
    Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r
  have h3 : Real.exp r ≤ 3 ^ r := by
    have : Real.exp (r : ℝ) = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul]; simp
    rw [this]
    gcongr
    linarith [Real.exp_one_lt_d9]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hrr : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  calc (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := h1
    _ = (N : ℝ) ^ r / (r : ℝ) ^ r * ((r : ℝ) ^ r / r.factorial) := by field_simp
    _ ≤ (N : ℝ) ^ r / (r : ℝ) ^ r * 3 ^ r := by gcongr; exact h2.trans h3
    _ = (3 * N / r) ^ r := by rw [div_pow, mul_pow]; ring

lemma arith_ratio_le (N t : ℕ) (ht : 1 ≤ t) (hN : 2 * t ≤ N) :
    ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ) ≤ (10 * t / N) ^ t := by
  have hnum : ((5 * t).descFactorial t : ℝ) ≤ ((5 * t : ℕ) : ℝ) ^ t := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hden0 : ((N + 1 - t : ℕ) : ℝ) ^ t ≤ (N.descFactorial t : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N t
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsub : (N : ℝ) / 2 ≤ ((N + 1 - t : ℕ) : ℝ) := by
    have hle : t ≤ N + 1 := by omega
    rw [Nat.cast_sub hle]
    have : (2 * t : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  have hden : ((N : ℝ) / 2) ^ t ≤ (N.descFactorial t : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hsub t).trans hden0
  calc ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ)
      ≤ ((5 * t : ℕ) : ℝ) ^ t / ((N : ℝ) / 2) ^ t :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (10 * t / N) ^ t := by
        rw [← div_pow]
        congr 1
        push_cast
        field_simp
        ring

lemma arith_term_le (n t : ℕ) (ht : 1 ≤ t) (hts : t * 100000 ≤ n) :
    ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 ≤
      (1 / 4 : ℝ) ^ t := by
  have htpos : (0 : ℝ) < t := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hN : ((n + 1 : ℕ) : ℝ) ≥ 100000 * t := by
    have : t * 100000 ≤ n + 1 := by omega
    have h : ((t * 100000 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h ⊢
    linarith
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 := arith_choose_le (n + 1) t (by omega)
  have h2 := arith_choose_le (n + 1) (5 * t) (by omega)
  have h3 := arith_ratio_le (n + 1) t ht (by omega)
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hratio0 : (0 : ℝ) ≤ ((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ) := by
    positivity
  have h5 : ((5 * t : ℕ) : ℝ) = 5 * (t : ℝ) := by push_cast; ring
  rw [h5] at h2
  have hbase : (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 = 23328000 * t ^ 2 / N ^ 2 := by
    field_simp
    ring
  have hq : (23328000 : ℝ) * t ^ 2 / N ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq0 : (0 : ℝ) ≤ (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 := by positivity
  calc ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ (3 * N / t) ^ t * (3 * N / (5 * t)) ^ (5 * t) * ((10 * t / N) ^ t) ^ 8 := by
        gcongr
    _ = ((3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8) ^ t := by
        rw [pow_mul (3 * N / (5 * t)) 5 t, ← pow_mul (10 * t / N) t 8, mul_comm t 8,
          pow_mul (10 * t / N) 8 t, mul_pow, mul_pow]
    _ ≤ (1 / 4 : ℝ) ^ t := by
        rw [hbase] at hq0 ⊢
        exact pow_le_pow_left₀ hq0 hq t

theorem arith : ArithStmt := by
  refine ⟨100000, 0, by norm_num, fun n _ => ?_⟩
  calc ∑ t ∈ Finset.Icc 1 (n / 100000),
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ ∑ t ∈ Finset.Icc 1 (n / 100000), (1 / 4 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Icc] at ht
        exact arith_term_le n t ht.1 ((Nat.le_div_iff_mul_le (by norm_num)).1 ht.2)
    _ = ∑ t ∈ Finset.Ico 1 (n / 100000 + 1), (1 / 4 : ℝ) ^ t := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (1 / 4 : ℝ) ^ 1 / (1 - 1 / 4) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ < 1 := by norm_num

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.ExpanderAssembly (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open PEqualNP.Expanders

theorem expander_of_parts (hP : PermCountStmt) (hA : ArithStmt)
    (hL : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.LeftDegLe (permGraph σ) b)
    (hR : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.RightDegLe (permGraph σ) b)
    (hT : ∀ {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1))),
      5 * T.card ≤ n + 1 →
      (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card →
      ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y) :
    ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
        PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧
        PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 := by
  classical
  obtain ⟨s₀, n₀, h5, hsum⟩ := hA
  refine ⟨8, s₀, n₀, by omega, ?_⟩
  intro n hn
  have hs1 := hsum n hn
  have hsn : 5 * (n / s₀) ≤ n := by
    have h1 := Nat.div_mul_le_self n s₀
    have h2 : 5 * (n / s₀) ≤ n / s₀ * s₀ := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left (n / s₀) h5
    omega
  set s := n / s₀ with hs
  suffices h : ∃ σ : Fin 8 → Equiv.Perm (Fin (n + 1)), IsBdryExpander (permGraph σ) s 2 by
    obtain ⟨σ, hσ⟩ := h
    exact ⟨permGraph σ, hL σ, hR σ, hσ⟩
  by_contra hno
  push Not at hno

  let A : Finset (Fin (n + 1)) → Finset (Fin (n + 1)) → Finset (Equiv.Perm (Fin (n + 1))) :=
    fun T Y => Finset.univ.filter (fun τ => ∀ x ∈ T, τ x ∈ Y)
  let U : Finset (Fin 8 → Equiv.Perm (Fin (n + 1))) :=
    (Finset.Icc 1 s).biUnion (fun t =>
      (Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun T =>
        (Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun Y =>
          Fintype.piFinset (fun _ : Fin 8 => A T Y))))
  have hsub : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))) ⊆ U := by
    intro σ _
    have hbad := hno σ
    unfold IsBdryExpander at hbad
    push Not at hbad
    obtain ⟨T, hTs, hTlt⟩ := hbad
    have ht1 : 1 ≤ T.card := by
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · rw [h0] at hTlt; omega
      · exact h0
    obtain ⟨Y, hYc, hY⟩ := hT σ T (by omega) hTlt
    simp only [U, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard,
      Fintype.mem_piFinset]
    refine ⟨T.card, ⟨ht1, hTs⟩, T, ⟨Finset.subset_univ _, rfl⟩, Y,
      ⟨Finset.subset_univ _, hYc⟩, ?_⟩
    intro k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun x hx => hY k x hx
  have hAcard : ∀ t, ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
      ∀ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
      (A T Y).card ≤ (5 * t).descFactorial t * (n + 1 - t).factorial := by
    intro t T hT' Y hY'
    rw [Finset.mem_powersetCard] at hT' hY'
    have h := hP (Fin (n + 1)) T Y
    rw [hT'.2, hY'.2, Fintype.card_fin] at h
    convert h
  have hUcard : U.card ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t * ((n + 1).choose (5 * t) *
      ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => ?_)
    refine (Finset.card_biUnion_le).trans ?_
    calc _ ≤ ∑ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
          (n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
          apply Finset.sum_le_sum
          intro T hT'
          refine (Finset.card_biUnion_le).trans ?_
          calc _ ≤ ∑ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
                ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
                apply Finset.sum_le_sum
                intro Y hY'
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                exact Nat.pow_le_pow_left (hAcard t T hT' Y hY') 8
            _ = _ := by
                rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  have hcardΩ : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))).card =
      ((n + 1).factorial) ^ 8 := by
    rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  have hle : ((n + 1).factorial) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t *
      ((n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) :=
    hcardΩ ▸ (Finset.card_le_card hsub).trans hUcard
  have hleR : (((n + 1).factorial : ℕ) : ℝ) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) := by
    exact_mod_cast hle
  have hid : ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) =
      (((n + 1).factorial : ℕ) : ℝ) ^ 8 * ∑ t ∈ Finset.Icc 1 s,
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have htn : t ≤ n + 1 := by omega
    have hEF : ((n + 1 - t).factorial : ℝ) * ((n + 1).descFactorial t : ℝ) =
        (((n + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial htn
    have hE : ((n + 1).descFactorial t : ℝ) ≠ 0 := by
      have : (n + 1).descFactorial t ≠ 0 := by
        rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
      exact_mod_cast this
    rw [← hEF]
    field_simp
  have hpos : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) ^ 8 := by
    have := Nat.factorial_pos (n + 1)
    positivity
  have hlt := mul_lt_mul_of_pos_left hs1 hpos
  rw [hid] at hleR
  linarith

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.L043 (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux
theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

end PEqualNP.Outside.L_pcx_383_aux

-- inlined from PEqualNP.ProofComplexity.Helpers.PCToolkit (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial

variable {σ τ : Type}

theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this

theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)

theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this

theorem bitPHPSystem_injective {m l : ℕ} (a : Fin m × Fin l → ZMod 2)
    (ha : ∀ f ∈ bitPHPSystem m l, eval a f = 0) :
    Function.Injective (fun (i : Fin m) (t : Fin l) => a (i, t)) := by
  intro i i' hii
  by_contra hne
  have h := ha _ (Or.inr ⟨i, i', hne, rfl⟩)
  rw [map_prod] at h
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h
  have hEq : a (i, t) = a (i', t) := congrFun hii t
  simp only [map_add, map_one, eval_X, hEq] at ht
  generalize a (i', t) = c at ht
  revert ht; revert c; decide

theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.PseudoReduction (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial

theorem not_pcRefutable_of_pseudoReduction {σ : Type}
    {F : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (R : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2))
    (hax : ∀ f ∈ F, f.totalDegree ≤ D → R f = 0)
    (hmul : ∀ (v : σ) (a : σ →₀ ℕ), a.degree + 1 ≤ D →
      R (X v * monomial a 1) = R (X v * R (monomial a 1)))
    (hone : R 1 ≠ 0) :
    ¬ PCRefutable F D := by

  have hsum : ∀ (v : σ) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ a ∈ s, a.degree + 1 ≤ D) →
      R (X v * ∑ a ∈ s, c a • monomial a 1) =
        R (X v * R (∑ a ∈ s, c a • monomial a 1)) := by
    intro v s c hs
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul]
    exact Finset.sum_congr rfl fun a ha => by rw [hmul v a (hs a ha)]
  have key : ∀ {p : MvPolynomial σ (ZMod 2)}, PCDerivable F D p → R p = 0 := by
    intro p h
    induction h with
    | ax hp hdeg => exact hax _ hp hdeg
    | zero => exact map_zero R
    | add _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
    | @mulX j p _ hdeg ih =>
      by_cases hp0 : p = 0
      · rw [hp0, mul_zero, map_zero]
      · have hdeg' : p.totalDegree + 1 ≤ D := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X] at hdeg
          omega
        have hp : p = ∑ a ∈ p.support, p.coeff a • monomial a (1 : ZMod 2) := by
          conv_lhs => rw [p.as_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
        have hs : ∀ a ∈ p.support, a.degree + 1 ≤ D := by
          intro a ha
          have h1 : a.degree ≤ p.totalDegree := le_totalDegree ha
          omega
        have h2 := hsum j p.support (fun a => p.coeff a) hs
        rw [← hp, ih, mul_zero, map_zero] at h2
        exact h2
  intro href
  exact hone (key href)

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.MomentReduction (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial

section Static

variable {σ : Type}

noncomputable def staticSpan (F : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2)
    {q | ∃ (a : σ →₀ ℕ) (f : MvPolynomial σ (ZMod 2)),
      f ∈ F ∧ (monomial a 1 * f).totalDegree ≤ k ∧ q = monomial a 1 * f}

theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]

theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

theorem X_mul_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} (j : σ)
    {g : MvPolynomial σ (ZMod 2)} (hg : g ∈ staticSpan F k) :
    X j * g ∈ staticSpan F (k + 1) := by
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    have heq : X j * (monomial a 1 * f) =
        monomial (a + Finsupp.single j 1) (1 : ZMod 2) * f := by
      rw [← monomial_one_mul_X]
      ring
    refine Submodule.subset_span ⟨a + Finsupp.single j 1, f, hf, ?_, heq⟩
    rw [← heq]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem pcDerivable_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) : p ∈ staticSpan F B := by
  induction h with
  | @ax p hp hdeg =>
    exact Submodule.subset_span ⟨0, p, hp, by simpa using hdeg, by simp⟩
  | zero => exact Submodule.zero_mem _
  | add _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simp
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    exact X_mul_mem_staticSpan j (hint k (Nat.lt_succ_self k) p ih (by omega))

theorem one_mem_staticSpan_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    (h : (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F B) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F 0 := by
  induction B with
  | zero => exact h
  | succ k ih =>
    exact ih (fun k' hk' => hint k' (by omega)) (hint k (by omega) 1 h (by simp))

theorem dual_eq_of_monomial_eq {k : ℕ}
    (f g : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h : ∀ a : σ →₀ ℕ, a.degree ≤ k → f (monomial a 1) = g (monomial a 1))
    (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ k) : f p = g p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hm : monomial a (p.coeff a) = p.coeff a • monomial a (1 : ZMod 2) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, h a ((le_totalDegree ha).trans hp)]

theorem support_add_single_one [DecidableEq σ] (a : σ →₀ ℕ) (v : σ) :
    (a + Finsupp.single v 1).support = insert v a.support := by
  ext u
  by_cases h : v = u
  · subst h
    simp
  · simp [Ne.symm h]

theorem card_support_le_degree (a : σ →₀ ℕ) : a.support.card ≤ a.degree := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)

end Static

section Matching

variable {m N : ℕ}

def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b

def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)

def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T

theorem isPartialMatching_empty : IsPartialMatching (∅ : Finset (Fin m × Fin N)) := by
  intro a ha
  simp at ha

theorem IsPartialMatching.mono {S T : Finset (Fin m × Fin N)} (hT : IsPartialMatching T)
    (hST : S ⊆ T) : IsPartialMatching S :=
  fun a ha b hb h => hT a (hST ha) b (hST hb) h

theorem isPartialMatching_insert_iff {S : Finset (Fin m × Fin N)} (hS : IsPartialMatching S)
    {i : Fin m} (hrow : ∀ a ∈ S, a.1 ≠ i) (j : Fin N) :
    IsPartialMatching (insert (i, j) S) ↔ ∀ a ∈ S, a.2 ≠ j := by
  constructor
  · intro h a ha haj
    have := h a (Finset.mem_insert_of_mem ha) (i, j) (Finset.mem_insert_self _ _) (Or.inr haj)
    exact hrow a ha (by rw [this])
  · intro hcol a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
    · rfl
    · rcases hab with h | h
      · exact absurd h.symm (hrow b hb')
      · exact absurd h.symm (hcol b hb')
    · rcases hab with h | h
      · exact absurd h (hrow a ha')
      · exact absurd h (hcol a ha')
    · exact hS a ha' b hb' hab

theorem not_isPartialMatching_insert {S : Finset (Fin m × Fin N)} {i : Fin m} {j j0 : Fin N}
    (h0 : (i, j0) ∈ S) (hj : j ≠ j0) : ¬ IsPartialMatching (insert (i, j) S) := by
  intro h
  have := h (i, j) (Finset.mem_insert_self _ _) (i, j0) (Finset.mem_insert_of_mem h0)
    (Or.inl rfl)
  exact hj (congrArg Prod.snd this)

open Classical in

noncomputable def momentWeight (z : Finset (Fin m × Fin N) → ZMod 2)
    (S : Finset (Fin m × Fin N)) : ZMod 2 :=
  if IsPartialMatching S then z S else 0

theorem momentWeight_of_not {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : ¬ IsPartialMatching S) : momentWeight z S = 0 :=
  ite_eq_right h

theorem momentWeight_of_matching {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : IsPartialMatching S) : momentWeight z S = z S :=
  ite_eq_left h

theorem momentWeight_row_sum {z : Finset (Fin m × Fin N) → ZMod 2} {k : ℕ}
    (hz : MomentConsistent m N k z) (S : Finset (Fin m × Fin N))
    (hS : IsPartialMatching S → S.card < k) (i : Fin m) :
    ∑ j : Fin N, momentWeight z (insert (i, j) S) = momentWeight z S := by
  by_cases hM : IsPartialMatching S
  · by_cases hrow : ∀ a ∈ S, a.1 ≠ i
    · rw [momentWeight_of_matching hM, hz S hM (hS hM) i hrow, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : ∀ a ∈ S, a.2 ≠ j
      · rw [ite_eq_left hc,
          momentWeight_of_matching ((isPartialMatching_insert_iff hM hrow j).mpr hc)]
      · rw [ite_eq_right hc, momentWeight_of_not
          (fun h => hc ((isPartialMatching_insert_iff hM hrow j).mp h))]
    · push Not at hrow
      obtain ⟨⟨i', j0⟩, ha, hi⟩ := hrow
      simp only at hi
      subst hi
      rw [Finset.sum_eq_single j0]
      · rw [Finset.insert_eq_of_mem ha]
      · intro j _ hj
        exact momentWeight_of_not (not_isPartialMatching_insert ha hj)
      · intro h
        exact absurd (Finset.mem_univ _) h
  · rw [momentWeight_of_not hM]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact momentWeight_of_not fun h => hM (h.mono (Finset.subset_insert _ _))

noncomputable def momentFunctional (z : Finset (Fin m × Fin N) → ZMod 2) :
    MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (basisMonomials (Fin m × Fin N) (ZMod 2)).constr (ZMod 2)
    fun a => momentWeight z a.support

theorem momentFunctional_monomial (z : Finset (Fin m × Fin N) → ZMod 2)
    (a : Fin m × Fin N →₀ ℕ) :
    momentFunctional z (monomial a 1) = momentWeight z a.support := by
  have h := (basisMonomials (Fin m × Fin N) (ZMod 2)).constr_basis (ZMod 2)
    (fun a => momentWeight z a.support) a
  rw [coe_basisMonomials] at h
  exact h

theorem rowAxiom_totalDegree_le (i : Fin m) :
    ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [totalDegree_X]

theorem one_le_rowAxiom_totalDegree (hN : 1 ≤ N) (i : Fin m) :
    1 ≤ ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree := by
  by_contra hlt
  have h0 : ((∑ j : Fin N, X (i, j)) + 1 :
      MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have e0 := congrArg (eval (fun _ : Fin m × Fin N => (0 : ZMod 2))) h0
  have e1 := congrArg
    (eval (fun v : Fin m × Fin N => if v = (i, (⟨0, hN⟩ : Fin N)) then (1 : ZMod 2) else 0)) h0
  simp only [map_add, map_sum, eval_X, map_one, eval_C, Finset.sum_const_zero, zero_add] at e0 e1
  rw [← e0] at e1
  simp [Prod.mk.injEq] at e1

theorem monomial_one_mul_rowAxiom (a : Fin m × Fin N →₀ ℕ) (i : Fin m) :
    monomial a (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) =
      (∑ j : Fin N, monomial (a + Finsupp.single (i, j) 1) 1) + monomial a 1 := by
  rw [mul_add, mul_one, Finset.mul_sum]
  simp only [monomial_one_mul_X]

theorem momentFunctional_staticSpan (hN : 1 ≤ N) {z : Finset (Fin m × Fin N) → ZMod 2}
    {k : ℕ} (hz : MomentConsistent m N k z) {p : MvPolynomial (Fin m × Fin N) (ZMod 2)}
    (hp : p ∈ staticSpan (funPHPSystem m N) k) : momentFunctional z p = 0 := by
  induction hp using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    rcases hf with ⟨v, rfl⟩ | ⟨i, j, j', hne, rfl⟩ | ⟨i, i', j, hne, rfl⟩ | ⟨i, rfl⟩
    · rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, map_add,
        momentFunctional_monomial, momentFunctional_monomial, support_add_single_one,
        support_add_single_one, Finset.insert_idem v a.support]
      exact CharTwo.add_self_eq_zero _
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i, j')
        (Finset.mem_insert_self _ _) (Or.inl rfl)
      exact congrArg Prod.snd this
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i', j)
        (Finset.mem_insert_self _ _) (Or.inr rfl)
      exact congrArg Prod.fst this
    · have hrow := one_le_rowAxiom_totalDegree (m := m) hN i
      have hne0 :
          ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) ≠ 0 := by
        intro h0
        rw [h0, totalDegree_zero] at hrow
        omega
      have hmon : monomial a (1 : ZMod 2) ≠ 0 := by
        rw [Ne, monomial_eq_zero]
        exact one_ne_zero
      rw [totalDegree_mul_of_isDomain hmon hne0, totalDegree_monomial_one] at hdeg
      have hcard := card_support_le_degree a
      rw [monomial_one_mul_rowAxiom, map_add, map_sum, momentFunctional_monomial]
      simp only [momentFunctional_monomial, support_add_single_one]
      rw [momentWeight_row_sum hz a.support (fun _ => by omega) i]
      exact CharTwo.add_self_eq_zero _

noncomputable def indMon (T : Finset (Fin m × Fin N)) : Fin m × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v ∈ T then 1 else 0

theorem indMon_apply (T : Finset (Fin m × Fin N)) (v : Fin m × Fin N) :
    indMon T v = if v ∈ T then 1 else 0 := rfl

theorem indMon_support (T : Finset (Fin m × Fin N)) : (indMon T).support = T := by
  ext v
  simp [indMon_apply]

theorem indMon_degree (T : Finset (Fin m × Fin N)) : (indMon T).degree = T.card := by
  rw [Finsupp.degree_eq_sum]
  simp [indMon_apply]

theorem indMon_insert {T : Finset (Fin m × Fin N)} {v : Fin m × Fin N} (hv : v ∉ T) :
    indMon (insert v T) = indMon T + Finsupp.single v 1 := by
  ext u
  by_cases h : u = v
  · subst h
    simp [indMon_apply, hv]
  · simp [indMon_apply, h]

theorem eq_indMon_support {a : Fin m × Fin N →₀ ℕ} (h : ∀ v, a v ≤ 1) :
    a = indMon a.support := by
  ext v
  have := h v
  by_cases h0 : a v = 0
  · simp [indMon_apply, h0]
  · simp [indMon_apply, h0]
    omega

theorem dual_monomial_eq_indMon {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    ∀ (n : ℕ) (a : Fin m × Fin N →₀ ℕ), a.degree = n → a.degree ≤ k →
      φ (monomial a 1) = φ (monomial (indMon a.support) 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a han hak
    by_cases h : ∀ v, a v ≤ 1
    · rw [← eq_indMon_support h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    have hle : Finsupp.single v 2 ≤ a := by
      intro u
      by_cases huv : v = u
      · subst huv
        rw [Finsupp.single_eq_same]
        omega
      · simp [huv]
    obtain ⟨b, hb⟩ : ∃ b, a = b + Finsupp.single v 2 :=
      ⟨a - Finsupp.single v 2, (tsub_add_cancel_of_le hle).symm⟩
    set c := b + Finsupp.single v 1 with hc
    have hac : a = c + Finsupp.single v 1 := by
      rw [hb, hc, add_assoc, ← Finsupp.single_add]
    have hdeg : a.degree = c.degree + 1 := by
      rw [hac, map_add, Finsupp.degree_single]
    have hq : monomial b (1 : ZMod 2) * (X v * X v + X v) = monomial a 1 + monomial c 1 := by
      rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, ← hc, ← hac]
    have hmem : monomial a (1 : ZMod 2) + monomial c 1 ∈ staticSpan (funPHPSystem m N) k := by
      refine Submodule.subset_span ⟨b, _, Or.inl ⟨v, rfl⟩, ?_, hq.symm⟩
      rw [hq]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_monomial_one]
        exact hak
      · rw [totalDegree_monomial_one]
        omega
    have h0 := hφ _ hmem
    rw [map_add, CharTwo.add_eq_zero] at h0
    have hsupp : a.support = c.support := by
      rw [hac, support_add_single_one, Finset.insert_eq_of_mem]
      rw [Finsupp.mem_support_iff, hc]
      simp
    rw [h0, hsupp]
    exact ih c.degree (by omega) c rfl (by omega)

theorem dual_monomial_eq_zero {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (a : Fin m × Fin N →₀ ℕ) (hak : a.degree ≤ k) (hM : ¬ IsPartialMatching a.support) :
    φ (monomial a 1) = 0 := by
  unfold IsPartialMatching at hM
  push Not at hM
  obtain ⟨u, hu, v, hv, huv, hne⟩ := hM
  have hle : Finsupp.single u 1 + Finsupp.single v 1 ≤ a := by
    intro w
    have h1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
    have h2 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    by_cases hwu : u = w
    · subst hwu
      simpa [Finsupp.single_apply, Ne.symm hne] using h1
    · by_cases hwv : v = w
      · subst hwv
        simpa [Finsupp.single_apply, hne] using h2
      · simp [hwu, hwv]
  obtain ⟨b, hb⟩ : ∃ b, a = b + (Finsupp.single u 1 + Finsupp.single v 1) :=
    ⟨a - (Finsupp.single u 1 + Finsupp.single v 1), (tsub_add_cancel_of_le hle).symm⟩
  have hq : monomial b (1 : ZMod 2) * (X u * X v) = monomial a 1 := by
    rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, hb, add_assoc]
  have hF : (X u * X v : MvPolynomial (Fin m × Fin N) (ZMod 2)) ∈ funPHPSystem m N := by
    obtain ⟨i, j⟩ := u
    obtain ⟨i', j'⟩ := v
    rcases huv with h | h
    · simp only at h
      subst h
      exact Or.inr (Or.inl ⟨i, j, j', fun h => hne (by rw [h]), rfl⟩)
    · simp only at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨i, i', j, fun h => hne (by rw [h]), rfl⟩))
  refine hφ _ (Submodule.subset_span ⟨b, _, hF, ?_, hq.symm⟩)
  rw [hq, totalDegree_monomial_one]
  exact hak

theorem momentConsistent_of_dual {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    MomentConsistent m N k fun T => φ (monomial (indMon T) 1) := by
  intro T hT hcard i hrow
  have hnot : ∀ j : Fin N, (i, j) ∉ T := fun j hj => hrow _ hj rfl
  have hmem : monomial (indMon T) (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) ∈
      staticSpan (funPHPSystem m N) k := by
    refine Submodule.subset_span ⟨indMon T, _, Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)), ?_, rfl⟩
    refine (totalDegree_mul _ _).trans ?_
    have h1 := rowAxiom_totalDegree_le (N := N) i
    rw [totalDegree_monomial_one, indMon_degree]
    omega
  have h0 := hφ _ hmem
  rw [monomial_one_mul_rowAxiom, map_add, CharTwo.add_eq_zero, map_sum] at h0
  show φ (monomial (indMon T) 1) = _
  rw [← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← indMon_insert (hnot j)]
  by_cases hc : ∀ a ∈ T, a.2 ≠ j
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    refine dual_monomial_eq_zero hφ _ ?_ ?_
    · rw [indMon_degree, Finset.card_insert_of_notMem (hnot j)]
      omega
    · rw [indMon_support]
      exact fun h => hc ((isPartialMatching_insert_iff hT hrow j).mp h)

theorem dual_eq_momentFunctional {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2)) (hp : p.totalDegree ≤ k) :
    φ p = momentFunctional (fun T => φ (monomial (indMon T) 1)) p := by
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hp
  rw [momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM]
    exact dual_monomial_eq_indMon hφ _ a rfl ha
  · rw [momentWeight_of_not hM]
    exact dual_monomial_eq_zero hφ a ha hM

theorem staticSpan_funPHP_inter (hN : 1 ≤ N) {k : ℕ} (hext : MomentExt m N k)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2))
    (hp : p ∈ staticSpan (funPHPSystem m N) (k + 1)) (hdeg : p.totalDegree ≤ k) :
    p ∈ staticSpan (funPHPSystem m N) k := by
  by_contra hnot
  obtain ⟨φ, hφp, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0 := by
    intro q hq
    have : φ q ∈ (staticSpan (funPHPSystem m N) k).map φ := Submodule.mem_map_of_mem hq
    rw [hmap] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨z', hz', hagree⟩ := hext _ (momentConsistent_of_dual hφ)
  apply hφp
  rw [dual_eq_momentFunctional hφ p hdeg, ← momentFunctional_staticSpan hN hz' hp]
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hdeg
  rw [momentFunctional_monomial, momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM, momentWeight_of_matching hM]
    exact (hagree _ hM ((card_support_le_degree a).trans ha)).symm
  · rw [momentWeight_of_not hM, momentWeight_of_not hM]

theorem no_pc_refutation_of_momentExt :
    ∀ m N B : ℕ, 1 ≤ N → (∀ k < B, MomentExt m N k) →
      ¬ PCRefutable (funPHPSystem m N) B := by
  intro m N B hN hext href
  have hint : ∀ k < B, ∀ p, p ∈ staticSpan (funPHPSystem m N) (k + 1) → p.totalDegree ≤ k →
      p ∈ staticSpan (funPHPSystem m N) k :=
    fun k hk p => staticSpan_funPHP_inter hN (hext k hk) p
  have h0 := one_mem_staticSpan_zero hint (pcDerivable_mem_staticSpan hint href)
  have hz : MomentConsistent m N 0 fun _ => 1 := by
    intro T _ hcard
    omega
  have hval := momentFunctional_staticSpan hN hz h0
  have h1 : (1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) = monomial 0 1 := rfl
  rw [h1, momentFunctional_monomial, Finsupp.support_zero,
    momentWeight_of_matching isPartialMatching_empty] at hval
  exact one_ne_zero hval

theorem momentExt_zero (m N : ℕ) (hN : 1 ≤ N) : MomentExt m N 0 := by
  intro z _
  refine ⟨fun T => if T = ∅ then z ∅ else
    if ∃ i : Fin m, T = {(i, (⟨0, hN⟩ : Fin N))} then z ∅ else 0, ?_, ?_⟩
  · intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      ite_true, insert_empty_eq, Finset.singleton_ne_empty, ite_false]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [ite_eq_left ⟨i, rfl⟩]
    · intro j _ hj
      refine ite_eq_right ?_
      rintro ⟨i', h⟩
      rw [Finset.singleton_inj] at h
      exact hj (congrArg Prod.snd h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro T _ hcard
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp

theorem not_momentExt_zero_of_no_holes (m : ℕ) (hm : 1 ≤ m) : ¬ MomentExt m 0 0 := by
  intro h
  obtain ⟨z', hz', hagree⟩ := h (fun _ => 1) (fun T _ hcard => by omega)
  have h1 := hz' ∅ isPartialMatching_empty (by simp) ⟨0, hm⟩ (by simp)
  rw [hagree ∅ isPartialMatching_empty (by simp)] at h1
  simp at h1

theorem not_momentExt_two_one_one : ¬ MomentExt 2 1 1 := by
  intro h
  have hz : MomentConsistent 2 1 1 fun _ => 1 := by
    intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp
  obtain ⟨z', hz', hagree⟩ := h _ hz
  have hM : IsPartialMatching ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)) := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  have h1 := hz' {((0 : Fin 2), (0 : Fin 1))} hM (by simp) 1 (by simp)
  rw [hagree _ hM (by simp)] at h1
  have hempty : (Finset.univ.filter fun j : Fin 1 =>
      ∀ a ∈ ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)), a.2 ≠ j) = ∅ := by
    decide
  rw [hempty, Finset.sum_empty] at h1
  exact one_ne_zero h1

end Matching

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.EchelonNF (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial

variable {σ : Type} [Countable σ]

noncomputable def monoKey (a : σ →₀ ℕ) : ℕ ×ₗ ℕ :=
  toLex (a.degree, Classical.choose (Countable.exists_injective_nat (σ →₀ ℕ)) a)

def MonoLt (b a : σ →₀ ℕ) : Prop := monoKey b < monoKey a

theorem monoKey_injective : Function.Injective (monoKey (σ := σ)) := by
  intro a b h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [monoKey, ofLex_toLex] at h2
  exact Classical.choose_spec (Countable.exists_injective_nat (σ →₀ ℕ)) h2

theorem monoLt_of_degree_lt {a b : σ →₀ ℕ} (h : b.degree < a.degree) : MonoLt b a := by
  unfold MonoLt monoKey
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

theorem degree_le_of_monoLt {a b : σ →₀ ℕ} (h : MonoLt b a) : b.degree ≤ a.degree := by
  unfold MonoLt monoKey at h
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem monoLt_wellFounded : WellFounded (MonoLt (σ := σ)) :=
  InvImage.wf monoKey wellFounded_lt

theorem monoLt_trans {a b c : σ →₀ ℕ} (h1 : MonoLt a b) (h2 : MonoLt b c) : MonoLt a c :=
  lt_trans (α := ℕ ×ₗ ℕ) h1 h2

def IsStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (a : σ →₀ ℕ) : Prop :=
  monomial a (1 : ZMod 2) ∉ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a}

noncomputable def echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {a | IsStd U a}

omit [Countable σ] in
theorem echelon_restrictSupport_le {s : Set (σ →₀ ℕ)}
    {P : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    (h : ∀ b ∈ s, monomial b (1 : ZMod 2) ∈ P) : restrictSupport (ZMod 2) s ≤ P := by
  rw [restrictSupport_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

theorem echelon_disjoint (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Disjoint (echelonStd U) U := by
  classical
  rw [Submodule.disjoint_def]
  intro h hS hU
  by_contra hne
  have hsupp : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image h.support monoKey hsupp
  have hstd : IsStd U a := ((mem_restrictSupport_iff (R := ZMod 2)).1 hS) ha
  apply hstd
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hc : h.coeff a = 1 := key _ (mem_support_iff.1 ha)
  have hw : h - monomial a 1 ∈ restrictSupport (ZMod 2) {b | MonoLt b a} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    have hb' : (h - monomial a 1).coeff b ≠ 0 := mem_support_iff.1 hb
    rw [coeff_sub, coeff_monomial] at hb'
    by_cases hab : a = b
    · subst hab
      simp [hc] at hb'
    · rw [if_neg hab, sub_zero] at hb'
      have hbS : b ∈ h.support := mem_support_iff.2 hb'
      exact lt_of_le_of_ne (hmax b hbS) (fun e => hab (monoKey_injective e).symm)
  have heq : monomial a (1 : ZMod 2) = h - (h - monomial a 1) := (sub_sub_cancel _ _).symm
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hU) (Submodule.mem_sup_right hw)

theorem echelon_monomial_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) :
    monomial a (1 : ZMod 2) ∈
      U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
  induction a using (monoLt_wellFounded (σ := σ)).induction
  rename_i a ih
  by_cases hs : IsStd U a
  · apply Submodule.mem_sup_right
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl hs)
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  · have hmem : monomial a (1 : ZMod 2) ∈ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} :=
      Classical.byContradiction fun h => hs h
    have hle : U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} ≤
        U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
      refine sup_le le_sup_left ?_
      refine echelon_restrictSupport_le ?_
      intro b hb
      refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
        (ih b hb)
      intro c hc
      rcases hc with rfl | hc
      · exact Or.inr hb
      · exact Or.inr (monoLt_trans hc hb)
    exact hle hmem

theorem echelon_le_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s) :
    restrictSupport (ZMod 2) s ≤ U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) s) := by
  refine echelon_restrictSupport_le ?_
  intro a ha
  refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
    (echelon_monomial_mem U a)
  intro b hb
  rcases hb with hb | hb
  · rw [hb]; exact ha
  · exact hs a ha b hb

theorem echelon_isCompl (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    IsCompl (echelonStd U) U := by
  refine ⟨echelon_disjoint U, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro f _
  have hf : f ∈ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ)) := by
    rw [mem_restrictSupport_iff]
    exact Set.subset_univ _
  have h := echelon_le_of_downClosed U (s := Set.univ) (fun _ _ _ _ => trivial) hf
  have hle : U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ))) ≤
      echelonStd U ⊔ U :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  exact hle h

noncomputable def nf (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Submodule.projection (echelonStd U) U (echelon_isCompl U)

theorem nf_mem_echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f ∈ echelonStd U :=
  Submodule.projection_apply_mem (echelon_isCompl U) f

theorem nf_sub_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : f - nf U f ∈ U :=
  Submodule.sub_projection_mem (echelon_isCompl U) f

theorem nf_support_isStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : ∀ a ∈ (nf U f).support, IsStd U a :=
  fun _ ha => ((mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_echelonStd U f)) ha

theorem nf_unique (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {f g : MvPolynomial σ (ZMod 2)} (hg : ∀ a ∈ g.support, IsStd U a) (hfg : f - g ∈ U) :
    nf U f = g := by
  have hgS : g ∈ echelonStd U := (mem_restrictSupport_iff (R := ZMod 2)).2 fun a ha => hg a ha
  have h1 : nf U f - g ∈ echelonStd U := Submodule.sub_mem _ (nf_mem_echelonStd U f) hgS
  have h2 : nf U f - g ∈ U := by
    have h3 := Submodule.sub_mem _ hfg (nf_sub_mem U f)
    rwa [sub_sub_sub_cancel_left] at h3
  exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (echelon_disjoint U)) _ h1 h2)

theorem nf_eq_zero_iff (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f = 0 ↔ f ∈ U := by
  constructor
  · intro h
    have h3 := nf_sub_mem U f
    rwa [h, sub_zero] at h3
  · intro h
    exact nf_unique U (by simp) (by rwa [sub_zero])

theorem nf_mem_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s)
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ restrictSupport (ZMod 2) s) :
    nf U f ∈ restrictSupport (ZMod 2) s := by
  obtain ⟨u, hu, g, hg, hug⟩ := Submodule.mem_sup.1 (echelon_le_of_downClosed U hs hf)
  have hgs := Submodule.mem_inf.1 hg
  have hnf : nf U f = g := by
    refine nf_unique U (fun c hc => (mem_restrictSupport_iff (R := ZMod 2)).1 hgs.1 hc) ?_
    rw [← hug, add_sub_cancel_right]
    exact hu
  rw [hnf]
  exact hgs.2

theorem nf_monomial_support (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) : ∀ b ∈ (nf U (monomial a 1)).support, b = a ∨ MonoLt b a := by
  have hd : ∀ c ∈ {b | b = a ∨ MonoLt b a}, ∀ b, MonoLt b c → b ∈ {b | b = a ∨ MonoLt b a} := by
    intro c hc b hb
    rcases hc with hc | hc
    · rw [hc] at hb
      exact Or.inr hb
    · exact Or.inr (monoLt_trans hb hc)
  have hm : monomial a (1 : ZMod 2) ∈ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a} :=
    (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  intro b hb
  exact (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hm) hb

omit [Countable σ] in
theorem echelon_sum_eq_degree (b : σ →₀ ℕ) : (b.sum fun _ e => e) = b.degree := by
  rw [Finsupp.degree_apply]
  rfl

theorem totalDegree_nf_le (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : (nf U f).totalDegree ≤ f.totalDegree := by
  have hd : ∀ c ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree}, ∀ b, MonoLt b c →
      b ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} :=
    fun _ hc _ hb => le_trans (degree_le_of_monoLt hb) hc
  have hf : f ∈ restrictSupport (ZMod 2) {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    exact (echelon_sum_eq_degree b).symm.trans_le (le_totalDegree hb)
  have hg := (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hf)
  unfold totalDegree
  exact Finset.sup_le fun b hb => (echelon_sum_eq_degree b).trans_le (hg hb)

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.ExpanderSupp (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

def ContainedIn (s : ℕ) (H : Finset (Fin N)) (T : Finset (Fin m)) : Prop :=
  T.card ≤ s ∧ uniqueNbrs G T ⊆ H

open Classical in

noncomputable def supp (s : ℕ) (H : Finset (Fin N)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ T, i ∈ T ∧ ContainedIn G s H T)

open Classical in
lemma mem_supp {s : ℕ} {H : Finset (Fin N)} {i : Fin m} :
    i ∈ supp G s H ↔ ∃ T, i ∈ T ∧ ContainedIn G s H T := by
  simp [supp]

def SuppClosed (s : ℕ) (K : Finset (Fin N)) (S : Finset (Fin m)) : Prop :=
  ∀ T : Finset (Fin m), S ⊂ T → T.card ≤ s → ¬ uniqueNbrs G T ⊆ K ∪ S.biUnion G

lemma mem_uniqueNbrs {T : Finset (Fin m)} {j : Fin N} :
    j ∈ uniqueNbrs G T ↔ (T.filter (fun i => j ∈ G i)).card = 1 := by
  simp [uniqueNbrs]

theorem uniqueNbrs_union_subset (A B : Finset (Fin m)) :
    uniqueNbrs G (A ∪ B) ⊆ uniqueNbrs G A ∪ uniqueNbrs G B := by
  intro j hj
  rw [mem_uniqueNbrs, Finset.filter_union] at hj
  rw [Finset.mem_union, mem_uniqueNbrs, mem_uniqueNbrs]
  by_cases hA : (A.filter (fun i => j ∈ G i)).card = 0
  · right
    rw [Finset.card_eq_zero] at hA
    rw [hA, Finset.empty_union] at hj
    exact hj
  · left
    have h1 : (A.filter (fun i => j ∈ G i)).card ≤ 1 :=
      hj ▸ Finset.card_le_card Finset.subset_union_left
    omega

lemma two_mul_card_le_of_containedIn {s : ℕ} (hG : IsBdryExpander G s 2)
    {H : Finset (Fin N)} {T : Finset (Fin m)} (hT : ContainedIn G s H T) :
    2 * T.card ≤ H.card :=
  (hG T hT.1).trans (Finset.card_le_card hT.2)

lemma containedIn_union {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) {A B : Finset (Fin m)} (hA : ContainedIn G s H A)
    (hB : ContainedIn G s H B) : ContainedIn G s H (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · have h1 := two_mul_card_le_of_containedIn G hG hA
    have h2 := two_mul_card_le_of_containedIn G hG hB
    have h3 := Finset.card_union_le A B
    omega
  · exact (uniqueNbrs_union_subset G A B).trans (Finset.union_subset hA.2 hB.2)

lemma containedIn_empty (s : ℕ) (H : Finset (Fin N)) :
    ContainedIn G s H (∅ : Finset (Fin m)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [uniqueNbrs] at hj

theorem supp_containedIn {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : ContainedIn G s H (supp G s H) := by

  have key : ∀ U : Finset (Fin m), U ⊆ supp G s H →
      ∃ T, U ⊆ T ∧ T ⊆ supp G s H ∧ ContainedIn G s H T := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, Finset.empty_subset _, Finset.empty_subset _, containedIn_empty G s H⟩
    | insert i U _ ih =>
      intro hU
      obtain ⟨T, hUT, hTS, hT⟩ := ih ((Finset.subset_insert i U).trans hU)
      have hi : i ∈ supp G s H := hU (Finset.mem_insert_self i U)
      obtain ⟨Ti, hiTi, hTi⟩ := (mem_supp G).mp hi
      have hTiS : Ti ⊆ supp G s H := fun k hk =>
        (mem_supp G).mpr ⟨Ti, hk, hTi⟩
      refine ⟨Ti ∪ T, ?_, Finset.union_subset hTiS hTS, containedIn_union G hG hH hTi hT⟩
      exact Finset.insert_subset (Finset.mem_union_left _ hiTi)
        (hUT.trans Finset.subset_union_right)
  obtain ⟨T, h1, h2, hT⟩ := key (supp G s H) (Finset.Subset.refl _)
  rw [← Finset.Subset.antisymm h2 h1]
  exact hT

theorem two_mul_card_supp_le {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : 2 * (supp G s H).card ≤ H.card :=
  two_mul_card_le_of_containedIn G hG (supp_containedIn G hG hH)

lemma mem_uniqueNbrs_of_subset {S T : Finset (Fin m)} (hST : S ⊆ T) {j : Fin N}
    (hj : j ∈ uniqueNbrs G T) (hjS : j ∈ S.biUnion G) : j ∈ uniqueNbrs G S := by
  rw [mem_uniqueNbrs] at hj ⊢
  obtain ⟨i, hiS, hji⟩ := Finset.mem_biUnion.mp hjS
  have h1 : (S.filter (fun i => j ∈ G i)).card ≤ 1 :=
    hj ▸ Finset.card_le_card (Finset.filter_subset_filter _ hST)
  have h2 : 0 < (S.filter (fun i => j ∈ G i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hji⟩⟩
  omega

theorem suppClosed_supp {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : SuppClosed G s H (supp G s H) := by
  intro T hST hT hsub
  have hS := supp_containedIn G hG hH
  have hTH : uniqueNbrs G T ⊆ H := by
    intro j hj
    rcases Finset.mem_union.mp (hsub hj) with h | h
    · exact h
    · exact hS.2 (mem_uniqueNbrs_of_subset G hST.subset hj h)
  have hTS : T ⊆ supp G s H := fun k hk =>
    (mem_supp G).mpr ⟨T, hk, hT, hTH⟩
  exact (Finset.not_subset.mp hST.2).elim fun k ⟨hkT, hkS⟩ => hkS (hTS hkT)

theorem SuppClosed.mono {s : ℕ} {K K' : Finset (Fin N)} {S : Finset (Fin m)}
    (h : SuppClosed G s K S) (hK : K' ⊆ K ∪ S.biUnion G) : SuppClosed G s K' S := by
  intro T hST hT hsub
  apply h T hST hT
  intro j hj
  rcases Finset.mem_union.mp (hsub hj) with h1 | h1
  · exact hK h1
  · exact Finset.mem_union_right _ h1

theorem SuppClosed.peel {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (h : SuppClosed G s K S) (hST : S ⊂ T) (hT : T.card ≤ s) :
    ∃ p ∈ T, p ∉ S ∧ ∃ j ∈ G p, j ∉ K ∧ j ∉ (T.erase p).biUnion G := by
  obtain ⟨j, hj, hjK⟩ := Finset.not_subset.mp (h T hST hT)
  rw [Finset.mem_union, not_or] at hjK
  obtain ⟨hjK, hjS⟩ := hjK
  rw [mem_uniqueNbrs, Finset.card_eq_one] at hj
  obtain ⟨p, hp⟩ := hj
  have hpmem : p ∈ T.filter (fun i => j ∈ G i) := hp ▸ Finset.mem_singleton_self p
  obtain ⟨hpT, hjp⟩ := Finset.mem_filter.mp hpmem
  refine ⟨p, hpT, ?_, j, hjp, hjK, ?_⟩
  · intro hpS
    exact hjS (Finset.mem_biUnion.mpr ⟨p, hpS, hjp⟩)
  · intro hj'
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp hj'
    obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
    have : q ∈ T.filter (fun i => j ∈ G i) := Finset.mem_filter.mpr ⟨hqT, hjq⟩
    rw [hp, Finset.mem_singleton] at this
    exact hqp this

lemma uniqueNbrs_singleton (i : Fin m) : uniqueNbrs G {i} = G i := by
  ext j
  rw [mem_uniqueNbrs]
  by_cases hj : j ∈ G i
  · simp [Finset.filter_singleton, hj]
  · simp [Finset.filter_singleton, hj]

theorem mem_supp_self {s : ℕ} (hs : 1 ≤ s) (i : Fin m) {H : Finset (Fin N)}
    (hi : G i ⊆ H) : i ∈ supp G s H :=
  (mem_supp G).mpr ⟨{i}, Finset.mem_singleton_self i,
    by simpa using hs, by rw [uniqueNbrs_singleton]; exact hi⟩

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.LocalSat (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

def localSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  (∀ e e' : GEdge G, e.1.2 = e'.1.2 → e.1.1 ≠ e'.1.1 → α e * α e' = 0) ∧
  ∀ i ∈ S, ∃ e : GEdge G, e.1.1 = i ∧ α e = 1

noncomputable def locIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : localSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_locIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ locIdeal G S ↔ ∀ α, localSat G S α → eval α f = 0 := by
  simp only [locIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

def monoHoles (a : GEdge G →₀ ℕ) : Finset (Fin N) := a.support.image (fun e => e.1.2)

def pigeonClause (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

theorem locIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') : locIdeal G S ≤ locIdeal G S' := by
  intro f hf
  rw [mem_locIdeal] at hf ⊢
  exact fun α hα => hf α ⟨hα.1, fun i hi => hα.2 i (h hi)⟩

theorem X_mul_mem_locIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) : X v * f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]

theorem bool_mem_locIdeal (S : Finset (Fin m)) (v : GEdge G) :
    X v * X v + X v ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α _
  have h : ∀ x : ZMod 2, x * x + x = 0 := by decide
  simpa using h (α v)

theorem hole_mem_locIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.2 = e'.1.2) (h2 : e.1.1 ≠ e'.1.1) : X e * X e' ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  simpa using hα.1 e e' h1 h2

theorem pigeon_mem_locIdeal {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) :
    clausePoly (pigeonClause G i) ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  obtain ⟨e, he, hαe⟩ := hα.2 i hi
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [clausePoly, map_prod]
  refine Finset.prod_eq_zero (i := ((e, true) : Literal (GEdge G))) ?_ ?_
  · simp [pigeonClause, he]
  · simp [hαe, h2]

theorem one_not_mem_locIdeal_empty : (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ locIdeal G ∅ := by
  rw [mem_locIdeal]
  intro h
  have h0 := h (fun _ => 0) ⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩
  rw [map_one] at h0
  exact one_ne_zero h0

theorem card_monoHoles_le (a : GEdge G →₀ ℕ) : (monoHoles G a).card ≤ a.degree := by
  refine Finset.card_image_le.trans ?_
  rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)

theorem localSat_clausePoly_pigeonClause (i : Fin m) :
    clausePoly (pigeonClause G i)
      = ∏ l ∈ pigeonClause G i, (1 + X l.1 : MvPolynomial (GEdge G) (ZMod 2)) := by
  rw [clausePoly]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl2 : l.2 = true := (Finset.mem_filter.mp hl).2.2
  simp only [hl2, ite_true]

theorem localSat_card_pigeonClause (i : Fin m) : (pigeonClause G i).card = (G i).card := by
  refine Finset.card_bij (fun l _ => l.1.1.2) ?_ ?_ ?_
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2.1
    have := l.1.2
    rwa [h] at this
  · rintro ⟨⟨⟨p, j⟩, hpj⟩, b⟩ hl ⟨⟨⟨p', j'⟩, hpj'⟩, b'⟩ hl' hjj
    have h := (Finset.mem_filter.mp hl).2
    have h' := (Finset.mem_filter.mp hl').2
    simp only at h h' hjj
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    subst hjj
    rfl
  · intro j hj
    exact ⟨((⟨(i, j), hj⟩ : GEdge G), true), by simp [pigeonClause], rfl⟩

theorem totalDegree_pigeonClause (i : Fin m) :
    (clausePoly (pigeonClause G i)).totalDegree = (G i).card := by
  classical
  have hdeg : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 1 := by
    intro v
    rw [totalDegree_add_eq_right_of_totalDegree_lt
      (by rw [totalDegree_one, totalDegree_X]; exact Nat.zero_lt_one), totalDegree_X]
  have hne : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)) ≠ 0 := by
    intro v h0
    have := hdeg v
    rw [h0, totalDegree_zero] at this
    exact Nat.zero_ne_one this
  rw [localSat_clausePoly_pigeonClause, ← localSat_card_pigeonClause]
  generalize pigeonClause G i = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      totalDegree_mul_of_isDomain (hne _) (Finset.prod_ne_zero_iff.mpr fun l _ => hne _),
      ih, hdeg, add_comm]

theorem monoHoles_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoHoles G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  have := l.1.2
  rwa [h] at this

theorem cnfSystem_graphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (graphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    ∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · refine Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩)
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.LocalNF (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]

theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]

noncomputable def localNF_zeroOut (K : Finset (Fin N)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 ∈ K then X e else 0

theorem localNF_zeroOut_monomial (K : Finset (Fin N)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (localNF_zeroOut G K) (monomial b c)
      = if monoHoles G b ⊆ K then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, localNF_zeroOut G K e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [localNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxK⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [localNF_zeroOut, ite_eq_right hxK, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem localNF_zeroOut_mem {S : Finset (Fin m)} {K : Finset (Fin N)} (hK : S.biUnion G ⊆ K)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) :
    bind₁ (localNF_zeroOut G K) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_zeroOut G K e) * eval α (localNF_zeroOut G K e') = 0
    by_cases h : e.1.2 ∈ K
    · by_cases h' : e'.1.2 ∈ K
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact hα.1 e e' h1 h2
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [localNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.2 i hi
    have hmem : e.1.2 ∈ K := by
      refine hK (Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩)
      rw [← he]
      exact e.2
    refine ⟨e, he, ?_⟩
    show eval α (localNF_zeroOut G K e) = 1
    rw [localNF_zeroOut, ite_eq_left hmem, eval_X, h1]

theorem localNF_zeroOut_eq (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (localNF_zeroOut G K) r
      = ∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => localNF_zeroOut_monomial G K b _

theorem localNF_support_sum_filter (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoHoles G b ⊆ K) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc

theorem nf_locIdeal_holes (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (locIdeal G S) (monomial a 1)).support,
      monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G := by
  have hsub := localNF_support_sum_filter G (monoHoles G a ∪ S.biUnion G)
    (nf (locIdeal G S) (monomial a 1))
  have heq : nf (locIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
          (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
          monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (locIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (locIdeal G S) (monomial a 1) b (Finset.mem_filter.mp (hsub hb)).1
    · have h := localNF_zeroOut_mem G (S := S) (K := monoHoles G a ∪ S.biUnion G)
        Finset.subset_union_right (nf_sub_mem (locIdeal G S) (monomial a 1))
      rw [map_sub, localNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        localNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
      (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
      monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2

noncomputable def localNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 = j then (if e.1.1 = p then 1 else 0) else X e

noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)

theorem localNF_override_monomial_of_notMem (p : Fin m) {j : Fin N} {b : GEdge G →₀ ℕ}
    (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (localNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, localNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [localNF_override, ite_eq_right hne]
  rw [hprod, monomial_eq]
  rfl

theorem localNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hj : j ∈ G p)
    (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ locIdeal G (insert p S)) :
    bind₁ (localNF_override G p j) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_override G p j e) * eval α (localNF_override G p j e') = 0
    by_cases h : e.1.2 = j
    · have h' : e'.1.2 = j := h1 ▸ h
      by_cases hp : e.1.1 = p
      · have hp' : ¬ e'.1.1 = p := fun h3 => h2 (hp.trans h3.symm)
        rw [localNF_override, localNF_override, ite_eq_left h', ite_eq_right hp', map_zero,
          mul_zero]
      · rw [localNF_override, ite_eq_left h, ite_eq_right hp, map_zero, zero_mul]
    · have h' : ¬ e'.1.2 = j := fun h3 => h (h1.trans h3)
      rw [localNF_override, localNF_override, ite_eq_right h, ite_eq_right h', eval_X, eval_X]
      exact hα.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (localNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [localNF_override, ite_eq_left rfl, ite_eq_left rfl, map_one]
    · obtain ⟨e, he, h1⟩ := hα.2 i h
      have hne : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (localNF_override G p j e) = 1
      rw [localNF_override, ite_eq_right hne, eval_X, h1]

theorem localNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (localNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (localNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, e.1.2 = j ∧ ¬ e.1.1 = p
  · obtain ⟨e, he, h1, h2⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rw [localNF_override, ite_eq_left h1, ite_eq_right h2, zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz' : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, h, h2⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), localNF_override, ite_eq_left h,
        ite_eq_left (hz' e he h), one_pow]
    · rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        localNF_override, ite_eq_right h]

theorem localNF_drop_eq_or_degree_lt (j : Fin N) (c : GEdge G →₀ ℕ) :
    localNF_drop G j c = c ∨ (localNF_drop G j c).degree < c.degree := by
  have hsplit : localNF_drop G j c + c.filter (fun e => ¬ e.1.2 ≠ j) = c :=
    Finsupp.filter_add_filter_not c _
  by_cases h0 : c.filter (fun e => ¬ e.1.2 ≠ j) = 0
  · left
    rw [h0, add_zero] at hsplit
    exact hsplit
  · right
    have hdeg : (localNF_drop G j c).degree + (c.filter (fun e => ¬ e.1.2 ≠ j)).degree
        = c.degree := by
      rw [← map_add, hsplit]
    have hpos : 0 < (c.filter (fun e => ¬ e.1.2 ≠ j)).degree :=
      Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    omega

theorem localNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (localNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b := 
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases localNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))

theorem nf_locIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoHoles G a) :
    nf (locIdeal G (insert p S)) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have _ := hp
  refine nf_unique (locIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (locIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hbj : j ∉ monoHoles G b := by
      intro h
      rcases Finset.mem_union.mp (nf_locIdeal_holes G S a b hb h) with h' | h'
      · exact ha h'
      · exact hjS h'
    have himg := congrArg (bind₁ (localNF_override G p j)) huw
    rw [map_add, localNF_override_monomial_of_notMem G p hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (localNF_override_mem G hj hjS hu)
      (localNF_override_mem_restrictSupport G p j hw)
  · exact locIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (locIdeal G S) (monomial a 1))

theorem nf_locIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoHoles G a ⊆ K) :
    nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_locIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.GraphPHPReduction (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

noncomputable def pseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1))

theorem pseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1)) a
  simpa only [pseudoR, coe_basisMonomials] using h

theorem monoHoles_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoHoles G (a + Finsupp.single v 1) = insert v.1.2 (monoHoles G a) := by
  unfold monoHoles
  rw [support_add_single_one, Finset.image_insert]

theorem monoHoles_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, e.1.2 ∈ K) : ∀ a ∈ f.support, monoHoles G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩)

theorem pseudoR_monomial_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {a : GEdge G →₀ ℕ} (ha : a.degree ≤ D)
    (haK : monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s K)) (monomial a 1) := by
  rw [pseudoR_monomial]
  have h3 := card_monoHoles_le G a
  have hH : (monoHoles G a).card ≤ s := h3.trans (ha.trans hD)
  have hKs : K.card ≤ s := hK.trans hD
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoHoles G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoHoles G a)) (supp G s K)
    omega
  have e1 := nf_locIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoHoles G a))
  have e2 := nf_locIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoHoles G a))
  exact e1.symm.trans e2

theorem pseudoR_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s f = nf (locIdeal G (supp G s K)) f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (pseudoR G s), e (nf (locIdeal G (supp G s K)))]
  exact Finset.sum_congr rfl fun a ha => by
    rw [pseudoR_monomial_eq_nf G hG hD hK ((le_totalDegree ha).trans hf) (hfK a ha)]

theorem pseudoR_mul {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    pseudoR G s (X v * monomial a 1) = pseudoR G s (X v * pseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoHoles G (a + Finsupp.single v 1)).card ≤ D :=
    (card_monoHoles_le G _).trans (by omega)
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoHoles G a ⊆ monoHoles G (a + Finsupp.single v 1) := by
    rw [monoHoles_add_single]
    exact Finset.subset_insert _ _
  have e1 : pseudoR G s (monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1) :=
    pseudoR_monomial_eq_nf G hG hD hK0 (by omega) (haK0.trans Finset.subset_union_left)
  have e2 : pseudoR G s (X v * monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact pseudoR_monomial_eq_nf G hG hD hK0 (by omega) Finset.subset_union_left
  have hq : (nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : pseudoR G s (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
        (monomial a 1))
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine pseudoR_eq_nf G hG hD hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := nf_locIdeal_holes G _ a c hc
      rw [addRightEmbedding_apply, monoHoles_add_single]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine Finset.mem_union_left _ ?_
        rw [monoHoles_add_single]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1)
      ∈ locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_locIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem pseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ s) (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K)
    (hmem : f ∈ locIdeal G (supp G s K)) : pseudoR G s f = 0 := by
  rw [pseudoR_eq_nf G hG le_rfl hK hf (fun a ha => (hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

theorem pseudoR_axiom {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s) (hD : D ≤ s)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ cnfSystem (graphPHP G))
    (hdeg : f.totalDegree ≤ D) : pseudoR G s f = 0 := by
  rcases cnfSystem_graphPHP_cases G hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · refine pseudoR_eq_zero_of_mem G hG (K := {v.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (bool_mem_locIdeal G _ v)
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
  · refine pseudoR_eq_zero_of_mem G hG (K := G i) ?_ (hdeg.trans hD)
      (monoHoles_pigeonClause G i)
      (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _)))
    rw [← totalDegree_pigeonClause G i]
    exact hdeg.trans hD
  · refine pseudoR_eq_zero_of_mem G hG (K := {e.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (hole_mem_locIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]
      exact Finset.mem_singleton_self _

theorem pseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : pseudoR G s 1 ≠ 0 := by
  have hm : monoHoles G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoHoles
    rw [Finsupp.support_zero, Finset.image_empty]
  have h0 : supp G s (monoHoles G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : pseudoR G s 1 = nf (locIdeal G ∅) 1 := by
    have h := pseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_locIdeal_empty G ((nf_eq_zero_iff _ _).mp h)

theorem graphPHP_no_pc_refutation {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s)
    (hD : D ≤ s) : ¬ PCRefutable (cnfSystem (graphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (pseudoR G s)
    (fun _ hf hdeg => pseudoR_axiom G hG hs hD hf hdeg)
    (fun v a ha => pseudoR_mul G hG hD v a ha)
    (pseudoR_one G hG)

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.FunLocalSat (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

def funLocalSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  localSat G S α ∧
  ∀ e e' : GEdge G, e.1.1 = e'.1.1 → e.1.2 ≠ e'.1.2 → α e * α e' = 0

noncomputable def funLocIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : funLocalSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_funLocIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ funLocIdeal G S ↔ ∀ α, funLocalSat G S α → eval α f = 0 := by
  simp only [funLocIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

theorem locIdeal_le_funLocIdeal (S : Finset (Fin m)) : locIdeal G S ≤ funLocIdeal G S := by
  intro f hf
  rw [mem_locIdeal] at hf
  rw [mem_funLocIdeal]
  exact fun α hα => hf α hα.1

theorem funLocIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') :
    funLocIdeal G S ≤ funLocIdeal G S' := by
  intro f hf
  rw [mem_funLocIdeal] at hf ⊢
  exact fun α hα => hf α ⟨⟨hα.1.1, fun i hi => hα.1.2 i (h hi)⟩, hα.2⟩

theorem X_mul_mem_funLocIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    X v * f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]

theorem fun_mem_funLocIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.1 = e'.1.1) (h2 : e.1.2 ≠ e'.1.2) : X e * X e' ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal]
  intro α hα
  simpa using hα.2 e e' h1 h2

theorem one_not_mem_funLocIdeal_empty :
    (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ funLocIdeal G ∅ := by
  rw [mem_funLocIdeal]
  intro h
  have h0 := h (fun _ => 0)
    ⟨⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩, fun _ _ _ _ => mul_zero _⟩
  rw [map_one] at h0
  exact one_ne_zero h0

def monoPigeons (a : GEdge G →₀ ℕ) : Finset (Fin m) := a.support.image (fun e => e.1.1)

def monoNbrs (a : GEdge G →₀ ℕ) : Finset (Fin N) := (monoPigeons G a).biUnion G

theorem card_monoNbrs_le {d : ℕ} (hd : LeftDegLe G d) (a : GEdge G →₀ ℕ) :
    (monoNbrs G a).card ≤ d * a.degree := by
  have h1 : (monoNbrs G a).card ≤ (monoPigeons G a).card * d :=
    Finset.card_biUnion_le_card_mul _ _ _ fun i _ => hd i
  have h2 : (monoPigeons G a).card ≤ a.degree := by
    refine Finset.card_image_le.trans ?_
    rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  calc (monoNbrs G a).card ≤ (monoPigeons G a).card * d := h1
    _ ≤ a.degree * d := Nat.mul_le_mul_right d h2
    _ = d * a.degree := Nat.mul_comm _ _

theorem monoNbrs_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoNbrs G (a + Finsupp.single v 1) = monoNbrs G a ∪ G v.1.1 := by
  ext j
  simp only [monoNbrs, monoPigeons, Finset.mem_biUnion, Finset.mem_image, Finset.mem_union,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hj⟩
    by_cases hev : e = v
    · exact Or.inr (hev ▸ hj)
    · refine Or.inl ⟨e.1.1, ⟨e, ?_, rfl⟩, hj⟩
      rwa [Finsupp.single_apply, ite_eq_right (Ne.symm hev), add_zero] at he
  · rintro (⟨i, ⟨e, he, rfl⟩, hj⟩ | hj)
    · exact ⟨e.1.1, ⟨e, fun h0 => he (Nat.eq_zero_of_add_eq_zero_right h0), rfl⟩, hj⟩
    · exact ⟨v.1.1, ⟨v, by rw [Finsupp.single_eq_same]; omega, rfl⟩, hj⟩

theorem monoNbrs_subset_of_monoPigeons {a b : GEdge G →₀ ℕ} {S : Finset (Fin m)}
    (h : monoPigeons G b ⊆ monoPigeons G a ∪ S) :
    monoNbrs G b ⊆ monoNbrs G a ∪ S.biUnion G := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  rcases Finset.mem_union.mp (h hi) with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)

theorem monoNbrs_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoNbrs G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨i', hi', hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi'
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  rwa [h] at hji

theorem cnfSystem_funGraphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    (∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e') ∨
    ∃ e e' : GEdge G, e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with hC | ⟨e, e', h1, h2, rfl⟩
    · rcases cnfSystem_graphPHP_cases G (Or.inr ⟨C, hC, rfl⟩) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩))
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.FunLocalNF (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

noncomputable def funNF_zeroOut (Q : Finset (Fin m)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 ∈ Q then X e else 0

theorem funNF_zeroOut_monomial (Q : Finset (Fin m)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (funNF_zeroOut G Q) (monomial b c)
      = if monoPigeons G b ⊆ Q then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, funNF_zeroOut G Q e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [funNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxQ⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [funNF_zeroOut, ite_eq_right hxQ, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem funNF_zeroOut_mem {S Q : Finset (Fin m)} (hQ : S ⊆ Q)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    bind₁ (funNF_zeroOut G Q) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have key : ∀ e e' : GEdge G, α e * α e' = 0 →
      eval α (funNF_zeroOut G Q e) * eval α (funNF_zeroOut G Q e') = 0 := by
    intro e e' h0
    by_cases h : e.1.1 ∈ Q
    · by_cases h' : e'.1.1 ∈ Q
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact h0
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [funNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    exact key e e' (hα.1.1 e e' h1 h2)
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.1.2 i hi
    have hmem : e.1.1 ∈ Q := by
      rw [he]
      exact hQ hi
    refine ⟨e, he, ?_⟩
    show eval α (funNF_zeroOut G Q e) = 1
    rw [funNF_zeroOut, ite_eq_left hmem, eval_X, h1]
  · intro e e' h1 h2
    exact key e e' (hα.2 e e' h1 h2)

theorem funNF_zeroOut_eq (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (funNF_zeroOut G Q) r
      = ∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => funNF_zeroOut_monomial G Q b _

theorem funNF_support_sum_filter (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoPigeons G b ⊆ Q) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc

theorem nf_funLocIdeal_pigeons (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support,
      monoPigeons G b ⊆ monoPigeons G a ∪ S := by
  have hsub := funNF_support_sum_filter G (monoPigeons G a ∪ S)
    (nf (funLocIdeal G S) (monomial a 1))
  have heq : nf (funLocIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
          (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
          monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (funLocIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (funLocIdeal G S) (monomial a 1) b
        (Finset.mem_filter.mp (hsub hb)).1
    · have h := funNF_zeroOut_mem G (S := S) (Q := monoPigeons G a ∪ S)
        Finset.subset_union_right (nf_sub_mem (funLocIdeal G S) (monomial a 1))
      rw [map_sub, funNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        funNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
      (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
      monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2

noncomputable def funNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else X e)

theorem funNF_override_monomial_of_notMem {p : Fin m} {j : Fin N} {b : GEdge G →₀ ℕ}
    (hp : p ∉ monoPigeons G b) (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (funNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, funNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne1 : e.1.1 ≠ p := fun h => hp (h ▸ Finset.mem_image_of_mem _ he)
    have hne2 : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [funNF_override, ite_eq_right hne1, ite_eq_right hne2]
  rw [hprod, monomial_eq]
  rfl

theorem funNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hp : p ∉ S)
    (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ funLocIdeal G (insert p S)) :
    bind₁ (funNF_override G p j) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have hval : ∀ e : GEdge G, eval α (funNF_override G p j e)
      = if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else α e) := by
    intro e
    rw [funNF_override]
    split_ifs <;> simp
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hj1 : e.1.2 = j
    · have hj2 : e'.1.2 = j := h1.symm.trans hj1
      by_cases hp1 : e.1.1 = p
      · have hp2 : ¬ e'.1.1 = p := fun h3 => h2 (hp1.trans h3.symm)
        rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
    · have hj2 : ¬ e'.1.2 = j := fun h3 => hj1 (h1.trans h3)
      by_cases hp1 : e.1.1 = p
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
      · by_cases hp2 : e'.1.1 = p
        · rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.1.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (funNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [hval, ite_eq_left rfl, ite_eq_left rfl]
    · obtain ⟨e, he, h1⟩ := hα.1.2 i h
      have hne1 : ¬ e.1.1 = p := by
        intro h3
        rw [he] at h3
        exact hp (h3 ▸ h)
      have hne2 : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (funNF_override G p j e) = 1
      rw [hval, ite_eq_right hne1, ite_eq_right hne2, h1]
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hp1 : e.1.1 = p
    · have hp2 : e'.1.1 = p := h1.symm.trans hp1
      by_cases hj1 : e.1.2 = j
      · have hj2 : ¬ e'.1.2 = j := fun h3 => h2 (hj1.trans h3.symm)
        rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
    · have hp2 : ¬ e'.1.1 = p := fun h3 => hp1 (h1.trans h3)
      by_cases hj1 : e.1.2 = j
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
      · by_cases hj2 : e'.1.2 = j
        · rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.2 e e' h1 h2

theorem funNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (funNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (funNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, (e.1.1 = p ∧ ¬ e.1.2 = j) ∨ (¬ e.1.1 = p ∧ e.1.2 = j)
  · obtain ⟨e, he, h⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [funNF_override, ite_eq_left h1, ite_eq_right h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
    · rw [funNF_override, ite_eq_right h1, ite_eq_left h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz1 : ∀ e ∈ c.support, e.1.1 = p → e.1.2 = j := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inl ⟨h, h2⟩⟩
    have hz2 : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inr ⟨h2, h⟩⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), funNF_override, ite_eq_left (hz2 e he h),
        ite_eq_left h, one_pow]
    · have hne : ¬ e.1.1 = p := fun h3 => h (hz1 e he h3)
      rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        funNF_override, ite_eq_right hne, ite_eq_right h]

theorem funNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (funNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases funNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))

theorem nf_funLocIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoNbrs G a) :
    nf (funLocIdeal G (insert p S)) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  refine nf_unique (funLocIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (funLocIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hloc := nf_funLocIdeal_pigeons G S a b hb
    have hbp : p ∉ monoPigeons G b := by
      intro h
      rcases Finset.mem_union.mp (hloc h) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨p, h', hj⟩)
      · exact hp h'
    have hbj : j ∉ monoHoles G b := by
      intro h
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp h
      have hje : j ∈ G e.1.1 := by
        rw [← hej]
        exact e.2
      rcases Finset.mem_union.mp (hloc (Finset.mem_image_of_mem _ he)) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
      · exact hjS (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
    have himg := congrArg (bind₁ (funNF_override G p j)) huw
    rw [map_add, funNF_override_monomial_of_notMem G hbp hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (funNF_override_mem G hp hj hjS hu)
      (funNF_override_mem_restrictSupport G p j hw)
  · exact funLocIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (funLocIdeal G S) (monomial a 1))

theorem nf_funLocIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoNbrs G a ⊆ K) :
    nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_funLocIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.Helpers.FunGraphPHPReduction (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

noncomputable def funPseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1))

theorem funPseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1)) a
  simpa only [funPseudoR, coe_basisMonomials] using h

theorem monoNbrs_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, G e.1.1 ⊆ K) : ∀ a ∈ f.support, monoNbrs G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩) hji

theorem funPseudoR_monomial_eq_nf {s B : ℕ} (hG : IsBdryExpander G s 2) (hB : B ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ B) {a : GEdge G →₀ ℕ}
    (ha : (monoNbrs G a).card ≤ B)
    (haK : monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s (monomial a 1) = nf (funLocIdeal G (supp G s K)) (monomial a 1) := by
  rw [funPseudoR_monomial]
  have hH : (monoNbrs G a).card ≤ s := ha.trans hB
  have hKs : K.card ≤ s := hK.trans hB
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoNbrs G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoNbrs G a)) (supp G s K)
    omega
  have e1 := nf_funLocIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoNbrs G a))
  have e2 := nf_funLocIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoNbrs G a))
  exact e1.symm.trans e2

theorem funPseudoR_eq_nf_of_monomials {s : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)))
    {f : MvPolynomial (GEdge G) (ZMod 2)}
    (h : ∀ a ∈ f.support, funPseudoR G s (monomial a 1) = nf U (monomial a 1)) :
    funPseudoR G s f = nf U f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (funPseudoR G s), e (nf U)]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

theorem funPseudoR_eq_nf {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) {K : Finset (Fin N)} (hK : K.card ≤ d * D)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s f = nf (funLocIdeal G (supp G s K)) f :=
  funPseudoR_eq_nf_of_monomials G _ fun a ha =>
    funPseudoR_monomial_eq_nf G hG hB hK
      ((card_monoNbrs_le G hd a).trans
        (Nat.mul_le_mul_left d ((le_totalDegree ha).trans hf))) (hfK a ha)

theorem funPseudoR_mul {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    funPseudoR G s (X v * monomial a 1)
      = funPseudoR G s (X v * funPseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoNbrs G (a + Finsupp.single v 1)).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hKa : (monoNbrs G a).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoNbrs G a ⊆ monoNbrs G (a + Finsupp.single v 1) := by
    rw [monoNbrs_add_single]
    exact Finset.subset_union_left
  have e1 : funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1)))) (monomial a 1) :=
    funPseudoR_monomial_eq_nf G hG hB hK0 hKa (haK0.trans Finset.subset_union_left)
  have e2 : funPseudoR G s (X v * monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact funPseudoR_monomial_eq_nf G hG hB hK0 hK0 Finset.subset_union_left
  have hq : (nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : funPseudoR G s
        (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1))
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine funPseudoR_eq_nf G hG hd hB hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := monoNbrs_subset_of_monoPigeons G (nf_funLocIdeal_pigeons G _ a c hc)
      rw [addRightEmbedding_apply, monoNbrs_add_single]
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
      · refine Finset.mem_union_left _ ?_
        rw [monoNbrs_add_single]
        exact Finset.mem_union_right _ hj
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1)
      ∈ funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_funLocIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem funPseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K)
    (hmem : f ∈ funLocIdeal G (supp G s K)) : funPseudoR G s f = 0 := by
  rw [funPseudoR_eq_nf_of_monomials G (funLocIdeal G (supp G s K)) fun a ha =>
    funPseudoR_monomial_eq_nf G hG le_rfl hK ((Finset.card_le_card (hfK a ha)).trans hK)
      ((hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

theorem totalDegree_X_mul_X (e e' : GEdge G) :
    (X e * X e' : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
  have h : (X e * X e' : MvPolynomial (GEdge G) (ZMod 2))
      = monomial (Finsupp.single e 1 + Finsupp.single e' 1) 1 := by
    have hX : (X e : MvPolynomial (GEdge G) (ZMod 2)) = monomial (Finsupp.single e 1) 1 := rfl
    rw [hX, monomial_one_mul_X]
  rw [h, totalDegree_monomial_one, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem funPseudoR_axiom {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hs : 1 ≤ s) (hB : d * D ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) (hdeg : f.totalDegree ≤ D) : funPseudoR G s f = 0 := by
  have hcard : ∀ i, 1 ≤ D → (G i).card ≤ d * D := fun i hD =>
    (hd i).trans (Nat.le_mul_of_pos_right d hD)
  rcases cnfSystem_funGraphPHP_cases G hf with
    ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · have h2 : (X v * X v + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
      rw [totalDegree_add_eq_left_of_totalDegree_lt, totalDegree_X_mul_X]
      rw [totalDegree_X_mul_X, totalDegree_X]
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G v.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (bool_mem_locIdeal G _ v))
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
  · have hi : (G i).card ≤ D := by
      rw [← totalDegree_pigeonClause G i]
      exact hdeg
    have hi' : (G i).card ≤ s := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · omega
      · exact (hcard i h0).trans hB
    exact funPseudoR_eq_zero_of_mem G hG (K := G i) hi' (monoNbrs_pigeonClause G i)
      (locIdeal_le_funLocIdeal G _
        (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _))))
  · rw [totalDegree_X_mul_X] at hdeg
    have hK : (G e.1.1 ∪ G e'.1.1).card ≤ s := by
      have h3 := Finset.card_union_le (G e.1.1) (G e'.1.1)
      have h4 := hd e.1.1
      have h5 := hd e'.1.1
      have h6 : d * 2 ≤ d * D := Nat.mul_le_mul_left d hdeg
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1 ∪ G e'.1.1) hK
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (hole_mem_locIdeal G _ h1 h2))
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_left
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_right
  · rw [totalDegree_X_mul_X] at hdeg
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_) (fun_mem_funLocIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]

theorem funPseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : funPseudoR G s 1 ≠ 0 := by
  have hm : monoNbrs G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoNbrs monoPigeons
    rw [Finsupp.support_zero, Finset.image_empty, Finset.biUnion_empty]
  have h0 : supp G s (monoNbrs G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : funPseudoR G s 1 = nf (funLocIdeal G ∅) 1 := by
    have h := funPseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_funLocIdeal_empty G ((nf_eq_zero_iff _ _).mp h)

theorem funGraphPHP_no_pc_refutation {s d D : ℕ} (hG : IsBdryExpander G s 2)
    (hd : LeftDegLe G d) (hs : 1 ≤ s) (hB : d * D ≤ s) :
    ¬ PCRefutable (cnfSystem (funGraphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (funPseudoR G s)
    (fun _ hf hdeg => funPseudoR_axiom G hG hd hs hB hf hdeg)
    (fun v a ha => funPseudoR_mul G hG hd hB v a ha)
    (funPseudoR_one G hG)

end PEqualNP.Outside.L_pcx_383_aux.Helpers

-- inlined from PEqualNP.ProofComplexity.L049 (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux
theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB

end PEqualNP.Outside.L_pcx_383_aux

-- inlined from PEqualNP.ProofComplexity.Helpers.BoolVanish (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.Helpers.BoolVanish

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_383_aux.Helpers

variable {σ : Type}

noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

theorem boolDerivable_monomial (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this

theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]

theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v

end PEqualNP.Outside.L_pcx_383_aux.Helpers.BoolVanish

-- inlined from PEqualNP.Outside.L_pcx_382 (upstream main, Apache-2.0)
namespace PEqualNP.Outside.L_pcx_383_aux.C382

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_383_aux.Helpers

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

private theorem degree_line {V : Type} {A : Set (Poly V)} {d : ℕ} {p : Poly V}
    (h : PCDerivable A d p) : p.totalDegree ≤ d := by
  induction h with
  | ax _ h => exact h
  | zero => simp
  | add _ _ ih₁ ih₂ => exact (totalDegree_add _ _).trans (max_le ih₁ ih₂)
  | mulX _ _ h _ => exact h

private theorem degree_product {V ι : Type} (S : Finset ι) (p : ι → Poly V) :
    (∏ i ∈ S, p i).totalDegree ≤ ∑ i ∈ S, (p i).totalDegree := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

private theorem with_factor {V : Type} {A F : Set (Poly V)} {d B : ℕ}
    (q : Poly V) (hq : q.totalDegree + d ≤ B)
    (base : ∀ p ∈ A, p.totalDegree ≤ d → PCDerivable F B (q * p))
    {p : Poly V} (h : PCDerivable A d p) : PCDerivable F B (q * p) := by
  induction h with
  | ax hp hd => exact base _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable F B 0)
  | add _ _ ih₁ ih₂ =>
    rw [mul_add]
    exact .add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [mul_left_comm q (X j)]
    apply PCDerivable.mulX j ih
    rw [← mul_left_comm q (X j)]
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add_left hd _).trans hq)

private theorem derive_products {V : Type} {F : Set (Poly V)} {B : ℕ} :
    ∀ (t : ℕ) (A : Fin t → Set (Poly V)) (D : Fin t → ℕ) (q : Poly V)
      (p : Fin t → Poly V), (∀ i, PCDerivable (A i) (D i) (p i)) →
      q.totalDegree + (∑ i, D i) ≤ B →
      (∀ f : Fin t → Poly V, (∀ i, f i ∈ A i ∧ (f i).totalDegree ≤ D i) →
        PCDerivable F B (q * ∏ i, f i)) →
      PCDerivable F B (q * ∏ i, p i) := by
  intro t
  induction t with
  | zero =>
    intro A D q p _ _ base
    exact base p (fun i => Fin.elim0 i)
  | succ t ih =>
    intro A D q p deriv hp base
    rw [Fin.sum_univ_succ] at hp
    let r : Poly V := ∏ i : Fin t, p i.succ
    have r_bound : r.totalDegree ≤ ∑ i : Fin t, D i.succ :=
      (degree_product Finset.univ (fun i : Fin t => p i.succ)).trans
        (Finset.sum_le_sum fun i _ => degree_line (deriv i.succ))
    have qr_bound : (q*r).totalDegree + D 0 ≤ B := by
      have h := totalDegree_mul q r
      omega
    rw [Fin.prod_univ_succ, ← mul_assoc]
    change PCDerivable F B ((q * p 0) * r)
    rw [mul_right_comm]
    apply with_factor (q*r) qr_bound _ (deriv 0)
    intro a ha da
    have qa_bound : (q*a).totalDegree + (∑ i : Fin t, D i.succ) ≤ B := by
      have h := totalDegree_mul q a
      omega
    have suffix := ih (fun i => A i.succ) (fun i => D i.succ) (q*a)
      (fun i => p i.succ) (fun i => deriv i.succ) qa_bound (by
        intro f hf
        let full : Fin (t+1) → Poly V := Fin.cons a f
        have hfull (j : Fin (t+1)) : full j ∈ A j ∧ (full j).totalDegree ≤ D j := by
          refine Fin.cases ?_ (fun i => ?_) j
          · simpa [full] using And.intro ha da
          · simpa [full] using hf i
        simpa only [full, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← mul_assoc]
          using base full hfull)
    simpa only [r, mul_right_comm q a] using suffix

theorem combine {V : Type} (F : Set (Poly V)) (t : ℕ)
    (E : Fin t → Set (Poly V)) (D : Fin t → ℕ)
    (boolean : ∀ v : V, X v * X v + X v ∈ F)
    (cover : ∀ x : V → ZMod 2, ∃ j : Fin t, ∀ e ∈ E j, eval x e = 0)
    (branches : ∀ j, PCRefutable (F ∪ E j) (D j)) : PCRefutable F (∑ j, D j) := by
  classical
  let B := ∑ j, D j
  have base (p : Fin t → Poly V) (hp : ∀ j, p j ∈ F ∪ E j ∧ (p j).totalDegree ≤ D j) :
      PCDerivable F B (1 * ∏ j, p j) := by
    rw [one_mul]
    by_cases hasBase : ∃ i, p i ∈ F
    · obtain ⟨i, hi⟩ := hasBase
      let r := Finset.univ.erase i
      have hsum : (∑ j ∈ r, D j) + D i = B :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i)
      let q := ∏ j ∈ r, p j
      have hq : q.totalDegree ≤ ∑ j ∈ r, D j := (degree_product r p).trans
        (Finset.sum_le_sum fun j _ => (hp j).2)
      have derived : PCDerivable F (D i) (p i) := .ax hi (hp i).2
      have step := pcDerivable_mul_left derived q
      have hstep : PCDerivable F B (q * p i) :=
        pcDerivable_mono step (max_le (by omega) (by have := (hp i).2; omega)) (fun _ h => h)
      rwa [Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at hstep
    · apply BoolVanish.vanish_derivable V F B _ boolean
      · exact (degree_product Finset.univ p).trans (Finset.sum_le_sum fun j _ => (hp j).2)
      · intro x
        obtain ⟨i, hi⟩ := cover x
        have hmem : p i ∈ E i := ((hp i).1).resolve_left (fun h => hasBase ⟨i,h⟩)
        rw [map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hi _ hmem)
  have h := derive_products t (fun j => F ∪ E j) D (1 : Poly V) (fun _ => 1)
    branches (by simp [B]) base
  simpa [PCRefutable, B] using h

end PEqualNP.Outside.L_pcx_383_aux.C382
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Sim

variable {V W : Type} [DecidableEq W]

noncomputable def cprod (φ : Literal W → MvPolynomial V (ZMod 2)) (D : Clause W) :
    MvPolynomial V (ZMod 2) := ∏ l ∈ D, φ l

theorem two_eq_zero_poly (q : MvPolynomial V (ZMod 2)) : q + q = 0 := by
  calc q + q = C (1 + 1 : ZMod 2) * q := by rw [map_add, map_one, add_mul, one_mul]
    _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from rfl, map_zero, zero_mul]

theorem mul_deriv {A : Set (MvPolynomial V (ZMod 2))} {K : ℕ} {g q : MvPolynomial V (ZMod 2)}
    (hg : PCDerivable A (2 * K) g) (hgd : g = 0 ∨ g.totalDegree ≤ K) (hq : q.totalDegree ≤ K) :
    PCDerivable A (2 * K) (q * g) := by
  rcases hgd with h0 | hd
  · rw [h0, mul_zero]; exact .zero
  · have := PEqualNP.Outside.L_pcx_383_aux.Helpers.pcDerivable_mul_left hg q
    have hm : max (2 * K) (q.totalDegree + g.totalDegree) = 2 * K := by
      apply max_eq_left; omega
    rw [hm] at this; exact this

theorem sim (φ : Literal W → MvPolynomial V (ZMod 2))
    (hφ : ∀ v, φ (v, false) = 1 + φ (v, true))
    (S : Set (Clause W)) (A : Set (MvPolynomial V (ZMod 2))) (K : ℕ) (π : List (Clause W))
    (hπ : IsDerivation S π) :
    (∀ D ∈ π, cprod φ D = 0 ∨ ∀ T ⊆ D, (cprod φ T).totalDegree ≤ K) →
    (∀ D ∈ π, D ∈ S → cprod φ D ∈ A) →
    ∀ D ∈ π, PCDerivable A (2 * K) (cprod φ D) := by
  induction hπ with
  | nil => intro _ _ D hD; simp at hD
  | @ax π C _ hCS ih =>
    intro hgood hax D hD
    have hgood' : ∀ D ∈ π, cprod φ D = 0 ∨ ∀ T ⊆ D, (cprod φ T).totalDegree ≤ K :=
      fun D hD => hgood D (List.mem_cons_of_mem _ hD)
    have hax' : ∀ D ∈ π, D ∈ S → cprod φ D ∈ A :=
      fun D hD => hax D (List.mem_cons_of_mem _ hD)
    rcases List.mem_cons.mp hD with rfl | hD
    · rcases hgood D List.mem_cons_self with h0 | hd
      · rw [h0]; exact .zero
      · exact .ax (hax D List.mem_cons_self hCS) ((hd D subset_rfl).trans (by omega))
    · exact ih hgood' hax' D hD
  | @res π C D R _ hC hD hR ih =>
    intro hgood hax E hE
    have hgood' : ∀ D ∈ π, cprod φ D = 0 ∨ ∀ T ⊆ D, (cprod φ T).totalDegree ≤ K :=
      fun D hD => hgood D (List.mem_cons_of_mem _ hD)
    have hax' : ∀ D ∈ π, D ∈ S → cprod φ D ∈ A :=
      fun D hD => hax D (List.mem_cons_of_mem _ hD)
    rcases List.mem_cons.mp hE with rfl | hE
    · rcases hgood E List.mem_cons_self with h0 | hT
      · rw [h0]; exact .zero
      · obtain ⟨v, hvC, hvD, hReq⟩ := hR
        have dC := ih hgood' hax' C hC
        have dD := ih hgood' hax' D hD
        have gC : cprod φ C = 0 ∨ (cprod φ C).totalDegree ≤ K := by
          rcases hgood' C hC with h | h
          · exact Or.inl h
          · exact Or.inr (h C subset_rfl)
        have gD : cprod φ D = 0 ∨ (cprod φ D).totalDegree ≤ K := by
          rcases hgood' D hD with h | h
          · exact Or.inl h
          · exact Or.inr (h D subset_rfl)
        have keyC : cprod φ (E \ C) * cprod φ C = cprod φ (insert (v, true) E) := by
          unfold cprod
          rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
          congr 1
          ext l
          simp only [Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro (h | h)
            · exact Or.inr h
            · by_cases hl : l = (v, true)
              · exact Or.inl hl
              · right; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hl, h⟩)
          · rintro (h | h)
            · right; rw [h]; exact hvC
            · exact Or.inl h
        have keyD : cprod φ (E \ D) * cprod φ D = cprod φ (insert (v, false) E) := by
          unfold cprod
          rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
          congr 1
          ext l
          simp only [Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro (h | h)
            · exact Or.inr h
            · by_cases hl : l = (v, false)
              · exact Or.inl hl
              · right; rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hl, h⟩)
          · rintro (h | h)
            · right; rw [h]; exact hvD
            · exact Or.inl h
        have pC : PCDerivable A (2 * K) (cprod φ (insert (v, true) E)) := by
          rw [← keyC]; exact mul_deriv dC gC (hT _ Finset.sdiff_subset)
        have pD : PCDerivable A (2 * K) (cprod φ (insert (v, false) E)) := by
          rw [← keyD]; exact mul_deriv dD gD (hT _ Finset.sdiff_subset)
        by_cases h1 : (v, true) ∈ E
        · rw [Finset.insert_eq_of_mem h1] at pC; exact pC
        by_cases h2 : (v, false) ∈ E
        · rw [Finset.insert_eq_of_mem h2] at pD; exact pD
        have hsum := PCDerivable.add pC pD
        unfold cprod at hsum ⊢
        rw [Finset.prod_insert h1, Finset.prod_insert h2, hφ v] at hsum
        have : φ (v, true) * ∏ l ∈ E, φ l + (1 + φ (v, true)) * ∏ l ∈ E, φ l
            = ∏ l ∈ E, φ l := by
          have h3 := two_eq_zero_poly (φ (v, true) * ∏ l ∈ E, φ l)
          linear_combination h3
        rw [this] at hsum; exact hsum
    · exact ih hgood' hax' E hE

end Sim

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Phi

variable {V : Type} {a h : ℕ}

noncomputable def phi (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool) :
    Literal ((V ⊕ Fin a) ⊕ Fin h) → MvPolynomial V (ZMod 2) := fun l =>
  match l.1 with
  | Sum.inl (Sum.inl v) => if l.2 then 1 + X v else X v
  | Sum.inl (Sum.inr i) => if l.2 then 1 + P i else P i
  | Sum.inr i => if l.2 = m i then 0 else 1

theorem one_add_one_poly : (1 : MvPolynomial V (ZMod 2)) + 1 = 0 :=
  two_eq_zero_poly 1

theorem phi_neg (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool)
    (v : (V ⊕ Fin a) ⊕ Fin h) : phi P m (v, false) = 1 + phi P m (v, true) := by
  rcases v with (v | i) | i
  · simp only [phi, if_true]
    rw [← add_assoc, one_add_one_poly, zero_add]; rfl
  · simp only [phi, if_true]
    rw [← add_assoc, one_add_one_poly, zero_add]; rfl
  · simp only [phi]
    cases m i <;> simp [one_add_one_poly]

theorem phi_deg (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool) (d : ℕ)
    (hd : 1 ≤ d) (hP : ∀ i, (P i).totalDegree ≤ d) (l : Literal ((V ⊕ Fin a) ⊕ Fin h)) :
    (phi P m l).totalDegree ≤ if l.1.isLeft then d else 0 := by
  rcases l with ⟨(v | i) | i, b⟩
  · simp only [phi, Sum.isLeft_inl, if_true]
    cases b
    · simp only [Bool.false_eq_true, if_false]; rw [totalDegree_X]; exact hd
    · simp only [if_true]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · simp
      · rw [totalDegree_X]; exact hd
  · simp only [phi, Sum.isLeft_inl, if_true]
    cases b
    · simp only [Bool.false_eq_true, if_false]; exact hP i
    · simp only [if_true]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · simp
      · exact hP i
  · simp only [phi, Sum.isLeft_inr, Bool.false_eq_true, if_false]
    split_ifs <;> simp

theorem cprod_deg [DecidableEq V] (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool)
    (d : ℕ) (hd : 1 ≤ d) (hP : ∀ i, (P i).totalDegree ≤ d)
    (T : Clause ((V ⊕ Fin a) ⊕ Fin h)) :
    (cprod (phi P m) T).totalDegree ≤ d * (T.filter (fun l => l.1.isLeft)).card := by
  unfold cprod
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ l ∈ T, (phi P m l).totalDegree ≤ ∑ l ∈ T, (if l.1.isLeft then d else 0) :=
        Finset.sum_le_sum fun l _ => phi_deg P m d hd hP l
    _ = d * (T.filter (fun l => l.1.isLeft)).card := by
        rw [← Finset.sum_filter]; simp [mul_comm]

theorem cprod_zero [DecidableEq V] (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool)
    (D : Clause ((V ⊕ Fin a) ⊕ Fin h)) (i : Fin h) (hi : ((Sum.inr i : (V ⊕ Fin a) ⊕ Fin h), m i) ∈ D) :
    cprod (phi P m) D = 0 := by
  unfold cprod
  exact Finset.prod_eq_zero hi (by simp [phi])

theorem cprod_lift [DecidableEq V] (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool)
    (cl : Clause V) :
    cprod (phi P m) (cl.image (fun l => ((Sum.inl (Sum.inl l.1) : (V ⊕ Fin a) ⊕ Fin h), l.2)))
      = clausePoly cl := by
  unfold cprod clausePoly
  rw [Finset.prod_image]
  · rfl
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq, Sum.inl.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2

theorem cprod_eval [DecidableEq V] (P : Fin a → MvPolynomial V (ZMod 2)) (m : Fin h → Bool)
    (x : V → Bool) (D : Clause ((V ⊕ Fin a) ⊕ Fin h))
    (hD : ClauseSat (Sum.elim (Sum.elim x (fun i : Fin a => decide
      (eval (fun v => (x v).toNat : V → ZMod 2) (P i) = 1))) m) D) :
    eval (fun v => (x v).toNat : V → ZMod 2) (cprod (phi P m) D) = 0 := by
  obtain ⟨l, hl, hsat⟩ := hD
  unfold cprod
  rw [map_prod]
  refine Finset.prod_eq_zero hl ?_
  rcases l with ⟨(v | i) | i, b⟩
  · simp only [Sum.elim_inl] at hsat
    simp only [phi]
    rw [← hsat]; cases hx : x v <;> simp [hx] <;> first | rfl | decide
  · simp only [Sum.elim_inl, Sum.elim_inr] at hsat
    simp only [phi]
    rw [← hsat]
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (eval (fun v => ((x v).toNat : ZMod 2)) (P i)) with hz | hz <;>
      simp [hz] <;> first | rfl | decide
  · simp only [Sum.elim_inr] at hsat
    simp [phi, hsat]

end Phi

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

section Scan

variable (cap ww : ℕ → ℕ)

def step (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if s.2.2 + 1 < cap s.1 then (s.1, s.2.1, s.2.2 + 1)
  else if s.2.1 + 1 < ww s.1 then (s.1, s.2.1 + 1, 0) else (s.1 + 1, 0, 0)

def st : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | p + 1 => step cap ww (st p)

def slots (s : ℕ × ℕ × ℕ) : ℕ :=
  (∑ i ∈ Finset.range s.1, cap i * ww i) + s.2.1 * cap s.1 + s.2.2

variable {cap ww}

theorem st_inv (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (p : ℕ) :
    (st cap ww p).2.2 < cap (st cap ww p).1 ∧ (st cap ww p).2.1 < ww (st cap ww p).1 := by
  induction p with
  | zero => exact ⟨hcap 0, hww 0⟩
  | succ p ih =>
    simp only [st, step]
    split_ifs with h1 h2
    · exact ⟨h1, ih.2⟩
    · exact ⟨hcap _, h2⟩
    · exact ⟨hcap _, hww _⟩

theorem slots_st (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (p : ℕ) :
    slots cap ww (st cap ww p) = p := by
  induction p with
  | zero => simp [slots, st]
  | succ p ih =>
    have hinv := st_inv hcap hww p
    simp only [st, step]
    generalize st cap ww p = s at ih hinv
    obtain ⟨k, b, r⟩ := s
    simp only at ih hinv ⊢
    unfold slots at ih ⊢
    simp only at ih ⊢
    split_ifs with h1 h2
    · simp only; omega
    · simp only
      have hr : cap k = r + 1 := by omega
      rw [hr] at ih ⊢
      rw [← ih]; ring
    · simp only
      have hr : cap k = r + 1 := by omega
      have hb : ww k = b + 1 := by omega
      rw [Finset.sum_range_succ, hr, hb, ← ih, hr]; ring

theorem st_bin_lt (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (t p : ℕ)
    (hp : p < ∑ i ∈ Finset.range t, cap i * ww i) : (st cap ww p).1 < t := by
  by_contra hcon
  push_neg at hcon
  have h1 := slots_st hcap hww p
  unfold slots at h1
  have h2 : ∑ i ∈ Finset.range t, cap i * ww i ≤ ∑ i ∈ Finset.range (st cap ww p).1, cap i * ww i :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hcon)
  omega

theorem st_succ_same (p : ℕ) (h : (st cap ww p).2.2 + 1 < cap (st cap ww p).1) :
    st cap ww (p + 1) = ((st cap ww p).1, (st cap ww p).2.1, (st cap ww p).2.2 + 1) := by
  simp [st, step, h]

theorem st_succ_not (p : ℕ) (h : ¬ (st cap ww p).2.2 + 1 < cap (st cap ww p).1) :
    (st cap ww (p + 1)).2.2 = 0 := by
  simp only [st, step, h, if_false]
  split_ifs <;> rfl

theorem same_of_eq (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (p q : ℕ) (hpq : p < q)
    (hk : (st cap ww p).1 = (st cap ww q).1) (hb : (st cap ww p).2.1 = (st cap ww q).2.1) :
    (st cap ww p).2.2 + 1 < cap (st cap ww p).1 := by
  have h1 := slots_st hcap hww p
  have h2 := slots_st hcap hww q
  have hq := (st_inv hcap hww q).1
  unfold slots at h1 h2
  rw [← hk, ← hb] at h2
  rw [← hk] at hq
  generalize (∑ i ∈ Finset.range (st cap ww p).1, cap i * ww i) = S at h1 h2
  generalize (st cap ww p).2.1 * cap (st cap ww p).1 = M at h1 h2
  omega

end Scan

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open PEqualNP.ProofComplexity

section Build

variable {W : Type} [DecidableEq W] (S : Set (Clause W)) (Q : Clause W → Prop)

def Good (π : List (Clause W)) : Prop := IsDerivation S π ∧ ∀ D ∈ π, Q D

variable {S Q}

theorem good_nil : Good S Q [] := ⟨.nil, fun _ h => by simp at h⟩

theorem good_ax {π : List (Clause W)} {C : Clause W} (h : Good S Q π) (hC : C ∈ S) (hQ : Q C) :
    Good S Q (C :: π) := by
  refine ⟨.ax h.1 hC, fun D hD => ?_⟩
  rcases List.mem_cons.mp hD with rfl | hD
  · exact hQ
  · exact h.2 D hD

theorem good_res {π : List (Clause W)} {C D R : Clause W} (h : Good S Q π) (hC : C ∈ π)
    (hD : D ∈ π) (hR : IsResolvent C D R) (hQ : Q R) : Good S Q (R :: π) := by
  refine ⟨.res h.1 hC hD hR, fun E hE => ?_⟩
  rcases List.mem_cons.mp hE with rfl | hE
  · exact hQ
  · exact h.2 E hE

theorem res_helper (v : W) (A B : Clause W) (hA : (v, true) ∉ A) (hB : (v, false) ∉ B) :
    IsResolvent (insert (v, true) A) (insert (v, false) B) (A ∪ B) :=
  ⟨v, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, by
    rw [Finset.erase_insert hA, Finset.erase_insert hB]⟩

theorem elim_gen {ι : Type} [DecidableEq ι] (f : ι → Literal W) (T0 : Finset ι) (R0 : Clause W)
    (partner : ι → Clause W)
    (hstep : ∀ i ∈ T0, ∀ T : Finset ι, ∀ A : Clause W, A ⊆ R0 → i ∉ T →
      IsResolvent (insert (f i) (T.image f ∪ A)) (partner i) (T.image f ∪ R0) ∨
      IsResolvent (partner i) (insert (f i) (T.image f ∪ A)) (T.image f ∪ R0))
    (hQ : ∀ T ⊆ T0, Q (T.image f ∪ R0)) :
    ∀ T ⊆ T0, ∀ A : Clause W, A ⊆ R0 → (T = ∅ → A = R0) → ∀ π : List (Clause W), Good S Q π →
      (∀ i ∈ T0, partner i ∈ π) → T.image f ∪ A ∈ π →
      ∃ π' : List (Clause W), Good S Q π' ∧ (∀ D ∈ π, D ∈ π') ∧ R0 ∈ π' ∧
        π'.length ≤ π.length + T.card := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ A _ hA π hπ _ hmem
    rw [hA rfl] at hmem
    simp only [Finset.image_empty, Finset.empty_union] at hmem
    exact ⟨π, hπ, fun _ h => h, hmem, by simp⟩
  | insert i T hi ih =>
    intro hT A hA _ π hπ hpart hmem
    have hiT0 : i ∈ T0 := hT (Finset.mem_insert_self i T)
    have hT' : T ⊆ T0 := fun x hx => hT (Finset.mem_insert_of_mem hx)
    have heq : (insert i T).image f ∪ A = insert (f i) (T.image f ∪ A) := by
      rw [Finset.image_insert, Finset.insert_union]
    rw [heq] at hmem
    have hp := hpart i hiT0
    have hgood : Good S Q ((T.image f ∪ R0) :: π) := by
      rcases hstep i hiT0 T A hA hi with h | h
      · exact good_res hπ hmem hp h (hQ T hT')
      · exact good_res hπ hp hmem h (hQ T hT')
    obtain ⟨π', h1, h2, h3, h4⟩ := ih hT' R0 subset_rfl (fun _ => rfl) _ hgood
      (fun j hj => List.mem_cons_of_mem _ (hpart j hj)) List.mem_cons_self
    refine ⟨π', h1, fun D hD => h2 D (List.mem_cons_of_mem _ hD), h3, ?_⟩
    simp only [List.length_cons] at h4
    rw [Finset.card_insert_of_notMem hi]
    omega

end Build

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr

variable {V : Type} [DecidableEq V] {N t : ℕ}

abbrev WW (V : Type) (N t : ℕ) : Type := (V ⊕ Fin N) ⊕ Fin t

def uL (p : Fin N) (b : Bool) : Literal (WW V N t) := (Sum.inl (Sum.inr p), b)
def gam (k : Fin t) : Literal (WW V N t) := (Sum.inr k, false)
def liftL (l : Literal V) : Literal (WW V N t) := (Sum.inl (Sum.inl l.1), l.2)
def negL (l : Literal V) : Literal (WW V N t) := (Sum.inl (Sum.inl l.1), !l.2)

theorem liftL_inj : Function.Injective (liftL : Literal V → Literal (WW V N t)) := by
  intro x y h
  simp only [liftL, Prod.mk.injEq, Sum.inl.injEq] at h
  exact Prod.ext h.1 h.2

theorem uL_inj (b : Bool) : Function.Injective (fun p : Fin N => (uL p b : Literal (WW V N t))) := by
  intro x y h
  simp only [uL, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, and_true] at h
  exact h

variable (cap ww : ℕ → ℕ) (bin : Fin N → Fin t)

abbrev same (q : ℕ) : Prop := (st cap ww q).2.2 + 1 < cap (st cap ww q).1

abbrev cont (p : Fin N) : Prop := 0 < p.val ∧ same cap ww (p.val - 1)

def pred (p : Fin N) : Fin N := ⟨p.val - 1, by have := p.isLt; omega⟩

def Dc (p : Fin N) : Clause (WW V N t) := {gam (bin p), uL p false}

def Rc (p : Fin N) : Clause (WW V N t) :=
  if cont cap ww p then insert (uL (pred p) true) (Dc bin p) else Dc bin p

def Xc (p : Fin N) (l : Literal V) : Clause (WW V N t) := insert (negL l) (Rc cap ww bin p)

abbrev root (p : Fin N) : Prop := p.val + 1 = N ∨ ¬ same cap ww p.val

def roots (k : Fin t) : Finset (Fin N) :=
  Finset.univ.filter (fun p => root cap ww p ∧ bin p = k)

def Wd (k : Fin t) : Clause (WW V N t) :=
  insert (gam k) ((roots cap ww bin k).image (fun p => uL p true))

def Mf : Clause (WW V N t) := Finset.univ.image (fun k : Fin t => ((Sum.inr k : WW V N t), true))

def extraF (c : Fin N → Clause V) : Finset (Clause (WW V N t)) :=
  (Finset.univ.biUnion fun p => (c p).image (Xc cap ww bin p)) ∪
    Finset.univ.image (Wd cap ww bin) ∪ {Mf}

def menuF (j : Fin t) (i : Fin t) : Bool := decide (i = j)

noncomputable def orP (x y : MvPolynomial V (ZMod 2)) : MvPolynomial V (ZMod 2) := x + y + x * y

def cN (c : Fin N → Clause V) (q : ℕ) : Clause V := if h : q < N then c ⟨q, h⟩ else ∅

noncomputable def U (c : Fin N → Clause V) : ℕ → MvPolynomial V (ZMod 2)
  | 0 => clausePoly (cN c 0)
  | q + 1 => if same cap ww q then orP (U c q) (clausePoly (cN c (q + 1)))
      else clausePoly (cN c (q + 1))

noncomputable def PF (c : Fin N → Clause V) (j : Fin t) (i : Fin N) : MvPolynomial V (ZMod 2) :=
  if bin i = j then U cap ww c i.val else 0

end Constr

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr2

variable {V : Type} [DecidableEq V] {N t : ℕ}

def Qp (wq : Fin t → ℕ) (D : Clause (WW V N t)) : Prop :=
  ∀ j : Fin t, (∃ i : Fin t, ((Sum.inr i : WW V N t), menuF j i) ∈ D) ∨
    (D.filter (fun l => l.1.isLeft)).card ≤ wq j

theorem Q_gam (wq : Fin t → ℕ) (k : Fin t) (D : Clause (WW V N t)) (hk : gam k ∈ D)
    (hw : (D.filter (fun l => l.1.isLeft)).card ≤ wq k) : Qp wq D := by
  intro j
  by_cases hj : k = j
  · subst hj; exact Or.inr hw
  · left; refine ⟨k, ?_⟩
    have : menuF j k = false := by simp [menuF, hj]
    rw [this]; exact hk

theorem Q_all (wq : Fin t → ℕ) (D : Clause (WW V N t))
    (hw : ∀ j, (D.filter (fun l => l.1.isLeft)).card ≤ wq j) : Qp wq D :=
  fun j => Or.inr (hw j)

theorem left_card_le (D E : Clause (WW V N t)) (h : ∀ l ∈ D, l.1.isLeft → l ∈ E) :
    (D.filter (fun l => l.1.isLeft)).card ≤ E.card :=
  Finset.card_le_card (fun l hl => by
    rw [Finset.mem_filter] at hl; exact h l hl.1 hl.2)

theorem uaux1 {α : Type} [DecidableEq α] (X A R : Finset α) (hA : A ⊆ R) :
    (X ∪ A) ∪ R = X ∪ R := by
  rw [Finset.union_assoc, Finset.union_eq_right.mpr hA]

theorem uaux2 {α : Type} [DecidableEq α] (X A R : Finset α) (hA : A ⊆ R) :
    R ∪ (X ∪ A) = X ∪ R := by
  rw [Finset.union_comm, uaux1 X A R hA]

variable {cap ww : ℕ → ℕ} {bin : Fin N → Fin t}

theorem gam_mem_Dc (p : Fin N) : gam (bin p) ∈ (Dc bin p : Clause (WW V N t)) := by
  simp [Dc]

theorem Dc_sub_Rc (p : Fin N) : (Dc bin p : Clause (WW V N t)) ⊆ Rc cap ww bin p := by
  unfold Rc; split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl

theorem mem_Rc (p : Fin N) (l : Literal (WW V N t)) (hl : l ∈ Rc cap ww bin p) :
    l = gam (bin p) ∨ l = uL p false ∨ l = uL (pred p) true := by
  unfold Rc Dc at hl
  split_ifs at hl <;> simp at hl <;> tauto

theorem notV_Rc (p : Fin N) (v : V) (b : Bool) :
    ((Sum.inl (Sum.inl v) : WW V N t), b) ∉ Rc cap ww bin p := by
  intro h
  rcases mem_Rc p _ h with h | h | h <;> simp [gam, uL] at h

theorem left_Rc (T : Finset (Literal V)) (p : Fin N) :
    ((T.image liftL ∪ Rc cap ww bin p).filter (fun l => l.1.isLeft)).card ≤ T.card + 2 := by
  refine (left_card_le _ (T.image liftL ∪ {uL p false, uL (pred p) true}) ?_).trans ?_
  · intro l hl hleft
    rcases Finset.mem_union.mp hl with h | h
    · exact Finset.mem_union_left _ h
    · rcases mem_Rc p l h with h | h | h
      · subst h; simp [gam] at hleft
      · subst h; simp
      · subst h; simp
  · refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := T) (f := (liftL : Literal V → Literal (WW V N t)))
    have h2 := Finset.card_le_two (a := (uL p false : Literal (WW V N t))) (b := uL (pred p) true)
    omega

theorem left_Xc (p : Fin N) (l : Literal V) :
    ((Xc cap ww bin p l).filter (fun l => l.1.isLeft)).card ≤ 3 := by
  refine (left_card_le _ {negL l, uL p false, uL (pred p) true} ?_).trans Finset.card_le_three
  intro x hx hleft
  rcases Finset.mem_insert.mp hx with h | h
  · subst h; simp
  · rcases mem_Rc p x h with h | h | h
    · subst h; simp [gam] at hleft
    · subst h; simp
    · subst h; simp

theorem bin_pred (hbin : ∀ p, (bin p).val = (st cap ww p.val).1) (p : Fin N)
    (h : cont cap ww p) : bin (pred p) = bin p := by
  apply Fin.ext
  rw [hbin, hbin]
  have e := st_succ_same (cap := cap) (ww := ww) (p.val - 1) h.2
  have hp : p.val - 1 + 1 = p.val := by omega
  rw [hp] at e
  simp only [pred]
  rw [e]

end Constr2

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr3

theorem add_axioms {W : Type} [DecidableEq W] {S : Set (Clause W)} {Q : Clause W → Prop}
    {ι : Type} [DecidableEq ι] (g : ι → Clause W) (s : Finset ι)
    (hs : ∀ i ∈ s, g i ∈ S ∧ Q (g i)) : ∀ π : List (Clause W), Good S Q π →
      ∃ π' : List (Clause W), Good S Q π' ∧ (∀ D ∈ π, D ∈ π') ∧ (∀ i ∈ s, g i ∈ π') ∧
        π'.length ≤ π.length + s.card := by
  induction s using Finset.induction_on with
  | empty => intro π hπ; exact ⟨π, hπ, fun _ h => h, by simp, by simp⟩
  | insert i s hi ih =>
    intro π hπ
    obtain ⟨π1, h1, h2, h3, h4⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj)) π hπ
    have hi' := hs i (Finset.mem_insert_self i s)
    refine ⟨g i :: π1, good_ax h1 hi'.1 hi'.2, fun D hD => List.mem_cons_of_mem _ (h2 D hD),
      fun j hj => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h3 j hj)
    · rw [Finset.card_insert_of_notMem hi]; simp only [List.length_cons]; omega

variable {V : Type} [DecidableEq V] {N t : ℕ}
variable {cap ww : ℕ → ℕ} {bin : Fin N → Fin t}

abbrev SS (cap ww : ℕ → ℕ) (bin : Fin N → Fin t) (F : Set (Clause V)) (c : Fin N → Clause V) :
    Set (Clause (WW V N t)) :=
  Set.image (fun cl : Clause V => cl.image liftL) F ∪ ↑(extraF cap ww bin c)

theorem Xc_mem (F : Set (Clause V)) (c : Fin N → Clause V) (p : Fin N) (l : Literal V)
    (hl : l ∈ c p) : Xc cap ww bin p l ∈ SS cap ww bin F c := by
  right
  simp only [extraF, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton]
  left; left
  simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
    Finset.mem_coe, Finset.mem_image]
  exact ⟨p, l, hl, rfl⟩

theorem Wd_mem (F : Set (Clause V)) (c : Fin N → Clause V) (k : Fin t) :
    Wd cap ww bin k ∈ SS cap ww bin F c := by
  right
  simp only [extraF, Finset.coe_union, Finset.coe_singleton]
  left; right
  simp

theorem Mf_mem (F : Set (Clause V)) (c : Fin N → Clause V) :
    (Mf : Clause (WW V N t)) ∈ SS cap ww bin F c := by
  right
  simp [extraF]

theorem stepA (hbin : ∀ p, (bin p).val = (st cap ww p.val).1)
    (F : Set (Clause V)) (c : Fin N → Clause V) (Δ : ℕ) (wq : Fin t → ℕ)
    (hwq : ∀ j, Δ + 2 ≤ wq j) (p : Fin N) (hne : (c p).Nonempty) (hcF : c p ∈ F)
    (hcw : (c p).card ≤ Δ) (π : List (Clause (WW V N t)))
    (hπ : Good (SS cap ww bin F c) (Qp wq) π)
    (hprev : cont cap ww p → Dc bin (pred p) ∈ π) :
    ∃ π' : List (Clause (WW V N t)), Good (SS cap ww bin F c) (Qp wq) π' ∧
      (∀ D ∈ π, D ∈ π') ∧ Dc bin p ∈ π' ∧ π'.length ≤ π.length + (2 * Δ + 2) := by
  obtain ⟨π1, g1, s1, m1, l1⟩ := add_axioms (S := SS cap ww bin F c) (Q := Qp wq)
    (Xc cap ww bin p) (c p) (fun l hl => ⟨Xc_mem F c p l hl,
      Q_gam wq (bin p) _ (Finset.mem_insert_of_mem (Dc_sub_Rc p (gam_mem_Dc p)))
        ((left_Xc p l).trans (by have := hwq (bin p); have := hne.card_pos; omega))⟩) π hπ
  have hlift : (c p).image (liftL : Literal V → Literal (WW V N t)) ∈ SS cap ww bin F c :=
    Or.inl ⟨c p, hcF, rfl⟩
  have qlift : Qp wq ((c p).image (liftL : Literal V → Literal (WW V N t))) := by
    apply Q_all; intro j
    refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    have := hwq j; omega
  have g2 := good_ax g1 hlift qlift
  obtain ⟨π3, g3, s3, m3, l3⟩ := elim_gen (S := SS cap ww bin F c) (Q := Qp wq) liftL (c p)
    (Rc cap ww bin p) (Xc cap ww bin p)
    (by
      intro l _ T A hA hlT
      obtain ⟨v, b⟩ := l
      have hnotT : ∀ b', ((Sum.inl (Sum.inl v) : WW V N t), b') ∈ T.image liftL → (v, b') ∈ T := by
        intro b' hb'
        obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hb'
        have : y = (v, b') := liftL_inj hyeq
        rw [← this]; exact hy
      cases b
      · right
        have h := res_helper ((Sum.inl (Sum.inl v) : WW V N t)) (Rc cap ww bin p) (T.image liftL ∪ A)
          (notV_Rc p v true)
          (by
            intro hm
            rcases Finset.mem_union.mp hm with hm | hm
            · exact hlT (hnotT false hm)
            · exact notV_Rc p v false (hA hm))
        rw [uaux2 _ _ _ hA] at h
        exact h
      · left
        have h := res_helper ((Sum.inl (Sum.inl v) : WW V N t)) (T.image liftL ∪ A) (Rc cap ww bin p)
          (by
            intro hm
            rcases Finset.mem_union.mp hm with hm | hm
            · exact hlT (hnotT true hm)
            · exact notV_Rc p v true (hA hm))
          (notV_Rc p v false)
        rw [uaux1 _ _ _ hA] at h
        exact h)
    (by
      intro T hT
      refine Q_gam wq (bin p) _ (Finset.mem_union_right _ (Dc_sub_Rc p (gam_mem_Dc p))) ?_
      refine (left_Rc T p).trans ?_
      have := Finset.card_le_card hT
      have := hwq (bin p); omega)
    (c p) subset_rfl ∅ (Finset.empty_subset _)
    (fun h => absurd h (Finset.nonempty_iff_ne_empty.mp hne)) _ g2
    (fun l hl => List.mem_cons_of_mem _ (m1 l hl))
    (by rw [Finset.union_empty]; exact List.mem_cons_self)
  simp only [List.length_cons] at l3
  by_cases hc : cont cap ww p
  · have hR : (Rc cap ww bin p : Clause (WW V N t)) = insert (uL (pred p) true) (Dc bin p) := by
      unfold Rc; rw [if_pos hc]
    have hbp := bin_pred hbin p hc
    have hD : (Dc bin (pred p) : Clause (WW V N t)) = insert (uL (pred p) false) {gam (bin p)} := by
      unfold Dc; rw [hbp]; exact Finset.pair_comm _ _
    have hres := res_helper ((Sum.inl (Sum.inr (pred p)) : WW V N t)) (Dc bin p) {gam (bin p)}
      (by simp [Dc, uL, gam]) (by simp [uL, gam])
    rw [Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (gam_mem_Dc p))] at hres
    have hDp : Qp wq (Dc bin p : Clause (WW V N t)) := by
      refine Q_gam wq (bin p) _ (gam_mem_Dc p) ((left_card_le _ {uL p false} ?_).trans ?_)
      · intro l hl hleft
        simp only [Dc, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · simp [gam] at hleft
        · simp
      · have := hwq (bin p); simp; omega
    refine ⟨Dc bin p :: π3, good_res g3 (hR ▸ m3) (hD ▸ s3 _ (List.mem_cons_of_mem _ (s1 _ (hprev hc))))
      hres hDp, fun D hD => List.mem_cons_of_mem _ (s3 D (List.mem_cons_of_mem _ (s1 D hD))),
      List.mem_cons_self, ?_⟩
    simp only [List.length_cons]; omega
  · have hR : (Rc cap ww bin p : Clause (WW V N t)) = Dc bin p := by unfold Rc; rw [if_neg hc]
    refine ⟨π3, g3, fun D hD => s3 D (List.mem_cons_of_mem _ (s1 D hD)), hR ▸ m3, ?_⟩
    omega

end Constr3

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr4

variable {V : Type} [DecidableEq V] {N t : ℕ}
variable {cap ww : ℕ → ℕ} {bin : Fin N → Fin t}

theorem stepAll (hbin : ∀ p, (bin p).val = (st cap ww p.val).1)
    (F : Set (Clause V)) (c : Fin N → Clause V) (Δ : ℕ) (wq : Fin t → ℕ)
    (hwq : ∀ j, Δ + 2 ≤ wq j)
    (hall : ∀ p, (c p).Nonempty ∧ c p ∈ F ∧ (c p).card ≤ Δ) :
    ∀ m, m ≤ N → ∃ π : List (Clause (WW V N t)), Good (SS cap ww bin F c) (Qp wq) π ∧
      (∀ q : Fin N, q.val < m → Dc bin q ∈ π) ∧ π.length ≤ m * (2 * Δ + 2) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨[], good_nil, fun q hq => absurd hq (Nat.not_lt_zero _), by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨π, g, hD, hl⟩ := ih (by omega)
    let p : Fin N := ⟨m, by omega⟩
    obtain ⟨π', g', s', m', l'⟩ := stepA hbin F c Δ wq hwq p (hall p).1 (hall p).2.1
      (hall p).2.2 π g (fun hc => hD _ (by have h0 := hc.1; change 0 < m at h0; show m - 1 < m; omega))
    refine ⟨π', g', fun q hq => ?_, ?_⟩
    · by_cases hqm : q.val < m
      · exact s' _ (hD q hqm)
      · have : q = p := Fin.ext (by simp only [p]; omega)
        rw [this]; exact m'
    · rw [Nat.succ_mul]; omega

theorem stepB (F : Set (Clause V)) (c : Fin N → Clause V) (wq : Fin t → ℕ) (k : Fin t)
    (hwr : (roots cap ww bin k).card ≤ wq k) (π : List (Clause (WW V N t)))
    (hπ : Good (SS cap ww bin F c) (Qp wq) π) (hD : ∀ q, Dc bin q ∈ π) :
    ∃ π' : List (Clause (WW V N t)), Good (SS cap ww bin F c) (Qp wq) π' ∧
      (∀ D ∈ π, D ∈ π') ∧ {gam k} ∈ π' ∧
      π'.length ≤ π.length + (1 + (roots cap ww bin k).card) := by
  have qW : Qp wq (Wd cap ww bin k : Clause (WW V N t)) := by
    refine Q_gam wq k _ (Finset.mem_insert_self _ _) ?_
    refine (left_card_le _ ((roots cap ww bin k).image (fun p : Fin N => (uL p true : Literal (WW V N t)))) ?_).trans
      (Finset.card_image_le.trans hwr)
    intro l hl hleft
    rcases Finset.mem_insert.mp hl with h | h
    · subst h; simp [gam] at hleft
    · exact h
  have g2 := good_ax hπ (Wd_mem F c k) qW
  have hroot : ∀ r ∈ roots cap ww bin k, bin r = k := by
    intro r hr; exact (Finset.mem_filter.mp hr).2.2
  obtain ⟨π3, g3, s3, m3, l3⟩ := elim_gen (S := SS cap ww bin F c) (Q := Qp wq)
    (fun p : Fin N => (uL p true : Literal (WW V N t))) (roots cap ww bin k) {gam k} (Dc bin)
    (by
      intro r hr T A hA hrT
      left
      have hDr : (Dc bin r : Clause (WW V N t)) = insert (uL r false) {gam k} := by
        unfold Dc; rw [hroot r hr]; exact Finset.pair_comm _ _
      rw [hDr]
      have h := res_helper ((Sum.inl (Sum.inr r) : WW V N t))
        (T.image (fun p : Fin N => (uL p true : Literal (WW V N t))) ∪ A) {gam k}
        (by
          intro hm
          rcases Finset.mem_union.mp hm with hm | hm
          · obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hm
            have : y = r := uL_inj true hyeq
            exact hrT (this ▸ hy)
          · have := hA hm; simp [gam] at this)
        (by simp [gam])
      rw [uaux1 _ _ _ hA] at h
      exact h)
    (by
      intro T hT
      refine Q_gam wq k _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)) ?_
      refine (left_card_le _ (T.image (fun p : Fin N => (uL p true : Literal (WW V N t)))) ?_).trans
        (Finset.card_image_le.trans ((Finset.card_le_card hT).trans hwr))
      intro l hl hleft
      rcases Finset.mem_union.mp hl with h | h
      · exact h
      · rw [Finset.mem_singleton] at h; subst h; simp [gam] at hleft)
    (roots cap ww bin k) subset_rfl {gam k} subset_rfl (fun _ => rfl) _ g2
    (fun q _ => List.mem_cons_of_mem _ (hD q))
    (by
      have : Wd cap ww bin k = (roots cap ww bin k).image (fun p : Fin N => (uL p true : Literal (WW V N t))) ∪ {gam k} := by
        unfold Wd; rw [Finset.insert_eq, Finset.union_comm]
      rw [← this]; exact List.mem_cons_self)
  refine ⟨π3, g3, fun D hD => s3 D (List.mem_cons_of_mem _ hD), m3, ?_⟩
  simp only [List.length_cons] at l3; omega

theorem stepBall (F : Set (Clause V)) (c : Fin N → Clause V) (wq : Fin t → ℕ)
    (hwr : ∀ k, (roots cap ww bin k).card ≤ wq k) (π : List (Clause (WW V N t)))
    (hπ : Good (SS cap ww bin F c) (Qp wq) π) (hD : ∀ q, Dc bin q ∈ π) :
    ∀ Ks : Finset (Fin t), ∃ π' : List (Clause (WW V N t)), Good (SS cap ww bin F c) (Qp wq) π' ∧
      (∀ D ∈ π, D ∈ π') ∧ (∀ k ∈ Ks, {gam k} ∈ π') ∧
      π'.length ≤ π.length + ∑ k ∈ Ks, (1 + (roots cap ww bin k).card) := by
  intro Ks
  induction Ks using Finset.induction_on with
  | empty => exact ⟨π, hπ, fun _ h => h, by simp, by simp⟩
  | insert k Ks hk ih =>
    obtain ⟨π1, g1, s1, m1, l1⟩ := ih
    obtain ⟨π2, g2, s2, m2, l2⟩ := stepB F c wq k (hwr k) π1 g1 (fun q => s1 _ (hD q))
    refine ⟨π2, g2, fun D hD => s2 D (s1 D hD), fun k' hk' => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hk' with rfl | hk'
      · exact m2
      · exact s2 _ (m1 k' hk')
    · rw [Finset.sum_insert hk]; omega

theorem stepC (F : Set (Clause V)) (c : Fin N → Clause V) (wq : Fin t → ℕ)
    (π : List (Clause (WW V N t)))
    (hπ : Good (SS cap ww bin F c) (Qp wq) π) (hG : ∀ k, {gam k} ∈ π) :
    ∃ π' : List (Clause (WW V N t)), Good (SS cap ww bin F c) (Qp wq) π' ∧
      (∅ : Clause (WW V N t)) ∈ π' ∧ π'.length ≤ π.length + (1 + t) := by
  let f : Fin t → Literal (WW V N t) := fun k => ((Sum.inr k : WW V N t), true)
  have hz : ∀ T : Finset (Fin t), ((T.image f ∪ ∅).filter (fun l => l.1.isLeft)).card = 0 := by
    intro T
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    simp only [Finset.union_empty, Finset.mem_image, f] at hx
    obtain ⟨k, _, rfl⟩ := hx
    simp
  have qM : Qp wq (Mf : Clause (WW V N t)) := by
    apply Q_all; intro j
    have := hz Finset.univ
    rw [Finset.union_empty] at this
    unfold Mf; rw [this]; exact Nat.zero_le _
  have g2 := good_ax hπ (Mf_mem F c) qM
  obtain ⟨π3, g3, _, m3, l3⟩ := elim_gen (S := SS cap ww bin F c) (Q := Qp wq)
    f Finset.univ ∅ (fun k => {gam k})
    (by
      intro k _ T A hA hkT
      left
      have hA0 : A = ∅ := Finset.subset_empty.mp hA
      subst hA0
      have e : ({gam k} : Clause (WW V N t)) = insert (gam k) ∅ := by simp
      rw [e]
      have h := res_helper ((Sum.inr k : WW V N t)) (T.image f ∪ ∅) ∅
        (by
          intro hm
          simp only [Finset.union_empty, Finset.mem_image, f, Prod.mk.injEq, Sum.inr.injEq,
            and_true] at hm
          obtain ⟨y, hy, rfl⟩ := hm
          exact hkT hy)
        (by simp)
      rw [Finset.union_empty (T.image f ∪ ∅)] at h
      exact h)
    (by intro T _; apply Q_all; intro j; rw [hz T]; exact Nat.zero_le _)
    Finset.univ subset_rfl ∅ subset_rfl (fun _ => rfl) _ g2
    (fun k _ => List.mem_cons_of_mem _ (hG k))
    (by rw [Finset.union_empty]; exact List.mem_cons_self)
  refine ⟨π3, g3, m3, ?_⟩
  simp only [List.length_cons, Finset.card_univ, Fintype.card_fin] at l3; omega

end Constr4

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr5

variable {V : Type} [DecidableEq V] {N t : ℕ}
variable {cap ww : ℕ → ℕ} {bin : Fin N → Fin t}

theorem roots_card_le (hbin : ∀ p, (bin p).val = (st cap ww p.val).1)
    (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (k : Fin t) :
    (roots cap ww bin k).card ≤ ww k.val := by
  have h := Finset.card_le_card_of_injOn (s := roots cap ww bin k) (t := Finset.range (ww k.val))
    (fun p => (st cap ww p.val).2.1)
    (by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.2
      have := (st_inv hcap hww p.val).2
      rw [← hbin p, hp'] at this
      simpa using this)
    (by
      intro p hp q hq hpq
      simp only at hpq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      have hk : (st cap ww p.val).1 = (st cap ww q.val).1 := by
        rw [← hbin p, ← hbin q, hp'.2, hq'.2]
      rcases lt_trichotomy p.val q.val with hlt | heq | hgt
      · exfalso
        have hs := same_of_eq hcap hww p.val q.val hlt hk hpq
        rcases hp'.1 with h1 | h1
        · have := q.isLt; omega
        · exact h1 hs
      · exact Fin.ext heq
      · exfalso
        have hs := same_of_eq hcap hww q.val p.val hgt hk.symm hpq.symm
        rcases hq'.1 with h1 | h1
        · have := p.isLt; omega
        · exact h1 hs)
  simpa using h

theorem clausePoly_deg (cl : Clause V) : (clausePoly cl).totalDegree ≤ cl.card := by
  unfold clausePoly
  refine (totalDegree_finsetProd _ _).trans ?_
  have : ∀ l ∈ cl, ((if l.2 = true then 1 + X l.1 else X l.1 : MvPolynomial V (ZMod 2))).totalDegree ≤ 1 := by
    intro l _
    split_ifs
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · simp
      · rw [totalDegree_X]
    · rw [totalDegree_X]
  calc _ ≤ ∑ l ∈ cl, 1 := Finset.sum_le_sum this
    _ = cl.card := by simp

theorem orP_deg (x y : MvPolynomial V (ZMod 2)) :
    (orP x y).totalDegree ≤ x.totalDegree + y.totalDegree := by
  unfold orP
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_add _ _).trans (max_le (by omega) (by omega))
  · exact totalDegree_mul _ _

theorem cN_fin (c : Fin N → Clause V) (p : Fin N) : cN c p.val = c p := by
  simp [cN]

theorem U_deg (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (c : Fin N → Clause V) (Δ : ℕ)
    (hcw : ∀ p, (c p).card ≤ Δ) (q : ℕ) :
    (U cap ww c q).totalDegree ≤ Δ * ((st cap ww q).2.2 + 1) := by
  have hcN : ∀ q, (clausePoly (cN c q)).totalDegree ≤ Δ := by
    intro q
    refine (clausePoly_deg _).trans ?_
    unfold cN; split_ifs
    · exact hcw _
    · simp
  induction q with
  | zero => simp only [U]; have := hcN 0; simp [st]; omega
  | succ q ih =>
    simp only [U]
    split_ifs with hs
    · rw [st_succ_same q hs]
      refine (orP_deg _ _).trans ?_
      have := hcN (q + 1)
      simp only
      nlinarith
    · rw [st_succ_not q hs]
      have := hcN (q + 1); omega

theorem PF_deg (hbin : ∀ p, (bin p).val = (st cap ww p.val).1)
    (hcap : ∀ k, 1 ≤ cap k) (hww : ∀ k, 1 ≤ ww k) (c : Fin N → Clause V) (Δ : ℕ)
    (hcw : ∀ p, (c p).card ≤ Δ) (j : Fin t) (i : Fin N) :
    (PF cap ww bin c j i).totalDegree ≤ Δ * cap j.val := by
  unfold PF
  split_ifs with h
  · refine (U_deg hcap hww c Δ hcw i.val).trans ?_
    have := (st_inv hcap hww i.val).1
    rw [← hbin i, h] at this
    exact Nat.mul_le_mul_left _ (by omega)
  · simp

theorem U_fin (c : Fin N → Clause V) (p : Fin N) :
    U cap ww c p.val = if cont cap ww p then orP (U cap ww c (p.val - 1)) (clausePoly (c p))
      else clausePoly (c p) := by
  obtain ⟨m, hm⟩ := p
  cases m with
  | zero =>
    simp only [U, cont, lt_irrefl, false_and, if_false]
    rw [← cN_fin c ⟨0, hm⟩]
  | succ m =>
    simp only [U, cont, Nat.succ_pos, true_and, Nat.add_sub_cancel]
    rw [← cN_fin c ⟨m + 1, hm⟩]

theorem clausePoly_eval_sat (x : V → Bool) (cl : Clause V) (h : ClauseSat x cl) :
    eval (fun v => ((x v).toNat : ZMod 2)) (clausePoly cl) = 0 := by
  obtain ⟨l, hl, hsat⟩ := h
  unfold clausePoly
  rw [map_prod]
  refine Finset.prod_eq_zero hl ?_
  rw [← hsat]
  cases hx : x l.1 <;> simp [hx] <;> first | rfl | decide

theorem clausePoly_eval_unsat (x : V → Bool) (cl : Clause V) (h : ¬ ClauseSat x cl) :
    eval (fun v => ((x v).toNat : ZMod 2)) (clausePoly cl) = 1 := by
  unfold clausePoly
  rw [map_prod]
  refine Finset.prod_eq_one fun l hl => ?_
  have hne : x l.1 ≠ l.2 := fun he => h ⟨l, hl, he⟩
  obtain ⟨v, b⟩ := l
  simp only at hne ⊢
  cases b <;> cases hx : x v <;> simp_all <;> first | rfl | decide

theorem orP_eval (e : V → ZMod 2) (x y : MvPolynomial V (ZMod 2)) :
    eval e (orP x y) = eval e x + eval e y + eval e x * eval e y := by
  simp [orP]

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

theorem walk (hbin : ∀ p, (bin p).val = (st cap ww p.val).1) (c : Fin N → Clause V)
    (e : V → ZMod 2) :
    ∀ m, ∀ q : Fin N, N - q.val = m → eval e (U cap ww c q.val) = 1 →
      ∃ r : Fin N, root cap ww r ∧ bin r = bin q ∧ eval e (U cap ww c r.val) = 1 := by
  intro m
  induction m with
  | zero => intro q hq; have := q.isLt; omega
  | succ m ih =>
    intro q hq hU
    by_cases hr : root cap ww q
    · exact ⟨q, hr, rfl, hU⟩
    · simp only [root, not_or, not_not] at hr
      have hlt : q.val + 1 < N := by have := q.isLt; omega
      let q' : Fin N := ⟨q.val + 1, hlt⟩
      have hc : cont cap ww q' := ⟨Nat.succ_pos _, by simpa [q'] using hr.2⟩
      have hpq : pred q' = q := Fin.ext (by simp [pred, q'])
      have hb := bin_pred hbin q' hc
      rw [hpq] at hb
      have hU' : eval e (U cap ww c q'.val) = 1 := by
        rw [U_fin c q', if_pos hc, orP_eval]
        have : q'.val - 1 = q.val := by simp [q']
        rw [this, hU]
        rcases zmod2_cases (eval e (clausePoly (c q'))) with h | h <;> rw [h] <;> decide
      obtain ⟨r, h1, h2, h3⟩ := ih q' (by simp only [q']; omega) hU'
      exact ⟨r, h1, h2.trans hb.symm, h3⟩

end Constr5

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr6

variable {V : Type} [DecidableEq V] {N t : ℕ}
variable {cap ww : ℕ → ℕ} {bin : Fin N → Fin t}

theorem cover (hbin : ∀ p, (bin p).val = (st cap ww p.val).1) (c : Fin N → Clause V)
    (hunsat : ∀ x : V → Bool, ∃ q, ¬ ClauseSat x (c q)) (x : V → Bool) :
    ∃ j : Fin t, Satisfies (Sum.elim (Sum.elim x (fun i : Fin N => decide
      (eval (fun v => (x v).toNat : V → ZMod 2) (PF cap ww bin c j i) = 1))) (menuF j))
      (↑(extraF cap ww bin c) : Set (Clause (WW V N t))) := by
  obtain ⟨q, hq⟩ := hunsat x
  let e : V → ZMod 2 := fun v => (x v).toNat
  refine ⟨bin q, ?_⟩
  set j := bin q with hj
  set asg := Sum.elim (Sum.elim x (fun i : Fin N => decide (eval e (PF cap ww bin c j i) = 1)))
    (menuF j) with hasg
  have hγ : ∀ k, k ≠ j → ∀ D : Clause (WW V N t), gam k ∈ D → ClauseSat asg D := by
    intro k hk D hD
    refine ⟨gam k, hD, ?_⟩
    simp [gam, hasg, menuF, hk]
  have hPF : ∀ p : Fin N, bin p = j → PF cap ww bin c j p = U cap ww c p.val := by
    intro p hp; simp [PF, hp]
  have hauxT : ∀ p : Fin N, bin p = j → eval e (U cap ww c p.val) = 1 →
      ∀ D : Clause (WW V N t), uL p true ∈ D → ClauseSat asg D := by
    intro p hp hu D hD
    refine ⟨uL p true, hD, ?_⟩
    simp only [uL, hasg, Sum.elim_inl, Sum.elim_inr]
    rw [hPF p hp]; simp only [e] at hu ⊢; simp [hu]
  have hauxF : ∀ p : Fin N, bin p = j → eval e (U cap ww c p.val) ≠ 1 →
      ∀ D : Clause (WW V N t), uL p false ∈ D → ClauseSat asg D := by
    intro p hp hu D hD
    refine ⟨uL p false, hD, ?_⟩
    simp only [uL, hasg, Sum.elim_inl, Sum.elim_inr]
    rw [hPF p hp]; simp only [e] at hu ⊢; simp [hu]
  intro D hD
  simp only [extraF, Finset.coe_union, Finset.coe_singleton, Set.mem_union,
    Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image] at hD
  rcases hD with (⟨p, l, hl, rfl⟩ | ⟨k, rfl⟩) | rfl
  · by_cases hb : bin p = j
    · by_cases hu : eval e (U cap ww c p.val) = 1
      · have hcl : eval e (clausePoly (c p)) = 1 → ClauseSat asg (Xc cap ww bin p l) := by
          intro h1
          have hns : ¬ ClauseSat x (c p) := by
            intro hs; have := clausePoly_eval_sat x (c p) hs
            simp only [e] at h1; rw [this] at h1; exact absurd h1 (by decide)
          refine ⟨negL l, Finset.mem_insert_self _ _, ?_⟩
          have hne : x l.1 ≠ l.2 := fun he => hns ⟨l, hl, he⟩
          simp only [negL, hasg, Sum.elim_inl]
          cases h2 : l.2 <;> cases h3 : x l.1 <;> simp_all
        rw [U_fin c p] at hu
        split_ifs at hu with hc
        · rw [orP_eval] at hu
          rcases zmod2_cases (eval e (U cap ww c (p.val - 1))) with h0 | h0
          · rw [h0] at hu
            apply hcl
            rcases zmod2_cases (eval e (clausePoly (c p))) with h4 | h4
            · rw [h4] at hu; exact absurd hu (by decide)
            · exact h4
          · have hbp := bin_pred hbin p hc
            refine hauxT (pred p) (hbp.trans hb) ?_ _ ?_
            · simpa [pred] using h0
            · unfold Xc Rc; rw [if_pos hc]
              exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact hcl hu
      · refine hauxF p hb hu _ ?_
        unfold Xc
        exact Finset.mem_insert_of_mem (Dc_sub_Rc p (by simp [Dc]))
    · exact hγ (bin p) hb _ (Finset.mem_insert_of_mem (Dc_sub_Rc p (gam_mem_Dc p)))
  · by_cases hk : k = j
    · subst hk
      have hq1 : eval e (U cap ww c q.val) = 1 := by
        rw [U_fin c q]
        have h1 : eval e (clausePoly (c q)) = 1 := clausePoly_eval_unsat x (c q) hq
        split_ifs
        · rw [orP_eval, h1]
          rcases zmod2_cases (eval e (U cap ww c (q.val - 1))) with h | h <;> rw [h] <;> decide
        · exact h1
      obtain ⟨r, hr1, hr2, hr3⟩ := walk hbin c e (N - q.val) q rfl hq1
      refine hauxT r hr2 hr3 _ ?_
      unfold Wd
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, ?_, rfl⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1, hr2⟩
    · exact hγ k hk _ (Finset.mem_insert_self _ _)
  · refine ⟨((Sum.inr j : WW V N t), true), ?_, ?_⟩
    · unfold Mf; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · simp [hasg, menuF]

theorem extra_card (c : Fin N → Clause V) (Δ : ℕ) (hcw : ∀ p, (c p).card ≤ Δ) :
    (extraF cap ww bin c).card ≤ N * Δ + t + 1 := by
  unfold extraF
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)) ?_
  · refine Finset.card_biUnion_le.trans ?_
    calc ∑ p, ((c p).image (Xc cap ww bin p)).card ≤ ∑ _p : Fin N, Δ :=
          Finset.sum_le_sum fun p _ => Finset.card_image_le.trans (hcw p)
      _ = N * Δ := by simp
  · exact Finset.card_image_le.trans (by simp)
  · simp

end Constr6

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity

section Constr7

variable {V : Type} [DecidableEq V] {N t : ℕ}
variable {cap ww : ℕ → ℕ} {bin : Fin N → Fin t}

theorem roots_sum : ∑ k, (roots cap ww bin k).card ≤ N := by
  have h := Finset.card_eq_sum_card_fiberwise (f := bin)
    (s := Finset.univ.filter (fun p : Fin N => root cap ww p)) (t := Finset.univ)
    (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  have e : ∀ k, (roots cap ww bin k) =
      (Finset.univ.filter (fun p : Fin N => root cap ww p)).filter (fun p => bin p = k) := by
    intro k; unfold roots; rw [Finset.filter_filter]
  simp only [e]
  rw [← h]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem refut (hbin : ∀ p, (bin p).val = (st cap ww p.val).1)
    (F : Set (Clause V)) (c : Fin N → Clause V) (Δ : ℕ) (wq : Fin t → ℕ)
    (hwq : ∀ j, Δ + 2 ≤ wq j) (hwr : ∀ k, (roots cap ww bin k).card ≤ wq k)
    (hall : ∀ p, (c p).Nonempty ∧ c p ∈ F ∧ (c p).card ≤ Δ) :
    ∃ π : List (Clause (WW V N t)), IsRefutation (SS cap ww bin F c) π ∧
      (∀ D ∈ π, Qp wq D) ∧ π.length ≤ N * (2 * Δ + 2) + (t + N) + (1 + t) := by
  obtain ⟨π1, g1, h1, l1⟩ := stepAll hbin F c Δ wq hwq hall N le_rfl
  obtain ⟨π2, g2, _, h2, l2⟩ := stepBall F c wq hwr π1 g1 (fun q => h1 q q.isLt) Finset.univ
  obtain ⟨π3, g3, h3, l3⟩ := stepC F c wq π2 g2 (fun k => h2 k (Finset.mem_univ _))
  refine ⟨π3, ⟨g3.1, h3⟩, g3.2, ?_⟩
  have hs : ∑ k ∈ Finset.univ, (1 + (roots cap ww bin k).card) ≤ t + N := by
    rw [Finset.sum_add_distrib]
    have := roots_sum (cap := cap) (ww := ww) (bin := bin)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  omega

end Constr7

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open PEqualNP.ProofComplexity PEqualNP.Expanders

section Graph

variable {n : ℕ} (G : BipGraph (n + 1) n)

abbrev Pairs : Type := {pr : GEdge G × GEdge G // pr.1.1.2 = pr.2.1.2 ∧ pr.1.1.1 ≠ pr.2.1.1}

abbrev Item : Type := Fin (n + 1) ⊕ Pairs G

def pcl (p : Fin (n + 1)) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = p ∧ l.2 = true)

def icl : Item G → Clause (GEdge G)
  | Sum.inl p => pcl G p
  | Sum.inr pr => {(pr.1.1, false), (pr.1.2, false)}

theorem icl_mem (i : Item G) : icl G i ∈ funGraphPHP G := by
  rcases i with p | pr
  · left; left; exact ⟨p, rfl⟩
  · left; right; exact ⟨pr.1.1, pr.1.2, pr.2.1, pr.2.2, rfl⟩

theorem icl_card (b : ℕ) (hb : LeftDegLe G b) (i : Item G) : (icl G i).card ≤ b + 2 := by
  rcases i with p | pr
  · have h := Finset.card_le_card_of_injOn (s := pcl G p) (t := G p)
      (fun l => l.1.1.2)
      (by
        intro l hl
        have hl' := (Finset.mem_filter.mp hl).2
        have := l.1.2
        rw [hl'.1] at this
        exact this)
      (by
        intro l hl l' hl' heq
        have h1 := (Finset.mem_filter.mp hl).2
        have h2 := (Finset.mem_filter.mp hl').2
        simp only at heq
        apply Prod.ext
        · apply Subtype.ext
          exact Prod.ext (h1.1.trans h2.1.symm) heq
        · exact h1.2.trans h2.2.symm)
    have := hb p
    simp only [icl]
    omega
  · simp only [icl]
    have := Finset.card_le_two (a := ((pr.1.1, false) : Literal (GEdge G))) (b := (pr.1.2, false))
    omega

theorem icl_unsat (x : GEdge G → Bool) : ∃ i : Item G, ¬ ClauseSat x (icl G i) := by
  by_contra hall
  push_neg at hall
  have hp : ∀ p : Fin (n + 1), ∃ e : GEdge G, e.1.1 = p ∧ x e = true := by
    intro p
    obtain ⟨l, hl, hx⟩ := hall (Sum.inl p)
    have hl' := (Finset.mem_filter.mp hl).2
    refine ⟨l.1, hl'.1, ?_⟩
    rw [hx, hl'.2]
  choose f hf using hp
  have hinj : Function.Injective (fun p => (f p).1.2) := by
    intro p p' hpp
    by_contra hne
    have hne' : (f p).1.1 ≠ (f p').1.1 := by rw [(hf p).1, (hf p').1]; exact hne
    obtain ⟨l, hl, hx⟩ := hall (Sum.inr ⟨(f p, f p'), hpp, hne'⟩)
    simp only [icl, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp only at hx; rw [(hf p).2] at hx; exact absurd hx (by decide)
    · simp only at hx; rw [(hf p').2] at hx; exact absurd hx (by decide)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem edge_card (b : ℕ) (hb : LeftDegLe G b) : Fintype.card (GEdge G) ≤ (n + 1) * b := by
  have e := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (p : Fin (n + 1)) (j : Fin n) => j ∈ G p))
  rw [Fintype.card_sigma] at e
  rw [e]
  calc ∑ p : Fin (n + 1), Fintype.card {j // j ∈ G p} ≤ ∑ _p : Fin (n + 1), b :=
        Finset.sum_le_sum fun p _ => by rw [Fintype.card_coe]; exact hb p
    _ = (n + 1) * b := by simp

theorem pairs_card (b : ℕ) (hb : LeftDegLe G b) (hr : RightDegLe G b) :
    Fintype.card (Pairs G) ≤ (n + 1) * b * b := by
  have e := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (e e' : GEdge G) => e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1))
  rw [Fintype.card_sigma] at e
  rw [e]
  calc ∑ e : GEdge G, Fintype.card {e' : GEdge G // e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1}
        ≤ ∑ _e : GEdge G, b := by
          refine Finset.sum_le_sum fun e _ => ?_
          have h := Fintype.card_le_of_injective
            (fun e' : {e' : GEdge G // e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1} =>
              (⟨e'.1.1.1, by
                unfold rightNbrs
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ _, ?_⟩
                have h := e'.1.2
                rw [← e'.2.1] at h
                exact h⟩ : {q // q ∈ rightNbrs G e.1.2}))
            (by
              intro y z hyz
              simp only [Subtype.mk.injEq] at hyz
              apply Subtype.ext; apply Subtype.ext
              exact Prod.ext hyz (y.2.1.symm.trans z.2.1))
          rw [Fintype.card_coe] at h
          exact h.trans (hr _)
    _ = Fintype.card (GEdge G) * b := by simp
    _ ≤ (n + 1) * b * b := Nat.mul_le_mul_right _ (edge_card G b hb)

theorem item_card (b : ℕ) (hb : LeftDegLe G b) (hr : RightDegLe G b) :
    Fintype.card (Item G) ≤ (n + 1) * (1 + b * b) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  have := pairs_card G b hb hr
  nlinarith

end Graph

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Expanders

section Upper

theorem main_upper {n : ℕ} (G : BipGraph (n + 1) n) (b : ℕ) (hb : LeftDegLe G b)
    (hr : RightDegLe G b) (hn : 1 ≤ n) (t : ℕ) (d w : Fin t → ℕ)
    (hdw : ∀ j, 1 ≤ d j ∧ 1 ≤ w j) (hsum : n ≤ ∑ j, d j * w j) (Cc : ℕ)
    (hC1 : (b + 2) * (2 * (1 + (b + 2) * (b + 2))) ≤ Cc)
    (hC3 : (3 * (b + 2) + 6) * (2 * (1 + (b + 2) * (b + 2))) ≤ Cc) :
    ∃ (a h : ℕ) (P : Fin t → Fin a → MvPolynomial (GEdge G) (ZMod 2))
      (menu : Fin t → Fin h → Bool)
      (extra : Finset (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))
      (π : List (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h))),
      ((∀ j i, (P j i).totalDegree ≤ Cc * d j) ∧
      (∀ x : GEdge G → Bool, ∃ j : Fin t,
        Satisfies (Sum.elim (Sum.elim x (fun i : Fin a => decide
          (eval (fun v => (x v).toNat : GEdge G → ZMod 2) (P j i) = 1))) (menu j))
          (↑extra : Set (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))) ∧
      IsRefutation (Set.image (fun cl : Clause (GEdge G) =>
        cl.image (fun l => ((Sum.inl (Sum.inl l.1) : (GEdge G ⊕ Fin a) ⊕ Fin h), l.2)))
        (funGraphPHP G) ∪ (↑extra : Set (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))) π ∧
      ∀ (j : Fin t) D, D ∈ π →
        (∃ i : Fin h, ((Sum.inr i : (GEdge G ⊕ Fin a) ⊕ Fin h), menu j i) ∈ D) ∨
        (D.filter (fun l => l.1.isLeft)).card ≤ Cc * w j) ∧
      a + h + extra.card + π.length ≤ Cc * (n + t) := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at hsum; omega
    · exact h0
  set Δ := b + 2 with hΔ
  set K := 2 * (1 + Δ * Δ) with hK
  have hK2 : 2 ≤ K := by rw [hK]; omega
  have hK4 : 4 ≤ K := by rw [hK, hΔ]; nlinarith
  have hΔK : Δ + 2 ≤ Δ * K :=
    le_trans (by omega : Δ + 2 ≤ Δ * 4) (Nat.mul_le_mul_left _ hK4)
  have hΔC : Δ + 2 ≤ Cc := le_trans hΔK hC1
  by_cases hne : ∀ i : Item G, (icl G i).Nonempty
  swap
  · push_neg at hne
    obtain ⟨i, hi⟩ := hne
    refine ⟨0, 0, fun _ i => Fin.elim0 i, fun _ i => Fin.elim0 i, ∅, [∅], ⟨fun _ i => Fin.elim0 i,
      fun _ => ⟨⟨0, ht⟩, fun C hC => by simp at hC⟩, ⟨.ax .nil (Or.inl ⟨icl G i, icl_mem G i, ?_⟩),
      List.mem_singleton_self _⟩, fun j D hD => Or.inr ?_⟩, ?_⟩
    · rw [hi]; simp
    · rw [List.mem_singleton] at hD; subst hD; simp
    · simp only [Finset.card_empty, List.length_singleton]
      have : 1 ≤ Cc := by nlinarith
      nlinarith
  -- the main construction
  let e := Fintype.equivFin (Item G)
  let N := Fintype.card (Item G)
  let c : Fin N → Clause (GEdge G) := fun q => icl G (e.symm q)
  have hNle : N ≤ K * n := by
    have := item_card G b hb hr
    have h2 : (n + 1) * (1 + b * b) ≤ K * n := by rw [hK, hΔ]; nlinarith
    omega
  let dd : ℕ → ℕ := fun k => if h : k < t then d ⟨k, h⟩ else 1
  let wwF : ℕ → ℕ := fun k => if h : k < t then w ⟨k, h⟩ else 1
  let cap : ℕ → ℕ := fun k => K * dd k
  have hcap : ∀ k, 1 ≤ cap k := by
    intro k
    have : 1 ≤ dd k := by
      simp only [dd]; split_ifs with h
      · exact (hdw _).1
      · exact le_rfl
    simp only [cap]; nlinarith
  have hww : ∀ k, 1 ≤ wwF k := by
    intro k; simp only [wwF]; split_ifs with h
    · exact (hdw _).2
    · exact le_rfl
  have hsumK : ∑ i ∈ Finset.range t, cap i * wwF i = K * ∑ j, d j * w j := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => cap i * wwF i) t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cap, dd, wwF, dif_pos j.isLt]
    ring
  have hNcap : N ≤ ∑ i ∈ Finset.range t, cap i * wwF i := by
    rw [hsumK]; exact hNle.trans (Nat.mul_le_mul_left _ hsum)
  have hlt : ∀ p : Fin N, (st cap wwF p.val).1 < t := fun p =>
    st_bin_lt hcap hww t p.val (lt_of_lt_of_le p.isLt hNcap)
  let bin : Fin N → Fin t := fun p => ⟨(st cap wwF p.val).1, hlt p⟩
  have hbin : ∀ p, (bin p).val = (st cap wwF p.val).1 := fun p => rfl
  let wq : Fin t → ℕ := fun j => (Δ + 2) * w j
  have hwq : ∀ j, Δ + 2 ≤ wq j := by
    intro j; have := (hdw j).2; simp only [wq]; nlinarith
  have hwr : ∀ k, (roots cap wwF bin k).card ≤ wq k := by
    intro k
    refine (roots_card_le hbin hcap hww k).trans ?_
    simp only [wwF, dif_pos k.isLt, wq]
    nlinarith
  have hall : ∀ p, (c p).Nonempty ∧ c p ∈ funGraphPHP G ∧ (c p).card ≤ Δ :=
    fun p => ⟨hne _, icl_mem G _, icl_card G b hb _⟩
  have hunsat : ∀ x : GEdge G → Bool, ∃ q, ¬ ClauseSat x (c q) := by
    intro x
    obtain ⟨i, hi⟩ := icl_unsat G x
    exact ⟨e i, by simp only [c, Equiv.symm_apply_apply]; exact hi⟩
  obtain ⟨π, hπ, hQ, hlen⟩ := refut hbin (funGraphPHP G) c Δ wq hwq hwr hall
  have hxc := extra_card (cap := cap) (ww := wwF) (bin := bin) c Δ (fun p => (hall p).2.2)
  refine ⟨N, t, PF cap wwF bin c, menuF, extraF cap wwF bin c, π,
    ⟨fun j i => ?_, fun x => cover hbin c hunsat x, hπ, fun j D hD => ?_⟩, ?_⟩
  · refine (PF_deg hbin hcap hww c Δ (fun p => (hall p).2.2) j i).trans ?_
    simp only [cap, dd, dif_pos j.isLt]
    have := Nat.mul_le_mul_right (d j) hC1
    nlinarith
  · rcases hQ D hD j with h1 | h1
    · exact Or.inl h1
    · right
      refine h1.trans ?_
      simp only [wq]
      exact Nat.mul_le_mul_right _ hΔC
  · have h3 : N * (3 * Δ + 4) + 4 * t + 2 ≤ (3 * Δ + 6) * K * (n + t) := by
      have h4 : N * (3 * Δ + 4) ≤ (K * n) * (3 * Δ + 6) :=
        Nat.mul_le_mul hNle (by omega)
      have h5 : 4 * t + 2 ≤ (3 * Δ + 6) * K * t := by nlinarith
      nlinarith
    have h6 : (3 * Δ + 6) * K * (n + t) ≤ Cc * (n + t) := Nat.mul_le_mul_right _ hC3
    have h7 : N + t + (extraF cap wwF bin c).card + π.length ≤ N * (3 * Δ + 4) + 4 * t + 2 := by
      nlinarith
    omega

end Upper

end PEqualNP.Outside.L_pcx_383
namespace PEqualNP.Outside.L_pcx_383

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Expanders

section Main

theorem main_lower {n : ℕ} (G : BipGraph (n + 1) n) (b s₀ : ℕ) (hs0 : 0 < s₀) (hn : s₀ ≤ n)
    (hexp : IsBdryExpander G (n / s₀) 2) (hb : LeftDegLe G b) (t : ℕ) (d w : Fin t → ℕ)
    (a h : ℕ) (P : Fin t → Fin a → MvPolynomial (GEdge G) (ZMod 2)) (menu : Fin t → Fin h → Bool)
    (extra : Set (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))
    (π : List (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))
    (hd1 : ∀ j, 1 ≤ d j)
    (hdeg : ∀ j i, (P j i).totalDegree ≤ d j)
    (hcov : ∀ x : GEdge G → Bool, ∃ j : Fin t,
      Satisfies (Sum.elim (Sum.elim x (fun i : Fin a => decide
        (eval (fun v => (x v).toNat : GEdge G → ZMod 2) (P j i) = 1))) (menu j)) extra)
    (href : IsRefutation (Set.image (fun cl : Clause (GEdge G) =>
      cl.image (fun l => ((Sum.inl (Sum.inl l.1) : (GEdge G ⊕ Fin a) ⊕ Fin h), l.2)))
      (funGraphPHP G) ∪ extra) π)
    (hw : ∀ (j : Fin t) D, D ∈ π →
      (∃ i : Fin h, ((Sum.inr i : (GEdge G ⊕ Fin a) ⊕ Fin h), menu j i) ∈ D) ∨
      (D.filter (fun l => l.1.isLeft)).card ≤ w j) :
    n ≤ (2 * b * s₀) * ∑ j, d j * w j := by
  let E : Fin t → Set (MvPolynomial (GEdge G) (ZMod 2)) :=
    fun j => Set.image (cprod (phi (P j) (menu j))) extra
  have branches : ∀ j, PCRefutable (cnfSystem (funGraphPHP G) ∪ E j) (2 * (d j * w j)) := by
    intro j
    have hs := sim (phi (P j) (menu j)) (phi_neg (P j) (menu j)) _
      (cnfSystem (funGraphPHP G) ∪ E j) (d j * w j) π href.1
      (by
        intro D hD
        rcases hw j D hD with ⟨i, hi⟩ | hc
        · exact Or.inl (cprod_zero (P j) (menu j) D i hi)
        · right
          intro T hT
          refine (cprod_deg (P j) (menu j) (d j) (hd1 j) (hdeg j) T).trans ?_
          refine Nat.mul_le_mul_left _ ((Finset.card_le_card ?_).trans hc)
          exact Finset.filter_subset_filter _ hT)
      (by
        intro D _ hS
        rcases hS with ⟨cl, hcl, rfl⟩ | hS
        · exact Or.inl (Or.inr ⟨cl, hcl, cprod_lift (P j) (menu j) cl⟩)
        · exact Or.inr ⟨D, hS, rfl⟩)
      ∅ href.2
    unfold cprod at hs
    rw [Finset.prod_empty] at hs
    exact hs
  have cover' : ∀ x : GEdge G → ZMod 2, ∃ j : Fin t, ∀ e ∈ E j, eval x e = 0 := by
    intro x
    let xb : GEdge G → Bool := fun v => decide (x v = 1)
    have hx : (fun v => ((xb v).toNat : ZMod 2)) = x := by
      funext v
      rcases zmod2_cases (x v) with h0 | h0 <;> simp [xb, h0]
    obtain ⟨j, hj⟩ := hcov xb
    refine ⟨j, ?_⟩
    rintro e ⟨D, hD, rfl⟩
    rw [← hx]
    exact cprod_eval (P j) (menu j) xb D (hj D hD)
  have hPC := PEqualNP.Outside.L_pcx_383_aux.C382.combine (cnfSystem (funGraphPHP G)) t E
    (fun j => 2 * (d j * w j)) (fun v => Or.inl ⟨v, rfl⟩) cover' branches
  have hlt : ¬ (b * ∑ j, 2 * (d j * w j) ≤ n / s₀) := fun hle =>
    PEqualNP.Outside.L_pcx_383_aux.L049 (n + 1) n G (n / s₀) b _ hexp hb
      (Nat.div_pos hn hs0) hle hPC
  push_neg at hlt
  rw [Nat.div_lt_iff_lt_mul hs0] at hlt
  have e : b * (∑ j, 2 * (d j * w j)) * s₀ = (2 * b * s₀) * ∑ j, d j * w j := by
    rw [← Finset.mul_sum]; ring
  omega

end Main

end PEqualNP.Outside.L_pcx_383
theorem PEqualNP.Outside.L_pcx_383 :
∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.Expanders.funGraphPHP G
    let valid := fun (a h t : ℕ) (d w : Fin t → ℕ)
        (P : Fin t → Fin a → MvPolynomial V (ZMod 2)) (menu : Fin t → Fin h → Bool)
        (extra : Set (PEqualNP.ProofComplexity.Clause ((V ⊕ Fin a) ⊕ Fin h)))
        (π : List (PEqualNP.ProofComplexity.Clause ((V ⊕ Fin a) ⊕ Fin h))) =>
      let W := (V ⊕ Fin a) ⊕ Fin h
      let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
        cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W), l.2))
      (∀ j i, (P j i).totalDegree ≤ d j) ∧
      (∀ x : V → Bool, ∃ j : Fin t,
        let aux := fun i : Fin a => decide
          (MvPolynomial.eval (fun v => (x v).toNat : V → ZMod 2) (P j i) = 1)
        PEqualNP.ProofComplexity.Satisfies (Sum.elim (Sum.elim x aux) (menu j)) extra) ∧
      PEqualNP.ProofComplexity.IsRefutation (Set.image lift F ∪ extra) π ∧
      ∀ (j : Fin t) D, D ∈ π →
        (∃ i : Fin h, ((Sum.inr i : W), menu j i) ∈ D) ∨
        (D.filter (fun l => l.1.isLeft)).card ≤ w j
    ∀ (t : ℕ) (d w : Fin t → ℕ), (∀ j, 1 ≤ d j ∧ 1 ≤ w j) →
      (∀ (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
          (menu : Fin t → Fin h → Bool) extra π, valid a h t d w P menu extra π →
          n ≤ C * ∑ j, d j * w j) ∧
      (n ≤ ∑ j, d j * w j →
        ∃ (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
          (menu : Fin t → Fin h → Bool)
          (extra : Finset (PEqualNP.ProofComplexity.Clause ((V ⊕ Fin a) ⊕ Fin h)))
          (π : List (PEqualNP.ProofComplexity.Clause ((V ⊕ Fin a) ⊕ Fin h))),
          valid a h t (fun j => C*d j) (fun j => C*w j) P menu
            (↑extra : Set (PEqualNP.ProofComplexity.Clause ((V ⊕ Fin a) ⊕ Fin h))) π ∧
          a + h + extra.card + π.length ≤ C*(n+t)) := by
  obtain ⟨b, s₀, n₁, hs0, hexp⟩ := PEqualNP.Outside.L_pcx_383_aux.L043
  refine ⟨(3 * (b + 2) + 6) * (2 * (1 + (b + 2) * (b + 2))) + 2 * b * s₀, n₁ + s₀ + 1,
    by nlinarith, fun n hn => ?_⟩
  obtain ⟨G, hl, hr, hx⟩ := hexp n (by omega)
  have hbC : b ≤ (3 * (b + 2) + 6) * (2 * (1 + (b + 2) * (b + 2))) + 2 * b * s₀ := by nlinarith
  refine ⟨G, fun i => (hl i).trans hbC, fun j => (hr j).trans hbC, ?_⟩
  dsimp only
  intro t d w hdw
  refine ⟨fun a h P menu extra π hv => ?_, fun hs => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hv
    have := PEqualNP.Outside.L_pcx_383.main_lower G b s₀ hs0 (by omega) hx hl t d w a h P menu
      extra π (fun j => (hdw j).1) h1 h2 h3 h4
    exact this.trans (Nat.mul_le_mul_right _ (by omega))
  · exact PEqualNP.Outside.L_pcx_383.main_upper G b hl hr (by omega) t d w hdw hs _
      (le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.le_add_right _ _))
      (Nat.le_add_right _ _)
