import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_388_aux

open PEqualNP.ProofComplexity

section S0
namespace Helpers

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

end Helpers
end S0

section S1
namespace Helpers

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

end Helpers
end S1

section S2
namespace Helpers

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

end Helpers
end S2

section S3
namespace Helpers

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

end Helpers
end S3

section S4
namespace Helpers

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

end Helpers
end S4

section S5


theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

end S5

section S6
namespace Helpers

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

end Helpers
end S6

section S7
namespace Helpers

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

end Helpers
end S7

section S8
namespace Helpers

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

end Helpers
end S8

section S9
namespace Helpers

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

end Helpers
end S9

section S10
namespace Helpers

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

end Helpers
end S10

section S11
namespace Helpers

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

end Helpers
end S11

section S12
namespace Helpers

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

end Helpers
end S12

section S13
namespace Helpers

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

end Helpers
end S13

section S14
namespace Helpers

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

end Helpers
end S14

section S15
namespace Helpers

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

end Helpers
end S15

section S16
namespace Helpers

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

end Helpers
end S16

section S17


theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB

end S17

section Body388

open MvPolynomial PEqualNP.Expanders PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_388_aux.Helpers

private lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  revert c; decide

private lemma zmod2_mul_self (c : ZMod 2) : c * c = c := by
  revert c; decide

private lemma totalDegree_X_le {σ : Type} (v : σ) :
    (X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 1 := by
  rw [totalDegree_X]

private lemma zmod2_pow_eq (c : ZMod 2) (k : ℕ) (hk : 0 < k) : c ^ k = c := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      rw [pow_succ, ih (by omega), zmod2_mul_self]

private lemma zmod2_coeff_eq_one {σ : Type} {p : MvPolynomial σ (ZMod 2)} {a : σ →₀ ℕ}
    (ha : a ∈ p.support) : p.coeff a = 1 := by
  have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
  rcases zmod2_cases (p.coeff a) with h | h
  · exact (h0 h).elim
  · exact h

private lemma exists_linear_sep {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (W : Submodule (ZMod 2) E) {v : E} (hv : v ∉ W) :
    ∃ ℓ : E →ₗ[ZMod 2] ZMod 2, (∀ w ∈ W, ℓ w = 0) ∧ ℓ v = 1 := by
  classical
  let qv : E ⧸ W := W.mkQ v
  have hqv : qv ≠ 0 := by
    intro h
    exact hv ((Submodule.Quotient.mk_eq_zero W).mp h)
  let L : Submodule (ZMod 2) (E ⧸ W) := Submodule.span (ZMod 2) {qv}
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl L
  let proj : (E ⧸ W) →ₗ[ZMod 2] L := Submodule.linearProjOfIsCompl L K hK
  let e : (ZMod 2) ≃ₗ[ZMod 2] L :=
    LinearEquiv.ofBijective
      ((LinearMap.toSpanSingleton (ZMod 2) (E ⧸ W) qv).codRestrict L
        (fun c => Submodule.smul_mem L c (Submodule.subset_span (Set.mem_singleton qv))))
      ⟨by
        intro a b hab
        have h1 : a • qv = b • qv := congrArg Subtype.val hab
        have h2 : (a - b) • qv = 0 := by rw [sub_smul, h1, sub_self]
        rcases smul_eq_zero.mp h2 with h | h
        · exact sub_eq_zero.mp h
        · exact (hqv h).elim,
      by
        rintro ⟨y, hy⟩
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
        exact ⟨c, Subtype.ext hc⟩⟩
  let ℓ : E →ₗ[ZMod 2] ZMod 2 := (e.symm.toLinearMap.comp proj).comp W.mkQ
  refine ⟨ℓ, ?_, ?_⟩
  · intro w hw
    have h0 : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hw
    simp [ℓ, h0]
  · have hmem : qv ∈ L := Submodule.subset_span (Set.mem_singleton qv)
    have hp : proj qv = ⟨qv, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hK ⟨qv, hmem⟩
    have he1 : e 1 = ⟨qv, hmem⟩ := by
      apply Subtype.ext
      change (1 : ZMod 2) • qv = qv
      exact one_smul _ _
    change e.symm (proj qv) = 1
    rw [hp, ← he1, LinearEquiv.symm_apply_apply]

private noncomputable def sqFreeExp {σ : Type} (a : σ →₀ ℕ) : σ →₀ ℕ :=
  a.mapRange (fun e => if e = 0 then 0 else 1) rfl

private lemma sqFreeExp_le {σ : Type} (a : σ →₀ ℕ) (v : σ) : sqFreeExp a v ≤ a v := by
  simp only [sqFreeExp, Finsupp.mapRange_apply]
  split_ifs with h
  · omega
  · omega

private lemma sqFreeExp_le_one {σ : Type} (a : σ →₀ ℕ) (v : σ) : sqFreeExp a v ≤ 1 := by
  simp only [sqFreeExp, Finsupp.mapRange_apply]
  split_ifs <;> omega

private lemma sqFreeExp_sum_le {σ : Type} (a : σ →₀ ℕ) :
    (sqFreeExp a).sum (fun _ e => e) ≤ a.sum (fun _ e => e) := by
  classical
  have hsub : (sqFreeExp a).support ⊆ a.support := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv ⊢
    intro h0
    apply hv
    simp [sqFreeExp, h0]
  calc (sqFreeExp a).sum (fun _ e => e)
      = ∑ v ∈ (sqFreeExp a).support, sqFreeExp a v := rfl
    _ ≤ ∑ v ∈ (sqFreeExp a).support, a v := Finset.sum_le_sum fun v _ => sqFreeExp_le a v
    _ ≤ ∑ v ∈ a.support, a v := Finset.sum_le_sum_of_subset hsub

private lemma eval_monomial_sqFree {σ : Type} (a : σ →₀ ℕ) (x : σ → ZMod 2) :
    eval x (monomial (sqFreeExp a) (1 : ZMod 2)) = eval x (monomial a (1 : ZMod 2)) := by
  classical
  rw [eval_monomial, eval_monomial, one_mul, one_mul]
  have hsupp : (sqFreeExp a).support = a.support := by
    ext v
    simp only [Finsupp.mem_support_iff, sqFreeExp, Finsupp.mapRange_apply]
    split_ifs with h <;> simp [h]
  simp only [Finsupp.prod, hsupp]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hne : a v ≠ 0 := Finsupp.mem_support_iff.mp hv
  simp only [sqFreeExp, Finsupp.mapRange_apply, hne, ↓reduceIte, pow_one]
  exact (zmod2_pow_eq (x v) (a v) (Nat.pos_of_ne_zero hne)).symm

private lemma pcDerivable_X_pow_sub_X {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))}
    (hbool : ∀ v : σ, X v * X v + X v ∈ F) (v : σ) :
    ∀ k : ℕ, 1 ≤ k → PCDerivable F k (X v ^ k + X v) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have : (X v : MvPolynomial σ (ZMod 2)) ^ 1 + X v = 0 := by
        rw [pow_one, CharTwo.add_self_eq_zero]
      rw [this]
      exact .zero
    | succ m =>
      have h1 : PCDerivable F (m + 1) (X v ^ (m + 1) + X v) := ih (by omega)
      have h2 : PCDerivable F (m + 2) (X v * (X v ^ (m + 1) + X v)) := by
        refine .mulX v (pcDerivable_mono h1 (by omega) subset_rfl) ?_
        have hd1 : (X v ^ (m + 1) + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ m + 1 := by
          refine (totalDegree_add _ _).trans (max_le ?_ ?_)
          · exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
          · exact (totalDegree_X_le v).trans (by omega)
        exact (totalDegree_mul _ _).trans (by have := totalDegree_X_le v; omega)
      have h3 : PCDerivable F (m + 2) (X v * X v + X v) := by
        refine .ax (hbool v) ?_
        refine (totalDegree_add _ _).trans (max_le ?_ ((totalDegree_X_le v).trans (by omega)))
        exact (totalDegree_mul _ _).trans (by have := totalDegree_X_le v; omega)
      have hEq : (X v ^ (m + 2) + X v : MvPolynomial σ (ZMod 2)) = X v * (X v ^ (m + 1) + X v) + (X v * X v + X v) := by
        have hsq : (X v * X v + X v * X v : MvPolynomial σ (ZMod 2)) = 0 := CharTwo.add_self_eq_zero _
        calc (X v ^ (m + 2) + X v : MvPolynomial σ (ZMod 2))
            = X v * X v ^ (m + 1) + (X v * X v + X v * X v) + X v := by rw [hsq, add_zero, pow_succ']
          _ = X v * (X v ^ (m + 1) + X v) + (X v * X v + X v) := by ring
      rw [hEq]
      exact .add h2 h3

private lemma pcDerivable_monomial_sqFree {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))}
    (hbool : ∀ v : σ, X v * X v + X v ∈ F) (a : σ →₀ ℕ) :
    PCDerivable F (a.sum fun _ e => e) (monomial a 1 + monomial (sqFreeExp a) 1) := by
  classical
  induction a using Finsupp.induction with
  | zero =>
    have h0 : sqFreeExp (0 : σ →₀ ℕ) = 0 := by ext v; simp [sqFreeExp]
    rw [h0, CharTwo.add_self_eq_zero]
    exact .zero
  | single_add v e b hv he ih =>
    have hsplit : monomial (Finsupp.single v e + b) (1 : ZMod 2)
        = X v ^ e * monomial b 1 := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    have hsq_split : sqFreeExp (Finsupp.single v e + b)
        = Finsupp.single v 1 + sqFreeExp b := by
      ext u
      by_cases huv : u = v
      · subst huv
        have hb0 : b u = 0 := Finsupp.notMem_support_iff.mp hv
        simp [sqFreeExp, hb0, he]
      · simp only [sqFreeExp, Finsupp.mapRange_apply, Finsupp.add_apply,
          Finsupp.single_apply, if_neg (Ne.symm huv), zero_add]
    have hsq_mul : monomial (sqFreeExp (Finsupp.single v e + b)) (1 : ZMod 2)
        = X v * monomial (sqFreeExp b) 1 := by
      rw [hsq_split, X, monomial_mul_monomial, one_mul]
    have hsum : (Finsupp.single v e + b).sum (fun _ k => k) = e + b.sum (fun _ k => k) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [hsum, hsplit, hsq_mul]
    have hEq : X v ^ e * monomial b (1 : ZMod 2) + X v * monomial (sqFreeExp b) 1
        = monomial b 1 * (X v ^ e + X v) + X v * (monomial b 1 + monomial (sqFreeExp b) 1) := by
      have hz : (X v * monomial b (1 : ZMod 2) + X v * monomial b 1 : MvPolynomial σ (ZMod 2)) = 0 :=
        CharTwo.add_self_eq_zero _
      calc (X v ^ e * monomial b (1 : ZMod 2) + X v * monomial (sqFreeExp b) 1 : MvPolynomial σ (ZMod 2))
          = X v ^ e * monomial b 1 + (X v * monomial b 1 + X v * monomial b 1) + X v * monomial (sqFreeExp b) 1 := by
            rw [hz, add_zero]
        _ = monomial b 1 * (X v ^ e + X v) + X v * (monomial b 1 + monomial (sqFreeExp b) 1) := by ring
    rw [hEq]
    have h1 : PCDerivable F (e + b.sum fun _ k => k) (monomial b 1 * (X v ^ e + X v)) := by
      have hx := pcDerivable_X_pow_sub_X hbool v e (Nat.pos_of_ne_zero he)
      have hm := pcDerivable_monomial_mul (B := e + b.sum fun _ k => k) b
        (pcDerivable_mono hx (by omega) subset_rfl) ?_
      · exact hm
      · have hd : (X v ^ e + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ e := by
          refine (totalDegree_add _ _).trans (max_le ?_ ?_)
          · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; omega)
          · exact (totalDegree_X_le v).trans (Nat.pos_of_ne_zero he)
        omega
    have h2 : PCDerivable F (e + b.sum fun _ k => k) (X v * (monomial b 1 + monomial (sqFreeExp b) 1)) := by
      refine .mulX v (pcDerivable_mono ih (by omega) subset_rfl) ?_
      have hd1 : (monomial b (1 : ZMod 2)).totalDegree ≤ b.sum fun _ k => k := totalDegree_monomial_le b 1
      have hd2 : (monomial (sqFreeExp b) (1 : ZMod 2)).totalDegree ≤ b.sum fun _ k => k :=
        (totalDegree_monomial_le _ 1).trans (sqFreeExp_sum_le b)
      have hd := (totalDegree_add _ _).trans (max_le hd1 hd2)
      refine (totalDegree_mul _ _).trans ?_
      have hxle := totalDegree_X_le v
      have hpos := Nat.pos_of_ne_zero he
      omega
    exact .add h1 h2

private lemma multilinear_eq_zero_of_eval_zero {σ : Type} [DecidableEq σ]
    (p : MvPolynomial σ (ZMod 2))
    (hml : ∀ a ∈ p.support, ∀ v, a v ≤ 1)
    (heval : ∀ x : σ → ZMod 2, eval x p = 0) : p = 0 := by
  classical
  by_contra hne
  have hsupp : p.support.Nonempty := by rwa [MvPolynomial.support_nonempty]
  obtain ⟨a, ha, hmin⟩ := p.support.exists_min_image (fun u => u.support.card) hsupp
  let x : σ → ZMod 2 := fun v => if v ∈ a.support then 1 else 0
  have h0 := heval x
  rw [p.as_sum, map_sum] at h0
  have hsingle : ∀ b ∈ p.support, b ≠ a → eval x (monomial b (p.coeff b)) = 0 := by
    intro b hb hba
    rw [eval_monomial]
    have hnot : ¬ (b.support ⊆ a.support) := by
      intro hsub
      have hcard : b.support.card ≤ a.support.card := Finset.card_le_card hsub
      have heq_card : b.support.card = a.support.card := le_antisymm hcard (hmin b hb)
      have heq_supp : b.support = a.support := Finset.eq_of_subset_of_card_le hsub (le_of_eq heq_card.symm)
      apply hba
      ext v
      by_cases hv : v ∈ a.support
      · have hbv : v ∈ b.support := heq_supp ▸ hv
        have ha1 := hml a ha v
        have hb1 := hml b hb v
        have ha0 : a v ≠ 0 := Finsupp.mem_support_iff.mp hv
        have hb0 : b v ≠ 0 := Finsupp.mem_support_iff.mp hbv
        omega
      · have hbv : v ∉ b.support := heq_supp ▸ hv
        rw [Finsupp.notMem_support_iff.mp hv, Finsupp.notMem_support_iff.mp hbv]
    obtain ⟨v, hvb, hva⟩ := Finset.not_subset.mp hnot
    have hbv_pos : 0 < b v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hvb)
    have hxv : x v = 0 := if_neg hva
    have hprod : b.prod (fun i e => x i ^ e) = 0 := by
      apply Finset.prod_eq_zero hvb
      dsimp only
      rw [hxv, zero_pow (Nat.ne_of_gt hbv_pos)]
    rw [hprod, mul_zero]
  rw [Finset.sum_eq_single a (fun b hb hba => hsingle b hb hba) (fun h => (h ha).elim)] at h0
  rw [eval_monomial] at h0
  have hpa : p.coeff a = 1 := zmod2_coeff_eq_one ha
  have hprod1 : a.prod (fun i e => x i ^ e) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    simp [x, hv]
  rw [hpa, hprod1, mul_one] at h0
  exact one_ne_zero h0

private noncomputable def sqFreePoly {σ : Type} (p : MvPolynomial σ (ZMod 2)) : MvPolynomial σ (ZMod 2) :=
  ∑ a ∈ p.support, monomial (sqFreeExp a) 1

private lemma sqFreePoly_multilinear {σ : Type} (p : MvPolynomial σ (ZMod 2)) :
    ∀ u ∈ (sqFreePoly p).support, ∀ v, u v ≤ 1 := by
  classical
  intro u hu v
  have hmem := MvPolynomial.support_sum (s := p.support) (f := fun a => monomial (sqFreeExp a) (1 : ZMod 2)) hu
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨a, _, hua⟩ := hmem
  have heq : u = sqFreeExp a := by
    by_contra hne
    rw [mem_support_iff, coeff_monomial, if_neg (Ne.symm hne)] at hua
    exact hua rfl
  rw [heq]
  exact sqFreeExp_le_one a v

private lemma sqFreePoly_totalDegree_le {σ : Type} (p : MvPolynomial σ (ZMod 2)) :
    (sqFreePoly p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_finsetSum_le fun a ha => ?_
  exact (totalDegree_monomial_le _ 1).trans ((sqFreeExp_sum_le a).trans (le_totalDegree ha))

private lemma sqFreePoly_eval {σ : Type} (p : MvPolynomial σ (ZMod 2)) (x : σ → ZMod 2) :
    eval x (sqFreePoly p) = eval x p := by
  unfold sqFreePoly
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [zmod2_coeff_eq_one ha, eval_monomial_sqFree]

private lemma pcDerivable_of_eval_zero {σ : Type} [DecidableEq σ]
    {F : Set (MvPolynomial σ (ZMod 2))} (hbool : ∀ v : σ, X v * X v + X v ∈ F)
    {B : ℕ} {p : MvPolynomial σ (ZMod 2)} (hdeg : p.totalDegree ≤ B)
    (heval : ∀ x : σ → ZMod 2, eval x p = 0) : PCDerivable F B p := by
  have hsq0 : sqFreePoly p = 0 :=
    multilinear_eq_zero_of_eval_zero (sqFreePoly p) (sqFreePoly_multilinear p)
      (fun x => (sqFreePoly_eval p x).trans (heval x))
  have hp : p = ∑ a ∈ p.support, (monomial a (1 : ZMod 2) + monomial (sqFreeExp a) 1) := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ a ∈ p.support, monomial a (1 : ZMod 2) = p := by
      conv_rhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun a ha => by rw [zmod2_coeff_eq_one ha]
    rw [h1]
    change p = p + sqFreePoly p
    rw [hsq0, add_zero]
  rw [hp]
  refine pcDerivable_sum p.support _ fun a ha => ?_
  exact pcDerivable_mono (pcDerivable_monomial_sqFree hbool a) ((le_totalDegree ha).trans hdeg) subset_rfl

private lemma eval_bind₁_zmod2 {σ τ : Type} (g : σ → MvPolynomial τ (ZMod 2))
    (P : MvPolynomial σ (ZMod 2)) (x : τ → ZMod 2) :
    eval x (bind₁ g P) = eval (fun j => eval x (g j)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq => simp [ihp, ihq]
  | mul_X p j ih => simp [ih]

private lemma cnfSystem_has_bool {σ : Type} (Φ : Set (Clause σ)) (v : σ) :
    X v * X v + X v ∈ cnfSystem Φ :=
  Or.inl ⟨v, rfl⟩

private lemma pcDerivable_advice {V : Type} [DecidableEq V] {t c D : ℕ}
    {Φ : Set (Clause V)}
    {g : Fin t → MvPolynomial V (ZMod 2)}
    {E : Fin t → Set (MvPolynomial V (ZMod 2))}
    (hg : ∀ j, (g j).totalDegree ≤ c)
    (hE : ∀ (x : V → ZMod 2) j, eval x (g j) = 1 → ∀ e ∈ E j, eval x e = 0)
    (href : ∀ j, PCRefutable (cnfSystem Φ ∪ E j) D) :
    ∀ j : Fin t, PCDerivable (cnfSystem Φ) (D + c) (g j) := by
  intro j
  have hrep := pcDerivable_replay (F := cnfSystem Φ ∪ E j) (G := cnfSystem Φ) (T := 1) (D := D) (s := c)
    (fun v => X v) (fun v => totalDegree_X_le v) (g j) (hg j) ?_ (href j)
  · simp only [one_mul, map_one, mul_one] at hrep
    exact hrep
  · intro a ha hdeg
    have hbind : bind₁ (fun v : V => (X v : MvPolynomial V (ZMod 2))) a = a := by
      simpa using (bind₁_X_left (R := ZMod 2) (σ := V) a)
    rw [hbind, one_mul]
    rcases ha with haF | haE
    · have h1 : PCDerivable (cnfSystem Φ) D a := .ax haF hdeg
      have hm := pcDerivable_mul_left h1 (g j)
      have hmax : max D ((g j).totalDegree + a.totalDegree) ≤ D + c := by
        have := hg j; omega
      exact pcDerivable_mono hm hmax subset_rfl
    · refine pcDerivable_of_eval_zero (cnfSystem_has_bool Φ) ?_ ?_
      · exact (totalDegree_mul _ _).trans (by have := hg j; omega)
      · intro x
        rw [map_mul]
        rcases zmod2_cases (eval x (g j)) with h0 | h1
        · rw [h0, zero_mul]
        · rw [hE x j h1 a haE, mul_zero]

private lemma pcDerivable_bind₁_nonconst {V : Type} {t c D L : ℕ}
    {F : Set (MvPolynomial V (ZMod 2))}
    {g : Fin t → MvPolynomial V (ZMod 2)}
    (hg : ∀ j, (g j).totalDegree ≤ c)
    (hdg : ∀ j, PCDerivable F (D + c) (g j))
    (a : Fin t →₀ ℕ) (ha0 : a ≠ 0) (hadeg : (a.sum fun _ e => e) ≤ L) :
    PCDerivable F (max (D + c) (c * L)) (bind₁ g (monomial a 1)) := by
  classical
  have hne : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr ha0
  obtain ⟨j, hj⟩ := hne
  have haj : 1 ≤ a j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
  let b : Fin t →₀ ℕ := a - Finsupp.single j 1
  have hab : a = b + Finsupp.single j 1 := by
    ext i
    by_cases hi : i = j
    · subst hi; simp [b]; omega
    · simp only [b, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
        if_neg (Ne.symm hi), tsub_zero, add_zero]
  have hbdeg : (b.sum fun _ e => e) + 1 = a.sum (fun _ e => e) := by
    conv_rhs => rw [hab]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmul : bind₁ g (monomial a (1 : ZMod 2)) = bind₁ g (monomial b 1) * g j := by
    rw [hab, ← one_mul (1 : ZMod 2), ← monomial_mul_monomial, map_mul]
    congr 1
    rw [← X, bind₁_X_right]
  rw [hmul]
  have hm := pcDerivable_mul_left (hdg j) (bind₁ g (monomial b 1))
  have hdeg_b : (bind₁ g (monomial b 1)).totalDegree ≤ c * (b.sum fun _ e => e) := by
    exact (totalDegree_bind₁_le g hg _).trans (Nat.mul_le_mul_left c (totalDegree_monomial_le b 1))
  have htot : (bind₁ g (monomial b 1)).totalDegree + (g j).totalDegree ≤ c * L := by
    have := hg j
    calc (bind₁ g (monomial b 1)).totalDegree + (g j).totalDegree
        ≤ c * (b.sum fun _ e => e) + c := Nat.add_le_add hdeg_b this
      _ = c * ((b.sum fun _ e => e) + 1) := by ring
      _ ≤ c * L := Nat.mul_le_mul_left c (by omega)
  exact pcDerivable_mono hm (max_le (le_max_left _ _) (htot.trans (le_max_right _ _))) subset_rfl

private lemma exists_pat_eval_one {V : Type} [DecidableEq V] {t c D L : ℕ}
    {Φ : Set (Clause V)}
    {g : Fin t → MvPolynomial V (ZMod 2)}
    {E : Fin t → Set (MvPolynomial V (ZMod 2))}
    (hg : ∀ j, (g j).totalDegree ≤ c)
    (hE : ∀ (x : V → ZMod 2) j, eval x (g j) = 1 → ∀ e ∈ E j, eval x e = 0)
    (href : ∀ j, PCRefutable (cnfSystem Φ ∪ E j) D)
    (hno : ¬ PCRefutable (cnfSystem Φ) (max (D + c) (c * L)))
    (P : MvPolynomial (Fin t) (ZMod 2)) (hPdeg : P.totalDegree ≤ L)
    (hP0 : eval (fun _ => (0 : ZMod 2)) P = 1) :
    ∃ x : V → ZMod 2, eval (fun j => eval x (g j)) P = 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hall0 : ∀ x : V → ZMod 2, eval x (bind₁ g P) = 0 := by
    intro x
    rw [eval_bind₁_zmod2]
    rcases zmod2_cases (eval (fun j => eval x (g j)) P) with h0 | h1
    · exact h0
    · exact (hnone x h1).elim
  have hdegH : (bind₁ g P).totalDegree ≤ c * L :=
    (totalDegree_bind₁_le g hg P).trans (Nat.mul_le_mul_left c hPdeg)
  have hH : PCDerivable (cnfSystem Φ) (max (D + c) (c * L)) (bind₁ g P) :=
    pcDerivable_mono (pcDerivable_of_eval_zero (cnfSystem_has_bool Φ) hdegH hall0)
      (le_max_right _ _) subset_rfl
  have hdg := pcDerivable_advice hg hE href
  have h0coeff : P.coeff 0 = 1 := by
    have he0 : eval (fun _ => (0 : ZMod 2)) P = P.coeff 0 := by
      rw [P.as_sum, map_sum]
      rw [Finset.sum_eq_single (0 : Fin t →₀ ℕ)]
      · simp [eval_monomial]
      · intro a _ ha0
        rw [eval_monomial]
        obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr ha0
        have hpos : 0 < a j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
        have : a.prod (fun _ e => (0 : ZMod 2) ^ e) = 0 :=
          Finset.prod_eq_zero hj (zero_pow (Nat.ne_of_gt hpos))
        rw [this, mul_zero]
      · intro h0
        simp [Finsupp.notMem_support_iff.mp h0]
    exact he0.symm.trans hP0
  have h0mem : (0 : Fin t →₀ ℕ) ∈ P.support := by
    rw [mem_support_iff, h0coeff]; exact one_ne_zero
  have hsplit : bind₁ g P + 1 = ∑ a ∈ P.support.erase 0, bind₁ g (monomial a 1) := by
    have hsum : bind₁ g P = 1 + ∑ a ∈ P.support.erase 0, bind₁ g (monomial a 1) := by
      conv_lhs => rw [P.as_sum, map_sum, ← Finset.insert_erase h0mem, Finset.sum_insert (Finset.notMem_erase 0 _)]
      congr 1
      · rw [h0coeff]; simp
      · refine Finset.sum_congr rfl fun a ha => ?_
        rw [zmod2_coeff_eq_one (Finset.mem_of_mem_erase ha)]
    rw [hsum]
    calc 1 + (∑ a ∈ P.support.erase 0, bind₁ g (monomial a 1)) + 1
        = (1 + 1) + ∑ a ∈ P.support.erase 0, bind₁ g (monomial a 1) := by ring
      _ = ∑ a ∈ P.support.erase 0, bind₁ g (monomial a 1) := by rw [CharTwo.add_self_eq_zero, zero_add]
  have hH1 : PCDerivable (cnfSystem Φ) (max (D + c) (c * L)) (bind₁ g P + 1) := by
    rw [hsplit]
    refine pcDerivable_sum _ _ fun a ha => ?_
    have ha' := Finset.mem_erase.mp ha
    exact pcDerivable_bind₁_nonconst hg hdg a ha'.1 ((le_totalDegree ha'.2).trans hPdeg)
  have h1 : PCRefutable (cnfSystem Φ) (max (D + c) (c * L)) := by
    have hadd : bind₁ g P + (bind₁ g P + 1) = (1 : MvPolynomial V (ZMod 2)) := by
      calc bind₁ g P + (bind₁ g P + 1)
          = (bind₁ g P + bind₁ g P) + 1 := by ring
        _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
    rw [PCRefutable, ← hadd]
    exact .add hH hH1
  exact hno h1

private def evVec (t L : ℕ) (y : Fin t → ZMod 2) :
    {S : Finset (Fin t) // S.card ≤ L} → ZMod 2 :=
  fun S => ∏ i ∈ S.1, y i

private lemma exists_annihilator {t L : ℕ} (seen : Finset (Fin t → ZMod 2))
    (h0not : (0 : Fin t → ZMod 2) ∉ seen)
    (hsep : ∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ L →
      eval (fun _ => (0 : ZMod 2)) P = 1 → ∃ y ∈ seen, eval y P = 1) :
    ∃ T : Finset (Fin t → ZMod 2), (0 : Fin t → ZMod 2) ∈ T ∧ T ⊆ insert 0 seen ∧
      ∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ L → ∑ y ∈ T, eval y P = 0 := by
  classical
  let W : Submodule (ZMod 2) ({S : Finset (Fin t) // S.card ≤ L} → ZMod 2) :=
    Submodule.span (ZMod 2) (evVec t L '' (seen : Set (Fin t → ZMod 2)))
  have hmem : evVec t L 0 ∈ W := by
    by_contra hnot
    obtain ⟨ℓ, hℓW, hℓ0⟩ := exists_linear_sep W hnot
    let P : MvPolynomial (Fin t) (ZMod 2) :=
      ∑ S : {S : Finset (Fin t) // S.card ≤ L}, C (ℓ (Pi.single S 1)) * ∏ i ∈ S.1, X i
    have hPdeg : P.totalDegree ≤ L := by
      refine totalDegree_finsetSum_le fun S _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_finsetProd _ _).trans ?_
      calc ∑ i ∈ S.1, (X i : MvPolynomial (Fin t) (ZMod 2)).totalDegree
          ≤ ∑ _i ∈ S.1, 1 := Finset.sum_le_sum fun i _ => totalDegree_X_le i
        _ = S.1.card := by simp
        _ ≤ L := S.2
    have hPeval : ∀ y : Fin t → ZMod 2, eval y P = ℓ (evVec t L y) := by
      intro y
      have hdecomp : evVec t L y = ∑ S : {S : Finset (Fin t) // S.card ≤ L},
          (evVec t L y S) • Pi.single S (1 : ZMod 2) := by
        ext S
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hdecomp, map_sum]
      simp only [P, map_sum, map_mul, eval_C, map_prod, eval_X, map_smul, smul_eq_mul, evVec, mul_comm]
    have hP0 : eval (fun _ => (0 : ZMod 2)) P = 1 := by
      rw [show (fun _ : Fin t => (0 : ZMod 2)) = (0 : Fin t → ZMod 2) from rfl, hPeval, hℓ0]
    obtain ⟨y, hy, hy1⟩ := hsep P hPdeg hP0
    have hy0 : eval y P = 0 := by
      rw [hPeval]
      exact hℓW _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hy0] at hy1
    exact zero_ne_one hy1
  rw [Submodule.mem_span_image_iff_exists_fun] at hmem
  obtain ⟨s, hs_sub, c, hc⟩ := hmem
  let S : Finset (Fin t → ZMod 2) := s.filter (fun y => if h : y ∈ s then c ⟨y, h⟩ = 1 else false)
  have hSsub : S ⊆ seen := (Finset.filter_subset _ _).trans (Finset.coe_subset.mp hs_sub)
  have hS0 : (0 : Fin t → ZMod 2) ∉ S := fun h => h0not (hSsub h)
  have hsum_ev : ∑ y ∈ S, evVec t L y = evVec t L 0 := by
    rw [← hc]
    have h1 : ∑ i : s, c i • evVec t L i.1 = ∑ y ∈ s, (if h : y ∈ s then c ⟨y, h⟩ else 0) • evVec t L y := by
      rw [← Finset.sum_attach s]
      refine Finset.sum_congr rfl fun i _ => by simp [i.2]
    rw [h1]
    have h2 : ∑ y ∈ s, (if h : y ∈ s then c ⟨y, h⟩ else 0) • evVec t L y = ∑ y ∈ S, evVec t L y := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [hy, ↓reduceDIte]
      rcases zmod2_cases (c ⟨y, hy⟩) with h0 | h1
      · simp [h0]
      · simp [h1]
    exact h2.symm
  refine ⟨insert 0 S, Finset.mem_insert_self _ _, Finset.insert_subset_insert 0 hSsub, ?_⟩
  intro P hPdeg
  have hT_ev : ∀ M : {M : Finset (Fin t) // M.card ≤ L}, ∑ y ∈ insert 0 S, evVec t L y M = 0 := by
    intro M
    rw [Finset.sum_insert hS0]
    have hm := congrFun hsum_ev M
    rw [Finset.sum_apply] at hm
    rw [hm, zmod2_add_self]
  have hP_sq : ∀ y, eval y P = eval y (sqFreePoly P) := fun y => (sqFreePoly_eval P y).symm
  simp_rw [hP_sq]
  unfold sqFreePoly
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a ha => ?_
  let M : Finset (Fin t) := (sqFreeExp a).support
  have hMcard : M.card ≤ L := by
    have h1 : M.card = (sqFreeExp a).sum (fun _ e => e) := by
      unfold M
      change (sqFreeExp a).support.card = ∑ i ∈ (sqFreeExp a).support, sqFreeExp a i
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : sqFreeExp a i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hle := sqFreeExp_le_one a i
      omega
    exact h1.le.trans ((sqFreeExp_sum_le a).trans ((le_totalDegree ha).trans hPdeg))
  have hmon : ∀ y : Fin t → ZMod 2, eval y (monomial (sqFreeExp a) (1 : ZMod 2)) = evVec t L y ⟨M, hMcard⟩ := by
    intro y
    rw [eval_monomial, one_mul]
    simp only [Finsupp.prod, evVec, M]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : sqFreeExp a i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle := sqFreeExp_le_one a i
    have h1 : sqFreeExp a i = 1 := by omega
    rw [h1, pow_one]
  simp_rw [hmon]
  exact hT_ev ⟨M, hMcard⟩

private lemma ann_filter_mul {t k s : ℕ} {A : Finset (Fin t → ZMod 2)}
    (hA : ∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ k + s → ∑ y ∈ A, eval y P = 0)
    (Q : MvPolynomial (Fin t) (ZMod 2)) (hQ : Q.totalDegree ≤ s) :
    ∀ R : MvPolynomial (Fin t) (ZMod 2), R.totalDegree ≤ k →
      ∑ y ∈ A.filter (fun y => eval y Q = 1), eval y R = 0 := by
  intro R hR
  have hdeg : (R * Q).totalDegree ≤ k + s := (totalDegree_mul _ _).trans (Nat.add_le_add hR hQ)
  have h0 := hA (R * Q) hdeg
  rw [← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul]
  rcases zmod2_cases (eval y Q) with hq0 | hq1
  · simp [hq0]
  · simp [hq1]

private lemma ann_card_ge {t : ℕ} : ∀ (k : ℕ) (A : Finset (Fin t → ZMod 2)),
    A.Nonempty →
    (∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ k → ∑ y ∈ A, eval y P = 0) →
    2 ^ (k + 1) ≤ A.card := by
  intro k
  induction k with
  | zero =>
    intro A hne hA
    have heven : ∑ _y ∈ A, (1 : ZMod 2) = 0 := by
      simpa using hA 1 (by simp)
    have hmod : A.card % 2 = 0 := by
      have hcast : (A.card : ZMod 2) = 0 := by simpa using heven
      have := (ZMod.natCast_eq_zero_iff A.card 2).mp hcast
      omega
    have hpos : 0 < A.card := Finset.card_pos.mpr hne
    omega
  | succ k ih =>
    intro A hne hA
    have hge2 : 2 ≤ A.card := by
      have h0 : ∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ 0 → ∑ y ∈ A, eval y P = 0 :=
        fun P hP => hA P (hP.trans (Nat.zero_le _))
      have heven : ∑ _y ∈ A, (1 : ZMod 2) = 0 := by simpa using h0 1 (by simp)
      have hcast : (A.card : ZMod 2) = 0 := by simpa using heven
      have hdvd : 2 ∣ A.card := (ZMod.natCast_eq_zero_iff A.card 2).mp hcast
      have hpos : 0 < A.card := Finset.card_pos.mpr hne
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hdiff : ∃ i : Fin t, a i ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i, hi⟩ := hdiff
    let A1 := A.filter (fun y => eval y (X i) = 1)
    let A0 := A.filter (fun y => eval y (1 + X i) = 1)
    have hA1_ne : A1.Nonempty := by
      rcases zmod2_cases (a i) with ha0 | ha1
      · rcases zmod2_cases (b i) with hb0 | hb1
        · exact (hi (ha0.trans hb0.symm)).elim
        · exact ⟨b, Finset.mem_filter.mpr ⟨hb, by simp [hb1]⟩⟩
      · exact ⟨a, Finset.mem_filter.mpr ⟨ha, by simp [ha1]⟩⟩
    have hA0_ne : A0.Nonempty := by
      rcases zmod2_cases (a i) with ha0 | ha1
      · exact ⟨a, Finset.mem_filter.mpr ⟨ha, by simp [ha0]⟩⟩
      · rcases zmod2_cases (b i) with hb0 | hb1
        · exact ⟨b, Finset.mem_filter.mpr ⟨hb, by simp [hb0]⟩⟩
        · exact (hi (ha1.trans hb1.symm)).elim
    have hdeg1 : (X i : MvPolynomial (Fin t) (ZMod 2)).totalDegree ≤ 1 := totalDegree_X_le i
    have hdeg0 : (1 + X i : MvPolynomial (Fin t) (ZMod 2)).totalDegree ≤ 1 :=
      (totalDegree_add _ _).trans (max_le (by simp) (totalDegree_X_le i))
    have hc1 : 2 ^ (k + 1) ≤ A1.card := ih A1 hA1_ne (ann_filter_mul hA (X i) hdeg1)
    have hc0 : 2 ^ (k + 1) ≤ A0.card := ih A0 hA0_ne (ann_filter_mul hA (1 + X i) hdeg0)
    have hdisj : Disjoint A0 A1 := by
      rw [Finset.disjoint_left]
      intro y hy0 hy1
      have h0 := (Finset.mem_filter.mp hy0).2
      have h1 := (Finset.mem_filter.mp hy1).2
      simp only [map_add, map_one, eval_X] at h0 h1
      rw [h1] at h0
      exact (by decide : (1 + 1 : ZMod 2) ≠ 1) h0
    have hsub : A0 ∪ A1 ⊆ A := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have htot := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at htot
    rw [pow_succ, mul_two]
    omega

private lemma card_affine_eq {t : ℕ} (a : Fin t → ZMod 2) (W : Submodule (ZMod 2) (Fin t → ZMod 2))
    (A : Finset (Fin t → ZMod 2)) (hA : ∀ y, y ∈ A ↔ y + a ∈ W) :
    A.card = 2 ^ Module.finrank (ZMod 2) W := by
  classical
  have hcardW : Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [← hcardW, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun y => ⟨y.1 + a, (hA y.1).mp y.2⟩
      invFun := fun w => ⟨w.1 + a, (hA (w.1 + a)).mpr (by
        have : w.1 + a + a = w.1 := by ext j; rw [Pi.add_apply, Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
        rw [this]; exact w.2)⟩
      left_inv := fun y => by
        apply Subtype.ext; ext j
        simp [add_assoc, zmod2_add_self]
      right_inv := fun w => by
        apply Subtype.ext; ext j
        simp [add_assoc, zmod2_add_self] }

private lemma ann_eq_affine {t : ℕ} : ∀ (k : ℕ) (A : Finset (Fin t → ZMod 2)),
    A.Nonempty →
    (∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ k → ∑ y ∈ A, eval y P = 0) →
    A.card = 2 ^ (k + 1) →
    ∃ (a : Fin t → ZMod 2) (W : Submodule (ZMod 2) (Fin t → ZMod 2)),
      Module.finrank (ZMod 2) W = k + 1 ∧ ∀ y, y ∈ A ↔ y + a ∈ W := by
  classical
  intro k
  induction k with
  | zero =>
    intro A _ _ hcard
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have hne : b + a ≠ 0 := by
      intro h
      apply hab
      ext j
      have hj := congrFun h j
      simp only [Pi.add_apply, Pi.zero_apply] at hj
      rcases zmod2_cases (a j) with ha | ha <;> rcases zmod2_cases (b j) with hb | hb <;> simp [ha, hb] at hj ⊢
    let W : Submodule (ZMod 2) (Fin t → ZMod 2) := Submodule.span (ZMod 2) {b + a}
    refine ⟨a, W, finrank_span_singleton hne, ?_⟩
    intro y
    rw [Finset.mem_insert, Finset.mem_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by ext j; simp [zmod2_add_self]⟩
      · exact ⟨1, by simp⟩
    · rintro ⟨c, hc⟩
      rcases zmod2_cases c with rfl | rfl
      · left
        ext j
        have hj := congrFun hc j
        simp only [zero_smul, Pi.zero_apply, Pi.add_apply] at hj
        rcases zmod2_cases (y j) with hy | hy <;> rcases zmod2_cases (a j) with ha | ha <;> simp [hy, ha] at hj ⊢
      · right
        ext j
        have hj := congrFun hc j
        simp only [one_smul, Pi.add_apply] at hj
        rcases zmod2_cases (y j) with hy | hy <;> rcases zmod2_cases (a j) with ha | ha <;> rcases zmod2_cases (b j) with hb | hb <;> simp [hy, ha, hb] at hj ⊢
  | succ k ih =>
    intro A _ hA hcard
    have h1lt : 1 < A.card := by
      rw [hcard]
      have h4 : 4 ≤ 2 ^ (k + 1 + 1) :=
        Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by omega) (by omega))
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h1lt
    have hdiff : ∃ i : Fin t, u i ≠ v i := by
      by_contra h; push Not at h; exact huv (funext h)
    obtain ⟨i, hi⟩ := hdiff
    let A1 := A.filter (fun y => eval y (X i) = 1)
    let A0 := A.filter (fun y => eval y (1 + X i) = 1)
    have hA1_ne : A1.Nonempty := by
      rcases zmod2_cases (u i) with hu0 | hu1
      · rcases zmod2_cases (v i) with hv0 | hv1
        · exact (hi (hu0.trans hv0.symm)).elim
        · exact ⟨v, Finset.mem_filter.mpr ⟨hv, by simp [hv1]⟩⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨hu, by simp [hu1]⟩⟩
    have hA0_ne : A0.Nonempty := by
      rcases zmod2_cases (u i) with hu0 | hu1
      · exact ⟨u, Finset.mem_filter.mpr ⟨hu, by simp [hu0]⟩⟩
      · rcases zmod2_cases (v i) with hv0 | hv1
        · exact ⟨v, Finset.mem_filter.mpr ⟨hv, by simp [hv0]⟩⟩
        · exact (hi (hu1.trans hv1.symm)).elim
    have hA1_ann := ann_filter_mul hA (X i) (totalDegree_X_le i)
    have hA0_ann := ann_filter_mul hA (1 + X i) ((totalDegree_add _ _).trans (max_le (by simp) (totalDegree_X_le i)))
    have hge1 := ann_card_ge k A1 hA1_ne hA1_ann
    have hge0 := ann_card_ge k A0 hA0_ne hA0_ann
    have hdisj : Disjoint A0 A1 := by
      rw [Finset.disjoint_left]
      intro y hy0 hy1
      have h0 := (Finset.mem_filter.mp hy0).2
      have h1 := (Finset.mem_filter.mp hy1).2
      simp only [map_add, map_one, eval_X] at h0 h1
      rw [h1] at h0
      exact (by decide : (1 + 1 : ZMod 2) ≠ 1) h0
    have hunion : A0 ∪ A1 = A := by
      ext y
      simp only [A0, A1, Finset.mem_union, Finset.mem_filter, map_add, map_one, eval_X]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases zmod2_cases (y i) with hy0 | hy1
        · left; exact ⟨h, by simp [hy0]⟩
        · right; exact ⟨h, hy1⟩
    have hsumcard : A0.card + A1.card = 2 ^ (k + 2) := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard]
    have hpow : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [pow_succ, mul_two]
    have hc0 : A0.card = 2 ^ (k + 1) := by omega
    have hc1 : A1.card = 2 ^ (k + 1) := by omega
    obtain ⟨a0, W0, hr0, hW0⟩ := ih A0 hA0_ne hA0_ann hc0
    obtain ⟨a1, W1, hr1, hW1⟩ := ih A1 hA1_ne hA1_ann hc1
    have ha0_mem : a0 ∈ A0 := (hW0 a0).mpr (by
      have : a0 + a0 = 0 := by ext j; exact zmod2_add_self (a0 j)
      rw [this]; exact W0.zero_mem)
    have ha1_mem : a1 ∈ A1 := (hW1 a1).mpr (by
      have : a1 + a1 = 0 := by ext j; exact zmod2_add_self (a1 j)
      rw [this]; exact W1.zero_mem)
    have hWeq : W0 = W1 := by
      by_contra hneq
      have hnotle : ¬ (W1 ≤ W0) := fun hle =>
        hneq (Submodule.eq_of_le_of_finrank_eq hle (by rw [hr1, hr0])).symm
      obtain ⟨w, hw1, hw0⟩ := SetLike.not_le_iff_exists.mp hnotle
      obtain ⟨ℓ, hℓ0, hℓw⟩ := exists_linear_sep W0 hw0
      let q : MvPolynomial (Fin t) (ZMod 2) :=
        (∑ j : Fin t, C (ℓ (Pi.single j 1)) * X j) + C (ℓ a0)
      have hqdeg : q.totalDegree ≤ 1 := by
        refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
        refine totalDegree_finsetSum_le fun j _ => ?_
        exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact totalDegree_X_le j)
      have hqeval : ∀ y : Fin t → ZMod 2, eval y q = ℓ y + ℓ a0 := by
        intro y
        have hdecomp : y = ∑ j : Fin t, y j • Pi.single j (1 : ZMod 2) := by
          ext j; simp [Finset.sum_apply, Pi.single_apply]
        have hℓy : ℓ y = ∑ j : Fin t, ℓ (Pi.single j 1) * y j := by
          conv_lhs => rw [hdecomp, map_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
        simp only [q, map_add, map_sum, map_mul, eval_C, eval_X, hℓy]
      let B := A.filter (fun y => eval y q = 1)
      have hBsub : B ⊆ A1 := by
        intro y hy
        obtain ⟨hyA, hyq⟩ := Finset.mem_filter.mp hy
        rw [← hunion, Finset.mem_union] at hyA
        rcases hyA with hy0 | hy1
        · have hyw : y + a0 ∈ W0 := (hW0 y).mp hy0
          have hly : ℓ y + ℓ a0 = 0 := by rw [← map_add]; exact hℓ0 _ hyw
          rw [hqeval, hly] at hyq
          exact (zero_ne_one hyq).elim
        · exact hy1
      have hBne : B.Nonempty := by
        rcases zmod2_cases (ℓ a1 + ℓ a0) with h0 | h1
        · refine ⟨a1 + w, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
          · rw [← hunion, Finset.mem_union]; right
            exact (hW1 (a1 + w)).mpr (by
              have : a1 + w + a1 = w := by ext j; simp only [Pi.add_apply]; rw [add_comm (a1 j), add_assoc, zmod2_add_self, add_zero]
              rw [this]; exact hw1)
          · rw [hqeval, map_add, hℓw]
            calc ℓ a1 + 1 + ℓ a0 = (ℓ a1 + ℓ a0) + 1 := by ring
              _ = 1 := by rw [h0, zero_add]
        · refine ⟨a1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
          · rw [← hunion, Finset.mem_union]; right; exact ha1_mem
          · rw [hqeval]; exact h1
      have hBstrict : B ⊂ A1 := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, ?_⟩
        intro hEq
        have hmiss : ∃ y ∈ A1, eval y q = 0 := by
          rcases zmod2_cases (ℓ a1 + ℓ a0) with h0 | h1
          · exact ⟨a1, ha1_mem, by rw [hqeval]; exact h0⟩
          · refine ⟨a1 + w, (hW1 (a1 + w)).mpr ?_, ?_⟩
            · have : a1 + w + a1 = w := by ext j; simp only [Pi.add_apply]; rw [add_comm (a1 j), add_assoc, zmod2_add_self, add_zero]
              rw [this]; exact hw1
            · rw [hqeval, map_add, hℓw]
              calc ℓ a1 + 1 + ℓ a0 = (ℓ a1 + ℓ a0) + 1 := by ring
                _ = 0 := by rw [h1]; exact zmod2_add_self 1
        obtain ⟨y, hy1, hyq0⟩ := hmiss
        rw [← hEq] at hy1
        have hyq1 := (Finset.mem_filter.mp hy1).2
        rw [hyq0] at hyq1
        exact zero_ne_one hyq1
      have hBlt : B.card < 2 ^ (k + 1) := hc1 ▸ Finset.card_lt_card hBstrict
      have hBge : 2 ^ (k + 1) ≤ B.card := ann_card_ge k B hBne (ann_filter_mul hA q hqdeg)
      omega
    subst hWeq
    have ha0i : a0 i = 0 := by
      have h := (Finset.mem_filter.mp ha0_mem).2
      simp only [map_add, map_one, eval_X] at h
      rcases zmod2_cases (a0 i) with h0 | h1
      · exact h0
      · rw [h1] at h; exact ((by decide : (1 + 1 : ZMod 2) ≠ 1) h).elim
    have ha1i : a1 i = 1 := by
      simpa [A1] using (Finset.mem_filter.mp ha1_mem).2
    have hnotmem : a1 + a0 ∉ W0 := by
      intro hmem
      have h1 : a1 ∈ A0 := (hW0 a1).mpr hmem
      have h2 := (Finset.mem_filter.mp h1).2
      simp only [map_add, map_one, eval_X, ha1i] at h2
      exact (by decide : (1 + 1 : ZMod 2) ≠ 1) h2
    let W := W0 ⊔ Submodule.span (ZMod 2) {a1 + a0}
    refine ⟨a0, W, ?_, ?_⟩
    · rw [Submodule.finrank_sup_span_singleton hnotmem, hr0]
    · intro y
      rw [← hunion, Finset.mem_union, hW0, hW1]
      constructor
      · rintro (h0 | h1)
        · exact Submodule.mem_sup_left h0
        · have heq : y + a0 = (y + a1) + (a1 + a0) := by
            ext j; simp only [Pi.add_apply]
            calc y j + a0 j = y j + (a1 j + a1 j) + a0 j := by rw [zmod2_add_self, add_zero]
              _ = (y j + a1 j) + (a1 j + a0 j) := by ring
          rw [heq]
          exact Submodule.add_mem_sup h1 (Submodule.subset_span (Set.mem_singleton _))
      · intro h
        rw [Submodule.mem_sup] at h
        obtain ⟨w, hw, z, hz, hwz⟩ := h
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        rcases zmod2_cases c with rfl | rfl
        · left; simpa [← hwz] using hw
        · right
          have heq : y + a1 = w := by
            ext j
            have hj := congrFun hwz j
            simp only [one_smul, Pi.add_apply] at hj
            calc y j + a1 j = (w j + (a1 j + a0 j)) + (a0 j + a1 j) := by
                  rw [hj]
                  calc y j + a1 j = y j + (a0 j + a0 j) + a1 j := by rw [zmod2_add_self, add_zero]
                    _ = (y j + a0 j) + (a0 j + a1 j) := by ring
              _ = w j + ((a1 j + a1 j) + (a0 j + a0 j)) := by ring
              _ = w j := by rw [zmod2_add_self, zmod2_add_self, add_zero, add_zero]
          rw [heq]; exact hw

private lemma schwartz_zippel_fin : ∀ (n d : ℕ) (H : MvPolynomial (Fin n) (ZMod 2)),
    H.totalDegree ≤ d →
    (∃ x : Fin n → ZMod 2, eval x H = 1) →
    2 ^ n ≤ 2 ^ d * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x H = 1)).card := by
  classical
  intro n
  induction n with
  | zero =>
    intro d H _ ⟨x, hx⟩
    have hpos : 1 ≤ ((Finset.univ : Finset (Fin 0 → ZMod 2)).filter (fun x => eval x H = 1)).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    have h2 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    simpa using Nat.mul_le_mul h2 hpos
  | succ n ih =>
    intro d H hdeg ⟨x0, hx0⟩
    let S := sqFreePoly H
    have hSdeg : S.totalDegree ≤ d := (sqFreePoly_totalDegree_le H).trans hdeg
    have hSeval : ∀ x, eval x S = eval x H := sqFreePoly_eval H
    have hSml : ∀ a ∈ S.support, ∀ v, a v ≤ 1 := sqFreePoly_multilinear H
    let toTail : (Fin (n + 1) →₀ ℕ) → (Fin n →₀ ℕ) :=
      fun a => Finsupp.comapDomain Fin.succ a (Fin.succ_injective n).injOn
    let A : MvPolynomial (Fin n) (ZMod 2) :=
      ∑ a ∈ S.support.filter (fun a => a 0 = 0), monomial (toTail a) 1
    let B : MvPolynomial (Fin n) (ZMod 2) :=
      ∑ a ∈ S.support.filter (fun a => a 0 = 1), monomial (toTail a) 1
    have hdecomp : ∀ (b : ZMod 2) (x : Fin n → ZMod 2),
        eval (Fin.cons b x) S = eval x A + b * eval x B := by
      intro b x
      have hpart : S.support = S.support.filter (fun a => a 0 = 0) ∪ S.support.filter (fun a => a 0 = 1) := by
        ext a
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ha
          have ha1 := hSml a ha 0
          rcases Nat.eq_zero_or_pos (a 0) with h0 | hpos
          · exact Or.inl ⟨ha, h0⟩
          · exact Or.inr ⟨ha, by omega⟩
        · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
      have hdisj : Disjoint (S.support.filter (fun a => a 0 = 0)) (S.support.filter (fun a => a 0 = 1)) := by
        rw [Finset.disjoint_left]
        intro a h0 h1
        have h0' := (Finset.mem_filter.mp h0).2
        have h1' := (Finset.mem_filter.mp h1).2
        omega
      have hmon : ∀ a : Fin (n + 1) →₀ ℕ,
          eval (Fin.cons b x) (monomial a (1 : ZMod 2)) = b ^ (a 0) * eval x (monomial (toTail a) 1) := by
        intro a
        rw [eval_monomial, eval_monomial, one_mul, one_mul]
        have h1 : a.prod (fun i e => (Fin.cons (α := fun _ => ZMod 2) b x i) ^ e)
            = ∏ i : Fin (n + 1), (Fin.cons (α := fun _ => ZMod 2) b x i) ^ (a i) :=
          Finsupp.prod_of_support_subset a (Finset.subset_univ _)
            (fun i e => (Fin.cons (α := fun _ => ZMod 2) b x i) ^ e) (fun _ _ => pow_zero _)
        have h2 : (toTail a).prod (fun i e => x i ^ e)
            = ∏ i : Fin n, x i ^ (a i.succ) := by
          rw [Finsupp.prod_of_support_subset (toTail a) (Finset.subset_univ _)
            (fun i e => x i ^ e) (fun _ _ => pow_zero _)]
          rfl
        rw [h1, h2, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      conv_lhs => rw [S.as_sum, hpart, Finset.sum_union hdisj, map_add, map_sum, map_sum]
      simp only [A, B, map_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun a ha => ?_
        have ha' := Finset.mem_filter.mp ha
        rw [zmod2_coeff_eq_one ha'.1, hmon, ha'.2, pow_zero, one_mul]
      · refine Finset.sum_congr rfl fun a ha => ?_
        have ha' := Finset.mem_filter.mp ha
        rw [zmod2_coeff_eq_one ha'.1, hmon, ha'.2, pow_one]
    have htail_sum : ∀ a : Fin (n + 1) →₀ ℕ,
        a 0 + (toTail a).sum (fun _ e => e) = a.sum (fun _ e => e) := by
      intro a
      have h1 : a.sum (fun _ e => e) = ∑ i : Fin (n + 1), a i :=
        Finsupp.sum_of_support_subset a (Finset.subset_univ _) (fun _ e => e) (fun _ _ => rfl)
      have h2 : (toTail a).sum (fun _ e => e) = ∑ i : Fin n, a i.succ := by
        rw [Finsupp.sum_of_support_subset (toTail a) (Finset.subset_univ _) (fun _ e => e) (fun _ _ => rfl)]
        rfl
      rw [h1, h2, Fin.sum_univ_succ]
    have hAdeg : A.totalDegree ≤ d := by
      refine totalDegree_finsetSum_le fun a ha => ?_
      have ha' := Finset.mem_filter.mp ha
      refine (totalDegree_monomial_le (toTail a) 1).trans ?_
      change (toTail a).sum (fun _ e => e) ≤ d
      have hts := htail_sum a
      have hda := (le_totalDegree ha'.1).trans hSdeg
      omega
    by_cases hB : ∃ x : Fin n → ZMod 2, eval x B = 1
    · have hB_ne : B ≠ 0 := by
        obtain ⟨x, hx⟩ := hB
        intro h0; rw [h0, map_zero] at hx; exact zero_ne_one hx
      have hsuppB : (S.support.filter (fun a => a 0 = 1)).Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        exact hB_ne (by simp [B, he])
      have hd1 : 1 ≤ d := by
        obtain ⟨a, ha⟩ := hsuppB
        have ha' := Finset.mem_filter.mp ha
        have hts := htail_sum a
        have hda := (le_totalDegree ha'.1).trans hSdeg
        have ha0 := ha'.2
        omega
      have hBdeg : B.totalDegree ≤ d - 1 := by
        refine totalDegree_finsetSum_le fun a ha => ?_
        have ha' := Finset.mem_filter.mp ha
        refine (totalDegree_monomial_le (toTail a) 1).trans ?_
        change (toTail a).sum (fun _ e => e) ≤ d - 1
        have hts := htail_sum a
        have hda := (le_totalDegree ha'.1).trans hSdeg
        have ha0 := ha'.2
        omega
      have hih := ih (d - 1) B hBdeg hB
      have hcard_le : ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x B = 1)).card ≤
          ((Finset.univ : Finset (Fin (n + 1) → ZMod 2)).filter (fun y => eval y H = 1)).card := by
        refine Finset.card_le_card_of_injOn (fun x => Fin.cons (eval x A + 1) x) ?_ ?_
        · intro x hx
          have hBx := (Finset.mem_filter.mp hx).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hSeval, hdecomp, hBx, mul_one]
          calc eval x A + (eval x A + 1) = (eval x A + eval x A) + 1 := by ring
            _ = 1 := by rw [zmod2_add_self, zero_add]
        · intro x1 _ x2 _ heq
          ext i
          have := congrFun heq i.succ
          simpa using this
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
        _ ≤ 2 * (2 ^ (d - 1) * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x B = 1)).card) :=
            Nat.mul_le_mul_left 2 hih
        _ = (2 * 2 ^ (d - 1)) * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x B = 1)).card := by ring
        _ = 2 ^ d * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x B = 1)).card := by
            rw [← pow_succ', Nat.sub_add_cancel hd1]
        _ ≤ 2 ^ d * ((Finset.univ : Finset (Fin (n + 1) → ZMod 2)).filter (fun y => eval y H = 1)).card :=
            Nat.mul_le_mul_left _ hcard_le
    · push Not at hB
      have hB0 : ∀ x, eval x B = 0 := fun x => (zmod2_cases (eval x B)).resolve_right (hB x)
      have hAx0 : eval (fun i => x0 i.succ) A = 1 := by
        have h := hdecomp (x0 0) (fun i => x0 i.succ)
        have hcons : Fin.cons (x0 0) (fun i => x0 i.succ) = x0 := Fin.cons_self_tail x0
        rw [hcons, hSeval, hx0, hB0, mul_zero, add_zero] at h
        exact h.symm
      have hih := ih d A hAdeg ⟨fun i => x0 i.succ, hAx0⟩
      let f0 : (Fin n → ZMod 2) → (Fin (n + 1) → ZMod 2) := fun x => Fin.cons (0 : ZMod 2) x
      let f1 : (Fin n → ZMod 2) → (Fin (n + 1) → ZMod 2) := fun x => Fin.cons (1 : ZMod 2) x
      let E0 := ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x A = 1)).image f0
      let E1 := ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x A = 1)).image f1
      have hdisj : Disjoint E0 E1 := by
        rw [Finset.disjoint_left]
        intro y hy0 hy1
        obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp hy0
        obtain ⟨x2, _, h2⟩ := Finset.mem_image.mp hy1
        have h0 := congrFun h2 0
        simp [f0, f1] at h0
      have hsub : E0 ∪ E1 ⊆ (Finset.univ : Finset (Fin (n + 1) → ZMod 2)).filter (fun y => eval y H = 1) := by
        intro y hy
        rw [Finset.mem_union] at hy
        rcases hy with hy0 | hy1
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy0
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hSeval]; simp only [f0]; rw [hdecomp, hB0, mul_zero, add_zero]
          exact (Finset.mem_filter.mp hx).2
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy1
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hSeval]; simp only [f1]; rw [hdecomp, hB0, mul_zero, add_zero]
          exact (Finset.mem_filter.mp hx).2
      have hinj0 : Function.Injective f0 :=
        fun x1 x2 h => funext fun i => by simpa [f0] using congrFun h i.succ
      have hinj1 : Function.Injective f1 :=
        fun x1 x2 h => funext fun i => by simpa [f1] using congrFun h i.succ
      have hcard_ge : 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x A = 1)).card ≤
          ((Finset.univ : Finset (Fin (n + 1) → ZMod 2)).filter (fun y => eval y H = 1)).card := by
        have hle := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ hinj0,
          Finset.card_image_of_injective _ hinj1,
          ← two_mul] at hle
        exact hle
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
        _ ≤ 2 * (2 ^ d * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x A = 1)).card) :=
            Nat.mul_le_mul_left 2 hih
        _ = 2 ^ d * (2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => eval x A = 1)).card) := by ring
        _ ≤ 2 ^ d * ((Finset.univ : Finset (Fin (n + 1) → ZMod 2)).filter (fun y => eval y H = 1)).card :=
            Nat.mul_le_mul_left _ hcard_ge

private lemma schwartz_zippel {V : Type} [Fintype V] [DecidableEq V]
    (d : ℕ) (H : MvPolynomial V (ZMod 2)) (hdeg : H.totalDegree ≤ d)
    (h1 : ∃ x : V → ZMod 2, eval x H = 1) :
    2 ^ (Fintype.card V) ≤ 2 ^ d * ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => eval x H = 1)).card := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H' : MvPolynomial (Fin (Fintype.card V)) (ZMod 2) := rename e H
  have hdeg' : H'.totalDegree ≤ d := (totalDegree_rename_le e H).trans hdeg
  have hev : ∀ y : Fin (Fintype.card V) → ZMod 2, eval y H' = eval (y ∘ e) H := by
    intro y; exact eval_rename e y H
  obtain ⟨x0, hx0⟩ := h1
  have hcomp0 : (x0 ∘ e.symm) ∘ e = x0 := by ext v; simp
  have h1' : ∃ y : Fin (Fintype.card V) → ZMod 2, eval y H' = 1 :=
    ⟨x0 ∘ e.symm, by rw [hev, hcomp0]; exact hx0⟩
  have hsz := schwartz_zippel_fin (Fintype.card V) d H' hdeg' h1'
  have hcard : ((Finset.univ : Finset (Fin (Fintype.card V) → ZMod 2)).filter (fun y => eval y H' = 1)).card =
      ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => eval x H = 1)).card := by
    refine Finset.card_bij (fun y _ => y ∘ e) ?_ ?_ ?_
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hev y).symm.trans (Finset.mem_filter.mp hy).2⟩
    · intro y1 _ y2 _ h
      ext i
      have := congrFun h (e.symm i)
      simpa using this
    · intro x hx
      refine ⟨x ∘ e.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hev]
        have : (x ∘ e.symm) ∘ e = x := by ext v; simp
        rw [this]; exact (Finset.mem_filter.mp hx).2
      · ext v; simp
  rwa [hcard] at hsz

private lemma clausePoly_totalDegree_le {V : Type} (C : Clause V) :
    (clausePoly C).totalDegree ≤ C.card := by
  unfold clausePoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ l ∈ C, (if l.2 = true then (1 : MvPolynomial V (ZMod 2)) + X l.1 else X l.1).totalDegree
      ≤ ∑ _l ∈ C, 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        split_ifs
        · exact (totalDegree_add _ _).trans (max_le (by simp) (totalDegree_X_le l.1))
        · exact totalDegree_X_le l.1
    _ = C.card := by simp

private lemma eval_clausePoly_eq_zero_iff {V : Type} (x : V → ZMod 2) (C : Clause V) :
    eval x (clausePoly C) = 0 ↔ ClauseSat (fun v => decide (x v = 1)) C := by
  unfold clausePoly ClauseSat
  rw [map_prod, Finset.prod_eq_zero_iff]
  refine ⟨fun ⟨l, hl, h0⟩ => ⟨l, hl, ?_⟩, fun ⟨l, hl, hs⟩ => ⟨l, hl, ?_⟩⟩
  · cases h2 : l.2
    · rw [h2] at h0; simp only [Bool.false_eq_true, ↓reduceIte, eval_X] at h0
      simp [h0]
    · rw [h2] at h0; simp only [↓reduceIte, map_add, map_one, eval_X] at h0
      rcases zmod2_cases (x l.1) with hx | hx
      · rw [hx] at h0; simp at h0
      · simp [hx]
  · cases h2 : l.2
    · rw [h2] at hs; simp only [decide_eq_false_iff_not] at hs
      simp only [Bool.false_eq_true, ↓reduceIte, eval_X]
      exact (zmod2_cases (x l.1)).resolve_right hs
    · rw [h2] at hs; simp only [decide_eq_true_eq] at hs
      simp only [↓reduceIte, map_add, map_one, eval_X, hs]
      exact zmod2_add_self 1

private lemma funGraphPHP_unsat_zmod2 {n : ℕ} (G : BipGraph (n + 1) n) (x : GEdge G → ZMod 2) :
    ∃ C ∈ funGraphPHP G, eval x (clausePoly C) = 1 := by
  classical
  by_contra h
  push Not at h
  have hsat : ∀ C ∈ funGraphPHP G, ClauseSat (fun v => decide (x v = 1)) C := by
    intro C hC
    rw [← eval_clausePoly_eq_zero_iff]
    exact (zmod2_cases (eval x (clausePoly C))).resolve_right (h C hC)
  have hex : ∀ i : Fin (n + 1), ∃ e : GEdge G, e.1.1 = i ∧ x e = 1 := by
    intro i
    let Ci : Clause (GEdge G) :=
      Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)
    have hCi : Ci ∈ funGraphPHP G := Or.inl (Or.inl ⟨i, rfl⟩)
    obtain ⟨l, hl, hls⟩ := hsat Ci hCi
    obtain ⟨hli, hl2⟩ := (Finset.mem_filter.mp hl).2
    rw [hl2] at hls
    exact ⟨l.1, hli, of_decide_eq_true hls⟩
  choose f hf1 hfx using hex
  have hinj : Function.Injective (fun i : Fin (n + 1) => (f i).1.2) := by
    intro i i' hii
    by_contra hne
    let Ch : Clause (GEdge G) := {(f i, false), (f i', false)}
    have hCh : Ch ∈ funGraphPHP G :=
      Or.inl (Or.inr ⟨f i, f i', hii, by rw [hf1 i, hf1 i']; exact hne, rfl⟩)
    obtain ⟨l, hl, hls⟩ := hsat Ch hCh
    simp only [Ch, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hfx i] at hls
    · simp [hfx i'] at hls
  have hle := Fintype.card_le_of_injective _ hinj
  simp at hle

private lemma pcDerivable_batch {V : Type} [DecidableEq V] {Φ : Set (Clause V)} {b : ℕ}
    (L : List (Clause V)) (hmem : ∀ C ∈ L, C ∈ Φ) (hcard : ∀ C ∈ L, C.card ≤ b) :
    (∏ C ∈ L.toFinset, (1 + clausePoly C)).totalDegree ≤ b * L.length ∧
    PCDerivable (cnfSystem Φ) (b * L.length) (1 + ∏ C ∈ L.toFinset, (1 + clausePoly C)) := by
  classical
  induction L with
  | nil =>
    simp only [List.toFinset_nil, Finset.prod_empty, List.length_nil, mul_zero, totalDegree_one,
      le_refl, true_and]
    rw [CharTwo.add_self_eq_zero]
    exact .zero
  | cons C L ih =>
    have hih := ih (fun D hD => hmem D (List.mem_cons_of_mem _ hD))
      (fun D hD => hcard D (List.mem_cons_of_mem _ hD))
    by_cases hCL : C ∈ L.toFinset
    · have heq : (C :: L).toFinset = L.toFinset := by
        rw [List.toFinset_cons, Finset.insert_eq_of_mem hCL]
      rw [heq, List.length_cons]
      exact ⟨hih.1.trans (Nat.mul_le_mul_left b (by omega)),
        pcDerivable_mono hih.2 (Nat.mul_le_mul_left b (by omega)) subset_rfl⟩
    · rw [List.toFinset_cons, Finset.prod_insert hCL, List.length_cons]
      set Q := ∏ D ∈ L.toFinset, (1 + clausePoly D)
      have hCdeg : (clausePoly C).totalDegree ≤ b :=
        (clausePoly_totalDegree_le C).trans (hcard C List.mem_cons_self)
      have h1Cdeg : (1 + clausePoly C).totalDegree ≤ b :=
        (totalDegree_add _ _).trans (max_le (by simp) hCdeg)
      have hQdeg : Q.totalDegree ≤ b * L.length := hih.1
      have hmuldeg : ((1 + clausePoly C) * Q).totalDegree ≤ b * (L.length + 1) := by
        refine (totalDegree_mul _ _).trans ?_
        calc (1 + clausePoly C).totalDegree + Q.totalDegree
            ≤ b + b * L.length := Nat.add_le_add h1Cdeg hQdeg
          _ = b * (L.length + 1) := by ring
      refine ⟨hmuldeg, ?_⟩
      have hsplit : 1 + (1 + clausePoly C) * Q = (1 + Q) + Q * clausePoly C := by ring
      rw [hsplit]
      have h1 : PCDerivable (cnfSystem Φ) (b * (L.length + 1)) (1 + Q) :=
        pcDerivable_mono hih.2 (Nat.mul_le_mul_left b (by omega)) subset_rfl
      have hCax : PCDerivable (cnfSystem Φ) b (clausePoly C) :=
        .ax (Or.inr ⟨C, hmem C List.mem_cons_self, rfl⟩) hCdeg
      have h2 : PCDerivable (cnfSystem Φ) (b * (L.length + 1)) (Q * clausePoly C) := by
        have hm := pcDerivable_mul_left hCax Q
        have hle : max b (Q.totalDegree + (clausePoly C).totalDegree) ≤ b * (L.length + 1) := by
          refine max_le (Nat.le_mul_of_pos_right b (by omega)) ?_
          calc Q.totalDegree + (clausePoly C).totalDegree
              ≤ b * L.length + b := Nat.add_le_add hQdeg hCdeg
            _ = b * (L.length + 1) := by ring
        exact pcDerivable_mono hm hle subset_rfl
      exact .add h1 h2

private lemma funGraphPHP_finset_bound {n b : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n)
    (G : BipGraph (n + 1) n) (hL : LeftDegLe G b) (hR : RightDegLe G b) :
    ∃ (S : Finset (Clause (GEdge G))),
      (∀ C, C ∈ S ↔ C ∈ funGraphPHP G) ∧
      (∀ C ∈ S, C.card ≤ b) ∧
      S.card ≤ (2 + 3 * b ^ 2) * n := by
  classical
  let S1 : Finset (Clause (GEdge G)) :=
    Finset.univ.image fun i : Fin (n + 1) =>
      Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)
  let S2 : Finset (Clause (GEdge G)) :=
    ((Finset.univ : Finset (GEdge G × GEdge G)).filter
      (fun p => p.1.1.2 = p.2.1.2 ∧ p.1.1.1 ≠ p.2.1.1)).image
      (fun p => {(p.1, false), (p.2, false)})
  let S3 : Finset (Clause (GEdge G)) :=
    ((Finset.univ : Finset (GEdge G × GEdge G)).filter
      (fun p => p.1.1.1 = p.2.1.1 ∧ p.1.1.2 ≠ p.2.1.2)).image
      (fun p => {(p.1, false), (p.2, false)})
  refine ⟨S1 ∪ (S2 ∪ S3), ?_, ?_, ?_⟩
  · intro C
    simp only [Finset.mem_union, S1, S2, S3, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, funGraphPHP, graphPHP, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨⟨e, e'⟩, ⟨h1, h2⟩, rfl⟩ | ⟨⟨e, e'⟩, ⟨h1, h2⟩, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨e, e', h1, h2, rfl⟩)
      · exact Or.inr ⟨e, e', h1, h2, rfl⟩
    · rintro ((⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩) | ⟨e, e', h1, h2, rfl⟩)
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr (Or.inl ⟨(e, e'), ⟨h1, h2⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨(e, e'), ⟨h1, h2⟩, rfl⟩)
  · intro C hC
    simp only [Finset.mem_union, S1, S2, S3, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hC
    rcases hC with ⟨i, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · have hle : (Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)).card ≤ (G i).card := by
        refine Finset.card_le_card_of_injOn (fun l => l.1.1.2) ?_ ?_
        · intro l hl
          have h1 := (Finset.mem_filter.mp hl).2.1
          rw [← h1]; exact l.1.2
        · intro l1 hl1 l2 hl2 h
          have h1 := (Finset.mem_filter.mp hl1).2
          have h2 := (Finset.mem_filter.mp hl2).2
          apply Prod.ext
          · apply Subtype.ext
            apply Prod.ext
            · exact h1.1.trans h2.1.symm
            · exact h
          · exact h1.2.trans h2.2.symm
      exact hle.trans (hL i)
    · exact (Finset.card_insert_le _ _).trans (by simp; omega)
    · exact (Finset.card_insert_le _ _).trans (by simp; omega)
  · have hc1 : S1.card ≤ n + 1 := (Finset.card_image_le).trans (by simp)
    have hc2 : S2.card ≤ n * b ^ 2 := by
      refine Finset.card_image_le.trans ?_
      let F2 := (Finset.univ : Finset (GEdge G × GEdge G)).filter
        (fun p => p.1.1.2 = p.2.1.2 ∧ p.1.1.1 ≠ p.2.1.1)
      have hfib : F2.card = ∑ j : Fin n, (F2.filter (fun p => p.1.1.2 = j)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext p; simp
        · intro j1 _ j2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro p h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [hfib]
      calc ∑ j : Fin n, (F2.filter (fun p => p.1.1.2 = j)).card
          ≤ ∑ _j : Fin n, b ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hle : (F2.filter (fun p => p.1.1.2 = j)).card ≤
                ((rightNbrs G j) ×ˢ (rightNbrs G j)).card := by
              refine Finset.card_le_card_of_injOn (fun p => (p.1.1.1, p.2.1.1)) ?_ ?_
              · intro p hp
                have hp1 := (Finset.mem_filter.mp hp).1
                have hpj := (Finset.mem_filter.mp hp).2
                have hpeq := (Finset.mem_filter.mp hp1).2.1
                refine Finset.mem_product.mpr ⟨?_, ?_⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpj ▸ p.1.2⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpeq.symm.trans hpj) ▸ p.2.2⟩
              · intro p1 hp1 p2 hp2 h
                have h' : (p1.1.1.1, p1.2.1.1) = (p2.1.1.1, p2.2.1.1) := h
                have h1j := (Finset.mem_filter.mp hp1).2
                have h2j := (Finset.mem_filter.mp hp2).2
                have h1eq := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).2.1
                have h2eq := (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).2.1
                have hi1 : p1.1.1.1 = p2.1.1.1 := (Prod.mk.inj h').1
                have hi2 : p1.2.1.1 = p2.2.1.1 := (Prod.mk.inj h').2
                apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
                · exact hi1
                · exact h1j.trans h2j.symm
                · exact hi2
                · exact (h1eq.symm.trans h1j).trans (h2eq.symm.trans h2j).symm
            rw [Finset.card_product, ← sq] at hle
            exact hle.trans (Nat.pow_le_pow_left (hR j) 2)
        _ = n * b ^ 2 := by simp
    have hc3 : S3.card ≤ (n + 1) * b ^ 2 := by
      refine Finset.card_image_le.trans ?_
      let F3 := (Finset.univ : Finset (GEdge G × GEdge G)).filter
        (fun p => p.1.1.1 = p.2.1.1 ∧ p.1.1.2 ≠ p.2.1.2)
      have hfib : F3.card = ∑ i : Fin (n + 1), (F3.filter (fun p => p.1.1.1 = i)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext p; simp
        · intro i1 _ i2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro p h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [hfib]
      calc ∑ i : Fin (n + 1), (F3.filter (fun p => p.1.1.1 = i)).card
          ≤ ∑ _i : Fin (n + 1), b ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hle : (F3.filter (fun p => p.1.1.1 = i)).card ≤
                ((G i) ×ˢ (G i)).card := by
              refine Finset.card_le_card_of_injOn (fun p => (p.1.1.2, p.2.1.2)) ?_ ?_
              · intro p hp
                have hp1 := (Finset.mem_filter.mp hp).1
                have hpi := (Finset.mem_filter.mp hp).2
                have hpeq := (Finset.mem_filter.mp hp1).2.1
                refine Finset.mem_product.mpr ⟨hpi ▸ p.1.2, (hpeq.symm.trans hpi) ▸ p.2.2⟩
              · intro p1 hp1 p2 hp2 h
                have h' : (p1.1.1.2, p1.2.1.2) = (p2.1.1.2, p2.2.1.2) := h
                have h1i := (Finset.mem_filter.mp hp1).2
                have h2i := (Finset.mem_filter.mp hp2).2
                have h1eq := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).2.1
                have h2eq := (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).2.1
                have hj1 : p1.1.1.2 = p2.1.1.2 := (Prod.mk.inj h').1
                have hj2 : p1.2.1.2 = p2.2.1.2 := (Prod.mk.inj h').2
                apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
                · exact h1i.trans h2i.symm
                · exact hj1
                · exact (h1eq.symm.trans h1i).trans (h2eq.symm.trans h2i).symm
                · exact hj2
            rw [Finset.card_product, ← sq] at hle
            exact hle.trans (Nat.pow_le_pow_left (hL i) 2)
        _ = (n + 1) * b ^ 2 := by simp
    calc (S1 ∪ (S2 ∪ S3)).card
        ≤ S1.card + (S2 ∪ S3).card := Finset.card_union_le _ _
      _ ≤ S1.card + (S2.card + S3.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ (n + 1) + (n * b ^ 2 + (n + 1) * b ^ 2) := by omega
      _ ≤ 2 * n + (n * b ^ 2 + 2 * n * b ^ 2) := by nlinarith
      _ = (2 + 3 * b ^ 2) * n := by ring

theorem main_388 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)
    (∀ (t c D L : ℕ) (g : Fin t → MvPolynomial V (ZMod 2))
        (E : Fin t → Set (MvPolynomial V (ZMod 2))),
      let pat := fun (x : V → ZMod 2) (j : Fin t) => MvPolynomial.eval x (g j)
      let seen := Finset.univ.image pat
      1 ≤ c → C * (max (D+c) (c*L) + 1) ≤ n →
      (∀ j, (g j).totalDegree ≤ c) →
      (∀ x : V → ZMod 2, ∃ j : Fin t, pat x j = 1) →
      (∀ (x : V → ZMod 2) j, pat x j = 1 → ∀ e ∈ E j, MvPolynomial.eval x e = 0) →
      (∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ E j) D) →
      (∀ (s : ℕ) (Q : MvPolynomial (Fin t) (ZMod 2)), s ≤ L → Q.totalDegree ≤ s →
        MvPolynomial.eval (fun _ => (0 : ZMod 2)) Q = 1 →
        2^(L-s+1) ≤ (seen.filter (fun y => MvPolynomial.eval y Q = 1)).card + 1 ∧
        2^(Fintype.card V) ≤ 2^(c*s) *
          ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => MvPolynomial.eval (pat x) Q = 1)).card) ∧
      (seen.card+1 = 2^(L+1) → ∃ U : Submodule (ZMod 2) (Fin t → ZMod 2),
        Module.finrank (ZMod 2) U = L+1 ∧ ∀ y, y ∈ seen ↔ y ∈ U ∧ y ≠ 0)) ∧
    ∀ u : ℕ, 1 ≤ u → ∃ (t : ℕ) (g : Fin t → MvPolynomial V (ZMod 2)),
      t ≤ C*((n+u-1)/u) ∧ (∀ j, (g j).totalDegree ≤ C*u) ∧
      (∀ x : V → ZMod 2, ∃ j : Fin t, MvPolynomial.eval x (g j) = 1) ∧
      ∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ {1+g j}) (C*u)) := by
  classical
  obtain ⟨b0, s₀, n₀, hs₀, hExp⟩ := L043
  let b := max b0 2
  let C := max (b * s₀ + s₀) (2 + 3 * b ^ 2)
  have hb2 : 2 ≤ b := le_max_right _ _
  have hC2 : 2 ≤ C := le_trans (by omega : 2 ≤ 2 + 3 * b ^ 2) (le_max_right _ _)
  have hbC : b ≤ C := by
    have : b ≤ 2 + 3 * b ^ 2 := by nlinarith
    exact this.trans (le_max_right _ _)
  refine ⟨C, max n₀ 1, hC2, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨G, hLb0, hRb0, hbdry⟩ := hExp n (le_trans (le_max_left _ _) hn)
  have hLb : LeftDegLe G b := fun i => (hLb0 i).trans (le_max_left _ _)
  have hRb : RightDegLe G b := fun j => (hRb0 j).trans (le_max_left _ _)
  refine ⟨G, fun i => (hLb i).trans hbC, fun j => (hRb j).trans hbC, ?_, ?_⟩
  · intro t c D L g E pat seen hc hCn hg hcov hE href
    have hns : 1 ≤ n / s₀ := by
      rw [Nat.le_div_iff_mul_le hs₀]
      have : s₀ ≤ C := le_trans (by nlinarith) (le_max_left _ _)
      have : C ≤ n := le_trans (Nat.le_mul_of_pos_right C (by omega)) hCn
      omega
    have hMle : b * max (D + c) (c * L) ≤ n / s₀ := by
      rw [Nat.le_div_iff_mul_le hs₀]
      have h1 : b * s₀ ≤ C := le_trans (by omega) (le_max_left _ _)
      calc b * max (D + c) (c * L) * s₀
          = (b * s₀) * max (D + c) (c * L) := by ring
        _ ≤ C * max (D + c) (c * L) := Nat.mul_le_mul_right _ h1
        _ ≤ C * (max (D + c) (c * L) + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ n := hCn
    have hno := L049 (n + 1) n G (n / s₀) b (max (D + c) (c * L)) hbdry hLb hns hMle
    have h0not : (0 : Fin t → ZMod 2) ∉ seen := by
      intro h0
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h0
      obtain ⟨j, hj⟩ := hcov x
      have hx0 : pat x j = 0 := congrFun hx j
      rw [hx0] at hj
      exact zero_ne_one hj
    have hsep : ∀ P : MvPolynomial (Fin t) (ZMod 2), P.totalDegree ≤ L →
        eval (fun _ => (0 : ZMod 2)) P = 1 → ∃ y ∈ seen, eval y P = 1 := by
      intro P hPdeg hP0
      obtain ⟨x, hx⟩ := exists_pat_eval_one hg hE href hno P hPdeg hP0
      exact ⟨pat x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hx⟩
    obtain ⟨T, h0T, hTsub, hTann⟩ := exists_annihilator seen h0not hsep
    constructor
    · intro s Q hsL hQdeg hQ0
      constructor
      · let A := T.filter (fun y => eval y Q = 1)
        have hAne : A.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0T, hQ0⟩⟩
        have hAann := ann_filter_mul (k := L - s) (s := s)
          (fun P hP => hTann P (by omega)) Q hQdeg
        have hge := ann_card_ge (L - s) A hAne hAann
        have hsub : A ⊆ insert 0 (seen.filter (fun y => eval y Q = 1)) := by
          intro y hy
          obtain ⟨hyT, hyQ⟩ := Finset.mem_filter.mp hy
          rcases Finset.mem_insert.mp (hTsub hyT) with rfl | hys
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hys, hyQ⟩)
        exact hge.trans ((Finset.card_le_card hsub).trans (Finset.card_insert_le _ _))
      · obtain ⟨x0, hx0⟩ := exists_pat_eval_one hg hE href hno Q (hQdeg.trans hsL) hQ0
        have hdegH : (bind₁ g Q).totalDegree ≤ c * s :=
          (totalDegree_bind₁_le g hg Q).trans (Nat.mul_le_mul_left c hQdeg)
        have hsz := schwartz_zippel (c * s) (bind₁ g Q) hdegH ⟨x0, by rwa [eval_bind₁_zmod2]⟩
        simpa only [eval_bind₁_zmod2] using hsz
    · intro hcard
      have hTge : 2 ^ (L + 1) ≤ T.card := ann_card_ge L T ⟨0, h0T⟩ hTann
      have hTle : T.card ≤ 2 ^ (L + 1) := by
        have h1 := Finset.card_le_card hTsub
        rw [Finset.card_insert_of_notMem h0not] at h1
        omega
      have hTeq_card : T.card = 2 ^ (L + 1) := le_antisymm hTle hTge
      have hTeq : T = insert 0 seen := by
        refine Finset.eq_of_subset_of_card_le hTsub ?_
        rw [Finset.card_insert_of_notMem h0not, hTeq_card, hcard]
      obtain ⟨a, U, hrank, hU⟩ := ann_eq_affine L T ⟨0, h0T⟩ hTann hTeq_card
      have haU : a ∈ U := by
        have := (hU 0).mp h0T
        simpa using this
      refine ⟨U, hrank, fun y => ?_⟩
      have hUy : y + a ∈ U ↔ y ∈ U := by
        constructor
        · intro h
          have : y = (y + a) + a := by ext j; simp only [Pi.add_apply]; rw [add_assoc, zmod2_add_self, add_zero]
          rw [this]; exact U.add_mem h haU
        · intro h; exact U.add_mem h haU
      rw [← hUy, ← hU, hTeq, Finset.mem_insert]
      constructor
      · intro hys
        exact ⟨Or.inr hys, fun h0 => h0not (h0 ▸ hys)⟩
      · rintro ⟨rfl | hys, hne⟩
        · exact (hne rfl).elim
        · exact hys
  · intro u hu
    obtain ⟨S, hSmem, hScard, hSbound⟩ := funGraphPHP_finset_bound hb2 hn1 G hLb hRb
    let L := S.toList
    have hLlen : L.length = S.card := Finset.length_toList S
    let t := (L.length + u - 1) / u
    let chunk : Fin t → List (Clause (GEdge G)) := fun j => (L.drop (j.val * u)).take u
    let g : Fin t → MvPolynomial (GEdge G) (ZMod 2) :=
      fun j => 1 + ∏ C ∈ (chunk j).toFinset, (1 + clausePoly C)
    have ht_le : t ≤ C * ((n + u - 1) / u) := by
      have hK : 2 + 3 * b ^ 2 ≤ C := le_max_right _ _
      have hq : n ≤ u * ((n + u - 1) / u) := by
        have h1 : n + u - 1 < u * ((n + u - 1) / u + 1) :=
          Nat.lt_mul_div_succ (n + u - 1) (by omega : 0 < u)
        rw [mul_add, mul_one] at h1
        omega
      have hLle : L.length ≤ u * (C * ((n + u - 1) / u)) := by
        calc L.length = S.card := hLlen
          _ ≤ (2 + 3 * b ^ 2) * n := hSbound
          _ ≤ C * n := Nat.mul_le_mul_right n hK
          _ ≤ C * (u * ((n + u - 1) / u)) := Nat.mul_le_mul_left C hq
          _ = u * (C * ((n + u - 1) / u)) := by ring
      have hdiv : (L.length + u - 1) / u ≤ C * ((n + u - 1) / u) := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < u)]
        have : L.length + u - 1 ≤ u * (C * ((n + u - 1) / u)) + (u - 1) := by omega
        linarith
      exact hdiv
    refine ⟨t, g, ht_le, ?_, ?_, ?_⟩
    · intro j
      have hch_mem : ∀ D ∈ chunk j, D ∈ funGraphPHP G := by
        intro D hD
        exact (hSmem D).mp (Finset.mem_toList.mp (List.mem_of_mem_drop (List.mem_of_mem_take hD)))
      have hch_card : ∀ D ∈ chunk j, D.card ≤ b := by
        intro D hD
        exact hScard D (Finset.mem_toList.mp (List.mem_of_mem_drop (List.mem_of_mem_take hD)))
      have hbatch := pcDerivable_batch (chunk j) hch_mem hch_card
      have hlen : (chunk j).length ≤ u := List.length_take_le u _
      refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
      exact hbatch.1.trans ((Nat.mul_le_mul_left b hlen).trans (Nat.mul_le_mul_right u hbC))
    · intro x
      obtain ⟨C, hC, hCx⟩ := funGraphPHP_unsat_zmod2 G x
      have hCL : C ∈ L := Finset.mem_toList.mpr ((hSmem C).mpr hC)
      obtain ⟨idx, hidx_lt, rfl⟩ := List.mem_iff_getElem.mp hCL
      have hj_lt : idx / u < t := by
        unfold t
        have h1 : idx / u * u ≤ idx := Nat.div_mul_le_self idx u
        have h2 : idx + 1 ≤ L.length := by omega
        have h3 : idx / u * u + u ≤ L.length + u - 1 := by omega
        have := Nat.div_le_div_right (c := u) h3
        rw [Nat.add_div_right _ (by omega : 0 < u), Nat.mul_div_cancel _ (by omega : 0 < u)] at this
        omega
      refine ⟨⟨idx / u, hj_lt⟩, ?_⟩
      have hmem_ch : L[idx] ∈ (chunk ⟨idx / u, hj_lt⟩).toFinset := by
        rw [List.mem_toFinset]
        have hmod : idx % u < u := Nat.mod_lt idx (by omega)
        have hdrop_len : idx % u < (L.drop (idx / u * u)).length := by
          rw [List.length_drop]
          have := Nat.div_add_mod idx u
          rw [mul_comm] at this
          omega
        have htake_len : idx % u < (chunk ⟨idx / u, hj_lt⟩).length := by
          simp only [chunk, List.length_take]
          omega
        have hget : (chunk ⟨idx / u, hj_lt⟩)[idx % u]'htake_len = L[idx] := by
          simp only [chunk, List.getElem_take, List.getElem_drop]
          congr 1
          have := Nat.div_add_mod idx u
          rw [mul_comm] at this
          exact this
        rw [← hget]
        exact List.getElem_mem htake_len
      simp only [g, map_add, map_one, map_prod]
      have hprod0 : ∏ D ∈ (chunk ⟨idx / u, hj_lt⟩).toFinset, (1 + eval x (clausePoly D)) = 0 := by
        refine Finset.prod_eq_zero hmem_ch ?_
        rw [hCx]
        exact zmod2_add_self 1
      rw [hprod0, add_zero]
    · intro j
      have hch_mem : ∀ D ∈ chunk j, D ∈ funGraphPHP G := by
        intro D hD
        exact (hSmem D).mp (Finset.mem_toList.mp (List.mem_of_mem_drop (List.mem_of_mem_take hD)))
      have hch_card : ∀ D ∈ chunk j, D.card ≤ b := by
        intro D hD
        exact hScard D (Finset.mem_toList.mp (List.mem_of_mem_drop (List.mem_of_mem_take hD)))
      have hbatch := pcDerivable_batch (chunk j) hch_mem hch_card
      have hlen : (chunk j).length ≤ u := List.length_take_le u _
      have hdeg_le : b * (chunk j).length ≤ C * u :=
        (Nat.mul_le_mul_left b hlen).trans (Nat.mul_le_mul_right u hbC)
      have hgj : PCDerivable (cnfSystem (funGraphPHP G) ∪ {1 + g j}) (C * u) (g j) :=
        pcDerivable_mono hbatch.2 hdeg_le Set.subset_union_left
      have h1gj : PCDerivable (cnfSystem (funGraphPHP G) ∪ {1 + g j}) (C * u) (1 + g j) := by
        refine .ax (Set.mem_union_right _ rfl) ?_
        have h1g : (1 + g j) = ∏ D ∈ (chunk j).toFinset, (1 + clausePoly D) := by
          simp only [g]
          calc (1 : MvPolynomial (GEdge G) (ZMod 2)) + (1 + ∏ D ∈ (chunk j).toFinset, (1 + clausePoly D))
              = (1 + 1) + ∏ D ∈ (chunk j).toFinset, (1 + clausePoly D) := by ring
            _ = ∏ D ∈ (chunk j).toFinset, (1 + clausePoly D) := by rw [CharTwo.add_self_eq_zero, zero_add]
        rw [h1g]
        exact hbatch.1.trans hdeg_le
      have hsum1 : g j + (1 + g j) = (1 : MvPolynomial (GEdge G) (ZMod 2)) := by
        calc g j + (1 + g j) = (g j + g j) + 1 := by ring
          _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
      have hadd := PCDerivable.add hgj h1gj
      rw [hsum1] at hadd
      exact hadd

end Body388

end PEqualNP.Outside.L_pcx_388_aux

theorem PEqualNP.Outside.L_pcx_388 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)
    (∀ (t c D L : ℕ) (g : Fin t → MvPolynomial V (ZMod 2))
        (E : Fin t → Set (MvPolynomial V (ZMod 2))),
      let pat := fun (x : V → ZMod 2) (j : Fin t) => MvPolynomial.eval x (g j)
      let seen := Finset.univ.image pat
      1 ≤ c → C * (max (D+c) (c*L) + 1) ≤ n →
      (∀ j, (g j).totalDegree ≤ c) →
      (∀ x : V → ZMod 2, ∃ j : Fin t, pat x j = 1) →
      (∀ (x : V → ZMod 2) j, pat x j = 1 → ∀ e ∈ E j, MvPolynomial.eval x e = 0) →
      (∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ E j) D) →
      (∀ (s : ℕ) (Q : MvPolynomial (Fin t) (ZMod 2)), s ≤ L → Q.totalDegree ≤ s →
        MvPolynomial.eval (fun _ => (0 : ZMod 2)) Q = 1 →
        2^(L-s+1) ≤ (seen.filter (fun y => MvPolynomial.eval y Q = 1)).card + 1 ∧
        2^(Fintype.card V) ≤ 2^(c*s) *
          ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => MvPolynomial.eval (pat x) Q = 1)).card) ∧
      (seen.card+1 = 2^(L+1) → ∃ U : Submodule (ZMod 2) (Fin t → ZMod 2),
        Module.finrank (ZMod 2) U = L+1 ∧ ∀ y, y ∈ seen ↔ y ∈ U ∧ y ≠ 0)) ∧
    ∀ u : ℕ, 1 ≤ u → ∃ (t : ℕ) (g : Fin t → MvPolynomial V (ZMod 2)),
      t ≤ C*((n+u-1)/u) ∧ (∀ j, (g j).totalDegree ≤ C*u) ∧
      (∀ x : V → ZMod 2, ∃ j : Fin t, MvPolynomial.eval x (g j) = 1) ∧
      ∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ {1+g j}) (C*u)) :=
  PEqualNP.Outside.L_pcx_388_aux.main_388
