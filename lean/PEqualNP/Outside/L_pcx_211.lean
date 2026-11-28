import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_211_aux

open PEqualNP PEqualNP.ProofComplexity PEqualNP.Expanders

namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity
theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)
end PEqualNP.ProofComplexity
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
open MvPolynomial
section Static
variable {σ : Type}
theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]
theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl
theorem support_add_single_one [DecidableEq σ] (a : σ →₀ ℕ) (v : σ) :
    (a + Finsupp.single v 1).support = insert v a.support := by
  ext u
  by_cases h : v = u
  · subst h
    simp
  · simp [Ne.symm h]
end Static
section Matching
variable {m N : ℕ}
def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b
theorem IsPartialMatching.mono {S T : Finset (Fin m × Fin N)} (hT : IsPartialMatching T)
    (hST : S ⊆ T) : IsPartialMatching S :=
  fun a ha b hb h => hT a (hST ha) b (hST hb) h
end Matching
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity
theorem L046 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → 2 * (D + 1) ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.graphPHP G)) D :=
  fun _ _ G _ _ hG hs => Helpers.graphPHP_no_pc_refutation G hG (by omega) (by omega)
end PEqualNP.ProofComplexity
namespace PEqualNP.ProofComplexity.Helpers
open MvPolynomial PEqualNP.ProofComplexity
section Generic
variable {σ : Type}
theorem char2_add_self (x : MvPolynomial σ (ZMod 2)) : x + x = 0 :=
  CharTwo.add_self_eq_zero x
theorem totalDegree_mul_le' {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
theorem totalDegree_prod_one_add_le {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) {e : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ e) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ e * s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ u ∈ s, (1 + a u).totalDegree ≤ ∑ _u ∈ s, e := by
        refine Finset.sum_le_sum fun u hu => ?_
        refine (totalDegree_add _ _).trans ?_
        rw [totalDegree_one]
        exact max_le (Nat.zero_le _) (ha u hu)
    _ = e * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
end Generic
section Blocks
variable {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {h M W : ℕ}
  {g : Fin M → Fin W → MvPolynomial V (ZMod 2)}
end Blocks
section Clauses
variable {V : Type} [DecidableEq V]
noncomputable def eqPoly (q : LinEq V) : MvPolynomial V (ZMod 2) :=
  ∑ v ∈ q.1, X v + C (if q.2 = true then 0 else 1)
omit [DecidableEq V] in
theorem totalDegree_eqPoly_le (q : LinEq V) : (eqPoly q).totalDegree ≤ 1 := by
  unfold eqPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact totalDegree_finsetSum_le fun v _ => (totalDegree_X v).le
  · rw [totalDegree_C]
    exact Nat.zero_le _
variable {F : Set (MvPolynomial V (ZMod 2))} {h M W : ℕ} {e : Fin W → LinEq V}
  {cl : Fin M → LinClause V}
end Clauses
section Axioms
variable {m l h M W : ℕ} {e : Fin W → LinEq (Fin m × Fin l)}
  {cl : Fin M → LinClause (Fin m × Fin l)}
end Axioms
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
open MvPolynomial PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]
def eqVec (q : LinEq V) : (V → ZMod 2) × ZMod 2 :=
  (fun v => if v ∈ q.1 then 1 else 0, if q.2 = true then 0 else 1)
noncomputable def affPoly : ((V → ZMod 2) × ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) :=
  (Fintype.linearCombination (ZMod 2) (fun v : V => (X v : MvPolynomial V (ZMod 2)))).coprod
    (Algebra.linearMap (ZMod 2) (MvPolynomial V (ZMod 2)))
theorem affPoly_eqVec (q : LinEq V) : affPoly (eqVec q) = eqPoly q := by
  simp [affPoly, eqVec, eqPoly, Fintype.linearCombination_apply, MvPolynomial.algebraMap_eq,
    Finset.sum_ite_mem]
omit [DecidableEq V] in
theorem affPoly_one : affPoly ((0, 1) : (V → ZMod 2) × ZMod 2) = 1 := by
  simp [affPoly, Fintype.linearCombination_apply]
omit [Fintype V] [DecidableEq V] in
theorem linEqSat_iff_sum (a : V → ZMod 2) (q : LinEq V) :
    LinEqSat (fun v => decide (a v = 1)) q ↔
      ∑ v ∈ q.1, a v + (if q.2 = true then 0 else 1) = 1 := by
  unfold LinEqSat
  have hs : ∑ v ∈ q.1, a v
      = ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    generalize a v = x
    revert x
    decide
  rw [hs, ← ZMod.natCast_eq_one_iff_odd]
  generalize ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) = x
  rcases q with ⟨f, b⟩
  cases b
  · simp only [Bool.false_eq_true, iff_false, ite_false]
    revert x
    decide
  · simp
theorem dual_apply (φ : Module.Dual (ZMod 2) ((V → ZMod 2) × ZMod 2))
    (h1 : φ (0, 1) = 1) (q : LinEq V) :
    φ (eqVec q) = ∑ v ∈ q.1, φ (fun j => if v = j then 1 else 0, 0) + (if q.2 = true then 0 else 1) := by
  have hsplit : eqVec q = LinearMap.inl (ZMod 2) (V → ZMod 2) (ZMod 2)
      (fun v => if v ∈ q.1 then 1 else 0)
      + (if q.2 = true then (0 : ZMod 2) else 1) • ((0, 1) : (V → ZMod 2) × ZMod 2) := by
    rcases q with ⟨f, b⟩
    cases b <;> simp [eqVec]
  rw [hsplit, map_add, map_smul, h1, ← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ]
  simp [Finset.sum_ite_mem]
theorem lin_alter_choice (q : LinEq V) (D : LinClause V)
    (himp : ∀ a : V → Bool, LinEqSat a q → LinClauseSat a D) :
    ∃ J : Finset (LinEq V), J ⊆ D ∧
      (∑ d ∈ J, eqPoly d = 1 ∨ ∑ d ∈ J, eqPoly d = eqPoly q) := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hq : LinEqSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) q := by
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Set.mem_insert _ _))
      rw [map_add, h1] at this
      generalize φ (eqVec q) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hq
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨d, hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.mem_span_insert] at hmem
  obtain ⟨c, z, hz, hEq⟩ := hmem
  rw [Finsupp.mem_span_image_iff_linearCombination] at hz
  obtain ⟨lc, hlc, rfl⟩ := hz
  have hJ : lc.support ⊆ D := by
    intro d hd
    exact Finsupp.mem_supported _ _ |>.mp hlc hd
  have hsum : affPoly (Finsupp.linearCombination (ZMod 2) eqVec lc)
      = ∑ d ∈ lc.support, eqPoly d := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
    have h1 : lc d = 1 := by
      generalize lc d = x at h0
      revert x
      decide
    rw [h1, one_smul, affPoly_eqVec]
  have hP := congrArg affPoly hEq
  rw [map_add, map_smul, map_add, affPoly_one, affPoly_eqVec, hsum] at hP
  refine ⟨lc.support, hJ, ?_⟩
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc c with rfl | rfl
  · left
    rw [zero_smul, zero_add] at hP
    exact hP.symm
  · right
    rw [one_smul] at hP
    linear_combination hP + char2_add_self (∑ d ∈ lc.support, eqPoly d)
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers.BoolVanish
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
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
end PEqualNP.ProofComplexity.Helpers.BoolVanish
namespace PEqualNP.ProofComplexity.Helpers.LowRankBlock
open MvPolynomial
theorem totalDegree_prod_one_add_le {σ : Type} (G : ℕ → MvPolynomial σ (ZMod 2))
    (hG : ∀ a, (G a).totalDegree ≤ 1) (n : ℕ) :
    (∏ a ∈ Finset.range n, (1 + G a)).totalDegree ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (1 + G n).totalDegree ≤ 1 := by
      refine (totalDegree_add _ _).trans ?_
      simp [hG n]
    omega
end PEqualNP.ProofComplexity.Helpers.LowRankBlock
namespace PEqualNP.ProofComplexity.Helpers
open MvPolynomial Module
theorem two_eq_zero_mvPolynomial {σ : Type} : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  calc (2 : MvPolynomial σ (ZMod 2)) = C (1 + 1) := by rw [C_add, C_1, one_add_one_eq_two]
    _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from rfl, C_0]
theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
open MvPolynomial Module PEqualNP.ProofComplexity
section Axiom
variable {V : Type} [DecidableEq V] {h M W : ℕ} {e : Fin W → LinEq V}
  {cl : Fin M → LinClause V}
omit [DecidableEq V] in
theorem clausePoly_eq_prod (A : Clause V) :
    clausePoly A = ∏ l ∈ A, (1 + eqPoly ((({l.1} : Finset V), l.2) : LinEq V)) := by
  unfold clausePoly
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases l with ⟨v, b⟩
  cases b
  · simp only [eqPoly, Finset.sum_singleton, Bool.false_eq_true, ite_false, C_1]
    linear_combination (-(1 : MvPolynomial V (ZMod 2))) * two_eq_zero_mvPolynomial (σ := V)
  · simp [eqPoly]
end Axiom
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.DegSizePlan
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
section Abstract
variable {σ : Type}
def pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) where
  carrier := {p | PCDerivable A D p}; add_mem' := fun hp hq => PCDerivable.add hp hq
  zero_mem' := PCDerivable.zero
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simpa using (PCDerivable.zero : PCDerivable A D 0)
    · simpa using hp
structure DegClosed (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ) : Prop where
  two_le : 2 ≤ D
  mulX : ∀ (v : σ) (f : MvPolynomial σ (ZMod 2)), f ∈ C → f.totalDegree + 1 ≤ D → X v * f ∈ C
  bool : ∀ v : σ, X v * X v + X v ∈ C
theorem degClosed_pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) (hD : 2 ≤ D)
    (hA : ∀ v : σ, X v * X v + X v ∈ A) : DegClosed (pcClosure A D) D where
  two_le := hD
  mulX := fun v f hf hdeg => PCDerivable.mulX v hf
    ((totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega))
  bool := fun v => PCDerivable.ax (hA v) (by
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
    · rw [totalDegree_X]; omega
    · rw [totalDegree_X]; omega)
noncomputable abbrev polyLE (σ : Type) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictTotalDegree σ (ZMod 2) k
noncomputable def errKer (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  polyLE σ k ⊓ ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)
theorem mem_errKer {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C M k ↔ f.totalDegree ≤ k ∧ ∀ m ∈ M, m * f ∈ C := by
  simp [errKer, polyLE, mem_restrictTotalDegree]
noncomputable def errRank (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ k) - finrank (ZMod 2) (errKer C M k)
noncomputable def zMul (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))) :
    Set (MvPolynomial σ (ZMod 2)) := (fun g => P * g) '' G
def numMono (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), n.choose j
noncomputable def hCodim (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ K) - finrank (ZMod 2) ↥(C ⊓ polyLE σ K)
noncomputable def eta (n K : ℕ) : ℝ := (numMono n (K - 1) : ℝ) / (2 * numMono n K)
end Abstract
end PEqualNP.ProofComplexity.DegSizePlan
namespace PEqualNP.ProofComplexity.DegSizeSim
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
section Abstract
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem monomial_mul_mem (hC : DegClosed C D) (a : σ →₀ ℕ) :
    ∀ {g : MvPolynomial σ (ZMod 2)}, g ∈ C → (a.sum fun _ e => e) + g.totalDegree ≤ D →
      monomial a 1 * g ∈ C := by
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
      exact hC.mulX j _ (ih hg (by omega)) (by omega)
theorem absorb_le (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ C) {a b : ℕ} (hg : g.totalDegree ≤ a)
    (hfd : f.totalDegree ≤ b) (hB : a + b ≤ D) : g * f ∈ C := by
  have hq : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hc : g.coeff u = 1 := by
    have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
    generalize g.coeff u = c at h0
    revert h0; revert c; decide
  rw [hc]
  have : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact monomial_mul_mem hC u hf (by omega)
theorem absorb : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ f g : MvPolynomial σ (ZMod 2), f ∈ C → g.totalDegree + f.totalDegree ≤ D → g * f ∈ C :=
  fun _ _ _ hC _ g hf hdeg => absorb_le hC g hf le_rfl le_rfl hdeg
theorem idem_sum {ι : Type} (s : Finset ι) (h : ι → MvPolynomial σ (ZMod 2))
    (hh : ∀ i ∈ s, h i * h i + h i ∈ C) :
    (∑ i ∈ s, h i) * (∑ i ∈ s, h i) + ∑ i ∈ s, h i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have e : (h i + ∑ x ∈ s, h x) * (h i + ∑ x ∈ s, h x) + (h i + ∑ x ∈ s, h x)
        = (h i * h i + h i) + ((∑ x ∈ s, h x) * (∑ x ∈ s, h x) + ∑ x ∈ s, h x) := by
      linear_combination char2_add_self (h i * ∑ x ∈ s, h x)
    rw [e]
    exact C.add_mem (hh i (Finset.mem_insert_self i s))
      (ih fun k hk => hh k (Finset.mem_insert_of_mem hk))
theorem exponent_le_one (u : σ →₀ ℕ) (hu : (u.sum fun _ e => e) ≤ 1) :
    u = 0 ∨ ∃ v, u = Finsupp.single v 1 := by
  classical
  by_cases h0 : u = 0
  · exact Or.inl h0
  right
  obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr h0
  refine ⟨v, ?_⟩
  have hsum : u v + ∑ x ∈ u.support.erase v, u x ≤ 1 := by
    rw [Finset.add_sum_erase _ _ hv]
    exact hu
  have hv1 : u v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hrest : ∑ x ∈ u.support.erase v, u x = 0 := by omega
  ext x
  by_cases hx : x = v
  · subst hx
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hx]
    by_contra hne
    have hmem : x ∈ u.support.erase v :=
      Finset.mem_erase.mpr ⟨hx, Finsupp.mem_support_iff.mpr hne⟩
    exact hne ((Finset.sum_eq_zero_iff.mp hrest) x hmem)
theorem affine_idem' (hC : DegClosed C D) {g : MvPolynomial σ (ZMod 2)}
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  have hsum : g = ∑ u ∈ g.support, monomial u (g.coeff u) := g.as_sum
  have key := idem_sum (C := C) g.support (fun u => monomial u (g.coeff u)) (fun u hu => by
    have hc : g.coeff u = 1 := by
      have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
      generalize g.coeff u = c at h0
      revert h0; revert c; decide
    rw [hc]
    have hdu : (u.sum fun _ e => e) ≤ 1 := (le_totalDegree hu).trans hg
    rcases exponent_le_one u hdu with rfl | ⟨v, rfl⟩
    · have h1 : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [h1, one_mul, char2_add_self]
      exact C.zero_mem
    · exact hC.bool v)
  rw [← hsum] at key
  exact key
theorem affine_idem : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), g.totalDegree ≤ 1 → g * g + g ∈ C :=
  fun _ _ _ hC _ hg => affine_idem' hC hg
theorem totalDegree_one_add_le {p : MvPolynomial σ (ZMod 2)} (h : p.totalDegree ≤ 1) :
    (1 + p).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h
theorem totalDegree_prod_le {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    (ha : ∀ u ∈ s, (a u).totalDegree ≤ 1) : (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := 1) ha
  omega
theorem prod_absorb (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ 1) (hB : s.card + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ 1 := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ 1 :=
      totalDegree_one_add_le (hdeg u (Finset.mem_insert_self u s))
    have h2 := absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3
theorem totalDegree_span_le {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem totalDegree_appr_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  have := totalDegree_prod_le Finset.univ qs (fun j _ => h j)
  simpa using this
theorem transfer' (hC : DegClosed C D) {K t r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem g hg' =>
      rw [← mul_assoc]
      exact hg g hg'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact C.add_mem hx hy
    | smul c x _ hx =>
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using hx
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j => totalDegree_span_le hG (hqs j)
  have h1 := prod_absorb hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h2 := absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3
theorem transfer : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg => transfer' hC qs hG hqs hf hR hB hP hg
end Abstract
section Lines
variable {V : Type} [Fintype V] [DecidableEq V]
  {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t : ℕ}
  {f : MvPolynomial V (ZMod 2)}
omit [Fintype V] [DecidableEq V] in
theorem totalDegree_eqImage_le (L : LinClause V) :
    ∀ g ∈ (fun q => eqPoly q) '' (↑L : Set (LinEq V)), g.totalDegree ≤ 1 := by
  rintro _ ⟨q, _, rfl⟩
  exact totalDegree_eqPoly_le q
omit [Fintype V] [DecidableEq V] in
theorem totalDegree_clausePoly_le (A : Clause V) : (clausePoly A).totalDegree ≤ A.card := by
  rw [clausePoly_eq_prod]
  exact totalDegree_prod_le A _ fun l _ => totalDegree_eqPoly_le _
omit [Fintype V] in
theorem step_ax (hC : DegClosed C D) (A : Clause V) {w : ℕ} (hA : clausePoly A ∈ C)
    (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2)
      ((fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ q ∈ linOfClause A, (∏ j, (1 + qs j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j =>
    totalDegree_span_le (totalDegree_eqImage_le _) (hqs j)
  have hQ : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h1 := prod_absorb hC A
    (fun l : Literal V => eqPoly ((({l.1} : Finset V), l.2) : LinEq V))
    ((∏ j, (1 + qs j)) * f) hQ
    (fun l hl => by
      have := hH _ (Finset.mem_image.2 ⟨l, hl, rfl⟩)
      have e : eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * ((∏ j, (1 + qs j)) * f)
          = (∏ j, (1 + qs j)) * eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * f := by ring
      rw [e]
      exact this)
    (fun l _ => totalDegree_eqPoly_le _) (by omega)
  rw [← clausePoly_eq_prod] at h1
  have h2 := absorb_le hC ((∏ j, (1 + qs j)) * f) hA hQ (totalDegree_clausePoly_le A)
    (by omega)
  have h3 := C.add_mem h1 h2
  have e : clausePoly A * ((∏ j, (1 + qs j)) * f) + (∏ j, (1 + qs j)) * f
      + (∏ j, (1 + qs j)) * f * clausePoly A = (∏ j, (1 + qs j)) * f := by
    linear_combination char2_add_self (clausePoly A * ((∏ j, (1 + qs j)) * f))
  rwa [e] at h3
theorem step_weak (hC : DegClosed C D) (L M : LinClause V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2))
    (hqL : ∀ j, qL j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB1 : K + 2 * t ≤ D) (hB2 : K + t + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinClauseSat a L → LinClauseSat a M)
    (hPL : (∏ j, (1 + qL j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  refine transfer' hC qL (totalDegree_eqImage_le L) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨J, hJ, hcase⟩ := lin_alter_choice q M fun a ha => himp a ⟨q, hq, ha⟩
  have hsum : (∑ d ∈ J, eqPoly d) * (∏ j, (1 + qM j)) * f ∈ C := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d hd => ?_
    have e : eqPoly d * (∏ j, (1 + qM j)) * f = (∏ j, (1 + qM j)) * eqPoly d * f := by ring
    rw [e]
    exact hHM d (hJ hd)
  rcases hcase with h1 | h2
  · rw [h1, one_mul] at hsum
    have := absorb_le hC (eqPoly q) hsum (totalDegree_eqPoly_le q)
      (totalDegree_mul_le' hdM hf) (by omega)
    rw [mul_assoc]
    exact this
  · rw [h2] at hsum
    exact hsum
omit [Fintype V] in
theorem step_half (hC : DegClosed C D) (L M : LinClause V) (q0 : LinEq V)
    (e' : MvPolynomial V (ZMod 2)) (qL qM : Fin t → MvPolynomial V (ZMod 2))
    (hqL : ∀ j, qL j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t + 2 ≤ D) (he' : e'.totalDegree ≤ 1)
    (hbad : eqPoly q0 * e' * ((∏ j, (1 + qM j)) * f) ∈ C)
    (hsub : ∀ q ∈ L, q ≠ q0 → q ∈ M)
    (hPL : (∏ j, (1 + qL j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    e' * (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  have hdR : (e' * ∏ j, (1 + qM j)).totalDegree ≤ 1 + t := totalDegree_mul_le' he' hdM
  refine transfer' hC qL (totalDegree_eqImage_le L) hqL hf hdR (by omega) hPL ?_
  rintro _ ⟨q, hq, rfl⟩
  by_cases hq0 : q = q0
  · subst hq0
    have e : eqPoly q * (e' * ∏ j, (1 + qM j)) * f
        = eqPoly q * e' * ((∏ j, (1 + qM j)) * f) := by ring
    rw [e]
    exact hbad
  · have hmem := hHM q (hsub q hq hq0)
    have hd : ((∏ j, (1 + qM j)) * eqPoly q * f).totalDegree ≤ t + 1 + K :=
      totalDegree_mul_le' (totalDegree_mul_le' hdM (totalDegree_eqPoly_le q)) hf
    have := absorb_le hC e' hmem he' hd (by omega)
    have e : eqPoly q * (e' * ∏ j, (1 + qM j)) * f
        = e' * ((∏ j, (1 + qM j)) * eqPoly q * f) := by ring
    rw [e]
    exact this
omit [Fintype V] in
theorem step_res (hC : DegClosed C D) (L1 L2 M : LinClause V)
    (q1 q2 qM : Fin t → MvPolynomial V (ZMod 2))
    (hq1 : ∀ j, q1 j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L1 : Set (LinEq V))))
    (hq2 : ∀ j, q2 j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L2 : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t + 2 ≤ D)
    (hres : IsLinResolvent L1 L2 M)
    (hP1 : (∏ j, (1 + q1 j)) * f ∈ C) (hP2 : (∏ j, (1 + q2 j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  obtain ⟨g, hg1, hg2, rfl⟩ := hres
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t + K := totalDegree_mul_le' hdM hf
  have he : eqPoly ((g, false) : LinEq V) = eqPoly ((g, true) : LinEq V) + 1 := by
    simp [eqPoly]
  have hd1 : (eqPoly ((g, true) : LinEq V)).totalDegree ≤ 1 := totalDegree_eqPoly_le _
  have hd0 : (eqPoly ((g, false) : LinEq V)).totalDegree ≤ 1 := totalDegree_eqPoly_le _
  have hidem := affine_idem' hC hd1
  have hdi : (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
      + eqPoly ((g, true) : LinEq V)).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hd1 hd1) (by omega))
  have hbad := absorb_le hC ((∏ j, (1 + qM j)) * f) hidem hQ hdi (by omega)
  have hA := step_half hC L1 _ (g, false) (eqPoly ((g, true) : LinEq V)) q1 qM hq1 hqM hf hB
    hd1
    (by
      have e : eqPoly ((g, false) : LinEq V) * eqPoly ((g, true) : LinEq V)
            * ((∏ j, (1 + qM j)) * f)
          = (∏ j, (1 + qM j)) * f * (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
            + eqPoly ((g, true) : LinEq V)) := by
        rw [he]; ring
      rw [e]
      exact hbad)
    (fun q hq hne => Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hq⟩)) hP1 hHM
  have hB' := step_half hC L2 _ (g, true) (eqPoly ((g, false) : LinEq V)) q2 qM hq2 hqM hf hB
    hd0
    (by
      have e : eqPoly ((g, true) : LinEq V) * eqPoly ((g, false) : LinEq V)
            * ((∏ j, (1 + qM j)) * f)
          = (∏ j, (1 + qM j)) * f * (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
            + eqPoly ((g, true) : LinEq V)) := by
        rw [he]; ring
      rw [e]
      exact hbad)
    (fun q hq hne => Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hq⟩)) hP2 hHM
  have h3 := C.add_mem hA hB'
  have e : eqPoly ((g, true) : LinEq V) * (∏ j, (1 + qM j)) * f
      + eqPoly ((g, false) : LinEq V) * (∏ j, (1 + qM j)) * f = (∏ j, (1 + qM j)) * f := by
    rw [he]
    linear_combination char2_add_self (eqPoly ((g, true) : LinEq V) * (∏ j, (1 + qM j)) * f)
  rwa [e] at h3
end Lines
theorem simulation : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinDerivation ((fun A => linOfClause A) '' F) π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f) := by
  intro V _ _ F π w D K t f qs hw hder hB hf
  have hB1 : K + (2 * t + 2) ≤ D := (Nat.add_le_add_left (le_max_left _ _) K).trans hB
  have hB2 : K + (t + w) ≤ D := (Nat.add_le_add_left (le_max_right _ _) K).trans hB
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ (by omega) fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinClause V), IsLinDerivation ((fun A => linOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2)
        ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
      (∀ L ∈ ρ, ∀ q ∈ L, (∏ j, (1 + qs L j)) * eqPoly q * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        obtain ⟨A, hAF, hA⟩ := hL0
        subst hA
        have hAw := hw A hAF
        have hmem : clausePoly A ∈ pcClosure (cnfSystem F) D :=
          PCDerivable.ax (Or.inr ⟨A, hAF, rfl⟩)
            ((totalDegree_clausePoly_le A).trans (by omega))
        exact step_ax hC A hmem hAw (qs (linOfClause A))
          (hs _ List.mem_cons_self) hf (by omega) (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @res ρ L1 L2 M _ h1 h2 hres ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact step_res hC L1 L2 L (qs L1) (qs L2) (qs L)
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf (by omega) hres (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M _ h1 himp ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact step_weak hC L1 L (qs L1) (qs L)
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf (by omega)
          (by omega) himp (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH
theorem simulation_refutation : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    PCDerivable (cnfSystem F) D f := by
  intro V _ _ F π w D K t f qs hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation V F π w D K t f qs hw hder hB hf hs hH ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa using this
  simpa [hq] using h
end PEqualNP.ProofComplexity.DegSizeSim
namespace PEqualNP.ProofComplexity.Helpers
namespace MonoRank
open Finset MvPolynomial
open scoped FinsetFamily MonomialOrder
section Combinatorial
variable {σ : Type*} [DecidableEq σ] [Fintype σ]
theorem slice_succ_mul_le (𝒜 : Finset (Finset σ)) (h : IsLowerSet (𝒜 : Set (Finset σ)))
    (j : ℕ) :
    (j + 1) * #(𝒜 # (j + 1)) ≤ (Fintype.card σ - j) * #(𝒜 # j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (j + 1) with hj | hj
  · have h0 : 𝒜 # (j + 1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    simp [h0]
  · have h1 := Finset.local_lubell_yamamoto_meshalkin_inequality_mul
      (Finset.sized_slice (𝒜 := 𝒜) (r := j + 1))
    have hsub : ∂ (𝒜 # (j + 1)) ⊆ 𝒜 # j := by
      intro t ht
      obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_shadow_iff.1 ht
      rw [Finset.mem_slice] at hs ⊢
      refine ⟨h (Finset.erase_subset a s) (Finset.mem_coe.2 hs.1), ?_⟩
      rw [Finset.card_erase_of_mem ha, hs.2]
      rfl
    have h2 := Finset.card_le_card hsub
    have h3 : Fintype.card σ - (j + 1) + 1 = Fintype.card σ - j := by omega
    rw [h3] at h1
    calc (j + 1) * #(𝒜 # (j + 1)) = #(𝒜 # (j + 1)) * (j + 1) := Nat.mul_comm _ _
      _ ≤ #(∂ (𝒜 # (j + 1))) * (Fintype.card σ - j) := h1
      _ ≤ #(𝒜 # j) * (Fintype.card σ - j) := Nat.mul_le_mul_right _ h2
      _ = (Fintype.card σ - j) * #(𝒜 # j) := Nat.mul_comm _ _
theorem slice_succ_mul_choose_le (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (j : ℕ) :
    #(𝒜 # (j + 1)) * (Fintype.card σ).choose j
      ≤ #(𝒜 # j) * (Fintype.card σ).choose (j + 1) := by
  have h1 := slice_succ_mul_le 𝒜 h j
  have h2 := Nat.choose_succ_right_eq (Fintype.card σ) j
  refine Nat.le_of_mul_le_mul_left (?_ : (j + 1) * _ ≤ (j + 1) * _) (Nat.succ_pos j)
  calc (j + 1) * (#(𝒜 # (j + 1)) * (Fintype.card σ).choose j)
      = ((j + 1) * #(𝒜 # (j + 1))) * (Fintype.card σ).choose j := by ring
    _ ≤ ((Fintype.card σ - j) * #(𝒜 # j)) * (Fintype.card σ).choose j :=
        Nat.mul_le_mul_right _ h1
    _ = #(𝒜 # j) * ((Fintype.card σ).choose j * (Fintype.card σ - j)) := by ring
    _ = #(𝒜 # j) * ((Fintype.card σ).choose (j + 1) * (j + 1)) := by rw [h2]
    _ = (j + 1) * (#(𝒜 # j) * (Fintype.card σ).choose (j + 1)) := by ring
omit [DecidableEq σ] [Fintype σ] in
theorem mediant_partial_sums (b c : ℕ → ℕ) (k : ℕ) (hc : ∀ j ≤ k, 0 < c j)
    (h : ∀ j ≤ k, b (j + 1) * c j ≤ b j * c (j + 1)) :
    (∑ j ∈ range (k + 2), b j) * (∑ j ∈ range (k + 1), c j)
      ≤ (∑ j ∈ range (k + 1), b j) * (∑ j ∈ range (k + 2), c j) := by
  have key : ∀ l, l ≤ k + 1 → ∀ j ≤ l, b l * c j ≤ b j * c l := by
    intro l
    induction l with
    | zero =>
      intro _ j hj
      obtain rfl : j = 0 := by omega
      exact le_rfl
    | succ l ih =>
      intro hl j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · exact le_rfl
      have i1 := ih (by omega) j (by omega)
      have i2 := h l (by omega)
      have hp := hc l (by omega)
      refine Nat.le_of_mul_le_mul_left (?_ : c l * _ ≤ c l * _) hp
      calc c l * (b (l + 1) * c j) = (b (l + 1) * c l) * c j := by ring
        _ ≤ (b l * c (l + 1)) * c j := Nat.mul_le_mul_right _ i2
        _ = (b l * c j) * c (l + 1) := by ring
        _ ≤ (b j * c l) * c (l + 1) := Nat.mul_le_mul_right _ i1
        _ = c l * (b j * c (l + 1)) := by ring
  rw [Finset.sum_range_succ b (k + 1), Finset.sum_range_succ c (k + 1)]
  have h1 : b (k + 1) * ∑ j ∈ range (k + 1), c j ≤ (∑ j ∈ range (k + 1), b j) * c (k + 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj =>
      key (k + 1) le_rfl j (by have := Finset.mem_range.1 hj; omega)
  rw [add_mul, mul_add]
  exact Nat.add_le_add_left h1 _
theorem downClosed_partial_sums (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (k : ℕ) :
    (∑ j ∈ range (k + 2), #(𝒜 # j)) * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ (∑ j ∈ range (k + 1), #(𝒜 # j))
          * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (k + 1) with hk | hk
  · have h0 : #(𝒜 # (k + 1)) = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    rw [Finset.sum_range_succ (fun j => #(𝒜 # j)) (k + 1), h0, add_zero]
    exact Nat.mul_le_mul_left _
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega)))
  · exact mediant_partial_sums (fun j => #(𝒜 # j)) (fun j => (Fintype.card σ).choose j) k
      (fun j hj => Nat.choose_pos (by omega)) (fun j _ => slice_succ_mul_choose_le 𝒜 h j)
omit [Fintype σ] in
theorem sum_slice_eq_card_filter (𝒜 : Finset (Finset σ)) (k : ℕ) :
    ∑ j ∈ range (k + 1), #(𝒜 # j) = #(𝒜.filter (fun s => #s ≤ k)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))
    (fun s hs => Finset.mem_range.2 (by have := (Finset.mem_filter.1 hs).2; omega))]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  ext s
  have := Finset.mem_range.1 hj
  simp only [Finset.mem_slice, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
omit [Fintype σ] in
theorem isLowerSet_of_erase (𝒜 : Finset (Finset σ))
    (h : ∀ s ∈ 𝒜, ∀ a ∈ s, s.erase a ∈ 𝒜) : IsLowerSet (𝒜 : Set (Finset σ)) := by
  intro s t hts hs
  have key : ∀ u : Finset σ, u ⊆ s → s \ u ∈ 𝒜 := by
    intro u
    induction u using Finset.induction_on with
    | empty => intro _; simpa using hs
    | insert a u ha ih =>
      intro hu
      rw [Finset.sdiff_insert]
      refine h _ (ih ((Finset.subset_insert a u).trans hu)) a ?_
      exact Finset.mem_sdiff.2 ⟨hu (Finset.mem_insert_self a u), ha⟩
  have h1 := key (s \ t) Finset.sdiff_subset
  rw [Finset.sdiff_sdiff_eq_self hts] at h1
  exact Finset.mem_coe.2 h1
end Combinatorial
section Algebraic
variable {σ : Type*} {F : Type*} [Field F]
def leadSet (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) : Set (σ →₀ ℕ) :=
  {d | ∃ q ∈ Z, q ≠ 0 ∧ m.degree q = d}
theorem degree_sub_lt_of_lead_eq (m : MonomialOrder σ) {f g : MvPolynomial σ F}
    (hd : m.degree f = m.degree g) (hc : m.leadingCoeff f = m.leadingCoeff g)
    (hne : f - g ≠ 0) : m.degree (f - g) ≺[m] m.degree f := by
  apply lt_of_le_of_ne
  · have h1 := m.degree_sub_le (f := f) (g := g)
    rw [← hd, sup_idem] at h1
    exact h1
  · intro h'
    have h'' : m.degree (f - g) = m.degree f := m.toSyn.injective h'
    have h2 := m.degree_mem_support hne
    rw [h'', mem_support_iff, coeff_sub] at h2
    apply h2
    have h3 : g.coeff (m.degree f) = m.leadingCoeff g := by rw [hd]; rfl
    rw [h3, ← hc]
    exact sub_self _
theorem linearIndependent_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) :
    LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
  have hli : LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => monomial (d : σ →₀ ℕ) (1 : F)) := by
    have := (MvPolynomial.basisMonomials σ F).linearIndependent.comp
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => (d : σ →₀ ℕ)) Subtype.val_injective
    simpa [Function.comp_def] using this
  refine hli.map ?_
  rw [Submodule.ker_mkQ, Submodule.disjoint_def]
  intro p hp hZ
  by_contra hne
  have hsupp : p ∈ restrictSupport F ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) := by
    rw [restrictSupport_eq_span, Set.image_eq_range]
    exact hp
  have h1 : m.degree p ∈ ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) :=
    ((mem_restrictSupport_iff F).1 hsupp) (Finset.mem_coe.2 (m.degree_mem_support hne))
  exact h1 ⟨p, hZ, hne, rfl⟩
theorem mkQ_mem_span_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F))
    (p : MvPolynomial σ F) :
    Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
      {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
  suffices H : ∀ a : m.syn, ∀ p : MvPolynomial σ F, m.toSyn (m.degree p) = a →
      Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
        {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) from H _ p rfl
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro p hpa
    by_cases hp : p = 0
    · rw [hp, map_zero]
      exact Submodule.zero_mem _
    have hc : m.leadingCoeff p ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hp
    obtain ⟨g, hgd, hgc, hgmem⟩ : ∃ g : MvPolynomial σ F, m.degree g = m.degree p ∧
        m.leadingCoeff g = m.leadingCoeff p ∧
        Z.mkQ g ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
          {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
      by_cases hd : m.degree p ∈ leadSet m Z
      · obtain ⟨q, hqZ, hq0, hqd⟩ := hd
        have hcq : m.leadingCoeff q ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hq0
        have hr : m.leadingCoeff p / m.leadingCoeff q ≠ 0 := div_ne_zero hc hcq
        have hdeg : m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q) = m.degree p := by
          rw [m.degree_smul_of_isRegular (IsRegular.of_ne_zero hr), hqd]
        refine ⟨(m.leadingCoeff p / m.leadingCoeff q) • q, hdeg, ?_, ?_⟩
        · show ((m.leadingCoeff p / m.leadingCoeff q) • q).coeff
            (m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q)) = _
          rw [hdeg, coeff_smul, smul_eq_mul, ← hqd]
          exact div_mul_cancel₀ _ hcq
        · have : Z.mkQ ((m.leadingCoeff p / m.leadingCoeff q) • q) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Z.smul_mem _ hqZ
          rw [this]
          exact Submodule.zero_mem _
      · classical
        refine ⟨monomial (m.degree p) (m.leadingCoeff p), ?_, ?_, ?_⟩
        · rw [m.degree_monomial, if_neg hc]
        · exact m.leadingCoeff_monomial _
        · have : monomial (m.degree p) (m.leadingCoeff p)
              = m.leadingCoeff p • monomial (m.degree p) (1 : F) := by
            rw [smul_monomial, smul_eq_mul, mul_one]
          rw [this, map_smul]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨m.degree p, ⟨hd, le_rfl⟩, rfl⟩)
    have hsplit : Z.mkQ p = Z.mkQ (p - g) + Z.mkQ g := by
      rw [← map_add, sub_add_cancel]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ hgmem
    by_cases hpg : p - g = 0
    · rw [hpg, map_zero]
      exact Submodule.zero_mem _
    have hlt : m.degree (p - g) ≺[m] m.degree p :=
      degree_sub_lt_of_lead_eq m hgd.symm hgc.symm hpg
    have h1 := ih (m.toSyn (m.degree (p - g))) (hpa ▸ hlt) (p - g) rfl
    refine Submodule.span_mono (Set.image_mono ?_) h1
    rintro d ⟨hd1, hd2⟩
    exact ⟨hd1, hd2.trans hlt.le⟩
section DegLex
variable [LinearOrder σ] [WellFoundedGT σ]
theorem map_restrictTotalDegree_eq_span (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    (restrictTotalDegree σ F k).map Z.mkQ
      = Submodule.span F (Set.range
          (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
            Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F)))) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ k := (mem_restrictTotalDegree σ k p).1 hp
    refine Submodule.span_mono ?_ (mkQ_mem_span_std MonomialOrder.degLex Z p)
    rintro _ ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have h1 : d.degree ≤ (MonomialOrder.degLex.degree p).degree :=
      Finsupp.DegLex.monotone_degree hd2
    rw [degree_degLexDegree] at h1
    exact ⟨⟨d, hd1, h1.trans hp'⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨d, hd1, hd2⟩, rfl⟩
    refine ⟨monomial d 1, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree, totalDegree_monomial _ one_ne_zero]
    exact hd2
theorem finrank_map_restrictTotalDegree (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
      = Set.ncard {d : σ →₀ ℕ | d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} := by
  have hli : LinearIndependent F
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
    have := (linearIndependent_std MonomialOrder.degLex Z).comp
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        (⟨d.1, d.2.1⟩ : ((leadSet MonomialOrder.degLex Z)ᶜ : Set (σ →₀ ℕ))))
      (by intro a b hab; simp only [Subtype.mk.injEq] at hab; exact Subtype.ext hab)
    simpa [Function.comp_def] using this
  rw [map_restrictTotalDegree_eq_span, Module.finrank_eq_nat_card_basis (Module.Basis.span hli)]
  rfl
noncomputable def ind (s : Finset σ) : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1
omit [WellFoundedGT σ] in
theorem ind_apply (s : Finset σ) (i : σ) : ind s i = if i ∈ s then 1 else 0 := by
  classical
  simp [ind, Finsupp.single_apply]
omit [WellFoundedGT σ] in
theorem ind_degree (s : Finset σ) : (ind s).degree = #s := by
  simp [ind]
omit [WellFoundedGT σ] in
theorem ind_injective : Function.Injective (ind : Finset σ → σ →₀ ℕ) := by
  intro s t h
  ext i
  have h1 := DFunLike.congr_fun h i
  rw [ind_apply, ind_apply] at h1
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
omit [WellFoundedGT σ] in
theorem ind_support_of_le_one (d : σ →₀ ℕ) (h : ∀ i, d i ≤ 1) : ind d.support = d := by
  ext i
  rw [ind_apply]
  have := h i
  by_cases hi : i ∈ d.support
  · rw [if_pos hi]
    have := Finsupp.mem_support_iff.1 hi
    omega
  · rw [if_neg hi]
    exact (Finsupp.notMem_support_iff.1 hi).symm
variable (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
theorem std_le_one
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ) :
    d i ≤ 1 := by
  classical
  by_contra hi
  apply hd
  set e : σ →₀ ℕ := d - Finsupp.single i 2 with he
  have hde : d = e + Finsupp.single i 2 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [he]; omega
    · simp [he, Finsupp.single_apply, Ne.symm hj]
  have hdeg : e.degree + 2 = d.degree := by
    rw [hde, map_add, Finsupp.degree_single]
  have hq : monomial e (1 : F) * (X i ^ 2 - X i)
      = monomial (e + Finsupp.single i 2) (1 : F) - monomial (e + Finsupp.single i 1) (1 : F) := by
    rw [mul_sub, X_pow_eq_monomial, monomial_mul, X, monomial_mul, mul_one]
  have hlt : MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 1) (1 : F))
      ≺[MonomialOrder.degLex]
      MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 2) (1 : F)) := by
    rw [MonomialOrder.degree_monomial, MonomialOrder.degree_monomial, if_neg one_ne_zero,
      if_neg one_ne_zero]
    apply MonomialOrder.degLex.toSyn_strictMono
    apply lt_of_le_of_ne
    · exact add_le_add le_rfl (Finsupp.single_le_single.2 (show (1 : ℕ) ≤ 2 by omega))
    · intro h
      have := DFunLike.congr_fun h i
      simp at this
  refine ⟨monomial e (1 : F) * (X i ^ 2 - X i), hB e i (by omega), ?_, ?_⟩
  · rw [hq]
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [hq, MonomialOrder.degree_sub_of_lt hlt, MonomialOrder.degree_monomial,
      if_neg one_ne_zero, ← hde]
theorem std_sub_single
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ)
    (hi : 1 ≤ d i) : d - Finsupp.single i 1 ∉ leadSet MonomialOrder.degLex Z := by
  classical
  rintro ⟨q, hqZ, hq0, hqd⟩
  apply hd
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  have hdeg : 1 + (d - Finsupp.single i 1).degree = d.degree := by
    conv_rhs => rw [hde, map_add, Finsupp.degree_single]
  have hqt : q.totalDegree < K := by
    rw [← degree_degLexDegree, hqd]
    omega
  have hXne : (X i : MvPolynomial σ F) ≠ 0 := X_ne_zero i
  refine ⟨X i * q, hX q hqZ hqt i, mul_ne_zero hXne hq0, ?_⟩
  rw [MonomialOrder.degree_mul hXne hq0, MonomialOrder.degree_X, hqd, ← hde]
end DegLex
end Algebraic
section Combined
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F]
theorem exists_downClosed_family [DecidableEq σ] (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z) :
    ∃ 𝒜 : Finset (Finset σ), IsLowerSet (𝒜 : Set (Finset σ)) ∧ ∀ k ≤ K,
      Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        = ∑ j ∈ range (k + 1), #(𝒜 # j) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  set L := leadSet (F := F) MonomialOrder.degLex Z with hL
  refine ⟨Finset.univ.filter (fun s => ind s ∉ L ∧ #s ≤ K), ?_, ?_⟩
  · apply isLowerSet_of_erase
    intro s hs a ha
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨-, hs1, hs2⟩ := hs
    refine ⟨Finset.mem_univ _, ?_, (Finset.card_erase_le).trans hs2⟩
    have h1 : ind (s.erase a) = ind s - Finsupp.single a 1 := by
      ext j
      rw [Finsupp.tsub_apply, ind_apply, ind_apply, Finsupp.single_apply]
      by_cases hj : a = j
      · subst hj; simp [ha]
      · simp [hj, Ne.symm hj]
    rw [h1]
    exact std_sub_single Z K hX (ind s) hs1 (by rw [ind_degree]; exact hs2) a
      (by rw [ind_apply, if_pos ha])
  · intro k hk
    rw [finrank_map_restrictTotalDegree, sum_slice_eq_card_filter, ← Set.ncard_coe_finset,
      ← Set.ncard_image_of_injective _ ind_injective]
    congr 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd1, hd2⟩
      have h1 : ind d.support = d :=
        ind_support_of_le_one d (std_le_one Z K hB d hd1 (hd2.trans hk))
      have h2 : #d.support = d.degree := by rw [← ind_degree, h1]
      refine ⟨d.support, ⟨⟨?_, ?_⟩, ?_⟩, h1⟩
      · rw [h1]; exact hd1
      · omega
      · omega
    · rintro ⟨s, ⟨⟨hs1, _⟩, hs3⟩, rfl⟩
      exact ⟨hs1, by rw [ind_degree]; exact hs3⟩
theorem rank_ratio_monotone (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (k : ℕ) (hk : k + 1 ≤ K) :
    Module.finrank F ((restrictTotalDegree σ F (k + 1)).map Z.mkQ)
        * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  classical
  obtain ⟨𝒜, h𝒜, hc⟩ := exists_downClosed_family Z K hX hB
  rw [hc (k + 1) hk, hc k (by omega)]
  exact downClosed_partial_sums 𝒜 h𝒜 k
end Combined
end MonoRank
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
open Module
section Abstract
variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
theorem threeTerm_finrank [FiniteDimensional F U] (I A B L : Submodule F U)
    (h : L ⊓ (A ⊔ B) ≤ A ⊓ B) :
    finrank F ↥(I ⊓ A) + finrank F ↥(I ⊓ B) + finrank F ↥(I ⊓ L)
      ≤ finrank F ↥I + 2 * finrank F ↥(I ⊓ A ⊓ B) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (I ⊓ A) (I ⊓ B)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq ((I ⊓ A) ⊔ (I ⊓ B)) (I ⊓ L)
  have hPQ : (I ⊓ A) ⊓ (I ⊓ B) = I ⊓ A ⊓ B := by
    rw [← inf_inf_distrib_left, inf_assoc]
  have hup : ((I ⊓ A) ⊔ (I ⊓ B)) ⊔ (I ⊓ L) ≤ I :=
    sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hdown : ((I ⊓ A) ⊔ (I ⊓ B)) ⊓ (I ⊓ L) ≤ I ⊓ A ⊓ B := by
    rw [inf_assoc]
    refine le_inf ?_ ?_
    · exact inf_le_right.trans inf_le_left
    · refine le_trans ?_ h
      exact le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (sup_le_sup inf_le_right inf_le_right))
  have h1 := Submodule.finrank_mono hup
  have h2 := Submodule.finrank_mono hdown
  rw [hPQ] at e1
  omega
variable {G : Type*}
noncomputable def subDim (S : Submodule F U) : ℕ := finrank F ↥S
theorem subDim_mono [FiniteDimensional F U] {S T : Submodule F U} (h : S ≤ T) :
    subDim S ≤ subDim T := Submodule.finrank_mono h
theorem subDim_top : subDim (⊤ : Submodule F U) = finrank F U := finrank_top F U
noncomputable def kerSum [Add G] (K : G → Submodule F U) : G → List G → ℕ
  | c, [] => subDim (K c)
  | c, b :: bs => kerSum K c bs + kerSum K (c + b) bs
def listInf (K : G → Submodule F U) : List G → Submodule F U
  | [] => ⊤
  | b :: bs => K b ⊓ listInf K bs
theorem listInf_le (K : G → Submodule F U) {b : G} :
    ∀ {bs : List G}, b ∈ bs → listInf K bs ≤ K b
  | [], hb => by simp at hb
  | a :: bs, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact inf_le_left
    · exact inf_le_right.trans (listInf_le K hb)
private theorem arith_step (N S1 S2 dI dU d1 d2 d3 dJ dJ' : ℕ)
    (ih1 : 2 * S1 + N * dI ≤ N * dU + 2 * (N * d1))
    (ih2 : 2 * S2 + N * dI ≤ N * dU + 2 * (N * d2))
    (tt : d1 + d2 + d3 ≤ dI + 2 * dJ) (hJ : dJ ≤ dJ') :
    2 * (S1 + S2) + (2 * N) * d3 ≤ (2 * N) * dU + 2 * ((2 * N) * dJ') := by
  nlinarith [Nat.mul_le_mul_left N tt, Nat.mul_le_mul_left N hJ]
theorem kerSum_le [Add G] [FiniteDimensional F U] (K : G → Submodule F U)
    (hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b)
    (hthree : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b)) :
    ∀ (bs : List G) (c : G),
      2 * kerSum K c bs + 2 ^ bs.length * subDim (listInf K bs)
        ≤ 2 ^ bs.length * finrank F U
          + 2 * (2 ^ bs.length * subDim (listInf K bs ⊓ K c))
  | [], c => by
    have h1 : listInf K ([] : List G) = ⊤ := rfl
    have h2 : kerSum K c [] = subDim (K c) := rfl
    rw [h1, h2, top_inf_eq, subDim_top]
    simp only [List.length_nil, pow_zero, one_mul]
    omega
  | b :: bs, c => by
    have ih1 := kerSum_le K hadd hthree bs c
    have ih2 := kerSum_le K hadd hthree bs (c + b)
    have tt : subDim (listInf K bs ⊓ K c) + subDim (listInf K bs ⊓ K (c + b))
        + subDim (K b ⊓ listInf K bs)
        ≤ subDim (listInf K bs) + 2 * subDim (listInf K bs ⊓ K c ⊓ K (c + b)) := by
      have := threeTerm_finrank (listInf K bs) (K c) (K (c + b)) (K b) (hthree c b)
      rw [inf_comm (listInf K bs) (K b)] at this
      exact this
    have hJ : listInf K bs ⊓ K c ⊓ K (c + b) ≤ K b ⊓ listInf K bs ⊓ K c := by
      refine le_inf (le_inf ?_ (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (hadd c b)
    have hJ' := subDim_mono hJ
    have h1 : listInf K (b :: bs) = K b ⊓ listInf K bs := rfl
    have h2 : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [h1, h2, hp]
    have hU := arith_step (2 ^ bs.length) _ _ _ (finrank F U) _ _ _ _ _ ih1 ih2 tt hJ'
    exact hU
theorem exists_le_kerSum [Add G] (K : G → Submodule F U) :
    ∀ (bs : List G) (c : G), ∃ c', 2 ^ bs.length * subDim (K c') ≤ kerSum K c bs
  | [], c => ⟨c, by simp [kerSum]⟩
  | b :: bs, c => by
    obtain ⟨c1, h1⟩ := exists_le_kerSum K bs c
    obtain ⟨c2, h2⟩ := exists_le_kerSum K bs (c + b)
    have e : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [e, hp]
    rcases le_total (subDim (K c1)) (subDim (K c2)) with h | h
    · refine ⟨c1, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
    · refine ⟨c2, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
end Abstract
section Maps
variable {F U W G : Type*} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup W]
  [Module F W] [AddCommGroup G]
theorem exists_two_mul_finrank_ker_le [FiniteDimensional F U] (Φ : G →+ (U →ₗ[F] W))
    (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (bs : List G) :
    ∃ c : G, 2 * finrank F ↥(LinearMap.ker (Φ c))
      ≤ finrank F U + finrank F ↥(listInf (fun c => LinearMap.ker (Φ c)) bs) := by
  set K : G → Submodule F U := fun c => LinearMap.ker (Φ c) with hKdef
  have hcancel : ∀ c b : G, c + (c + b) = b := fun c b => by
    rw [← add_assoc, h2, zero_add]
  have hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b := by
    intro c b f hf
    have h1 : Φ c f = 0 := hf.1
    have h3 : Φ (c + b) f = 0 := hf.2
    have : Φ b f = 0 := by
      rw [map_add, LinearMap.add_apply, h1, zero_add] at h3
      exact h3
    exact this
  have hthree' : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b) := by
    intro c b f hf
    have hb : Φ b f = 0 := hf.1
    refine ⟨?_, ?_⟩
    · exact hthree c (c + b) f (by rw [hcancel]; exact hb) hf.2
    · refine hthree (c + b) c f ?_ ?_
      · rw [add_comm, hcancel]; exact hb
      · have := hf.2
        rwa [sup_comm] at this
  have key := kerSum_le K hadd hthree' bs 0
  obtain ⟨c, hc⟩ := exists_le_kerSum K bs (0 : G)
  refine ⟨c, ?_⟩
  have hle : subDim (listInf K bs ⊓ K 0) ≤ subDim (listInf K bs) := subDim_mono inf_le_left
  have hpos : 0 < 2 ^ bs.length := by positivity
  have t := Nat.mul_le_mul_left (2 ^ bs.length) hle
  have : 2 ^ bs.length * (2 * subDim (K c))
      ≤ 2 ^ bs.length * (finrank F U + subDim (listInf K bs)) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this hpos
theorem rank_retention [FiniteDimensional F U] {W' : Type*} [AddCommGroup W'] [Module F W']
    (Φ : G →+ (U →ₗ[F] W)) (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (S : U →ₗ[F] W') (bs : List G)
    (hS : ∀ f : U, (∀ b ∈ bs, Φ b f = 0) → S f = 0) :
    ∃ c : G, finrank F ↥(LinearMap.range S) ≤ 2 * finrank F ↥(LinearMap.range (Φ c)) := by
  obtain ⟨c, hc⟩ := exists_two_mul_finrank_ker_le Φ h2 hthree bs
  refine ⟨c, ?_⟩
  have hI : listInf (fun c => LinearMap.ker (Φ c)) bs ≤ LinearMap.ker S := by
    intro f hf
    exact hS f fun b hb => listInf_le (fun c => LinearMap.ker (Φ c)) hb hf
  have hI' := Submodule.finrank_mono hI
  have r1 := LinearMap.finrank_range_add_finrank_ker S
  have r2 := LinearMap.finrank_range_add_finrank_ker (Φ c)
  omega
end Maps
section Multiplication
open MvPolynomial
variable {σ ι τ : Type*}
noncomputable def mulMap (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) :
    ↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C) :=
  LinearMap.pi fun α => C.mkQ ∘ₗ LinearMap.mulRight (ZMod 2) (q * h α) ∘ₗ U.subtype
theorem mulMap_apply_eq_zero (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) (f : ↥U) :
    mulMap C U h q f = 0 ↔ ∀ α, (f : MvPolynomial σ (ZMod 2)) * q * h α ∈ C := by
  rw [funext_iff]
  refine forall_congr' fun α => ?_
  simp [mulMap, mul_assoc]
noncomputable def comb [Fintype ι] (g : ι → MvPolynomial σ (ZMod 2)) (c : ι → ZMod 2) :
    MvPolynomial σ (ZMod 2) := ∑ i, c i • g i
theorem rank_retention_mul [Fintype ι]
    (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (g : ι → MvPolynomial σ (ZMod 2)) (h : τ → MvPolynomial σ (ZMod 2))
    (hmul : ∀ (c c' : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * comb g c * h α ∈ C → f * comb g c * comb g c' * h α ∈ C)
    (hidem : ∀ (c : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * (comb g c * comb g c + comb g c) * h α ∈ C) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi fun i => mulMap C U h (g i)))
        ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (mulMap C U h (comb g c))) := by
  classical
  have hcomb_add : ∀ a b : ι → ZMod 2, comb g (a + b) = comb g a + comb g b := fun a b => by
    simp [comb, add_smul, Finset.sum_add_distrib]
  have hcomb_single : ∀ i : ι, comb g (Pi.single i 1) = g i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • g j = g i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let Φ : (ι → ZMod 2) →+ (↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C)) :=
    { toFun := fun c => mulMap C U h (comb g c)
      map_zero' := by
        ext f α
        simp [mulMap, comb]
      map_add' := fun a b => by
        ext f α
        simp [mulMap, hcomb_add, add_mul, mul_add, mul_assoc] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hthree : ∀ a b : ι → ZMod 2, ∀ f : ↥U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0 := by
    intro a b f hab hf
    obtain ⟨fa, hfa, fb, hfb, rfl⟩ := Submodule.mem_sup.1 hf
    have hfa' : ∀ α, (fa : MvPolynomial σ (ZMod 2)) * comb g a * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g a) fa).1 hfa
    have hfb' : ∀ α, (fb : MvPolynomial σ (ZMod 2)) * comb g b * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g b) fb).1 hfb
    have hab' : ∀ α, ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g (a + b)) (fa + fb)).1 hab
    refine (mulMap_apply_eq_zero C U h (comb g a) (fa + fb)).2 fun α => ?_
    have A1 := hmul a b α fa fa.2 (hfa' α)
    have A2 := hmul b a α fb fb.2 (hfb' α)
    have A3 := hmul (a + b) a α _ (fa + fb).2 (hab' α)
    have A4 := hidem a α _ (fa + fb).2
    have e : ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g a * h α
        = ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * (comb g a * comb g a + comb g a) * h α
          - ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * comb g a * h α
          + ((fa : MvPolynomial σ (ZMod 2)) * comb g a * comb g b * h α
            + (fb : MvPolynomial σ (ZMod 2)) * comb g b * comb g a * h α) := by
      rw [hcomb_add, Submodule.coe_add]
      ring
    rw [e]
    exact C.add_mem (C.sub_mem A4 A3) (C.add_mem A1 A2)
  obtain ⟨c, hc⟩ := rank_retention Φ h2 hthree
    (LinearMap.pi fun i => mulMap C U h (g i))
    (Finset.univ.toList.map fun i => Pi.single i 1) (by
      intro f hf
      funext i
      have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
      have e : Φ (Pi.single i 1) = mulMap C U h (g i) := by
        show mulMap C U h (comb g (Pi.single i 1)) = _
        rw [hcomb_single]
      rw [e] at this
      simpa using this)
  exact ⟨c, hc⟩
noncomputable def affine [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) : MvPolynomial σ (ZMod 2) :=
  C a + ∑ j, C (B j) * X j
theorem comb_affine [Fintype σ] [Fintype ι] (a : ι → ZMod 2) (B : ι → σ → ZMod 2)
    (c : ι → ZMod 2) :
    comb (fun i => affine (a i) (B i)) c
      = affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) := by
  simp only [comb, affine, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · simp [map_sum, smul_eq_C_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_sum, Finset.sum_mul, smul_eq_C_mul, mul_assoc]
theorem affine_totalDegree_le [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    (affine a B).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine totalDegree_finsetSum_le fun j _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]
theorem affine_idem [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    affine a B * affine a B + affine a B = ∑ j, C (B j) * (X j * X j + X j) := by
  have ha : ∀ x : ZMod 2, x * x = x := by decide
  have hC : ∀ x : ZMod 2, (C x : MvPolynomial σ (ZMod 2)) * C x = C x := fun x => by
    rw [← C_mul, ha]
  have e1 : (∑ j, (C (B j) : MvPolynomial σ (ZMod 2)) * X j) * (∑ j, C (B j) * X j)
      = ∑ j, C (B j) * (X j * X j) := by
    rw [← sq, CharTwo.sum_sq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
    calc (C (B j) : MvPolynomial σ (ZMod 2)) * X j * (C (B j) * X j)
        = (C (B j) * C (B j)) * (X j * X j) := by ring
      _ = C (B j) * (X j * X j) := by rw [hC]
  rw [affine, CharTwo.add_mul_self, hC, e1]
  have e2 : ∀ u v w : MvPolynomial σ (ZMod 2), u + v + (u + w) = (u + u) + (v + w) :=
    fun u v w => by ring
  rw [e2, CharTwo.add_self_eq_zero, zero_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring
theorem rank_retention_closure [Fintype σ] [Fintype ι]
    (Cl U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (D k d : ℕ)
    (hX : ∀ p ∈ Cl, p.totalDegree < D → ∀ j, X j * p ∈ Cl)
    (hBool : ∀ p : MvPolynomial σ (ZMod 2), p.totalDegree + 2 ≤ D →
      ∀ j, p * (X j * X j + X j) ∈ Cl)
    (hU : ∀ f ∈ U, f.totalDegree ≤ k)
    (a : ι → ZMod 2) (B : ι → σ → ZMod 2) (h : τ → MvPolynomial σ (ZMod 2))
    (hh : ∀ α, (h α).totalDegree ≤ d) (hD : d + k + 2 ≤ D) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2)
          ↥(LinearMap.range (LinearMap.pi fun i => mulMap Cl U h (affine (a i) (B i))))
        ≤ 2 * finrank (ZMod 2)
          ↥(LinearMap.range (mulMap Cl U h (comb (fun i => affine (a i) (B i)) c))) := by
  have hmulaff : ∀ p ∈ Cl, p.totalDegree < D → ∀ (a' : ZMod 2) (B' : σ → ZMod 2),
      p * affine a' B' ∈ Cl := by
    intro p hp hdeg a' B'
    have e : p * affine a' B' = a' • p + ∑ j, B' j • (X j * p) := by
      rw [affine, mul_add, Finset.mul_sum]
      congr 1
      · rw [smul_eq_C_mul, mul_comm]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_C_mul]
        ring
    rw [e]
    exact Cl.add_mem (Cl.smul_mem _ hp)
      (Cl.sum_mem fun j _ => Cl.smul_mem _ (hX p hp hdeg j))
  refine rank_retention_mul Cl U (fun i => affine (a i) (B i)) h ?_ ?_
  · intro c c' α f hf hmem
    rw [comb_affine] at hmem ⊢
    rw [comb_affine]
    have hdeg : (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) * h α).totalDegree
        < D := by
      have h1 := totalDegree_mul
        (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)) (h α)
      have h2 := totalDegree_mul f (affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j))
      have h3 := hU f hf
      have h4 := hh α
      have h5 := affine_totalDegree_le (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)
      omega
    have := hmulaff _ hmem hdeg (∑ i, c' i * a i) (fun j => ∑ i, c' i * B i j)
    have e : ∀ u v w x : MvPolynomial σ (ZMod 2), u * v * w * x = u * v * x * w :=
      fun u v w x => by ring
    rw [e]
    exact this
  · intro c α f hf
    rw [comb_affine, affine_idem]
    have e : f * (∑ j, C (∑ i, c i * B i j) * (X j * X j + X j)) * h α
        = ∑ j, (∑ i, c i * B i j) • ((f * h α) * (X j * X j + X j)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]
      ring
    rw [e]
    refine Cl.sum_mem fun j _ => Cl.smul_mem _ (hBool _ ?_ j)
    have h1 := totalDegree_mul f (h α)
    have h3 := hU f hf
    have h4 := hh α
    omega
end Multiplication
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.DegSizeRank
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
section Glue
variable {σ : Type}
theorem exists_single_add (d : σ →₀ ℕ) (hd : d ≠ 0) :
    ∃ (i : σ) (e : σ →₀ ℕ), d = Finsupp.single i 1 + e ∧ e.degree + 1 = d.degree := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Finsupp.ext h)
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp [Ne.symm hj]
  refine ⟨i, d - Finsupp.single i 1, hde, ?_⟩
  have h := congrArg Finsupp.degree hde
  rw [map_add, Finsupp.degree_single] at h
  omega
theorem totalDegree_monomial_one (d : σ →₀ ℕ) :
    (monomial d (1 : ZMod 2)).totalDegree = d.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl
theorem bool_totalDegree_le (v : σ) :
    (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_X]
    omega
theorem monomial_mul_mem {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (hC : DegClosed C D) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree = n → ∀ f ∈ C, n + f.totalDegree ≤ D →
      monomial d (1 : ZMod 2) * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro d hd f hf _
    have h0 : d = 0 := by
      by_contra hne
      obtain ⟨i, e, -, he⟩ := exists_single_add d hne
      omega
    subst h0
    simpa using hf
  | succ n ih =>
    intro d hd f hf hdeg
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, e, hde, he⟩ := exists_single_add d hne
    have h1 := ih e (by omega) f hf (by omega)
    have h2 : (monomial e (1 : ZMod 2) * f).totalDegree + 1 ≤ D := by
      have h3 := totalDegree_mul (monomial e (1 : ZMod 2)) f
      have h4 := totalDegree_monomial_one e
      omega
    have h5 := hC.mulX i _ h1 h2
    have e5 : monomial d (1 : ZMod 2) * f = X i * (monomial e 1 * f) := by
      rw [hde, ← mul_assoc]
      congr 1
      rw [X, monomial_mul_monomial, mul_one]
    rw [e5]
    exact h5
theorem absorb {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ} (hC : DegClosed C D)
    (f g : MvPolynomial σ (ZMod 2)) (hf : f ∈ C) (hdeg : g.totalDegree + f.totalDegree ≤ D) :
    g * f ∈ C := by
  have e : g * f = ∑ v ∈ g.support, g.coeff v • (monomial v (1 : ZMod 2) * f) := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine C.sum_mem fun v hv => C.smul_mem _ (monomial_mul_mem hC _ v rfl f hf ?_)
  have h1 : v.degree ≤ g.totalDegree := le_totalDegree hv
  omega
instance finite_restrictTotalDegree [Finite σ] (k : ℕ) :
    Module.Finite (ZMod 2) ↥(restrictTotalDegree σ (ZMod 2) k) := by
  have hfin : Finite ↥{u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k} :=
    Set.Finite.to_subtype ((Finsupp.finite_of_degree_le k).subset fun u hu => hu)
  exact Module.Finite.of_basis
    (basisRestrictSupport (ZMod 2) {u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k})
theorem errRank_eq_range [Finite σ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (M : Set (MvPolynomial σ (ZMod 2)))
    (k : ℕ) (L : ↥(polyLE σ k) →ₗ[ZMod 2] W)
    (hL : ∀ f : ↥(polyLE σ k), L f = 0 ↔ ∀ m ∈ M, m * (f : MvPolynomial σ (ZMod 2)) ∈ C) :
    finrank (ZMod 2) ↥(LinearMap.range L) = errRank C M k := by
  have hle : errKer C M k ≤ polyLE σ k := inf_le_left
  have hker : LinearMap.ker L = (errKer C M k).comap (polyLE σ k).subtype := by
    ext f
    rw [LinearMap.mem_ker, hL, Submodule.mem_comap, mem_errKer]
    exact ⟨fun h => ⟨(mem_restrictTotalDegree σ k _).1 f.2, h⟩, fun h => h.2⟩
  have r := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at r
  unfold errRank
  omega
noncomputable def annih (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)
theorem mem_annih {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ annih C M ↔ ∀ m ∈ M, m * f ∈ C := by
  simp [annih]
theorem errRank_eq_map [Finite σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errRank C M k = finrank (ZMod 2) ↥((polyLE σ k).map (annih C M).mkQ) := by
  rw [← errRank_eq_range C M k ((annih C M).mkQ ∘ₗ (polyLE σ k).subtype)
    (fun f => by simp [mem_annih]), LinearMap.range_comp, Submodule.range_subtype]
theorem iterate_ratio (c N : ℕ → ℕ) (K : ℕ) (hpos : ∀ j, 0 < N j)
    (step : ∀ j, j + 1 ≤ K → c (j + 1) * N j ≤ c j * N (j + 1)) (k : ℕ) :
    ∀ t, k + t ≤ K → c (k + t) * N k ≤ c k * N (k + t) := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ t ih =>
    intro hK
    have h1 := ih (by omega)
    have h2 := step (k + t) (by omega)
    have h3 : c (k + t + 1) * N k * N (k + t) ≤ c k * N (k + t + 1) * N (k + t) := by
      calc c (k + t + 1) * N k * N (k + t) = c (k + t + 1) * N (k + t) * N k := by ring
        _ ≤ c (k + t) * N (k + t + 1) * N k := Nat.mul_le_mul_right _ h2
        _ = c (k + t) * N k * N (k + t + 1) := by ring
        _ ≤ c k * N (k + t) * N (k + t + 1) := Nat.mul_le_mul_right _ h1
        _ = c k * N (k + t + 1) * N (k + t) := by ring
    exact Nat.le_of_mul_le_mul_right h3 (hpos (k + t))
theorem exists_affine [Fintype σ] (g : MvPolynomial σ (ZMod 2)) (hg : g.totalDegree ≤ 1) :
    ∃ (a : ZMod 2) (B : σ → ZMod 2), g = affine a B := by
  classical
  refine ⟨g.coeff 0, fun j => g.coeff (Finsupp.single j 1), ?_⟩
  ext d
  by_cases hd : 1 < d.degree
  · rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hg hd),
      coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt (affine_totalDegree_le _ _) hd)]
  · by_cases h0 : d = 0
    · subst h0
      simp [affine, coeff_C_mul]
    · obtain ⟨i, e, hde, he⟩ := exists_single_add d h0
      have he0 : e = 0 := by
        by_contra hne
        obtain ⟨_, _, -, he'⟩ := exists_single_add e hne
        omega
      subst he0
      rw [add_zero] at hde
      subst hde
      have h0' : ¬ ((0 : σ →₀ ℕ) = Finsupp.single i 1) := fun h => h0 h.symm
      simp [affine, coeff_C_mul, coeff_X, Finsupp.single_left_inj, h0']
end Glue
theorem monoRank_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
      ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
        errRank C (zMul P G) k' * numMono (Fintype.card σ) k
          ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k' := by
  intro σ _ C D a K P G hC hP hG hD
  have hmdeg : ∀ m ∈ zMul P G, m.totalDegree ≤ a + 1 := by
    rintro _ ⟨g, hg, rfl⟩
    show (P * g).totalDegree ≤ a + 1
    have h1 := totalDegree_mul P g
    have h2 := hG g hg
    omega
  have hX : ∀ p ∈ annih C (zMul P G), p.totalDegree < K → ∀ i : σ,
      X i * p ∈ annih C (zMul P G) := by
    intro p hp hdeg i
    rw [mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ annih C (zMul P G) := by
    intro d i hd
    rw [mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := totalDegree_monomial_one d
    have h3 := bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C (zMul P G) (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C (zMul P G) j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [errRank_eq_map, errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (annih C (zMul P G)) K hX hB j hj
  have hpos : ∀ j, 0 < numMono (Fintype.card σ) j := by
    intro j
    unfold numMono
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  intro k k' hkk' hk'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  exact iterate_ratio (fun j => errRank C (zMul P G) j) (fun j => numMono (Fintype.card σ) j)
    K hpos step k t hk'
theorem rankRetention_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
      (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
      b + k + 2 ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) k
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
  classical
  intro σ _ C D b k H G hC hH hG hD
  have haff : ∀ i : ↥G, ∃ (a : ZMod 2) (B : σ → ZMod 2),
      (i : MvPolynomial σ (ZMod 2)) = affine a B := fun i => exists_affine _ (hG i i.2)
  choose a B hab using haff
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  obtain ⟨c, hc⟩ := rank_retention_closure (ι := ↥G) (τ := ↥H) C (polyLE σ k) D k b
    (fun p hp hdeg j => hC.mulX j p hp (by omega))
    (fun p hp j => absorb hC _ _ (hC.bool j) (by
      have h1 := bool_totalDegree_le (σ := σ) j
      omega))
    (fun f hf => (mem_restrictTotalDegree σ k f).1 hf)
    a B hfun (fun α => hH α α.2) hD
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb (fun i => affine (a i) (B i)) c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • affine (a i) (B i) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    rw [← hab i]
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ k) hfun (affine (a i) (B i))))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ k) hfun (affine (a ⟨g, hg⟩) (B ⟨g, hg⟩)) f = 0 :=
        congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ k) hfun _ f).1 hz' ⟨h, hh⟩
      rw [← hab ⟨g, hg⟩] at h1
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ k) hfun (affine (a i) (B i)) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      rw [← hab i]
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ k) hfun (comb (fun i => affine (a i) (B i)) c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩
end PEqualNP.ProofComplexity.DegSizeRank
namespace PEqualNP.ProofComplexity.DegSizeGain
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.DegSizePlan
def Stmt41 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      errRank C (zMul P G) k' * numMono (Fintype.card σ) k
        ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k'
def Stmt35 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
    b + k + 2 ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) k
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k
section LinearAlgebra
variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']
theorem finrank_eq_map_add_inf_ker (g : V →ₗ[ZMod 2] V') (S : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) S] :
    finrank (ZMod 2) S
      = finrank (ZMod 2) ↥(S.map g) + finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
  have h := (g ∘ₗ S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  have e : finrank (ZMod 2) ↥((LinearMap.ker g).comap S.subtype)
      = finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  omega
theorem finrank_add_le (f : V →ₗ[ZMod 2] V) (A W : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) W] :
    finrank (ZMod 2) A + finrank (ZMod 2) W
      ≤ finrank (ZMod 2) ↥(A ⊓ W.comap f) + finrank (ZMod 2) ↥(A.map f ⊔ W) := by
  have h1 := finrank_eq_map_add_inf_ker (W.mkQ ∘ₗ f) A
  have h2 := finrank_eq_map_add_inf_ker W.mkQ (A.map f ⊔ W)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h1
  rw [Submodule.ker_mkQ, inf_eq_right.mpr le_sup_right] at h2
  have h3 : finrank (ZMod 2) ↥(A.map (W.mkQ ∘ₗ f))
      ≤ finrank (ZMod 2) ↥((A.map f ⊔ W).map W.mkQ) := by
    rw [Submodule.map_comp]
    exact Submodule.finrank_mono (Submodule.map_mono le_sup_left)
  omega
theorem codim_iInf {ι : Type} (E : Submodule (ZMod 2) V) [FiniteDimensional (ZMod 2) E]
    (W : ι → Submodule (ZMod 2) V) (hW : ∀ ν, W ν ≤ E) (S : Finset ι) :
    finrank (ZMod 2) E
      ≤ finrank (ZMod 2) ↥(E ⊓ ⨅ ν ∈ S, W ν)
        + ∑ ν ∈ S, (finrank (ZMod 2) E - finrank (ZMod 2) (W ν)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (⨅ ν ∈ (∅ : Finset ι), W ν) = ⊤ := by simp
    rw [h0, inf_top_eq]
    exact Nat.le_add_right _ _
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.sum_insert ha, inf_left_comm]
    have : FiniteDimensional (ZMod 2) ↥(W a) := Submodule.finiteDimensional_of_le (hW a)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W a) (E ⊓ ⨅ ν ∈ s, W ν)
    have h2 : finrank (ZMod 2) ↥(W a ⊔ (E ⊓ ⨅ ν ∈ s, W ν)) ≤ finrank (ZMod 2) E :=
      Submodule.finrank_mono (sup_le (hW a) inf_le_left)
    have h3 : finrank (ZMod 2) (W a) ≤ finrank (ZMod 2) E := Submodule.finrank_mono (hW a)
    omega
end LinearAlgebra
section Poly
variable {σ : Type}
theorem mem_polyLE {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ polyLE σ k ↔ f.totalDegree ≤ k := by
  simp [polyLE, mem_restrictTotalDegree]
theorem deg_mul_le {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (add_le_add hp hq)
theorem deg_one_add_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (1 + q).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)
theorem deg_idem_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (q * q + q).totalDegree ≤ 2 :=
  (totalDegree_add _ _).trans (max_le (deg_mul_le hq hq) (by omega))
theorem deg_le_one_of_mem_span {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 :=
  mem_polyLE.mp (Submodule.span_le.mpr (fun g hg => mem_polyLE.mpr (hG g hg)) hq)
theorem deg_prod_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, 1 :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le (h j))
    _ = t := by simp
theorem eq_zero_of_sum_eq_zero (u : σ →₀ ℕ) (h : (u.sum fun _ e => e) = 0) : u = 0 := by
  rw [Finsupp.sum] at h
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hi
  exact hi ((Finset.sum_eq_zero_iff.mp h) i (Finsupp.mem_support_iff.mpr hi))
theorem exists_single_add (u : σ →₀ ℕ) (h : u ≠ 0) :
    ∃ (v : σ) (u' : σ →₀ ℕ), u = Finsupp.single v 1 + u' ∧
      (u.sum fun _ e => e) = 1 + (u'.sum fun _ e => e) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, u v ≠ 0 := by
    by_contra hcon
    refine h (Finsupp.ext (fun a => ?_))
    by_contra ha
    exact hcon ⟨a, ha⟩
  have hu : u = Finsupp.single v 1 + (u - Finsupp.single v 1) := by
    ext i
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with hvi
    · subst hvi; omega
    · omega
  refine ⟨v, u - Finsupp.single v 1, hu, ?_⟩
  conv_lhs => rw [hu]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem absorb_monomial (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ) (c : ZMod 2) (f : MvPolynomial σ (ZMod 2)),
      (u.sum fun _ e => e) = n → f ∈ C → n + f.totalDegree ≤ D → monomial u c * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u c f hu hf _
    have h0 : u = 0 := eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : monomial (0 : σ →₀ ℕ) c = MvPolynomial.C c := rfl
    rw [hm, C_mul']
    exact C.smul_mem c hf
  | succ n ih =>
    intro u c f hu hf hd
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
    rw [monomial_single_add, pow_one, mul_assoc]
    have hm := ih u' c f (by omega) hf (by omega)
    refine hC.mulX v _ hm ?_
    have h1 := totalDegree_mul (monomial u' c) f
    have h2 : (monomial u' c).totalDegree ≤ (u'.sum fun _ e => e) := totalDegree_monomial_le u' c
    omega
theorem absorb (hC : DegClosed C D) {f g : MvPolynomial σ (ZMod 2)} (hf : f ∈ C)
    (h : g.totalDegree + f.totalDegree ≤ D) : g * f ∈ C := by
  have e : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    rw [← Finset.sum_mul, support_sum_monomial_coeff]
  rw [e]
  refine C.sum_mem fun u hu => ?_
  have h1 : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact absorb_monomial hC _ u _ f rfl hf (by omega)
theorem idem_monomial (hC : DegClosed C D) (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ 1) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · by_cases h0 : u = 0
    · subst h0
      have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [hm, one_mul, CharTwo.add_self_eq_zero]
      exact C.zero_mem
    · obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
      have hu' : u' = 0 := eq_zero_of_sum_eq_zero u' (by omega)
      subst hu'
      rw [add_zero]
      exact hC.bool v
theorem affine_idem (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ 1) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial hC a (c a) (hs a (Finset.mem_insert_self a s)))
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h
theorem errKer_le (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errKer C M k ≤ polyLE σ k := by
  unfold errKer
  exact inf_le_left
instance errKer_finite [Fintype σ] (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    FiniteDimensional (ZMod 2) ↥(errKer C M k) :=
  Submodule.finiteDimensional_of_le (errKer_le M k)
theorem mem_errKer_zMul {P : MvPolynomial σ (ZMod 2)} {G : Set (MvPolynomial σ (ZMod 2))}
    {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C (zMul P G) k ↔ f.totalDegree ≤ k ∧ ∀ g ∈ G, P * g * f ∈ C := by
  rw [mem_errKer]
  simp [zMul]
theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : ∑ j ∈ Finset.range 1, n.choose j ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have h1 : ∑ j ∈ Finset.range 1, n.choose j = 1 := by simp
  omega
theorem numMono_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') : numMono n k ≤ numMono n k' := by
  unfold numMono
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
theorem errRank_one_le [Fintype σ] (hC : DegClosed C D) {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {K : ℕ} (hD : K + 1 ≤ D) :
    errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := mem_polyLE.mp hf.2
    rw [mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact absorb hC hfC (by omega)
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega
end Poly
theorem gain (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := h35 σ C D a (K - 1) {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - 1) ≤ 2 * errRank C {P * q} (K - 1) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ 1 := deg_le_one_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := affine_idem hC q hq1
  have hidem2 := deg_idem_le hq1
  refine ⟨q, hqs, ?_⟩
  have hi : polyLE σ (K - 1) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - 1) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := deg_mul_le hP hfd
      exact absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  have hii : (polyLE σ (K - 1)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [mem_errKer_zMul]
      have hd0 := deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact absorb hC hidem (by omega)
    · intro f hf
      rw [mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact absorb hC (hf.2 g hg) (by omega)
  have key := finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - 1))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - 1)) ≤ finrank (ZMod 2) (polyLE σ (K - 1)) :=
    Submodule.finrank_mono (errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega
theorem greedy_arith {c c' c1 h n K t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - 1) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta n K) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta n K) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast numMono_pos n K
  have hN1 : (numMono n (K - 1) : ℝ) ≤ numMono n K := by
    exact_mod_cast numMono_mono n (Nat.sub_le K 1)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - 1) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta n K := by
    have hle : eta n K ≤ 1 := by
      unfold eta
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta n K ≤ c1 / 2 := by
    unfold eta
    have e1 : (c : ℝ) * (numMono n (K - 1) / (2 * numMono n K))
        = (c * numMono n (K - 1)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta n K) := by linarith
    _ ≤ (h * (1 - eta n K) ^ t) * (1 - eta n K) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta n K) ^ (t + 1) := by ring
theorem greedy (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le hC hG' (by omega)
  | succ t ih =>
    intro hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t :=
      deg_prod_le qs (fun j => deg_le_one_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain h35 σ C D t K _ G hC hP hG hK (by omega)
    have h41' := h41 σ C D t K _ (↑G) hC hP hG' (by omega) (K - 1) K (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith hgain h41' hb
theorem common (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy h41 h35 σ C D K t (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact mem_polyLE.mpr (by simp)
    exact h1 hone.1
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    codim_iInf (polyLE σ K) (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩, fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)
end PEqualNP.ProofComplexity.DegSizeGain
namespace PEqualNP.ProofComplexity.Helpers
open PEqualNP.ProofComplexity
abbrev PVar (n : ℕ) : Type := Fin (n + 1) × Fin n
def mono {n : ℕ} (C : Clause (PVar n)) : Finset (PVar n) :=
  Finset.univ.filter (fun p => (p, true) ∈ C ∨ ∃ i : Fin (n + 1), i ≠ p.1 ∧ ((i, p.2), false) ∈ C)
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.Helpers
open PEqualNP.ProofComplexity
theorem linEqSat_singleton {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  unfold LinEqSat
  rw [Finset.filter_singleton]
  cases h : a v <;> cases s <;> simp
end PEqualNP.ProofComplexity.Helpers
namespace PEqualNP.ProofComplexity.DegSizeArith
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
section Completeness
variable {V : Type}
noncomputable def fac (a : V → Bool) (v : V) : MvPolynomial V (ZMod 2) :=
  if a v = true then X v else 1 + X v
theorem totalDegree_fac_le (a : V → Bool) (v : V) : (fac a v).totalDegree ≤ 1 := by
  unfold fac
  split_ifs
  · rw [totalDegree_X]
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    simp
theorem totalDegree_prod_fac_le (a : V → Bool) (S : Finset V) :
    (∏ v ∈ S, fac a v).totalDegree ≤ S.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ v ∈ S, (fac a v).totalDegree ≤ ∑ _v ∈ S, 1 :=
        Finset.sum_le_sum fun v _ => totalDegree_fac_le a v
    _ = S.card := by simp
theorem eval_fac (a : V → Bool) (x : V → ZMod 2) (v : V) :
    eval x (fac a v) = if (x v = 1 ↔ a v = true) then 1 else 0 := by
  unfold fac
  have hx : x v = 0 ∨ x v = 1 := by
    generalize x v = c
    revert c
    decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hx with h | h <;> cases a v <;> simp [h, h11]
theorem complete_deg :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → ¬ Satisfiable F → w ≤ D → Fintype.card V ≤ D →
      PCRefutable (cnfSystem F) D := by
  classical
  intro V _ _ F w D hw hunsat hwD hVD
  have hfals : ∀ a : V → Bool, ∃ A ∈ F, ¬ ClauseSat a A := by
    intro a
    by_contra hb
    exact hunsat ⟨a, fun A hA => by_contra fun hn => hb ⟨A, hA, hn⟩⟩
  have hind : ∀ a : V → Bool, PCDerivable (cnfSystem F) D (∏ v, fac a v) := by
    intro a
    obtain ⟨A, hAF, hA⟩ := hfals a
    have hne : ∀ l ∈ A, a l.1 = !l.2 := by
      intro l hl
      have h0 : ¬ a l.1 = l.2 := fun h => hA ⟨l, hl, h⟩
      revert h0
      cases a l.1 <;> cases l.2 <;> simp
    have hinj : Set.InjOn (fun l : Literal V => l.1) (↑A : Set (Literal V)) := by
      intro l hl l' hl' h
      have h' : l.1 = l'.1 := h
      have h1 := hne l hl
      have h2 := hne l' hl'
      rw [h'] at h1
      have h3 : (!l.2) = !l'.2 := h1.symm.trans h2
      have h4 : l.2 = l'.2 := by simpa using h3
      exact Prod.ext h' h4
    set S : Finset V := A.image (fun l => l.1) with hS
    have hcl : clausePoly A = ∏ v ∈ S, fac a v := by
      rw [hS, Finset.prod_image hinj]
      unfold clausePoly
      refine Finset.prod_congr rfl fun l hl => ?_
      have h1 := hne l hl
      unfold fac
      rw [h1]
      cases l.2 <;> simp
    have hsplit : ∏ v, fac a v = (∏ v ∈ Sᶜ, fac a v) * clausePoly A := by
      rw [hcl, Finset.prod_compl_mul_prod]
    have hdegc : (clausePoly A).totalDegree ≤ S.card := by
      rw [hcl]
      exact totalDegree_prod_fac_le a S
    have hScard : S.card ≤ w := Finset.card_image_le.trans (hw A hAF)
    have hax : PCDerivable (cnfSystem F) D (clausePoly A) :=
      .ax (Or.inr ⟨A, hAF, rfl⟩) (hdegc.trans (hScard.trans hwD))
    rw [hsplit]
    refine pcDerivable_mono (pcDerivable_mul_left hax (∏ v ∈ Sᶜ, fac a v)) ?_ subset_rfl
    refine max_le le_rfl ?_
    have h1 := totalDegree_prod_fac_le a Sᶜ
    have h2 : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    omega
  set p : MvPolynomial V (ZMod 2) := ∑ a : V → Bool, ∏ v, fac a v with hp
  have hpder : PCDerivable (cnfSystem F) D p := pcDerivable_sum _ _ fun a _ => hind a
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hvan : ∀ x : V → ZMod 2, eval x (1 + p) = 0 := by
    intro x
    have hx : eval x p = 1 := by
      rw [hp, map_sum]
      simp only [map_prod, eval_fac, Finset.prod_boole]
      rw [Finset.sum_eq_single (fun v => decide (x v = 1))]
      · simp
      · intro b _ hb
        split_ifs with h
        · exfalso
          apply hb
          funext v
          have := h v (Finset.mem_univ v)
          cases hbv : b v <;> simp_all
        · rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [map_add, map_one, hx, h11]
  have hdeg : (1 + p).totalDegree ≤ D := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_one]
      exact Nat.zero_le _
    · rw [hp]
      refine totalDegree_finsetSum_le fun a _ => ?_
      refine (totalDegree_prod_fac_le a Finset.univ).trans ?_
      rwa [Finset.card_univ]
  have h1 := BoolVanish.vanish_derivable V (cnfSystem F) D (1 + p)
    (fun v => Or.inl ⟨v, rfl⟩) hdeg hvan
  have h2 := PCDerivable.add h1 hpder
  have e : 1 + p + p = 1 := by
    rw [add_assoc, ← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
  rw [e] at h2
  exact h2
end Completeness
section Binomial
theorem numMono_succ (n k : ℕ) : numMono n (k + 1) = numMono n k + n.choose (k + 1) := by
  unfold numMono
  rw [Finset.sum_range_succ]
theorem choose_le_numMono (n k : ℕ) : n.choose k ≤ numMono n k := by
  unfold numMono
  exact Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
    (Finset.self_mem_range_succ k)
theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : n.choose 0 ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.succ_pos k))
  rw [Nat.choose_zero_right] at h
  exact h
theorem numMono_ratio (n k : ℕ) (hk : k ≤ n) :
    (k + 1) * numMono n (k + 1) ≤ (n + 1) * numMono n k := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 := choose_le_numMono n k
  have h3 : n.choose k * (n - k) ≤ numMono n k * (n - k) := Nat.mul_le_mul_right _ h2
  have h4 : numMono n k * (k + 1) + numMono n k * (n - k) = numMono n k * (n + 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [numMono_succ]
  calc (k + 1) * (numMono n k + n.choose (k + 1))
      = numMono n k * (k + 1) + n.choose (k + 1) * (k + 1) := by ring
    _ ≤ numMono n k * (k + 1) + numMono n k * (n - k) := by rw [h1]; exact Nat.add_le_add_left h3 _
    _ = (n + 1) * numMono n k := by rw [h4]; ring
theorem eta_le_one (n K : ℕ) (hK : 1 ≤ K) : eta n K ≤ 1 := by
  unfold eta
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hpos : (0 : ℝ) < numMono n (k + 1) := by exact_mod_cast numMono_pos n (k + 1)
  have hle : (numMono n k : ℝ) ≤ numMono n (k + 1) := by
    exact_mod_cast (numMono_succ n k) ▸ Nat.le_add_right _ _
  rw [Nat.add_sub_cancel, div_le_one (by positivity)]
  linarith
end Binomial
end PEqualNP.ProofComplexity.DegSizeArith
namespace PEqualNP.ProofComplexity.DegSizeAssembly
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
theorem assembly :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
      (w D K t : ℕ),
      (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π → ¬ PCRefutable (cnfSystem F) D →
      1 ≤ K → K + max (2 * t + 2) (t + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - eta (Fintype.card V) K) ^ t := by
  classical
  intro V _ _ F π w D K t hw href hnr hK hB
  by_contra hlt
  rw [not_le] at hlt
  have hD2 : 2 ≤ D := by omega
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure (cnfSystem F) D hD2 (fun v => Or.inl ⟨v, rfl⟩)
  have h1 : (1 : MvPolynomial V (ZMod 2)) ∉ pcClosure (cnfSystem F) D := hnr
  have hnn : (0 : ℝ) ≤ (1 - eta (Fintype.card V) K) ^ t :=
    pow_nonneg (sub_nonneg.mpr (DegSizeArith.eta_le_one _ K hK)) t
  have hcard : (π.toFinset.card : ℝ) ≤ (π.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le π
  have hS : (π.toFinset.card : ℝ) * (1 - eta (Fintype.card V) K) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hnn) hlt
  obtain ⟨f, qs, hf, hfC, hspan, hmem⟩ :=
    DegSizeGain.common DegSizeRank.monoRank_used DegSizeRank.rankRetention_used
      V (pcClosure (cnfSystem F) D) D K t (LinClause V) π.toFinset
      (fun L => L.image (fun q => eqPoly q)) hC h1
      (by
        intro L _ g hg
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hg
        exact totalDegree_eqPoly_le q)
      hK (by omega) hS
  apply hfC
  refine DegSizeSim.simulation_refutation V F π w D K t f qs hw href hB hf ?_ ?_
  · intro L hL j
    have := hspan L (List.mem_toFinset.mpr hL) j
    simpa [Finset.coe_image] using this
  · intro L hL q hq
    exact hmem L (List.mem_toFinset.mpr hL) (eqPoly q) (Finset.mem_image_of_mem _ hq)
end PEqualNP.ProofComplexity.DegSizeAssembly
namespace PEqualNP.ProofComplexity.PhpFinal
open PEqualNP.ProofComplexity PEqualNP.Expanders
theorem card_gedge_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    Fintype.card (GEdge G) ≤ m * b := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ((Finset.univ.filter (fun e : Fin m × Fin N => e.2 ∈ G e.1)).filter
        (fun e => e.1 = i)).card ≤ b := by
    intro i _
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hb i)
    · intro e he
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have h1 := (Finset.mem_filter.mp he'.1).2
      rw [he'.2] at h1
      exact Finset.mem_coe.mpr h1
    · intro e he e' he' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
      exact Prod.ext (h1.trans h2.symm) h
  calc _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum hfib
    _ = m * b := by simp
theorem graphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ graphPHP G, C.card ≤ max b 2 := by
  classical
  intro C hC
  rcases hC with ⟨i, rfl⟩ | ⟨e, e', -, -, rfl⟩
  · refine le_trans (le_trans
      (Finset.card_le_card_of_injOn (fun l : Literal (GEdge G) => l.1.1.2) ?_ ?_) (hb i))
      (le_max_left _ _)
    · intro l hl
      have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h1 : l.1.1.2 ∈ G l.1.1.1 := l.1.2
      rw [hl'.1] at h1
      exact Finset.mem_coe.mpr h1
    · intro l hl l' hl' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl')).2
      exact Prod.ext (Subtype.ext (Prod.ext (h1.1.trans h2.1.symm) h)) (h1.2.trans h2.2.symm)
  · exact le_trans Finset.card_le_two (le_max_right _ _)
end PEqualNP.ProofComplexity.PhpFinal
namespace PEqualNP.ProofComplexity.Helpers.ThreeCnf
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
variable {V : Type}
def idx (w i : ℕ) : Fin (w + 1) := ⟨min i w, by omega⟩
theorem idx_val (w i : ℕ) : (idx w i).val = min i w := rfl
open Classical in
noncomputable def to3 (F : Set (Clause V)) (w : ℕ) :
    Set (Clause (V ⊕ (↥F × Fin (w + 1)))) :=
  {K | ∃ C : ↥F,
      K = {(Sum.inr (C, idx w 0), true)} ∨
      (∃ (i : ℕ) (l : Literal V), C.1.toList[i]? = some l ∧
        K = {(Sum.inr (C, idx w i), false), (Sum.inl l.1, l.2),
          (Sum.inr (C, idx w (i + 1)), true)}) ∨
      K = {(Sum.inr (C, idx w C.1.card), false)}}
theorem to3_width (F : Set (Clause V)) (w : ℕ) : ∀ K ∈ to3 F w, K.card ≤ 3 := by
  classical
  rintro K ⟨C, rfl | ⟨i, l, -, rfl⟩ | rfl⟩
  · simp
  · exact Finset.card_le_three
  · simp
theorem to3_unsat (F : Set (Clause V)) (w : ℕ) (h : ¬ Satisfiable F) :
    ¬ Satisfiable (to3 F w) := by
  classical
  rintro ⟨a, ha⟩
  apply h
  refine ⟨fun v => a (Sum.inl v), fun C hC => ?_⟩
  by_contra hns
  have hall : ∀ i, i ≤ C.card → a (Sum.inr (⟨C, hC⟩, idx w i)) = true := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨l, hl, hal⟩ := ha _ ⟨⟨C, hC⟩, Or.inl rfl⟩
      rw [Finset.mem_singleton] at hl
      subst hl
      exact hal
    | succ i ih =>
      intro hi
      have hlen : i < C.toList.length := by
        rw [Finset.length_toList]
        omega
      have hget : C.toList[i]? = some C.toList[i] := List.getElem?_eq_getElem hlen
      obtain ⟨l, hl, hal⟩ := ha _ ⟨⟨C, hC⟩, Or.inr (Or.inl ⟨i, C.toList[i], hget, rfl⟩)⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · have := ih (by omega)
        rw [this] at hal
        exact absurd hal (by simp)
      · exfalso
        exact hns ⟨C.toList[i], Finset.mem_toList.mp (List.getElem_mem hlen), hal⟩
      · exact hal
  obtain ⟨l, hl, hal⟩ := ha _ ⟨⟨C, hC⟩, Or.inr (Or.inr rfl)⟩
  rw [Finset.mem_singleton] at hl
  subst hl
  have := hall C.card le_rfl
  rw [this] at hal
  exact absurd hal (by simp)
noncomputable def litPoly (l : Literal V) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1
theorem totalDegree_litPoly_le (l : Literal V) : (litPoly l).totalDegree ≤ 1 := by
  unfold litPoly
  split_ifs
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    simp
  · rw [totalDegree_X]
noncomputable def pre (C : Clause V) (i : ℕ) : MvPolynomial V (ZMod 2) :=
  ((C.toList.take i).map litPoly).prod
theorem pre_zero (C : Clause V) : pre C 0 = 1 := by
  simp [pre]
theorem pre_succ (C : Clause V) (i : ℕ) (l : Literal V) (hl : C.toList[i]? = some l) :
    pre C (i + 1) = pre C i * litPoly l := by
  unfold pre
  rw [List.take_add_one, hl]
  simp
theorem pre_card (C : Clause V) : pre C C.card = clausePoly C := by
  unfold pre
  have h : C.toList.take C.card = C.toList :=
    List.take_of_length_le (by rw [Finset.length_toList])
  rw [h, Finset.prod_map_toList]
  rfl
theorem totalDegree_list_le (L : List (Literal V)) :
    ((L.map litPoly).prod).totalDegree ≤ L.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons]
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_litPoly_le l
    omega
theorem totalDegree_pre_le (C : Clause V) (i : ℕ) : (pre C i).totalDegree ≤ i := by
  unfold pre
  refine (totalDegree_list_le _).trans ?_
  rw [List.length_take]
  exact min_le_left _ _
noncomputable def sub (F : Set (Clause V)) (w : ℕ) :
    V ⊕ (↥F × Fin (w + 1)) → MvPolynomial V (ZMod 2) :=
  Sum.elim X (fun p => pre p.1.1 p.2.val)
theorem totalDegree_sub_le (F : Set (Clause V)) (w : ℕ) (hw1 : 1 ≤ w)
    (j : V ⊕ (↥F × Fin (w + 1))) : (sub F w j).totalDegree ≤ w := by
  rcases j with v | ⟨C, j⟩
  · simp only [sub, Sum.elim_inl]
    rw [totalDegree_X]
    exact hw1
  · simp only [sub, Sum.elim_inr]
    exact (totalDegree_pre_le _ _).trans (Nat.lt_succ_iff.mp j.isLt)
theorem bind_clausePoly {σ τ : Type} (φ : σ → MvPolynomial τ (ZMod 2)) (K : Clause σ) :
    bind₁ φ (clausePoly K) = ∏ l ∈ K, (if l.2 = true then 1 + φ l.1 else φ l.1) := by
  unfold clausePoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs
  · rw [map_add, map_one, bind₁_X_right]
  · rw [bind₁_X_right]
theorem eval_sq_add (x : V → ZMod 2) (g : MvPolynomial V (ZMod 2)) :
    eval x (g * g + g) = 0 := by
  rw [map_add, map_mul]
  generalize eval x g = c
  revert c
  decide
theorem eval_mul_one_add (x : V → ZMod 2) (g f : MvPolynomial V (ZMod 2)) :
    eval x (g * (f * (1 + g * f))) = 0 := by
  simp only [map_add, map_mul, map_one]
  generalize eval x g = c
  generalize eval x f = d
  revert c d
  decide
theorem to3_pc (F : Set (Clause V)) (w D : ℕ) (hw1 : 1 ≤ w) (hw : ∀ C ∈ F, C.card ≤ w)
    (h : PCRefutable (cnfSystem (to3 F w)) D) :
    PCRefutable (cnfSystem F) (w * D + 2 * w) := by
  classical
  have hbool : ∀ v : V, (X v * X v + X v : MvPolynomial V (ZMod 2)) ∈ cnfSystem F :=
    fun v => Or.inl ⟨v, rfl⟩
  have hB : 2 * w ≤ w * D + 2 * w := Nat.le_add_left _ _
  have hax : ∀ a ∈ cnfSystem (to3 F w), a.totalDegree ≤ D →
      PCDerivable (cnfSystem F) (w * D + 2 * w) (1 * bind₁ (sub F w) a) := by
    intro a ha _
    rw [one_mul]
    rcases ha with ⟨y, rfl⟩ | ⟨K, hK, rfl⟩
    ·
      rw [map_add, map_mul, bind₁_X_right]
      refine pcDerivable_mono (BoolVanish.vanish_derivable V (cnfSystem F) (2 * w) _ hbool ?_
        (fun x => eval_sq_add x _)) hB subset_rfl
      have hd := totalDegree_sub_le F w hw1 y
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      refine (totalDegree_mul _ _).trans ?_
      omega
    · rw [bind_clausePoly]
      obtain ⟨C, rfl | ⟨i, l, hl, rfl⟩ | rfl⟩ := hK
      ·
        rw [Finset.prod_singleton]
        have : (1 : MvPolynomial V (ZMod 2)) + 1 = 0 := by
          rw [← two_smul (ZMod 2) (1 : MvPolynomial V (ZMod 2)),
            show (2 : ZMod 2) = 0 from rfl, zero_smul]
        simp only [sub, Sum.elim_inr, idx_val, Nat.zero_min, pre_zero, ite_true, this]
        exact .zero
      ·
        have hi : i < C.1.card := by
          have := (List.getElem?_eq_some_iff.mp hl).1
          rwa [Finset.length_toList] at this
        have hCw : C.1.card ≤ w := hw C.1 C.2
        rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
        have e1 : min i w = i := by omega
        have e2 : min (i + 1) w = i + 1 := by omega
        have e3 : (if l.2 = true then (1 : MvPolynomial V (ZMod 2)) + X l.1 else X l.1)
            = litPoly l := rfl
        simp only [sub, Sum.elim_inr, Sum.elim_inl, idx_val, e1, e2, ite_true, e3,
          Bool.false_eq_true, ite_false]
        rw [pre_succ C.1 i l hl]
        refine pcDerivable_mono (BoolVanish.vanish_derivable V (cnfSystem F) (2 * w) _ hbool ?_
          (fun x => eval_mul_one_add x _ _)) hB subset_rfl
        have d1 := totalDegree_pre_le C.1 i
        have d2 := totalDegree_litPoly_le l
        have d3 : (pre C.1 i * litPoly l).totalDegree ≤ i + 1 :=
          (totalDegree_mul _ _).trans (by omega)
        have d4 : (1 + pre C.1 i * litPoly l).totalDegree ≤ i + 1 := by
          refine (totalDegree_add _ _).trans (max_le ?_ d3)
          rw [totalDegree_one]
          omega
        have d5 : (litPoly l * (1 + pre C.1 i * litPoly l)).totalDegree ≤ 1 + (i + 1) :=
          (totalDegree_mul _ _).trans (by omega)
        refine (totalDegree_mul _ _).trans ?_
        omega
      ·
        have hCw : C.1.card ≤ w := hw C.1 C.2
        rw [Finset.prod_singleton]
        have e1 : min C.1.card w = C.1.card := by omega
        simp only [sub, Sum.elim_inr, idx_val, e1, Bool.false_eq_true, ite_false, pre_card]
        refine .ax (Or.inr ⟨C.1, C.2, rfl⟩) ?_
        rw [← pre_card]
        have := totalDegree_pre_le C.1 C.1.card
        omega
  have key := pcDerivable_replay (G := cnfSystem F) (T := w) (D := D) (s := 2 * w)
    (sub F w) (totalDegree_sub_le F w hw1) 1 (by rw [totalDegree_one]; omega) hax h
  rw [map_one, one_mul] at key
  exact key
theorem to3_pc_lower (F : Set (Clause V)) (w D : ℕ) (hw1 : 1 ≤ w) (hw : ∀ C ∈ F, C.card ≤ w)
    (h : ¬ PCRefutable (cnfSystem F) (w * D + 2 * w)) :
    ¬ PCRefutable (cnfSystem (to3 F w)) D :=
  fun h3 => h (to3_pc F w D hw1 hw h3)
end PEqualNP.ProofComplexity.Helpers.ThreeCnf
namespace PEqualNP.ProofComplexity.ThreeCnfFamily
open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers.ThreeCnf
theorem graphPHP_unsat {m N : ℕ} (G : BipGraph m N) (h : N < m) :
    ¬ Satisfiable (graphPHP G) := by
  classical
  rintro ⟨a, ha⟩
  have hp : ∀ i : Fin m, ∃ e : GEdge G, e.1.1 = i ∧ a e = true := by
    intro i
    obtain ⟨l, hl, hal⟩ := ha _ (Or.inl ⟨i, rfl⟩)
    have h2 := (Finset.mem_filter.mp hl).2
    exact ⟨l.1, h2.1, by rw [hal, h2.2]⟩
  choose g hg1 hg2 using hp
  obtain ⟨i, i', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => (g i).1.2)
    (by simpa using h)
  obtain ⟨l, hl, hal⟩ := ha _ (Or.inr ⟨g i, g i', heq, by rw [hg1, hg1]; exact hne, rfl⟩)
  rcases Finset.mem_insert.mp hl with rfl | hl
  · simp [hg2] at hal
  · rw [Finset.mem_singleton] at hl
    subst hl
    simp [hg2] at hal
theorem card_pairs_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hR : RightDegLe G b) :
    ((Finset.univ : Finset (GEdge G × GEdge G)).filter (fun p => p.1.1.2 = p.2.1.2)).card
      ≤ Fintype.card (GEdge G) * b := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ e ∈ (Finset.univ : Finset (GEdge G)),
      (((Finset.univ : Finset (GEdge G × GEdge G)).filter
        (fun p => p.1.1.2 = p.2.1.2)).filter (fun p => p.1 = e)).card ≤ b := by
    intro e _
    refine le_trans (Finset.card_le_card_of_injOn (t := rightNbrs G e.1.2)
      (fun p : GEdge G × GEdge G => p.2.1.1) ?_ ?_) (hR e.1.2)
    · intro p hp
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have h1 := (Finset.mem_filter.mp hp'.1).2
      have h2 : p.2.1.2 ∈ G p.2.1.1 := p.2.2
      rw [← h1, hp'.2] at h2
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
    · intro p hp p' hp' h
      have hq := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
      have h1 := (Finset.mem_filter.mp hq.1).2
      have h1' := (Finset.mem_filter.mp hq'.1).2
      have e1 : p.1 = p'.1 := hq.2.trans hq'.2.symm
      have e2 : p.2.1.2 = p'.2.1.2 := by rw [← h1, ← h1', e1]
      exact Prod.ext e1 (Subtype.ext (Prod.ext h e2))
  calc _ ≤ ∑ _e : GEdge G, b := Finset.sum_le_sum hfib
    _ = Fintype.card (GEdge G) * b := by simp
theorem card_graphPHP_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hL : LeftDegLe G b)
    (hR : RightDegLe G b) [Fintype ↥(graphPHP G)] :
    Fintype.card ↥(graphPHP G) ≤ m + m * b * b := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (GEdge G × GEdge G),
      S = Finset.univ.filter (fun p => p.1.1.2 = p.2.1.2) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Clause (GEdge G)),
      T = (Finset.univ : Finset (Fin m)).image
          (fun i => Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true))
        ∪ S.image (fun p => {(p.1, false), (p.2, false)}) := ⟨_, rfl⟩
  have hsub : ∀ C, C ∈ graphPHP G → C ∈ T := by
    rintro C (⟨i, rfl⟩ | ⟨e, e', h, -, rfl⟩)
    · rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · rw [hT]
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, e'), ?_, rfl⟩)
      rw [hS]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hinj : Function.Injective
      (fun x : ↥(graphPHP G) => (⟨x.1, hsub x.1 x.2⟩ : {C // C ∈ T})) :=
    fun x y h => Subtype.ext (congrArg (fun z : {C // C ∈ T} => z.1) h)
  have hSc : S.card ≤ m * b * b := by
    rw [hS]
    exact le_trans (card_pairs_le G b hR)
      (Nat.mul_le_mul_right _ (PhpFinal.card_gedge_le G b hL))
  have hTc : T.card ≤ m + S.card := by
    rw [hT]
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ Finset.card_image_le)
    refine le_trans Finset.card_image_le ?_
    simp
  calc Fintype.card ↥(graphPHP G) ≤ Fintype.card {C // C ∈ T} :=
        Fintype.card_le_of_injective _ hinj
    _ = T.card := Fintype.card_coe T
    _ ≤ m + S.card := hTc
    _ ≤ m + m * b * b := Nat.add_le_add_left hSc _
end PEqualNP.ProofComplexity.ThreeCnfFamily
namespace PEqualNP.ProofComplexity.LinKPlan
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
section Vanish
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem mem_of_boolDerivable (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hp : PCDerivable (BoolVanish.boolAxioms σ) D p) : p ∈ C := by
  induction hp with
  | ax hp _ =>
    obtain ⟨v, rfl⟩ := hp
    exact hC.bool v
  | zero => exact C.zero_mem
  | add _ _ ih1 ih2 => exact C.add_mem ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases h0 : p = 0
    · subst h0
      simp
    · refine hC.mulX j p ih ?_
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) h0, totalDegree_X] at hdeg
      omega
theorem vanish_mem (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hd : p.totalDegree ≤ D) (hv : ∀ x : σ → ZMod 2, eval x p = 0) : p ∈ C :=
  mem_of_boolDerivable hC
    (BoolVanish.vanish_derivable σ (BoolVanish.boolAxioms σ) D p (fun v => ⟨v, rfl⟩) hd hv)
theorem idem_mul (hC : DegClosed C D) (g h : MvPolynomial σ (ZMod 2)) {b e : ℕ}
    (hh : h.totalDegree ≤ b) (hg : g.totalDegree ≤ e) (hB : b + 2 * e ≤ D) :
    h * (g * g + g) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 : (g * g + g).totalDegree ≤ e + e :=
      (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hg hg) (by omega))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have : ∀ c : ZMod 2, c * c + c = 0 := by decide
    rw [this, mul_zero]
end Vanish
noncomputable def termPoly {V : Type} (T : LinTerm V) : MvPolynomial V (ZMod 2) :=
  ∏ e ∈ T, eqPoly e
section Terms
variable {V : Type}
theorem termPoly_singleton (q : LinEq V) : termPoly ({q} : LinTerm V) = eqPoly q := by
  simp [termPoly]
theorem totalDegree_termPoly_le (T : LinTerm V) : (termPoly T).totalDegree ≤ T.card := by
  unfold termPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ e ∈ T, (eqPoly e).totalDegree ≤ ∑ _e ∈ T, 1 :=
        Finset.sum_le_sum fun e _ => totalDegree_eqPoly_le e
    _ = T.card := by simp
theorem eval_eqPoly (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = ∑ v ∈ q.1, x v + (if q.2 = true then 0 else 1) := by
  unfold eqPoly
  rw [map_add, map_sum, eval_C]
  simp only [eval_X]
theorem eval_eqPoly_eq_one_iff (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = 1 ↔ LinEqSat (fun v => decide (x v = 1)) q := by
  rw [eval_eqPoly, linEqSat_iff_sum]
theorem eval_eqPoly_neg (x : V → ZMod 2) (e : LinEq V) :
    eval x (eqPoly (negLinEq e)) = eval x (eqPoly e) + 1 := by
  rw [eval_eqPoly, eval_eqPoly]
  rcases e with ⟨f, b⟩
  show ∑ v ∈ f, x v + (if (!b) = true then 0 else 1)
    = ∑ v ∈ f, x v + (if b = true then 0 else 1) + 1
  generalize ∑ v ∈ f, x v = s
  cases b
  · revert s
    decide
  · revert s
    decide
theorem eval_termPoly_of_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 1 := by
  unfold termPoly
  rw [map_prod]
  exact Finset.prod_eq_one fun e he => (eval_eqPoly_eq_one_iff x e).mpr (h e he)
theorem eval_termPoly_of_not_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : ¬ LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 0 := by
  obtain ⟨e, he, hne⟩ : ∃ e ∈ T, ¬ LinEqSat (fun v => decide (x v = 1)) e := by
    by_contra hcon
    exact h fun e he => by_contra fun hn => hcon ⟨e, he, hn⟩
  unfold termPoly
  rw [map_prod]
  refine Finset.prod_eq_zero he ?_
  rcases zmod2_cases (eval x (eqPoly e)) with h0 | h1
  · exact h0
  · exact absurd ((eval_eqPoly_eq_one_iff x e).mp h1) hne
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_term_mul (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T.card + S.card ≤ D) :
    h * (termPoly T + termPoly T * termPoly S) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have hT := totalDegree_termPoly_le T
    have hS := totalDegree_termPoly_le S
    have h1 : (termPoly T + termPoly T * termPoly S).totalDegree ≤ T.card + S.card :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hS))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [eval_termPoly_of_sat x T hT, eval_termPoly_of_sat x S (himp _ hT)]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem term_neg_mul (hC : DegClosed C D) (T : LinTerm V) (e : LinEq V) (he : e ∈ T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card + 1 ≤ D) :
    h * (termPoly T * eqPoly (negLinEq e)) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_mul_le' (totalDegree_termPoly_le T)
      (totalDegree_eqPoly_le (negLinEq e))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_mul, eval_eqPoly_neg]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [(eval_eqPoly_eq_one_iff x e).mpr (hT e he)]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, mul_zero, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem term_union_mul [DecidableEq V] (hC : DegClosed C D) (T₁ T₂ : LinTerm V)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T₁.card + T₂.card ≤ D) :
    h * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_termPoly_le T₁
    have h2 := totalDegree_termPoly_le T₂
    have h3 := (totalDegree_termPoly_le (T₁ ∪ T₂)).trans (Finset.card_union_le T₁ T₂)
    have h4 : (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂).totalDegree
        ≤ T₁.card + T₂.card :=
      (totalDegree_add _ _).trans (max_le h3 (totalDegree_mul_le' h1 h2))
    exact (totalDegree_mul_le' hh h4).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have h11 : (1 : ZMod 2) + 1 * 1 = 0 := by decide
    by_cases h1 : LinTermSat (fun v => decide (x v = 1)) T₁
    · by_cases h2 : LinTermSat (fun v => decide (x v = 1)) T₂
      · have hu : LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := by
          intro q hq
          rcases Finset.mem_union.mp hq with hq | hq
          · exact h1 q hq
          · exact h2 q hq
        rw [eval_termPoly_of_sat x _ hu, eval_termPoly_of_sat x _ h1,
          eval_termPoly_of_sat x _ h2, h11, mul_zero]
      · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
          h2 fun q hq => hu q (Finset.mem_union_right _ hq)
        rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h2]
        simp
    · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
        h1 fun q hq => hu q (Finset.mem_union_left _ hq)
      rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h1]
      simp
end Terms
section AlterChoice
theorem span_image_sum {ι M : Type} [AddCommGroup M] [Module (ZMod 2) M] (w : ι → M)
    (s : Finset ι) {y : M} (hy : y ∈ Submodule.span (ZMod 2) (w '' (↑s : Set ι))) :
    ∃ I : Finset ι, I ⊆ s ∧ y = ∑ i ∈ I, w i := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hy
  obtain ⟨lc, hlc, rfl⟩ := hy
  refine ⟨lc.support, fun d hd => Finset.mem_coe.mp ((Finsupp.mem_supported _ _).mp hlc hd), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
  have h1 : lc d = 1 := by
    generalize lc d = x at h0
    revert x
    decide
  rw [h1, one_smul]
variable {V : Type} [Fintype V] [DecidableEq V]
theorem term_alter_choice (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ ∃ I : Finset (LinEq V), I ⊆ T ∧
      ∑ e ∈ I, (eqPoly e + 1) + ∑ d ∈ J, eqPoly d = 1 := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
        ∪ (eqVec '' (↑Q : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
          ∪ (eqVec '' (↑Q : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
            ∪ (eqVec '' (↑Q : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hT : LinTermSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) T := by
      intro e he
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Or.inl ⟨e, Finset.mem_coe.mpr he, rfl⟩))
      rw [map_add, h1] at this
      generalize φ (eqVec e) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hT
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Or.inr ⟨d, Finset.mem_coe.mpr hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.span_union, Submodule.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨I, hI, rfl⟩ := span_image_sum (fun e : LinEq V => eqVec e + (0, 1)) T hy
  obtain ⟨J, hJ, rfl⟩ := span_image_sum eqVec Q hz
  refine ⟨J, hJ, I, hI, ?_⟩
  have hP := congrArg affPoly hyz
  simp only [map_add, map_sum, affPoly_eqVec, affPoly_one] at hP
  exact hP
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_disj_mul (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, I, hI, hid⟩ := term_alter_choice T Q himp
  refine ⟨J, hJ, fun h b hh hB => vanish_mem hC ?_ ?_⟩
  · have hT := totalDegree_termPoly_le T
    have hs : (∑ d ∈ J, eqPoly d).totalDegree ≤ 1 :=
      totalDegree_finsetSum_le fun d _ => totalDegree_eqPoly_le d
    have h1 : (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d).totalDegree ≤ T.card + 1 :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hs))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · have h0 : eval x (∑ e ∈ I, (eqPoly e + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun e he => ?_
        rw [map_add, map_one, (eval_eqPoly_eq_one_iff x e).mpr (hT e (hI he))]
        decide
      have h1 : eval x (∑ d ∈ J, eqPoly d) = 1 := by
        have := congrArg (eval x) hid
        rw [map_add, h0, zero_add, map_one] at this
        exact this
      rw [eval_termPoly_of_sat x T hT, h1]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem weak_disj_line (hC : DegClosed C D) (T : LinTerm V) (M : LinKLine V)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q) :
    ∃ J : Finset (LinEq V), (∀ d ∈ J, ({d} : LinTerm V) ∈ M) ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T
    ((M.biUnion id).filter (fun q => ({q} : LinTerm V) ∈ M))
    (fun a ha => by
      obtain ⟨q, hq, hs⟩ := himp a ha
      exact ⟨q, Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨{q}, hq, Finset.mem_singleton_self q⟩, hq⟩, hs⟩)
  exact ⟨J, fun d hd => (Finset.mem_filter.mp (hJ hd)).2, hmul⟩
end AlterChoice
noncomputable def lineInputs {V : Type} (L : LinKLine V) : Set (MvPolynomial V (ZMod 2)) :=
  (fun T => termPoly T) '' (↑L : Set (LinTerm V))
noncomputable def etaK (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)
end PEqualNP.ProofComplexity.LinKPlan
namespace PEqualNP.ProofComplexity.LinKSimA
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan
section Abstract
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem totalDegree_one_add_le_k {p : MvPolynomial σ (ZMod 2)} {k : ℕ}
    (h : p.totalDegree ≤ k) : (1 + p).totalDegree ≤ k := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h
theorem totalDegree_prod_le_k {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    {k : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ k) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card * k := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := k) ha
  rw [Nat.mul_comm]
  exact this
theorem prod_absorb_k (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ k : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ k) (hB : s.card * k + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu, Nat.add_mul, Nat.one_mul] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ k := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card * k + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le_k s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ k :=
      totalDegree_one_add_le_k (hdeg u (Finset.mem_insert_self u s))
    have h2 := DegSizeSim.absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3
theorem totalDegree_span_le_k {G : Set (MvPolynomial σ (ZMod 2))} {k : ℕ}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem totalDegree_appr_le_k {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_le_k Finset.univ qs (fun j _ => h j)
  simpa using this
theorem span_mul_mem {G : Set (MvPolynomial σ (ZMod 2))} {Q : MvPolynomial σ (ZMod 2)}
    (hg : ∀ g ∈ G, g * Q ∈ C) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q * Q ∈ C := by
  induction hq using Submodule.span_induction with
  | mem g hg' => exact hg g hg'
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact C.add_mem hx hy
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem transfer_k' (hC : DegClosed C D) {K t k r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t * k + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := fun q hq =>
    span_mul_mem (fun g hg' => by
      rw [← mul_assoc]
      exact hg g hg') hq
  have hdq : ∀ j, (qs j).totalDegree ≤ k := fun j => totalDegree_span_le_k hG (hqs j)
  have h1 := prod_absorb_k hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t * k + K :=
    totalDegree_mul_le' (totalDegree_appr_le_k qs hdq) hf
  have h2 := DegSizeSim.absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3
theorem transfer_k :
    ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t * k + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg =>
    transfer_k' hC qs hG hqs hf hR hB hP hg
end Abstract
section Lines
variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t k : ℕ}
  {f : MvPolynomial V (ZMod 2)}
theorem totalDegree_lineInputs_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem totalDegree_lineAppr_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  totalDegree_appr_le_k qs fun j =>
    totalDegree_span_le_k (totalDegree_lineInputs_le hL) (hqs j)
theorem lineInputs_linKOfClause_subset [DecidableEq V] (A : Clause V) :
    lineInputs (linKOfClause A) ⊆ (fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V)) := by
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
  exact ⟨q, Finset.mem_coe.mpr hq, (termPoly_singleton q).symm⟩
theorem step_ax_k' [DecidableEq V] (hC : DegClosed C D) (A : Clause V) {w : ℕ}
    (hA : clausePoly A ∈ C) (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A)))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  refine DegSizeSim.step_ax hC A hA hw qs
    (fun j => Submodule.span_mono (lineInputs_linKOfClause_subset A) (hqs j)) hf hB ?_
  intro q hq
  have := hH {q} (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  rwa [termPoly_singleton] at this
theorem step_ax_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C := by
  intro V _ C D K t k w f A qs hC hk hA hw hqs hf hB hH
  have htk : t ≤ t * k := Nat.le_mul_of_pos_right t hk
  exact step_ax_k' hC A hA hw qs hqs hf (by omega) hH
theorem step_cut_k' [DecidableEq V] (hC : DegClosed C D) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2))
    (h1 : ∀ T ∈ L₁, T.card ≤ k) (h2 : ∀ T ∈ L₂, T.card ≤ k) (hM : ∀ T ∈ M, T.card ≤ k)
    (hq1 : ∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁))
    (hq2 : ∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t * k + 2 * k ≤ D) (hcut : IsLinKCut L₁ L₂ M)
    (hP1 : (∏ j, (1 + q₁ j)) * f ∈ C) (hP2 : (∏ j, (1 + q₂ j)) * f ∈ C)
    (hHM : ∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k := totalDegree_lineAppr_le hM qM hqM
  generalize (∏ j, (1 + qM j)) = P at hdM hHM ⊢
  obtain ⟨T, hT1, -, rfl⟩ := hcut
  have hTk : T.card ≤ k := h1 T hT1
  have hτ : (termPoly T).totalDegree ≤ k := (totalDegree_termPoly_le T).trans hTk
  have hQ : (P * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hd1 : (1 + termPoly T).totalDegree ≤ k := totalDegree_one_add_le_k hτ
  have hmul : 2 * t * k = t * k + t * k := by ring
  have hA : (1 + termPoly T) * P * f ∈ C := by
    have hdR : ((1 + termPoly T) * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hd1 hdM
    refine transfer_k' hC q₁ (totalDegree_lineInputs_le h1) hq1 hf hdR (by omega) hP1 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₁ := Finset.mem_coe.mp hS
    by_cases hST : S = T
    · rw [hST]
      have := idem_mul hC (termPoly T) (P * f) hQ hτ (by omega)
      have e1 : termPoly T * ((1 + termPoly T) * P) * f
          = P * f * (termPoly T * termPoly T + termPoly T) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS'⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h1 S hS'))) hf
      have := DegSizeSim.absorb_le hC (1 + termPoly T) hmem hd1 hd (by omega)
      have e1 : termPoly S * ((1 + termPoly T) * P) * f
          = (1 + termPoly T) * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have hB' : termPoly T * P * f ∈ C := by
    have hdR : (termPoly T * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hτ hdM
    refine transfer_k' hC q₂ (totalDegree_lineInputs_le h2) hq2 hf hdR (by omega) hP2 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₂ := Finset.mem_coe.mp hS
    by_cases hSi : S ∈ T.image (fun e => ({negLinEq e} : LinTerm V))
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hSi
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨e, he⟩
      have := term_neg_mul hC T e he (P * f) hQ (by omega)
      show termPoly {negLinEq e} * (termPoly T * P) * f ∈ C
      rw [termPoly_singleton]
      have e1 : eqPoly (negLinEq e) * (termPoly T * P) * f
          = P * f * (termPoly T * eqPoly (negLinEq e)) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hS', hSi⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h2 S hS'))) hf
      have := DegSizeSim.absorb_le hC (termPoly T) hmem hτ hd (by omega)
      have e1 : termPoly S * (termPoly T * P) * f
          = termPoly T * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have h3 := C.add_mem hA hB'
  have e1 : (1 + termPoly T) * P * f + termPoly T * P * f = P * f := by
    linear_combination char2_add_self (termPoly T * P * f)
  rwa [e1] at h3
theorem step_cut_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
  exact step_cut_k' hC L₁ L₂ M q₁ q₂ qM h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
end Lines
end PEqualNP.ProofComplexity.LinKSimA
namespace PEqualNP.ProofComplexity.LinKSim
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan
section Abstract
variable {σ : Type}
theorem and_totalDegree_span_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem and_totalDegree_appr_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := Helpers.totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, mul_comm] at this
  exact this
end Abstract
section Lines
variable {V : Type}
theorem and_totalDegree_lineInputs_le {k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem and_totalDegree_lineAppr_le {t k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  and_totalDegree_appr_le qs fun j =>
    and_totalDegree_span_le (and_totalDegree_lineInputs_le L hL) (hqs j)
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem and_half (hC : DegClosed C D) (L M : LinKLine V) (T₀ : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) {K m k : ℕ}
    (hM : ∀ T ∈ M, T.card ≤ k) (hT₀ : T₀.card ≤ k)
    (hP : P.totalDegree ≤ m) (hf : f.totalDegree ≤ K) (hB : K + m + 2 * k ≤ D)
    (htr : ∀ R : MvPolynomial V (ZMod 2), R.totalDegree ≤ m + k →
      (∀ T ∈ L, termPoly T * R * f ∈ C) → R * f ∈ C)
    (hsub : ∀ T ∈ L, T ≠ T₀ → T ∈ M)
    (hHM : ∀ T ∈ M, P * termPoly T * f ∈ C) :
    (1 + termPoly T₀) * P * f ∈ C := by
  have hg0 : (termPoly T₀).totalDegree ≤ k := (totalDegree_termPoly_le T₀).trans hT₀
  have hd1 : (1 + termPoly T₀).totalDegree ≤ k :=
    (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg0)
  refine htr _ ((totalDegree_mul_le' hd1 hP).trans (by omega)) ?_
  intro T hT
  by_cases h0 : T = T₀
  · subst h0
    have h1 := idem_mul hC (termPoly T) (P * f) (totalDegree_mul_le' hP hf) hg0
      (by omega)
    have e : termPoly T * ((1 + termPoly T) * P) * f
        = P * f * (termPoly T * termPoly T + termPoly T) := by ring
    rw [e]
    exact h1
  · have hTM := hsub T hT h0
    have hmem := hHM T hTM
    have hd : (P * termPoly T * f).totalDegree ≤ m + k + K :=
      totalDegree_mul_le'
        (totalDegree_mul_le' hP ((totalDegree_termPoly_le T).trans (hM T hTM))) hf
    have h1 := DegSizeSim.absorb_le hC (1 + termPoly T₀) hmem hd1 hd (by omega)
    have e : termPoly T * ((1 + termPoly T₀) * P) * f
        = (1 + termPoly T₀) * (P * termPoly T * f) := by ring
    rw [e]
    exact h1
end Lines
theorem step_andIntro_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
      (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
      (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
      (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC hL1 hL2 hM hq1 hq2 hqM hf hB hand hP1 hP2 hHM
  obtain ⟨T₁, T₂, hT1, hT2, rfl⟩ := hand
  rw [mul_assoc] at hB
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    and_totalDegree_lineAppr_le _ hM qM hqM
  have hc1 : T₁.card ≤ k := hL1 T₁ hT1
  have hc2 : T₂.card ≤ k := hL2 T₂ hT2
  have hg1 : (termPoly T₁).totalDegree ≤ k := (totalDegree_termPoly_le T₁).trans hc1
  have hg2 : (termPoly T₂).totalDegree ≤ k := (totalDegree_termPoly_le T₂).trans hc2
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hA : (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₁ _ T₁ _ f hM hc1 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₁) q₁ f R hC
        (and_totalDegree_lineInputs_le L₁ hL1) hq1 hf hR (by omega) hP1 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  have hA2 : (1 + termPoly T₂) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₂ _ T₂ _ f hM hc2 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₂) q₂ f R hC
        (and_totalDegree_lineInputs_le L₂ hL2) hq2 hf hR (by omega) hP2 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  have hU : (∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f ∈ C :=
    hHM _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hun := term_union_mul hC T₁ T₂ ((∏ j, (1 + qM j)) * f) hQ (by omega)
  have hd2 : ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f).totalDegree ≤ k + t * k + K := by
    have hd : (1 + termPoly T₂).totalDegree ≤ k :=
      (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg2)
    exact totalDegree_mul_le' (totalDegree_mul_le' hd hdM) hf
  have hmid := DegSizeSim.absorb_le hC (termPoly T₁) hA2 hg1 hd2 (by omega)
  have hsum := C.add_mem (C.add_mem hA hmid) (C.add_mem hU hun)
  have e : (∏ j, (1 + qM j)) * f
      = (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f
        + termPoly T₁ * ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f)
        + ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f
          + (∏ j, (1 + qM j)) * f * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂)) := by
    linear_combination
      (-1 : MvPolynomial V (ZMod 2)) * char2_add_self (termPoly T₁ * (∏ j, (1 + qM j)) * f)
      - char2_add_self (termPoly T₁ * termPoly T₂ * (∏ j, (1 + qM j)) * f)
      - char2_add_self ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f)
  rw [e]
  exact hsum
end PEqualNP.ProofComplexity.LinKSim
namespace PEqualNP.ProofComplexity.LinKSim
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan
section Degrees
variable {σ : Type}
theorem weak_span_degree_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem weak_lineInputs_degree_le {V : Type} {k : ℕ} (L : LinKLine V)
    (hL : ∀ T ∈ L, T.card ≤ k) : ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem weak_appr_degree_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, Nat.mul_comm] at this
  exact this
end Degrees
section Cases
variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_case_term (hC : DegClosed C D) {K r k : ℕ} (T S : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k) (hS : S.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + 2 * k ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (hS' : P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  have h1 := weak_term_mul hC T S himp (P * f) (b := r + K) (totalDegree_mul_le' hP hf)
    (by omega)
  have hdS : (P * termPoly S * f).totalDegree ≤ r + k + K :=
    totalDegree_mul_le' (totalDegree_mul_le' hP ((totalDegree_termPoly_le S).trans hS)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hS'
    ((totalDegree_termPoly_le T).trans hT) hdS (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * termPoly S) + termPoly T * (P * termPoly S * f) := by
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * termPoly S * f))
  rw [e]
  exact C.add_mem h1 h2
theorem weak_case_disj [Fintype V] [DecidableEq V] (hC : DegClosed C D) {K r k : ℕ}
    (T : LinTerm V) (M : LinKLine V) (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + k + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q)
    (hM : ∀ S ∈ M, P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_line (C := C) (D := D) hC T M himp
  have h1 := hmul (P * f) (r + K) (totalDegree_mul_le' hP hf) (by omega)
  have hsum : ∑ d ∈ J, P * eqPoly d * f ∈ C := by
    refine Submodule.sum_mem _ fun d hd => ?_
    have := hM {d} (hJ d hd)
    rwa [termPoly_singleton] at this
  have hds : (∑ d ∈ J, P * eqPoly d * f).totalDegree ≤ r + 1 + K :=
    totalDegree_finsetSum_le fun d _ =>
      totalDegree_mul_le' (totalDegree_mul_le' hP (totalDegree_eqPoly_le d)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hsum
    ((totalDegree_termPoly_le T).trans hT) hds (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d)
        + termPoly T * ∑ d ∈ J, P * eqPoly d * f := by
    have e1 : ∑ d ∈ J, P * eqPoly d * f = P * (∑ d ∈ J, eqPoly d) * f := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1]
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * (∑ d ∈ J, eqPoly d) * f))
  rw [e]
  exact C.add_mem h1 h2
end Cases
theorem step_weak_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
      (qL qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
      (∏ j, (1 + qL j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ _ C D K t k f L M qL qM hC hk hL hM hqL hqM hf hB hweak hPL hHM
  have h2 : 2 * t * k = t * k + t * k := by ring
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    weak_appr_degree_le qM fun j =>
      weak_span_degree_le (weak_lineInputs_degree_le M hM) (hqM j)
  refine htransfer V C D K t k (t * k) (lineInputs L) qL f _ hC
    (weak_lineInputs_degree_le L hL) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ L := Finset.mem_coe.mp hT
  rcases hweak T hT' with ⟨S, hS, himp⟩ | himp
  · exact weak_case_term hC T S _ f (hL T hT') (hM S hS) hdM hf (by omega) himp (hHM S hS)
  · exact weak_case_disj hC T M _ f (hL T hT') hdM hf (by omega) himp hHM
end PEqualNP.ProofComplexity.LinKSim
namespace PEqualNP.ProofComplexity.LinKSim
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan
def AxRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C
def CutRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def AndRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def WeakRule : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
    (∏ j, (1 + qL j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def SimDrv : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) →
    IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f)
def SimRef : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f
theorem drv_card_le {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil =>
    intro L hL
    simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | cut _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
theorem simulation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule) (hweak : WeakRule) :
    SimDrv := by
  intro V _ _ F π k w D K t f qs hk hw hder hB hf
  have hB1 : K + 2 * t * k + 2 * k ≤ D := by
    have := (Nat.add_le_add_left (le_max_left (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hB2 : K + t * k + w ≤ D := by
    have := (Nat.add_le_add_left (le_max_right (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hD2 : 2 ≤ D := by
    have h2 : 2 ≤ 2 * k := by omega
    exact h2.trans ((Nat.le_add_left _ _).trans hB1)
  have hwD : w ≤ D := (Nat.le_add_left _ _).trans hB2
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ hD2 fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ L ∈ ρ, ∀ T ∈ L, (∏ j, (1 + qs L j)) * termPoly T * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 _ ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        obtain ⟨A, hAF, hA⟩ := hL0
        subst hA
        have hAw := hw A hAF
        have hmem : clausePoly A ∈ pcClosure (cnfSystem F) D :=
          PCDerivable.ax (Or.inr ⟨A, hAF, rfl⟩)
            ((DegSizeSim.totalDegree_clausePoly_le A).trans (hAw.trans hwD))
        exact hax V (pcClosure (cnfSystem F) D) D K t k w f A (qs (linKOfClause A))
          hC hk hmem hAw (hs _ List.mem_cons_self) hf hB2 (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @cut ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hcut V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @andIntro ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hand V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M hρ' h1 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hweak V (pcClosure (cnfSystem F) D) D K t k f L1 L (qs L1) (qs L)
          hC hk (drv_card_le hρ' L1 h1) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf hB1 hrule
          (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH
theorem simulation_refutation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule)
    (hweak : WeakRule) : SimRef := by
  intro V _ _ F π k w D K t f qs hk hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation_of hax hcut hand hweak V F π k w D K t f qs hk hw hder hB hf hs hH
    ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa [lineInputs] using this
  simpa [hq] using h
end PEqualNP.ProofComplexity.LinKSim
namespace PEqualNP.ProofComplexity.DegSizeGainK
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
noncomputable def eta_k (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)
section Poly
variable {σ : Type}
theorem deg_one_add_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (1 + q).totalDegree ≤ k :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)
theorem deg_idem_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (q * q + q).totalDegree ≤ 2 * k :=
  (totalDegree_add _ _).trans (max_le ((DegSizeGain.deg_mul_le hq hq).trans (by omega))
    (by omega))
theorem deg_le_of_mem_span {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k :=
  DegSizeGain.mem_polyLE.mp
    (Submodule.span_le.mpr (fun g hg => DegSizeGain.mem_polyLE.mpr (hG g hg)) hq)
theorem deg_prod_le_k {k t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, k :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le_k (h j))
    _ = t * k := by simp
variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem idem_monomial_one (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ), (u.sum fun _ e => e) = n → 2 * n ≤ D →
      monomial u (1 : ZMod 2) * monomial u 1 + monomial u 1 ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    have h0 : u = 0 := DegSizeGain.eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [hm, one_mul, CharTwo.add_self_eq_zero]
    exact C.zero_mem
  | succ n ih =>
    intro u hu hD
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := DegSizeGain.exists_single_add u h0
    have hm' := ih u' (by omega) (by omega)
    have hmd : (monomial u' (1 : ZMod 2)).totalDegree ≤ n := by
      have h2 : (monomial u' (1 : ZMod 2)).totalDegree ≤ (u'.sum fun _ e => e) :=
        totalDegree_monomial_le u' 1
      omega
    have e0 : monomial (Finsupp.single v 1 + u') (1 : ZMod 2) = X v * monomial u' 1 := by
      rw [monomial_single_add, pow_one]
    rw [e0]
    generalize monomial u' (1 : ZMod 2) = m at hm' hmd ⊢
    have e : X v * m * (X v * m) + X v * m
        = (m * m) * (X v * X v + X v) + X v * (m * m + m) := by
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) *
        CharTwo.add_self_eq_zero (X v * (m * m))
    rw [e]
    refine C.add_mem ?_ (hC.mulX v _ hm' ?_)
    · refine DegSizeGain.absorb hC (hC.bool v) ?_
      have h1 := DegSizeGain.deg_mul_le hmd hmd
      have h2 := DegSizeRank.bool_totalDegree_le v
      omega
    · have h1 := deg_idem_le_k hmd
      omega
theorem idem_monomial_k (hC : DegClosed C D) {k : ℕ} (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ k) (hD : 2 * k ≤ D) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · exact idem_monomial_one hC _ u rfl (by omega)
theorem idem_k (hC : DegClosed C D) {k : ℕ} (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ k) (hD : 2 * k ≤ D) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ k) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial_k hC a (c a) (hs a (Finset.mem_insert_self a s)) hD)
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h
theorem errRank_one_le_k [Fintype σ] (hC : DegClosed C D) {k : ℕ}
    {G : Set (MvPolynomial σ (ZMod 2))} (hG : ∀ g ∈ G, g.totalDegree ≤ k) {K : ℕ}
    (hD : K + k ≤ D) : errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := DegSizeGain.mem_polyLE.mp hf.2
    rw [DegSizeGain.mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact DegSizeGain.absorb hC hfC (by omega)
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega
end Poly
theorem monoRank_mul :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b K : ℕ)
      (M : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ m ∈ M, m.totalDegree ≤ b) → b + K ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C M l' * numMono (Fintype.card σ) l
          ≤ errRank C M l * numMono (Fintype.card σ) l' := by
  intro σ _ C D b K M hC hmdeg hD
  have hX : ∀ p ∈ DegSizeRank.annih C M, p.totalDegree < K → ∀ i : σ,
      X i * p ∈ DegSizeRank.annih C M := by
    intro p hp hdeg i
    rw [DegSizeRank.mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ DegSizeRank.annih C M := by
    intro d i hd
    rw [DegSizeRank.mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine DegSizeRank.absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := DegSizeRank.totalDegree_monomial_one d
    have h3 := DegSizeRank.bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C M (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C M j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [DegSizeRank.errRank_eq_map, DegSizeRank.errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (DegSizeRank.annih C M) K hX hB j hj
  intro l l' hll' hl'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hll'
  exact DegSizeRank.iterate_ratio (fun j => errRank C M j)
    (fun j => numMono (Fintype.card σ) j) K (fun j => DegSizeGain.numMono_pos _ j) step l t hl'
theorem monoRank_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → a + K + k ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C (zMul P G) l' * numMono (Fintype.card σ) l
          ≤ errRank C (zMul P G) l * numMono (Fintype.card σ) l' := by
  intro σ _ C D a K k P G hC hP hG hD
  refine monoRank_mul σ C D (a + k) K (zMul P G) hC ?_ (by omega)
  rintro _ ⟨g, hg, rfl⟩
  exact DegSizeGain.deg_mul_le hP (hG g hg)
theorem rankRetention_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D b l k : ℕ) (H : Set (MvPolynomial σ (ZMod 2)))
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ k) →
      b + l + 2 * k ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) l
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
  classical
  intro σ _ C D b l k H G hC hH hG hD
  let gfun : ↥G → MvPolynomial σ (ZMod 2) := fun i => i
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  have hcd : ∀ c : ↥G → ZMod 2, (comb gfun c).totalDegree ≤ k := by
    intro c
    refine DegSizeGain.mem_polyLE.mp ?_
    unfold comb
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (DegSizeGain.mem_polyLE.mpr (hG i i.2))
  have hmul : ∀ (c c' : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * comb gfun c * hfun α ∈ C → f * comb gfun c * comb gfun c' * hfun α ∈ C := by
    intro c c' α f hf hmem
    have e : f * comb gfun c * comb gfun c' * hfun α
        = comb gfun c' * (f * comb gfun c * hfun α) := by ring
    rw [e]
    refine DegSizeGain.absorb hC hmem ?_
    have h1 : (f * comb gfun c * hfun α).totalDegree ≤ l + k + b := DegSizeGain.deg_mul_le
      (DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hcd c)) (hH α α.2)
    have h2 := hcd c'
    omega
  have hidem : ∀ (c : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * (comb gfun c * comb gfun c + comb gfun c) * hfun α ∈ C := by
    intro c α f hf
    have e : f * (comb gfun c * comb gfun c + comb gfun c) * hfun α
        = (f * hfun α) * (comb gfun c * comb gfun c + comb gfun c) := by ring
    rw [e]
    refine DegSizeGain.absorb hC (idem_k hC _ (hcd c) (by omega)) ?_
    have h1 : (f * hfun α).totalDegree ≤ l + b :=
      DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hH α α.2)
    have h2 := deg_idem_le_k (hcd c)
    omega
  obtain ⟨c, hc⟩ := rank_retention_mul (ι := ↥G) (τ := ↥H) C (polyLE σ l) gfun hfun
    hmul hidem
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb gfun c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • (i : MvPolynomial σ (ZMod 2)) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ l) hfun (gfun i)))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ l) hfun (gfun ⟨g, hg⟩) f = 0 := congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ l) hfun _ f).1 hz' ⟨h, hh⟩
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ l) hfun (gfun i) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * gfun i * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ l) hfun (comb gfun c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩
theorem gain_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K →
      a + K + 2 * k ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - k)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K k P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := rankRetention_used_k σ C D a (K - k) k {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - k) ≤ 2 * errRank C {P * q} (K - k) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ k := deg_le_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := idem_k hC q hq1 (by omega)
  have hidem2 := deg_idem_le_k hq1
  refine ⟨q, hqs, ?_⟩
  have hi : polyLE σ (K - k) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - k) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [DegSizeGain.mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := DegSizeGain.deg_mul_le hP hfd
      exact DegSizeGain.absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  have hii : (polyLE σ (K - k)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [DegSizeGain.mem_errKer_zMul]
      have hd0 := DegSizeGain.deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact DegSizeGain.absorb hC hidem (by omega)
    · intro f hf
      rw [DegSizeGain.mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le_k hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact DegSizeGain.absorb hC (hf.2 g hg) (by omega)
  have key := DegSizeGain.finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - k))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - k)) ≤ finrank (ZMod 2) (polyLE σ (K - k)) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega
theorem greedy_arith_k {c c' c1 h n K k t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - k) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta_k n K k) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta_k n K k) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - k) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta_k n K k := by
    have hle : eta_k n K k ≤ 1 := by
      unfold eta_k
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta_k n K k ≤ c1 / 2 := by
    unfold eta_k
    have e1 : (c : ℝ) * (numMono n (K - k) / (2 * numMono n K))
        = (c * numMono n (K - k)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta_k n K k) := by linarith
    _ ≤ (h * (1 - eta_k n K k) ^ t) * (1 - eta_k n K k) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta_k n K k) ^ (t + 1) := by ring
theorem greedy_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t := by
  intro σ _ C D K t k G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le_k hC hG' (by omega)
  | succ t ih =>
    intro hD
    have et : (t + 1) * k = t * k + k := by ring
    rw [et] at hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
      deg_prod_le_k qs (fun j => deg_le_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain_k σ C D (t * k) K k _ G hC hP hG hK (by omega)
    have h41' := monoRank_used_k σ C D (t * k) K k _ (↑G) hC hP hG' (by omega) (K - k) K
      (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith_k hgain h41' hb
theorem common_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      (S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t k ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy_k σ C D K t k (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact DegSizeGain.mem_polyLE.mpr (by simp)
    exact h1 hone.1
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    DegSizeGain.codim_iInf (polyLE σ K)
      (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => DegSizeGain.errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, DegSizeGain.mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩,
    fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (DegSizeGain.mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)
end PEqualNP.ProofComplexity.DegSizeGainK
namespace PEqualNP.ProofComplexity.LinKAsm
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.LinKPlan PEqualNP.ProofComplexity.DegSizePlan
def StmtSimRefutation : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f
def StmtArith : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t) →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
def StmtAssembly : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π → ¬ PCRefutable (cnfSystem F) D →
    k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
    1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t
def StmtGeneral : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
theorem term_card {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | cut _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | weak _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
theorem etaK_le_one (n K k : ℕ) : etaK n K k ≤ 1 := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  unfold etaK
  exact (div_le_one (by positivity)).mpr (by linarith)
theorem assembly (hSim : StmtSimRefutation) : StmtAssembly := by
  classical
  intro V _ _ F π k w D K t hk hw href hnr hkK hB
  by_contra hlt
  rw [not_le] at hlt
  have hk2 : 2 * k ≤ 2 * t * k + 2 * k := Nat.le_add_left _ _
  have hD2 : 2 ≤ D := by omega
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure (cnfSystem F) D hD2 (fun v => Or.inl ⟨v, rfl⟩)
  have h1 : (1 : MvPolynomial V (ZMod 2)) ∉ pcClosure (cnfSystem F) D := hnr
  have hnn : (0 : ℝ) ≤ (1 - etaK (Fintype.card V) K k) ^ t :=
    pow_nonneg (sub_nonneg.mpr (etaK_le_one _ K k)) t
  have hcard : (π.toFinset.card : ℝ) ≤ (π.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le π
  have hS : (π.toFinset.card : ℝ) * (1 - DegSizeGainK.eta_k (Fintype.card V) K k) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hnn) hlt
  have htk : t * k + k ≤ 2 * t * k + 2 * k := by nlinarith
  obtain ⟨f, qs, hf, hfC, hspan, hmem⟩ :=
    DegSizeGainK.common_k V (pcClosure (cnfSystem F) D) D K t k (LinKLine V) π.toFinset
      (fun L => L.image (fun T => termPoly T)) hC h1
      (by
        intro L hL g hg
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hg
        exact le_trans (totalDegree_termPoly_le T)
          (term_card href.1 L (List.mem_toFinset.mp hL) T hT))
      hkK (by omega) hS
  apply hfC
  refine hSim V F π k w D K t f qs hk hw href hB hf ?_ ?_
  · intro L hL j
    have := hspan L (List.mem_toFinset.mpr hL) j
    simpa [lineInputs, Finset.coe_image] using this
  · intro L hL T hT
    exact hmem L (List.mem_toFinset.mpr hL) (termPoly T) (Finset.mem_image_of_mem _ hT)
theorem degree_to_size_k (hSim : StmtSimRefutation) (hArith : StmtArith) : StmtGeneral := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href
  exact hArith V F π k w D hw hk hkD hwD hnr href
    (fun K t hkK hB => assembly hSim V F π k w D K t hk hw href hnr hkK hB)
end PEqualNP.ProofComplexity.LinKAsm
namespace PEqualNP.ProofComplexity.LinKSim
open PEqualNP.ProofComplexity.LinKPlan PEqualNP.ProofComplexity.LinKSimA
theorem step_andIntro : AndRule := step_andIntro_of transfer_k
theorem step_weak : WeakRule := step_weak_of transfer_k
theorem simulation : SimDrv := simulation_of step_ax_k step_cut_k step_andIntro step_weak
theorem simulation_refutation : PEqualNP.ProofComplexity.LinKAsm.StmtSimRefutation :=
  simulation_refutation_of step_ax_k step_cut_k step_andIntro step_weak
end PEqualNP.ProofComplexity.LinKSim
namespace PEqualNP.ProofComplexity.Helpers.LinKOne
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
omit [DecidableEq V] in
theorem weakening_sound {a : V → Bool} {L M : LinKLine V} (h : IsLinKWeakening L M)
    (hs : LinKLineSat a L) : LinKLineSat a M := by
  obtain ⟨T, hT, hTs⟩ := hs
  rcases h T hT with ⟨S, hS, himp⟩ | hb
  · exact ⟨S, hS, himp a hTs⟩
  · obtain ⟨q, hq, hqs⟩ := hb a hTs
    refine ⟨{q}, hq, fun q' hq' => ?_⟩
    rw [Finset.mem_singleton.mp hq']
    exact hqs
end PEqualNP.ProofComplexity.Helpers.LinKOne
namespace PEqualNP.ProofComplexity.DegSizeArithK
open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
open PEqualNP.ProofComplexity.DegSizeGainK (eta_k)
theorem numMono_ratio_iter (n j k : ℕ) (h : j + k ≤ n + 1) :
    (j + 1) ^ k * numMono n (j + k) ≤ (n + 1) ^ k * numMono n j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hr := DegSizeArith.numMono_ratio n (j + k) (by omega)
    calc (j + 1) ^ (k + 1) * numMono n (j + (k + 1))
        = (j + 1) ^ k * ((j + 1) * numMono n (j + k + 1)) := by
          rw [show j + (k + 1) = j + k + 1 from rfl]; ring
      _ ≤ (j + 1) ^ k * ((j + k + 1) * numMono n (j + k + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ (j + 1) ^ k * ((n + 1) * numMono n (j + k)) := Nat.mul_le_mul_left _ hr
      _ = (n + 1) * ((j + 1) ^ k * numMono n (j + k)) := by ring
      _ ≤ (n + 1) * ((n + 1) ^ k * numMono n j) := Nat.mul_le_mul_left _ ih'
      _ = (n + 1) ^ (k + 1) * numMono n j := by ring
theorem eta_k_le_half (n K k : ℕ) : eta_k n K k ≤ 1 / 2 := by
  unfold eta_k
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeArith.numMono_pos n K
  have hle : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith
theorem eta_k_le_one (n K k : ℕ) : eta_k n K k ≤ 1 :=
  (eta_k_le_half n K k).trans (by norm_num)
theorem eta_k_ge (n K k : ℕ) (hk : k ≤ K) (hK : K ≤ n + 1) :
    (1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k ≤ eta_k n K k := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + k := ⟨K - k, by omega⟩
  have hnat := numMono_ratio_iter n j k hK
  unfold eta_k
  rw [Nat.add_sub_cancel]
  have hN : (0 : ℝ) < numMono n (j + k) := by
    exact_mod_cast DegSizeArith.numMono_pos n (j + k)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : ((j : ℝ) + 1) ^ k * (numMono n (j + k) : ℝ)
      ≤ ((n : ℝ) + 1) ^ k * (numMono n j : ℝ) := by exact_mod_cast hnat
  push_cast
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hn k) (by linarith)]
  nlinarith [hr]
theorem exp_le_of_one_le (S x : ℝ) (t : ℕ) (hx : x ≤ 1) (h : 1 ≤ S * (1 - x) ^ t) :
    Real.exp ((t : ℝ) * x) ≤ S := by
  have hp0 : (0 : ℝ) ≤ (1 - x) ^ t := pow_nonneg (by linarith) t
  have hS : 0 ≤ S := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hp0
    linarith
  have hpow : (1 - x) ^ t ≤ Real.exp (-((t : ℝ) * x)) := by
    have h1 : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    have h2 : (1 - x) ^ t ≤ Real.exp (-x) ^ t := pow_le_pow_left₀ (by linarith) h1 t
    rw [← Real.exp_nat_mul] at h2
    rwa [mul_neg] at h2
  have h3 : 1 ≤ S * Real.exp (-((t : ℝ) * x)) :=
    h.trans (mul_le_mul_of_nonneg_left hpow hS)
  have hpos : 0 < Real.exp ((t : ℝ) * x) := Real.exp_pos _
  calc Real.exp ((t : ℝ) * x) = Real.exp ((t : ℝ) * x) * 1 := (mul_one _).symm
    _ ≤ Real.exp ((t : ℝ) * x) * (S * Real.exp (-((t : ℝ) * x))) :=
        mul_le_mul_of_nonneg_left h3 hpos.le
    _ = S * (Real.exp ((t : ℝ) * x) * Real.exp (-((t : ℝ) * x))) := by ring
    _ = S := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
theorem size_core (n k K t : ℕ) (S : ℝ) (hkK : k ≤ K) (hKn : K ≤ n + 1)
    (h : 1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S := by
  have h1 := exp_le_of_one_le S (eta_k n K k) t (eta_k_le_one n K k) h
  refine le_trans (Real.exp_le_exp.mpr ?_) h1
  exact mul_le_mul_of_nonneg_left (eta_k_ge n K k hkK hKn) (Nat.cast_nonneg t)
section Plan
theorem negLinEq_not_sat {V : Type} (a : V → Bool) (e : LinEq V) (h : LinEqSat a e) :
    ¬ LinEqSat a (negLinEq e) := by
  unfold LinEqSat at h
  unfold LinEqSat negLinEq
  intro h'
  cases hb : e.2 <;> simp_all
theorem linK_cut_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKCut C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) : LinKLineSat a R := by
  obtain ⟨T, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases hTT : T' = T
  · subst hTT
    refine ⟨U, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hU, ?_⟩), hsU⟩
    intro hmem
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    exact negLinEq_not_sat a e (hs' e he) (hsU _ (Finset.mem_singleton_self _))
  · exact ⟨T', Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTT, hT'⟩), hs'⟩
theorem linK_andIntro_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) :
    LinKLineSat a R := by
  obtain ⟨T₁, T₂, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases h1 : T' = T₁
  · by_cases h2 : U = T₂
    · subst h1 h2
      refine ⟨T' ∪ U, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hs' q hq
      · exact hsU q hq
    · exact ⟨U, Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h2, hU⟩)), hsU⟩
  · exact ⟨T', Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1, hT'⟩)), hs'⟩
theorem linK_derivation_sound {V : Type} [DecidableEq V] (a : V → Bool) {k : ℕ}
    {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) (ha : ∀ C ∈ F, LinKLineSat a C) :
    ∀ C ∈ π, LinKLineSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hCF _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ha _ hCF
    · exact ih E hE
  | cut _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_cut_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | andIntro _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_andIntro_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | weak _ hC hw _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact LinKOne.weakening_sound hw (ih _ hC)
    · exact ih E hE
theorem linK_refutation_unsat :
    ∀ (V : Type) [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (π : List (LinKLine V)),
      IsLinKRefutation k F π → ¬ Satisfiable F := by
  rintro V _ F k π h ⟨a, ha⟩
  have hax : ∀ C ∈ (fun C => linKOfClause C) '' F, LinKLineSat a C := by
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨l, hl, hs⟩ := ha C hC
    refine ⟨{(({l.1} : Finset V), l.2)},
      Finset.mem_image.mpr ⟨(({l.1} : Finset V), l.2), Finset.mem_image.mpr ⟨l, hl, rfl⟩, rfl⟩,
      ?_⟩
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    exact (linEqSat_singleton a l.1 l.2).mpr hs
  obtain ⟨T, hT, -⟩ := linK_derivation_sound a h.1 hax ∅ h.2
  exact absurd hT (Finset.notMem_empty T)
theorem etaK_le_one : ∀ n K k : ℕ, LinKPlan.etaK n K k ≤ 1 :=
  fun n K k => eta_k_le_one n K k
theorem final_plan_num (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = D / (4 * k) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = q - 1 := ⟨_, rfl⟩
  have hqk : q * (4 * k) ≤ D := by rw [hq]; exact Nat.div_mul_le_self D (4 * k)
  have hq4 : 4 ≤ q := by rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 4 * k * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : q * (4 * k) = 4 * (q * k) := by ring
  have e3 : 4 * k * (q + 1) = 4 * (q * k) + 4 * k := by ring
  have h4k : 4 * k ≤ q * k := Nat.mul_le_mul_right k hq4
  have etk : t * k = q * k - k := by rw [ht, Nat.sub_mul, one_mul]
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have hbud : K + max (2 * t * k + 2 * k) (t * k + w) ≤ D := by
    rw [e2]
    rcases max_cases (2 * (t * k) + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
      rw [h'] <;> omega
  have hDt : D ≤ 8 * (t * k) := by omega
  have haD : 7 * D ≤ 16 * a := by omega
  have hcore := size_core n k K t S (by omega) (by omega) (hasm K t (by omega) hbud)
  rw [← ha] at hcore
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hDtR : (D : ℝ) ≤ 8 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have h1 : (D : ℝ) / (16 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hr : (D : ℝ) / (4 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  have hr0 : (0 : ℝ) ≤ (D : ℝ) / (4 * (n : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k
      ≤ (t : ℝ) / 2 * ((a : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * ((a : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring
theorem final_of_assembly_plan :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
      (k w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
      ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
      (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
        1 ≤ (π.length : ℝ) * (1 - LinKPlan.etaK (Fintype.card V) K k) ^ t) →
      Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
        ≤ (π.length : ℝ) := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href hasm
  have hunsat : ¬ Satisfiable F := linK_refutation_unsat V F k π href
  have hDn : D < Fintype.card V := by
    by_contra hcon
    exact hnr (DegSizeArith.complete_deg V F w D hw hunsat (by omega) (by omega))
  exact final_plan_num (Fintype.card V) k w D _ hk hkD hwD hDn hasm
end Plan
end PEqualNP.ProofComplexity.DegSizeArithK
namespace P210
namespace Cycles210
private theorem rotate_constant {n : Nat} (f : Fin n → Bool)
    (h : ∀ a, f a = true → f (finRotate n a) = true) (i j : Fin n) : f i = f j := by
  by_cases hn : 2 ≤ n
  · have nonfixed (x : Fin n) : finRotate n x ≠ x := by
      apply Equiv.Perm.mem_support.mp
      rw [support_finRotate_of_le hn]
      exact Finset.mem_univ _
    have reach (a b : Fin n) (ha : f a = true) : f b = true := by
      obtain ⟨m,hm⟩ := (isCycle_finRotate_of_le hn).exists_pow_eq (nonfixed a) (nonfixed b)
      have go (s : Nat) : f ((finRotate n ^ s) a) = true := by
        induction s with
        | zero => simpa using ha
        | succ s ih =>
            rw [pow_succ', Equiv.Perm.mul_apply]
            exact h _ ih
      rw [← hm]
      exact go m
    cases hi : f i <;> cases hj : f j
    · rfl
    · exact Bool.noConfusion (hi.symm.trans (reach j i hj))
    · exact Bool.noConfusion (hj.symm.trans (reach i j hi))
    · rfl
  · have hsame : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    rw [hsame]
noncomputable def onFiber {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (b : β) :
    Equiv.Perm {a : α // f a = b} :=
  let e := Fintype.equivFin {a : α // f a = b}
  e.trans ((finRotate _).trans e.symm)
noncomputable def cycle {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (onFiber f)).trans (Equiv.sigmaFiberEquiv f))
theorem keeps {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    f (cycle f a) = f a :=
  (onFiber f (f a) ⟨a,rfl⟩).property
theorem on_value {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (b : β)
    (a : {a : α // f a = b}) : cycle f a.val = (onFiber f b a).val := by
  obtain ⟨a, ha⟩ := a
  subst b
  rfl
theorem equal {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (a : α → Bool)
    (h : ∀ x, a x = true → a (cycle f x) = true) {x y : α} (he : f x = f y) : a x = a y := by
  let e := Fintype.equivFin {z : α // f z = f x}
  let g := fun j => a (e.symm j).val
  have step (z : Fin _) (hz : g z = true) : g (finRotate _ z) = true := by
    let v := e.symm z
    have same := on_value f (f x) v
    have h' := h v.val hz
    rw [same] at h'
    change a ((Fintype.equivFin {z : α // f z = f x}).symm
      (finRotate _ (e (e.symm z)))).val = true at h'
    simpa only [Equiv.apply_symm_apply] using h'
  have res := rotate_constant g step (e ⟨x,rfl⟩) (e ⟨y,he.symm⟩)
  simpa only [g, Equiv.symm_apply_apply] using res
end Cycles210
namespace Replay210
open PEqualNP.ProofComplexity MvPolynomial
def litMap {V W : Type} (f : V → W) (l : Literal V) : Literal W :=
  (f l.1, l.2)
theorem renameReplay {V W : Type} (f : V → W)
    {F : Set (MvPolynomial V (ZMod 2))} {G : Set (MvPolynomial W (ZMod 2))}
    {D : ℕ} {p : MvPolynomial V (ZMod 2)}
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G D (rename f a))
    (hp : PCDerivable F D p) : PCDerivable G D (rename f p) := by
  induction hp with
  | ax ha hd => exact hax _ ha hd
  | zero => simpa using (PCDerivable.zero : PCDerivable G D 0)
  | add _ _ h₁ h₂ => simpa only [map_add] using h₁.add h₂
  | @mulX j p _ hd ih =>
      rw [map_mul, rename_X]
      apply PCDerivable.mulX (f j) ih
      simpa only [map_mul, rename_X] using (totalDegree_rename_le f (X j * p)).trans hd
theorem clausePoly_image {V W : Type} [DecidableEq W] (f : V → W) (A : Clause V)
    (hf : Set.InjOn (litMap f) (↑A : Set (Literal V))) :
    rename f (clausePoly A) = clausePoly (A.image (litMap f)) := by
  unfold clausePoly
  rw [map_prod, Finset.prod_image]
  · refine Finset.prod_congr rfl ?_
    rintro ⟨v,b⟩ _
    cases b <;> simp [litMap]
  · exact fun x hx y hy h => hf hx hy h
theorem clausePoly_pair {W : Type} [DecidableEq W] (w : W) :
    clausePoly ({(w, true), (w, false)} : Clause W) = X w * X w + X w := by
  simp [clausePoly, Finset.prod_insert, add_mul, add_comm]
theorem link_image {V W : Type} [DecidableEq V] [DecidableEq W]
    (f : V → W) (x y : V) (b : Bool) (hxy : f x = f y) :
    let A : Clause V := {(x, b), (y, !b)}
    Set.InjOn (litMap f) (↑A : Set (Literal V)) ∧
      A.image (litMap f) = {(f x, true), (f x, false)} := by
  dsimp only
  constructor
  · intro u hu v hv huv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · have he := congrArg Prod.snd huv
      cases b <;> simp [litMap] at he
    · have he := congrArg Prod.snd huv
      cases b <;> simp [litMap] at he
    · rfl
  · cases b <;> simp [litMap, hxy, Finset.pair_comm]
theorem refutable {V W : Type} [DecidableEq W] (f : V → W)
    (F : Set (Clause V)) (G : Set (Clause W))
    (h : ∀ A ∈ F, Set.InjOn (litMap f) (↑A : Set (Literal V)) ∧
      (A.image (litMap f) ∈ G ∨ ∃ w : W, A.image (litMap f) = {(w, true), (w, false)}))
    {D : ℕ} (hp : PCRefutable (cnfSystem F) D) : PCRefutable (cnfSystem G) D := by
  have hg := renameReplay f (G := cnfSystem G) (p := 1) ?_ hp
  · simpa only [PCRefutable, map_one] using hg
  · intro a ha hdeg
    refine .ax ?_ ((totalDegree_rename_le f a).trans hdeg)
    rcases ha with ⟨v, rfl⟩ | ⟨A, hA, rfl⟩
    · exact Or.inl ⟨f v, by simp⟩
    · obtain ⟨hinj, himage⟩ := h A hA
      rw [clausePoly_image f A hinj]
      rcases himage with hAG | ⟨w, hw⟩
      · exact Or.inr ⟨_, hAG, rfl⟩
      · exact Or.inl ⟨w, by rw [hw, clausePoly_pair]⟩
end Replay210
namespace Split210
open PEqualNP.ProofComplexity
abbrev Occ {v : Nat} (F : Finset (Clause (Fin v))) := Σ C : ↑F, ↥C.val
def label {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) : Fin v := x.2.val.1
def sign {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) : Bool := x.2.val.2
noncomputable def next {v : Nat} (F : Finset (Clause (Fin v))) : Equiv.Perm (Occ F) :=
  Cycles210.cycle label
def lift {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) (l : ↥C.val) : Literal (Occ F) :=
  (⟨C,l⟩,l.val.2)
theorem lift_inj {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) : Function.Injective (lift C) := by
  intro a b eq
  obtain ⟨_, h⟩ := Sigma.mk.inj (congrArg Prod.fst eq)
  exact eq_of_heq h
noncomputable def copyClause {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) : Clause (Occ F) := by
  classical
  exact Finset.univ.image (lift C)
noncomputable def link {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) : Clause (Occ F) := by
  classical
  exact {(x,false), (next F x,true)}
noncomputable def base {v : Nat} (F : Finset (Clause (Fin v))) : Finset (Clause (Occ F)) := by
  classical
  exact Finset.univ.image copyClause
noncomputable def links {v : Nat} (F : Finset (Clause (Fin v))) : Finset (Clause (Occ F)) := by
  classical
  exact Finset.univ.image link
noncomputable def split {v : Nat} (F : Finset (Clause (Fin v))) : Finset (Clause (Occ F)) := by
  classical
  exact base F ∪ links F
theorem card_occ {v : Nat} (F : Finset (Clause (Fin v))) :
    Fintype.card (Occ F) = F.sum (fun C => C.card) := by
  classical
  simpa [Occ, Fintype.card_sigma] using Finset.sum_attach F (fun C => C.card)
theorem width {v w : Nat} (F : Finset (Clause (Fin v)))
    (h : ∀ C ∈ F, C.Nonempty ∧ C.card ≤ w) :
    ∀ C ∈ split F, C.Nonempty ∧ C.card ≤ max 2 w := by
  classical
  intro C hC
  rcases Finset.mem_union.mp hC with hC | hC
  · obtain ⟨old, _, rfl⟩ := Finset.mem_image.mp hC
    have cw : (copyClause old).card = old.val.card := by
      rw [copyClause, Finset.card_image_of_injective _ (lift_inj old)]
      simp
    refine ⟨Finset.card_pos.mp ?_, ?_⟩ <;> rw [cw]
    · exact Finset.card_pos.mpr (h old.val old.property).1
    · exact (h old.val old.property).2.trans (le_max_right _ _)
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨Finset.insert_nonempty _ _, Finset.card_le_two.trans (le_max_left _ _)⟩
theorem map_copy {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) :
    Set.InjOn (Replay210.litMap label) (↑(copyClause C) : Set (Literal (Occ F))) ∧
    (copyClause C).image (Replay210.litMap label) = C.val := by
  classical
  constructor
  · intro a ha b hb eq
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact congrArg (lift C) (Subtype.ext eq)
  · ext l
    constructor
    · intro hl
      obtain ⟨lifted, hlifted, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hlifted
      exact m.property
    · intro hl
      exact Finset.mem_image.mpr ⟨lift C ⟨l,hl⟩, Finset.mem_image.mpr ⟨⟨l,hl⟩,Finset.mem_univ _,rfl⟩, rfl⟩
theorem replay {v : Nat} (F : Finset (Clause (Fin v))) {D : Nat} :
    PCRefutable (cnfSystem (↑(split F) : Set (Clause (Occ F)))) D →
      PCRefutable (cnfSystem (↑F : Set (Clause (Fin v)))) D := by
  classical
  apply Replay210.refutable label
  intro C hC
  rcases Finset.mem_union.mp hC with hb | hl
  · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h, eq⟩ := map_copy B
    exact ⟨h, Or.inl (eq.symm ▸ B.property)⟩
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hl
    have h := Replay210.link_image label x (next F x) false (Cycles210.keeps label x).symm
    refine ⟨?_, Or.inr ⟨label x, ?_⟩⟩
    · simpa only [link, Bool.not_false] using h.1
    · simpa only [link, Bool.not_false] using h.2
theorem unsat {v : Nat} (F : Finset (Clause (Fin v)))
    (hF : ¬Satisfiable (↑F : Set (Clause (Fin v)))) :
    ¬Satisfiable (↑(split F) : Set (Clause (Occ F))) := by
  classical
  rintro ⟨a, hs⟩
  have hnext (x : Occ F) (hx : a x = true) : a (next F x) = true := by
    have hlink : link x ∈ (↑(split F) : Set (Clause (Occ F))) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩))
    obtain ⟨l, hl, hv⟩ := hs (link x) hlink
    change l ∈ ({(x,false),(next F x,true)} : Clause (Occ F)) at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hx] at hv
    · exact hv
  let project (i : Fin v) : Bool := if h : ∃ x : Occ F, label x = i then a h.choose else false
  have project_at (x : Occ F) : project (label x) = a x := by
    have h : ∃ y : Occ F, label y = label x := ⟨x,rfl⟩
    unfold project
    rw [dite_eq_left h]
    exact Cycles210.equal label a hnext h.choose_spec
  apply hF
  refine ⟨project, ?_⟩
  intro C hC
  let old : ↑F := ⟨C,hC⟩
  have mem : copyClause old ∈ (↑(split F) : Set (Clause (Occ F))) :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨old,Finset.mem_univ _,rfl⟩))
  obtain ⟨l, hl, val⟩ := hs (copyClause old) mem
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hl
  refine ⟨m.val,m.property,?_⟩
  exact (project_at ⟨old,m⟩).trans val
end Split210
namespace Split210
open PEqualNP.ProofComplexity
abbrev has {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) (b : Bool)
    (C : Clause (Occ F)) : Prop := (x,b) ∈ C
theorem counts {v : Nat} (F : Finset (Clause (Fin v))) : (by
    classical
    exact ∀ x : Occ F,
      ((split F).filter (has x true)).card + ((split F).filter (has x false)).card ≤ 3) := by
  classical
  intro x
  have base_at (b : Bool) {C : Clause (Occ F)} (h : C ∈ (base F).filter (has x b)) :
      C = copyClause x.1 ∧ sign x = b := by
    obtain ⟨hC, hx⟩ := Finset.mem_filter.mp h
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp (show (x,b) ∈ copyClause C from hx)
    have hx' : (⟨C,l⟩ : Occ F) = x :=
      congrArg (fun p : Literal (Occ F) => p.1) he
    rw [← hx']
    exact ⟨rfl, congrArg (fun p : Literal (Occ F) => p.2) he⟩
  have base_card (b : Bool) : ((base F).filter (has x b)).card ≤ 1 := by
    calc
      _ ≤ ({copyClause x.1} : Finset (Clause (Occ F))).card :=
        Finset.card_le_card fun _ h => Finset.mem_singleton.mpr (base_at b h).1
      _ = 1 := Finset.card_singleton _
  have base_zero (b : Bool) (hb : sign x ≠ b) : ((base F).filter (has x b)).card = 0 := by
    exact Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr
      fun _ h => hb (base_at b h).2)
  have base_sum :
      ((base F).filter (has x true)).card + ((base F).filter (has x false)).card ≤ 1 := by
    cases hx : sign x
    · rw [base_zero true (by simp [hx]), zero_add]
      exact base_card false
    · rw [base_zero false (by simp [hx]), add_zero]
      exact base_card true
  have link_card (b : Bool) : ((links F).filter (has x b)).card ≤ 1 := by
    let source := if b then (next F).symm x else x
    calc
      _ ≤ ({link source} : Finset (Clause (Occ F))).card := by
        apply Finset.card_le_card
        intro C h
        obtain ⟨hC, hx⟩ := Finset.mem_filter.mp h
        obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hC
        change (x,b) ∈ ({(o,false), (next F o,true)} : Clause (Occ F)) at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        apply Finset.mem_singleton.mpr
        rcases hx with hl | hl
        · have hv := congrArg (fun p : Literal (Occ F) => p.1) hl
          have hb := congrArg (fun p : Literal (Occ F) => p.2) hl
          change x = o at hv
          change b = false at hb
          simp [source, hb, hv]
        · have hv := congrArg (fun p : Literal (Occ F) => p.1) hl
          have hb := congrArg (fun p : Literal (Occ F) => p.2) hl
          change x = next F o at hv
          change b = true at hb
          simp [source, hb, hv]
      _ = 1 := Finset.card_singleton _
  have split_le (b : Bool) : ((split F).filter (has x b)).card ≤
      ((base F).filter (has x b)).card + ((links F).filter (has x b)).card := by
    rw [split, Finset.filter_union]
    exact Finset.card_union_le _ _
  have ht := split_le true
  have hf := split_le false
  have hlt := link_card true
  have hlf := link_card false
  omega
end Split210
namespace Core
open PEqualNP.ProofComplexity
open MvPolynomial
variable {V W : Type}
theorem choose_core [DecidableEq V] (F : Finset (Clause V)) (hU : ¬ Satisfiable (↑F : Set (Clause V))) :
    ∃ K ⊆ F, ¬ Satisfiable (↑K : Set (Clause V)) ∧
      ∀ C ∈ K, Satisfiable (↑(K.erase C) : Set (Clause V)) := by
  classical
  revert hU
  refine Finset.strongInductionOn F ?_
  intro J ih hUJ
  by_cases hm : ∃ C ∈ J, ¬ Satisfiable (↑(J.erase C) : Set (Clause V))
  · obtain ⟨C, hC, hcU⟩ := hm
    obtain ⟨K, hK, hu, hmin⟩ := ih (J.erase C) (Finset.erase_ssubset hC) hcU
    exact ⟨K, hK.trans (Finset.erase_subset _ _), hu, hmin⟩
  · refine ⟨J, Finset.Subset.rfl, hUJ, ?_⟩
    intro C hC
    by_contra h
    exact hm ⟨C,hC,h⟩
theorem opposite_used [DecidableEq V] (K : Finset (Clause V)) (hU : ¬ Satisfiable (↑K : Set (Clause V)))
    (hmin : ∀ C ∈ K, Satisfiable (↑(K.erase C) : Set (Clause V))) (x : V) (b : Bool)
    (hb : ∃ C ∈ K, (x,b) ∈ C) : ∃ C ∈ K, (x,!b) ∈ C := by
  classical
  by_contra hn
  obtain ⟨C, hC, hl⟩ := hb
  obtain ⟨a, ha⟩ := hmin C hC
  refine hU ⟨Function.update a x b, ?_⟩
  intro D hD
  change D ∈ K at hD
  by_cases hd : (x,b) ∈ D
  · exact ⟨(x,b), hd, Function.update_self _ _ _⟩
  · have hnot : (x,!b) ∉ D := fun h => hn ⟨D,hD,h⟩
    have dne : D ≠ C := fun h => hd (h ▸ hl)
    obtain ⟨⟨y,s⟩, hys, hy⟩ := ha D (Finset.mem_erase.mpr ⟨dne,hD⟩)
    have hne : y ≠ x := by
      intro he
      subst y
      cases b <;> cases s <;> simp_all
    exact ⟨(y,s), hys, by simpa only [Function.update_of_ne hne] using hy⟩
def literalEmbed (e : W ↪ V) : Literal W ↪ Literal V := e.prodMap (Function.Embedding.refl Bool)
private theorem clause_sat_map (e : W ↪ V) (a : V → Bool) (C : Clause W) :
    ClauseSat a (C.map (literalEmbed e)) ↔ ClauseSat (fun j => a (e j)) C := by
  constructor
  · rintro ⟨l, hl, ha⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨q, hq, ha⟩
  · rintro ⟨l, hl, ha⟩
    exact ⟨literalEmbed e l, Finset.mem_map.mpr ⟨l, hl, rfl⟩, ha⟩
def pullClause [Fintype W] [DecidableEq V] (e : W ↪ V) (C : Clause V) : Clause W :=
  Finset.univ.filter (fun l => literalEmbed e l ∈ C)
private theorem mem_pullClause [Fintype W] [DecidableEq V] (e : W ↪ V) (C : Clause V) (l : Literal W) :
    l ∈ pullClause e C ↔ literalEmbed e l ∈ C := by simp [pullClause]
private theorem map_pullClause [Fintype W] [DecidableEq V] (e : W ↪ V) (C : Clause V)
    (hC : ∀ l ∈ C, ∃ q : Literal W, literalEmbed e q = l) :
    (pullClause e C).map (literalEmbed e) = C := by
  ext l
  constructor
  · intro hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hl
    exact (mem_pullClause e C q).mp hq
  · intro hl
    obtain ⟨q, rfl⟩ := hC l hl
    exact Finset.mem_map.mpr ⟨q, (mem_pullClause e C q).mpr hl, rfl⟩
private theorem rename_clausePoly (e : W ↪ V) (C : Clause W) :
    rename e (clausePoly C) = clausePoly (C.map (literalEmbed e)) := by
  simp only [clausePoly, map_prod, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro l _
  cases h : l.2 <;> simp [h, literalEmbed]
private theorem rename_derivation (e : W ↪ V)
    (F : Set (MvPolynomial W (ZMod 2))) (G : Set (MvPolynomial V (ZMod 2))) (D : ℕ)
    (hax : ∀ p ∈ F, rename e p ∈ G) (p : MvPolynomial W (ZMod 2))
    (hp : PCDerivable F D p) : PCDerivable G D (rename e p) := by
  induction hp with
  | ax hm hd => exact .ax (hax _ hm) ((totalDegree_rename_le _ _).trans hd)
  | zero => simpa only [map_zero] using (PCDerivable.zero (F := G) (B := D))
  | add _ _ ih₁ ih₂ => simpa only [map_add] using PCDerivable.add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [map_mul, rename_X]
    apply PCDerivable.mulX (e j) ih
    simpa only [map_mul, rename_X] using (totalDegree_rename_le e _).trans hd
theorem rename_refutation (e : W ↪ V) (F : Finset (Clause V)) (H : Finset (Clause W))
    (hmap : ∀ C ∈ H, C.map (literalEmbed e) ∈ F) (D : ℕ)
    (hp : PCRefutable (cnfSystem (↑H : Set (Clause W))) D) :
    PCRefutable (cnfSystem (↑F : Set (Clause V))) D := by
  have hax : ∀ p ∈ cnfSystem (↑H : Set (Clause W)),
      rename e p ∈ cnfSystem (↑F : Set (Clause V)) := by
    intro p hp
    rcases hp with ⟨x,rfl⟩ | ⟨C,hC,rfl⟩
    · exact Or.inl ⟨e x, by simp⟩
    · exact Or.inr ⟨C.map (literalEmbed e), hmap C hC, rename_clausePoly e C⟩
  have hh := rename_derivation e _ _ D hax 1 hp
  simpa only [map_one, PCRefutable] using hh
theorem reduce (V : Type) [Fintype V] [DecidableEq V] (w : ℕ) (F : Finset (Clause V))
    (hwidth : ∀ C ∈ F, C.Nonempty ∧ C.card ≤ w)
    (hocc : ∀ x : V, (F.filter (fun C => (x,true) ∈ C)).card +
      (F.filter (fun C => (x,false) ∈ C)).card ≤ 3)
    (hU : ¬ Satisfiable (↑F : Set (Clause V))) :
    ∃ m ≤ Fintype.card V, ∃ H : Finset (Clause (Fin m)),
      (∀ C ∈ H, C.Nonempty ∧ C.card ≤ w) ∧
      (∀ x : Fin m,
        let pos := (H.filter (fun A => (x,true) ∈ A)).card
        let neg := (H.filter (fun A => (x,false) ∈ A)).card
        1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
      ¬ Satisfiable (↑H : Set (Clause (Fin m))) ∧
      (∀ C ∈ H, Satisfiable (↑(H.erase C) : Set (Clause (Fin m)))) ∧
      ∀ D : ℕ, PCRefutable (cnfSystem (↑H : Set (Clause (Fin m)))) D →
        PCRefutable (cnfSystem (↑F : Set (Clause V))) D := by
  classical
  obtain ⟨K,hKF,hKU,hKm⟩ := choose_core F hU
  let S : Finset V := K.biUnion (fun C => C.image Prod.fst)
  let m := S.card
  let e : Fin m ≃ ↥S := S.equivFin.symm
  let emb : Fin m ↪ V := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let H : Finset (Clause (Fin m)) := K.image (pullClause emb)
  have hpre (C : Clause V) (hC : C ∈ K) : (pullClause emb C).map (literalEmbed emb) = C := by
    apply map_pullClause
    intro l hl
    have hv : l.1 ∈ S := Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩
    refine ⟨(e.symm ⟨l.1,hv⟩,l.2), ?_⟩
    exact Prod.ext (congrArg Subtype.val (e.apply_symm_apply _)) rfl
  refine ⟨m, by simpa [m] using Finset.card_le_card (Finset.subset_univ S), H, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨_, hbound⟩ := hwidth A (hKF hA)
    have eqcard : (pullClause emb A).card = A.card :=
      (Finset.card_map _).symm.trans (congrArg Finset.card (hpre A hA))
    refine ⟨Finset.card_pos.mp ?_, eqcard.trans_le hbound⟩
    rw [eqcard]
    exact Finset.card_pos.mpr (hwidth A (hKF hA)).1
  · intro j
    have hj : emb j ∈ S := (e j).property
    obtain ⟨A,hA,hmem⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hmem
    have hl0 : (emb j,l.2) ∈ A := by rw [← he]; simpa using hl
    have all_signs (b : Bool) : ∃ C ∈ K, (emb j,b) ∈ C := by
      by_cases h : b = l.2
      · exact ⟨A,hA,by rwa [h]⟩
      · have heq : b = !l.2 := Bool.eq_not_iff.mpr h
        rw [heq]
        exact opposite_used K hKU hKm (emb j) l.2 ⟨A,hA,hl0⟩
    have hfilter (b : Bool) : H.filter (fun C => (j,b) ∈ C) =
        (K.filter (fun C => (emb j,b) ∈ C)).image (pullClause emb) := by
      ext C
      simp only [H, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨A,hA,rfl⟩,hc⟩
        exact ⟨A, ⟨hA, (mem_pullClause emb A (j,b)).mp hc⟩, rfl⟩
      · rintro ⟨A,⟨hA,ha⟩,rfl⟩
        exact ⟨⟨A,hA,rfl⟩, (mem_pullClause emb A (j,b)).mpr ha⟩
    have lower (b : Bool) : 1 ≤ (H.filter (fun C => (j,b) ∈ C)).card := by
      obtain ⟨A,hA,ha⟩ := all_signs b
      apply Finset.card_pos.mpr
      rw [hfilter]
      exact ⟨pullClause emb A, Finset.mem_image.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,ha⟩,rfl⟩⟩
    have upper (b : Bool) : (H.filter (fun C => (j,b) ∈ C)).card ≤
        (F.filter (fun C => (emb j,b) ∈ C)).card := by
      rw [hfilter]
      apply Finset.card_image_le.trans
      apply Finset.card_le_card
      intro A hA
      obtain ⟨hAK, ha⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hKF hAK,ha⟩
    exact ⟨lower true, lower false, (Nat.add_le_add (upper true) (upper false)).trans (hocc _)⟩
  · rintro ⟨a,ha⟩
    let extend := fun x : V => if hx : x ∈ S then a (e.symm ⟨x,hx⟩) else false
    have agree (j : Fin m) : extend (emb j) = a j := by
      unfold extend
      rw [dite_eq_left (c := emb j ∈ S) (e j).property]
      change a (e.symm (e j)) = a j
      rw [e.symm_apply_apply]
    refine hKU ⟨extend, ?_⟩
    intro C hC
    change C ∈ K at hC
    have hp := ha (pullClause emb C) (Finset.mem_image.mpr ⟨C,hC,rfl⟩)
    rw [← hpre C hC, clause_sat_map]
    simpa only [agree] using hp
  · intro C hC
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨a,ha⟩ := hKm A hA
    refine ⟨fun j => a (emb j), ?_⟩
    intro C hC
    obtain ⟨hneq,hCH⟩ := Finset.mem_erase.mp hC
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hCH
    apply (clause_sat_map emb a _).mp
    rw [hpre B hB]
    exact ha B (Finset.mem_erase.mpr ⟨fun h => hneq (congrArg (pullClause emb) h),hB⟩)
  · intro D hp
    apply rename_refutation emb F H ?_ D hp
    intro C hC
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
    rw [hpre A hA]
    exact hKF hA
end Core
namespace Pad
open PEqualNP.ProofComplexity
def Good (bound : Nat) {m : Nat} (H : Finset (Clause (Fin m))) : Prop :=
  (∀ C ∈ H, C.Nonempty ∧ C.card ≤ bound) ∧
  (∀ x : Fin m,
    let pos := (H.filter (fun C => (x, true) ∈ C)).card
    let neg := (H.filter (fun C => (x, false) ∈ C)).card
    1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
  ¬ Satisfiable (↑H : Set (Clause (Fin m))) ∧
  ∀ C ∈ H, Satisfiable (↑(H.erase C) : Set (Clause (Fin m)))
private def litLift (m : Nat) : Literal (Fin m) ↪ Literal (Fin (m+1)) where
  toFun l := (l.1.castSucc, l.2)
  inj' _ _ e := Prod.ext (Fin.ext (congrArg (fun l => l.1.val) e))
    (congrArg (fun l : Literal (Fin (m+1)) => l.2) e)
private def clLift (m : Nat) : Clause (Fin m) ↪ Clause (Fin (m+1)) where
  toFun C := C.map (litLift m)
  inj' _ _ e := Finset.map_injective (litLift m) e
private def fresh (m : Nat) (b : Bool) : Literal (Fin (m+1)) := (Fin.last m,b)
private theorem old_ne (m : Nat) (l : Literal (Fin m)) (b : Bool) : litLift m l ≠ fresh m b := by
  intro h
  have e : l.1.val = m := congrArg (fun a => a.1.val) h
  have := l.1.isLt
  omega
@[simp] private theorem fresh_not_lift (m : Nat) (C : Clause (Fin m)) (b : Bool) :
    fresh m b ∉ clLift m C := by
  intro h
  obtain ⟨l, _, he⟩ := Finset.mem_map.mp h
  exact old_ne m l b he
@[simp] private theorem old_mem_lift (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) :
    litLift m l ∈ clLift m C ↔ l ∈ C := by
  change litLift m l ∈ C.map (litLift m) ↔ l ∈ C
  simp
private def rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m)) :=
  (H.erase C).map (clLift m)
private def first (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) : Clause (Fin (m+1)) :=
  insert (fresh m l.2) (clLift m (C.erase l))
private def second (m : Nat) (l : Literal (Fin m)) : Clause (Fin (m+1)) :=
  {fresh m (!l.2), litLift m l}
private def padded (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) := insert (first m C l) (insert (second m l) (rest m H C))
@[simp] private theorem old_mem_first (m : Nat) (C : Clause (Fin m)) (l p : Literal (Fin m)) :
    litLift m p ∈ first m C l ↔ p ∈ C.erase l := by
  simp [first, old_ne]
@[simp] private theorem old_mem_second (m : Nat) (l p : Literal (Fin m)) :
    litLift m p ∈ second m l ↔ p = l := by
  simp [second, old_ne]
@[simp] private theorem fresh_mem_first (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) (b : Bool) :
    fresh m b ∈ first m C l ↔ b = l.2 := by
  simp only [first, Finset.mem_insert, fresh_not_lift, or_false]
  simp [fresh]
@[simp] private theorem fresh_mem_second (m : Nat) (l : Literal (Fin m)) (b : Bool) :
    fresh m b ∈ second m l ↔ b = !l.2 := by
  have hn := (old_ne m l b).symm
  simp only [second, Finset.mem_insert, Finset.mem_singleton, hn, or_false]
  simp [fresh]
private theorem sign_ne_neg : ∀ b : Bool, b ≠ !b := by decide
private theorem first_ne_second (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) :
    first m C l ≠ second m l := by
  intro e
  have hm : fresh m l.2 ∈ first m C l := (fresh_mem_first ..).mpr rfl
  rw [e, fresh_mem_second] at hm
  exact sign_ne_neg _ hm
private theorem first_not_rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) : first m C l ∉ rest m H C := by
  intro hm
  obtain ⟨A, _, he⟩ := Finset.mem_map.mp hm
  exact fresh_not_lift m A l.2 (he.symm ▸ (fresh_mem_first m C l l.2).mpr rfl)
private theorem second_not_rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) : second m l ∉ rest m H C := by
  intro hm
  obtain ⟨A, _, he⟩ := Finset.mem_map.mp hm
  exact fresh_not_lift m A (!l.2) (he.symm ▸ (fresh_mem_second m l (!l.2)).mpr rfl)
private def restrict (m : Nat) (a : Fin (m+1) → Bool) : Fin m → Bool := fun x => a x.castSucc
private def extend (m : Nat) (a : Fin m → Bool) (b : Bool) : Fin (m+1) → Bool := Fin.lastCases b a
@[simp] private theorem restrict_extend (m : Nat) (a : Fin m → Bool) (b : Bool) :
    restrict m (extend m a b) = a := by
  funext x
  simp [restrict, extend]
@[simp] private theorem extend_last (m : Nat) (a : Fin m → Bool) (b : Bool) :
    extend m a b (Fin.last m) = b := by simp [extend]
private theorem sat_lift (m : Nat) (a : Fin (m+1) → Bool) (C : Clause (Fin m)) :
    ClauseSat a (clLift m C) ↔ ClauseSat (restrict m a) C := by
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨p,hp,he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨litLift m l, Finset.mem_map.mpr ⟨l,hl,rfl⟩, he⟩
private theorem sat_first (m : Nat) (a : Fin (m+1) → Bool) (C : Clause (Fin m)) (l : Literal (Fin m)) :
    ClauseSat a (first m C l) ↔ a (Fin.last m) = l.2 ∨ ClauseSat (restrict m a) (C.erase l) := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h] at he
      exact Or.inl he
    · exact Or.inr ((sat_lift m a _).mp ⟨p,h,he⟩)
  · rintro (h | h)
    · exact ⟨fresh m l.2, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨p,hp,he⟩ := (sat_lift m a _).mpr h
      exact ⟨p,Finset.mem_insert_of_mem hp,he⟩
private theorem sat_second (m : Nat) (a : Fin (m+1) → Bool) (l : Literal (Fin m)) :
    ClauseSat a (second m l) ↔ a (Fin.last m) = !l.2 ∨ restrict m a l.1 = l.2 := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h] at he
      exact Or.inl he
    · rw [Finset.mem_singleton.mp h] at he
      exact Or.inr he
  · rintro (h | h)
    · exact ⟨fresh m (!l.2), Finset.mem_insert_self _ _, h⟩
    · exact ⟨litLift m l, by simp [second], h⟩
private theorem sat_merge {m : Nat} (a : Fin (m+1) → Bool) (C : Clause (Fin m))
    (l : Literal (Fin m)) (hl : l ∈ C) (h1 : ClauseSat a (first m C l))
    (h2 : ClauseSat a (second m l)) : ClauseSat (restrict m a) C := by
  rcases (sat_first m a C l).mp h1 with e | ⟨p,hp,hq⟩
  · rcases (sat_second m a l).mp h2 with f | f
    · have hbad : l.2 = !l.2 := e.symm.trans f
      exact (sign_ne_neg _ hbad).elim
    · exact ⟨l,hl,f⟩
  · exact ⟨p, (Finset.mem_erase.mp hp).2, hq⟩
private theorem sat_split {m : Nat} (a : Fin m → Bool) (C : Clause (Fin m))
    (l : Literal (Fin m)) (hs : ClauseSat a C) :
    ClauseSat (extend m a (a l.1)) (first m C l) ∧
      ClauseSat (extend m a (a l.1)) (second m l) := by
  constructor
  · apply (sat_first m _ C l).mpr
    obtain ⟨p,hp,he⟩ := hs
    by_cases e : p = l
    · subst p
      exact Or.inl (by simpa using he)
    · exact Or.inr (by rw [restrict_extend]; exact ⟨p,Finset.mem_erase.mpr ⟨e,hp⟩,he⟩)
  · apply (sat_second m _ l).mpr
    rw [extend_last, restrict_extend]
    cases l.2 <;> cases a l.1 <;> simp
private theorem mem_padded (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) (B : Clause (Fin (m+1))) :
    B ∈ padded m H C l ↔ B = first m C l ∨ B = second m l ∨
      ∃ A ∈ H.erase C, clLift m A = B := by
  simp only [padded, rest, Finset.mem_insert, Finset.mem_map]
private theorem padded_unsat {m : Nat} (H : Finset (Clause (Fin m)))
    (C : Clause (Fin m)) (l : Literal (Fin m)) (hl : l ∈ C)
    (hus : ¬ Satisfiable (↑H : Set (Clause (Fin m)))) :
    ¬ Satisfiable (↑(padded m H C l) : Set (Clause (Fin (m+1)))) := by
  intro ⟨a,ha⟩
  apply hus
  refine ⟨restrict m a, ?_⟩
  intro B hB
  by_cases e : B = C
  · subst B
    apply sat_merge a C l hl
    · exact ha _ ((mem_padded ..).mpr (Or.inl rfl))
    · exact ha _ ((mem_padded ..).mpr (Or.inr (Or.inl rfl)))
  · exact (sat_lift m a B).mp (ha _ ((mem_padded ..).mpr
      (Or.inr (Or.inr ⟨B,Finset.mem_erase.mpr ⟨e,hB⟩,rfl⟩))))
private theorem padded_min {m : Nat} (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (hC : C ∈ H) (l : Literal (Fin m))
    (hmin : ∀ A ∈ H, Satisfiable (↑(H.erase A) : Set (Clause (Fin m)))) :
    ∀ B ∈ padded m H C l, Satisfiable (↑((padded m H C l).erase B) : Set (Clause (Fin (m+1)))) := by
  intro B hB
  rcases (mem_padded m H C l B).mp hB with h₁ | h₂ | ⟨A,hA,h₃⟩
  · subst B
    obtain ⟨a,ha⟩ := hmin C hC
    refine ⟨extend m a (!l.2), ?_⟩
    intro X hX
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hX
    rcases (mem_padded m H C l X).mp hmem with e | e | ⟨D,hD,e⟩
    · exact (hne e).elim
    · subst X
      exact (sat_second m _ l).mpr (Or.inl (extend_last ..))
    · subst X
      apply (sat_lift m _ D).mpr
      rw [restrict_extend]
      exact ha D hD
  · subst B
    obtain ⟨a,ha⟩ := hmin C hC
    refine ⟨extend m a l.2, ?_⟩
    intro X hX
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hX
    rcases (mem_padded m H C l X).mp hmem with e | e | ⟨D,hD,e⟩
    · subst X
      exact (sat_first m _ C l).mpr (Or.inl (extend_last ..))
    · exact (hne e).elim
    · subst X
      apply (sat_lift m _ D).mpr
      rw [restrict_extend]
      exact ha D hD
  · subst B
    have hAC := (Finset.mem_erase.mp hA).1
    obtain ⟨a,ha⟩ := hmin A (Finset.mem_erase.mp hA).2
    have hs := sat_split a C l (ha C (Finset.mem_erase.mpr ⟨Ne.symm hAC,hC⟩))
    refine ⟨extend m a (a l.1), ?_⟩
    intro X hX
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hX
    rcases (mem_padded m H C l X).mp hmem with e | e | ⟨D,hD,e⟩
    · subst X
      exact hs.1
    · subst X
      exact hs.2
    · subst X
      have hDA : D ≠ A := fun e => hne (congrArg (clLift m) e)
      apply (sat_lift m _ D).mpr
      rw [restrict_extend]
      exact ha D (Finset.mem_erase.mpr ⟨hDA,(Finset.mem_erase.mp hD).2⟩)
private def occ {V : Type} [DecidableEq V] (H : Finset (Clause V)) (l : Literal V) : Nat :=
  (H.filter (fun B => l ∈ B)).card
private theorem occ_insert {V : Type} [DecidableEq V] (H : Finset (Clause V))
    (B : Clause V) (l : Literal V) (hB : B ∉ H) :
    occ (insert B H) l = occ H l + if l ∈ B then 1 else 0 := by
  by_cases h : l ∈ B
  · have H' : B ∉ H.filter (fun A => l ∈ A) := fun hb => hB (Finset.mem_filter.mp hb).1
    simp [occ, Finset.filter_insert, h, Finset.card_insert_of_notMem H']
  · simp [occ, Finset.filter_insert, h]
private theorem occ_rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (p : Literal (Fin m)) : occ (rest m H C) (litLift m p) = occ (H.erase C) p := by
  unfold occ
  have h : (rest m H C).filter (fun A => litLift m p ∈ A) =
      ((H.erase C).filter (fun A => p ∈ A)).map (clLift m) := by
    ext A
    constructor
    · intro hA
      obtain ⟨hB, hmem⟩ := Finset.mem_filter.mp hA
      obtain ⟨B,hB',rfl⟩ := Finset.mem_map.mp hB
      exact Finset.mem_map.mpr ⟨B, Finset.mem_filter.mpr ⟨hB', (old_mem_lift m B p).mp hmem⟩, rfl⟩
    · intro hA
      obtain ⟨B,hB,rfl⟩ := Finset.mem_map.mp hA
      obtain ⟨hB', hmem⟩ := Finset.mem_filter.mp hB
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨B,hB',rfl⟩, (old_mem_lift m B p).mpr hmem⟩
  rw [h, Finset.card_map]
private theorem occ_old (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m)) (hC : C ∈ H)
    (l : Literal (Fin m)) (hl : l ∈ C) (p : Literal (Fin m)) :
    occ (padded m H C l) (litLift m p) = occ H p := by
  have hh : occ H p = occ (H.erase C) p + if p ∈ C then 1 else 0 := by
    conv_lhs => rw [← Finset.insert_erase hC]
    exact occ_insert _ _ _ (Finset.notMem_erase _ _)
  rw [padded, occ_insert _ _ _ (by simp [first_ne_second, first_not_rest]),
    occ_insert _ _ _ (second_not_rest m H C l), occ_rest, hh]
  simp only [old_mem_first, old_mem_second, Finset.mem_erase]
  by_cases h : p = l
  · subst p
    simp [hl]
  · by_cases hc : p ∈ C <;> simp [h,hc]
private theorem occ_fresh (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) (b : Bool) : occ (padded m H C l) (fresh m b) = 1 := by
  have e : occ (rest m H C) (fresh m b) = 0 := by
    unfold occ
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    obtain ⟨hB,hm⟩ := Finset.mem_filter.mp hA
    obtain ⟨B,_,rfl⟩ := Finset.mem_map.mp hB
    exact fresh_not_lift m B b hm
  rw [padded, occ_insert _ _ _ (by simp [first_ne_second, first_not_rest]),
    occ_insert _ _ _ (second_not_rest m H C l), e]
  simp only [fresh_mem_first, fresh_mem_second]
  cases b <;> cases l.2 <;> decide
private theorem padded_good (bound m : Nat) (h₂ : 2 ≤ bound) (H : Finset (Clause (Fin m)))
    (hH : Good bound H) (C : Clause (Fin m)) (hC : C ∈ H) (l : Literal (Fin m)) (hl : l ∈ C) :
    Good bound (padded m H C l) := by
  rcases hH with ⟨hw,hs,hu,hm⟩
  refine ⟨?_, ?_, padded_unsat H C l hl hu, padded_min H C hC l hm⟩
  · intro B hB
    rcases (mem_padded m H C l B).mp hB with rfl | rfl | ⟨A,hA,rfl⟩
    · refine ⟨⟨fresh m l.2, by simp [first]⟩, ?_⟩
      rw [first, Finset.card_insert_of_notMem (fresh_not_lift m (C.erase l) l.2)]
      change ((C.erase l).map (litLift m)).card + 1 ≤ bound
      rw [Finset.card_map, Finset.card_erase_of_mem hl]
      have hp := Finset.card_pos.mpr (hw C hC).1
      have hc := (hw C hC).2
      omega
    · refine ⟨⟨fresh m (!l.2), by simp [second]⟩, ?_⟩
      exact ((Finset.card_insert_le _ _).trans (show ({litLift m l} : Clause (Fin (m+1))).card + 1 ≤ 2 by simp)).trans h₂
    · obtain ⟨hne,hca⟩ := hw A (Finset.mem_erase.mp hA).2
      obtain ⟨p,hp⟩ := hne
      refine ⟨⟨litLift m p, (old_mem_lift m A p).mpr hp⟩, ?_⟩
      change (A.map (litLift m)).card ≤ bound
      simpa using hca
  · intro x
    refine Fin.lastCases ?_ (fun y => ?_) x
    · change 1 ≤ occ (padded m H C l) (fresh m true) ∧
        1 ≤ occ (padded m H C l) (fresh m false) ∧
          occ (padded m H C l) (fresh m true) + occ (padded m H C l) (fresh m false) ≤ 3
      rw [occ_fresh, occ_fresh]
      decide
    · change 1 ≤ occ (padded m H C l) (litLift m (y,true)) ∧
        1 ≤ occ (padded m H C l) (litLift m (y,false)) ∧
          occ (padded m H C l) (litLift m (y,true)) + occ (padded m H C l) (litLift m (y,false)) ≤ 3
      rw [occ_old m H C hC l hl, occ_old m H C hC l hl]
      exact hs y
private def project (m : Nat) (l : Literal (Fin m)) : Fin (m+1) → Fin m := Fin.lastCases l.1 id
@[simp] private theorem project_old (m : Nat) (l p : Literal (Fin m)) :
    Replay210.litMap (project m l) (litLift m p) = p := by
  change (Fin.lastCases l.1 id p.1.castSucc, p.2) = p
  simp
@[simp] private theorem project_fresh (m : Nat) (l : Literal (Fin m)) (b : Bool) :
    Replay210.litMap (project m l) (fresh m b) = (l.1,b) := by
  change (Fin.lastCases l.1 id (Fin.last m), b) = (l.1,b)
  simp
private theorem project_lift_inj (m : Nat) (l : Literal (Fin m)) (C : Clause (Fin m)) :
    Set.InjOn (Replay210.litMap (project m l)) (↑(clLift m C) : Set (Literal (Fin (m+1)))) := by
  intro a ha b hb h
  obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hb
  simpa only [project_old] using congrArg (litLift m) h
private theorem project_lift_image (m : Nat) (l : Literal (Fin m)) (C : Clause (Fin m)) :
    (clLift m C).image (Replay210.litMap (project m l)) = C := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    rw [project_old] at he
    exact he ▸ hq
  · intro hx
    exact Finset.mem_image.mpr ⟨litLift m x, Finset.mem_map.mpr ⟨x,hx,rfl⟩, project_old m l x⟩
private theorem project_first (m : Nat) (l : Literal (Fin m)) (C : Clause (Fin m)) (hl : l ∈ C) :
    Set.InjOn (Replay210.litMap (project m l)) (↑(first m C l) : Set (Literal (Fin (m+1)))) ∧
      (first m C l).image (Replay210.litMap (project m l)) = C := by
  constructor
  · intro a ha b hb h
    have ha' := Finset.mem_insert.mp ha
    have hb' := Finset.mem_insert.mp hb
    rcases ha' with rfl | ha'
    · rcases hb' with rfl | hb'
      · rfl
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hb'
        rw [project_fresh,project_old] at h
        exact ((Finset.mem_erase.mp hq).1 h.symm).elim
    · rcases hb' with rfl | hb'
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp ha'
        rw [project_fresh,project_old] at h
        exact ((Finset.mem_erase.mp hq).1 h).elim
      · exact project_lift_inj m l (C.erase l) ha' hb' h
  · rw [first, Finset.image_insert, project_fresh, project_lift_image, Finset.insert_erase hl]
private theorem project_second (m : Nat) (l : Literal (Fin m)) :
    Set.InjOn (Replay210.litMap (project m l)) (↑(second m l) : Set (Literal (Fin (m+1)))) ∧
      ∃ x : Fin m, (second m l).image (Replay210.litMap (project m l)) = {(x,true),(x,false)} := by
  have hxy : project m l (Fin.last m) = project m l l.1.castSucc := by simp [project]
  have h := Replay210.link_image (project m l) (Fin.last m) l.1.castSucc (!l.2) hxy
  dsimp only at h
  rw [Bool.not_not] at h
  exact ⟨h.1,_,h.2⟩
theorem pad_one (bound m : Nat) (h₂ : 2 ≤ bound) (H : Finset (Clause (Fin m))) (hH : Good bound H) :
    ∃ K : Finset (Clause (Fin (m+1))), Good bound K ∧ ∃ f : Fin (m+1) → Fin m,
      ∀ A ∈ K, Set.InjOn (Replay210.litMap f) (↑A : Set (Literal (Fin (m+1)))) ∧
        (A.image (Replay210.litMap f) ∈ H ∨ ∃ x : Fin m,
          A.image (Replay210.litMap f) = {(x,true),(x,false)}) := by
  classical
  have hn : H.Nonempty := by
    by_contra h
    apply hH.2.2.1
    exact ⟨fun _ => false, fun C hC => (h ⟨C,hC⟩).elim⟩
  obtain ⟨C,hC⟩ := hn
  obtain ⟨l,hl⟩ := (hH.1 C hC).1
  refine ⟨padded m H C l, padded_good bound m h₂ H hH C hC l hl, project m l, ?_⟩
  intro A hA
  rcases (mem_padded m H C l A).mp hA with rfl | rfl | ⟨B,hB,rfl⟩
  · have hh := project_first m l C hl
    exact ⟨hh.1,Or.inl (hh.2.symm ▸ hC)⟩
  · have hh := project_second m l
    exact ⟨hh.1,Or.inr hh.2⟩
  · exact ⟨project_lift_inj m l B,Or.inl (by rw [project_lift_image]; exact (Finset.mem_erase.mp hB).2)⟩
theorem pad_to (bound m n : Nat) (h₂ : 2 ≤ bound) (hn : m ≤ n)
    (H : Finset (Clause (Fin m))) (hH : Good bound H) :
    ∃ K : Finset (Clause (Fin n)), Good bound K ∧
      ∀ D : Nat, PCRefutable (cnfSystem (↑K : Set (Clause (Fin n)))) D →
        PCRefutable (cnfSystem (↑H : Set (Clause (Fin m)))) D := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction q with
  | zero => exact ⟨H,hH,fun _ h => h⟩
  | succ q ih =>
    obtain ⟨L,hL,transfer⟩ := ih (Nat.le_add_right _ _)
    obtain ⟨K,hK,f,image⟩ := pad_one bound (m+q) h₂ L hL
    exact ⟨K,hK,fun D h => transfer D (Replay210.refutable f _ _ image h)⟩
end Pad
namespace Exact210
open PEqualNP.ProofComplexity
theorem result :
∀ (v w : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin v))),
  (∀ C ∈ F, C.Nonempty ∧ C.card ≤ w) →
  ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin v))) →
  ∀ n : ℕ, F.sum (fun A₀ => A₀.card) ≤ n →
    ∃ H : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
      (∀ C ∈ H, C.Nonempty ∧ C.card ≤ max 2 w) ∧
      (∀ x : Fin n,
        let pos := (H.filter (fun A => (x, true) ∈ A)).card
        let neg := (H.filter (fun E => (x, false) ∈ E)).card
        1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
      ¬ PEqualNP.ProofComplexity.Satisfiable (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
      (∀ C ∈ H, PEqualNP.ProofComplexity.Satisfiable
        (↑(H.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) ∧
      ∀ D : ℕ,
        PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) D →
        PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin v)))) D := by
  classical
  intro v w F small unsat n le_n
  let S := Split210.split F
  obtain ⟨m, hm, H, hw, ho, hu, hmin, core⟩ :=
    Core.reduce (Split210.Occ F) (max 2 w) S
      (Split210.width F small) (by
        intro x
        refine (le_of_eq ?_).trans (Split210.counts F x)
        apply congrArg₂ Nat.add <;> apply congrArg Finset.card <;> ext C <;>
          simp only [Finset.mem_filter, Split210.has, S]) (Split210.unsat F unsat)
  have hmn : m ≤ n := hm.trans ((Split210.card_occ F).symm ▸ le_n)
  have good : Pad.Good (max 2 w) H := ⟨hw, ho, hu, hmin⟩
  obtain ⟨K, hK, replay⟩ := Pad.pad_to (max 2 w) m n (le_max_left _ _) hmn H good
  exact ⟨K, hK.1, hK.2.1, hK.2.2.1, hK.2.2.2, fun d h => Split210.replay F (core d (replay d h))⟩
end Exact210
end P210

namespace Glue211
open PEqualNP.ProofComplexity PEqualNP.Expanders
open Classical in
noncomputable def code3 {V : Type} (F : Set (Clause V)) (w : ℕ) (C : ↥F) :
    ℕ → Clause (V ⊕ (↥F × Fin (w + 1)))
  | 0 => {(Sum.inr (C, PEqualNP.ProofComplexity.Helpers.ThreeCnf.idx w 0), true)}
  | i + 1 =>
    match C.1.toList[i]? with
    | some l => {(Sum.inr (C, PEqualNP.ProofComplexity.Helpers.ThreeCnf.idx w i), false),
        (Sum.inl l.1, l.2), (Sum.inr (C, PEqualNP.ProofComplexity.Helpers.ThreeCnf.idx w (i + 1)), true)}
    | none => {(Sum.inr (C, PEqualNP.ProofComplexity.Helpers.ThreeCnf.idx w C.1.card), false)}
theorem to3_sub_range {V : Type} (F : Set (Clause V)) (w : ℕ) (hw : ∀ C ∈ F, C.card ≤ w) :
    PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3 F w ⊆
      Set.range (fun p : ↥F × Fin (w + 2) => code3 F w p.1 p.2.val) := by
  rintro K ⟨C, rfl | ⟨i, l, hl, rfl⟩ | rfl⟩
  · exact ⟨(C, ⟨0, by omega⟩), rfl⟩
  · have hi : i < C.1.card := by
      have h1 := (List.getElem?_eq_some_iff.mp hl).1
      simpa using h1
    have hC := hw C.1 C.2
    refine ⟨(C, ⟨i + 1, by omega⟩), ?_⟩
    simp only [code3, hl]
  · have hC := hw C.1 C.2
    refine ⟨(C, ⟨C.1.card + 1, by omega⟩), ?_⟩
    have hnone : C.1.toList[C.1.card]? = none := by
      rw [List.getElem?_eq_none_iff]
      simp
    simp only [code3, hnone]
theorem to3_finset {V : Type} (F : Set (Clause V)) [Fintype ↥F] (w : ℕ)
    (hw : ∀ C ∈ F, C.card ≤ w) :
    ∃ S : Finset (Clause (V ⊕ (↥F × Fin (w + 1)))),
      (↑S : Set (Clause (V ⊕ (↥F × Fin (w + 1))))) =
        PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3 F w ∧
      S.card ≤ Fintype.card ↥F * (w + 2) := by
  classical
  have hfin : (PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3 F w).Finite :=
    (Set.finite_range _).subset (to3_sub_range F w hw)
  refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
  calc hfin.toFinset.card
      ≤ (Finset.univ.image (fun p : ↥F × Fin (w + 2) => code3 F w p.1 p.2.val)).card := by
        apply Finset.card_le_card
        intro K hK
        obtain ⟨p, hp⟩ := to3_sub_range F w hw (hfin.mem_toFinset.mp hK)
        exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩
    _ ≤ (Finset.univ : Finset (↥F × Fin (w + 2))).card := Finset.card_image_le
    _ = Fintype.card ↥F * (w + 2) := by simp [Finset.card_univ, Fintype.card_prod]
open Classical in
theorem to3_nonempty {V : Type} (F : Set (Clause V)) (w : ℕ) :
    ∀ K ∈ PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3 F w, K.Nonempty := by
  rintro K ⟨C, rfl | ⟨i, l, -, rfl⟩ | rfl⟩
  · exact Finset.singleton_nonempty _
  · exact Finset.insert_nonempty _ _
  · exact Finset.singleton_nonempty _
theorem rename_fin {V : Type} [Fintype V] [DecidableEq V] (S : Finset (Clause V))
    (hS : ∀ K ∈ S, K.Nonempty ∧ K.card ≤ 3) (hU : ¬ Satisfiable (↑S : Set (Clause V))) :
    ∃ F1 : Finset (Clause (Fin (Fintype.card V))),
      (∀ C ∈ F1, C.Nonempty ∧ C.card ≤ 3) ∧
      ¬ Satisfiable (↑F1 : Set (Clause (Fin (Fintype.card V)))) ∧
      F1.sum (fun A₀ => A₀.card) ≤ S.sum (fun A₀ => A₀.card) ∧
      ∀ D : ℕ, PCRefutable (cnfSystem (↑F1 : Set (Clause (Fin (Fintype.card V))))) D →
        PCRefutable (cnfSystem (↑S : Set (Clause V))) D := by
  classical
  let e' : V ↪ Fin (Fintype.card V) := (Fintype.equivFin V).toEmbedding
  let e : Fin (Fintype.card V) ↪ V := (Fintype.equivFin V).symm.toEmbedding
  have hid : ∀ l : Literal V, P210.Core.literalEmbed e (P210.Core.literalEmbed e' l) = l := by
    rintro ⟨x, b⟩
    simp [P210.Core.literalEmbed, e, e', Prod.map_apply, Function.Embedding.refl_apply,
      Equiv.symm_apply_apply]
  have hback : ∀ K : Clause V,
      (K.map (P210.Core.literalEmbed e')).map (P210.Core.literalEmbed e) = K := by
    intro K
    ext l
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      rw [hid]
      exact ha
    · intro hl
      exact ⟨P210.Core.literalEmbed e' l, ⟨l, hl, rfl⟩, hid l⟩
  refine ⟨S.image (fun K => K.map (P210.Core.literalEmbed e')), ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨(hS K hK).1.map, by rw [Finset.card_map]; exact (hS K hK).2⟩
  · rintro ⟨a, ha⟩
    apply hU
    refine ⟨fun v => a (e' v), fun K hK => ?_⟩
    obtain ⟨l, hl, hal⟩ :=
      ha _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hK)))
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨q, hq, hal⟩
  · rw [Finset.sum_image (fun x _ y _ h => Finset.map_injective _ h)]
    simp only [Finset.card_map, le_refl]
  · intro D hD
    refine P210.Core.rename_refutation e S _ ?_ D hD
    intro C hC
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hC
    rw [hback]
    exact hK
theorem family : ∃ Q n₁ : ℕ, 1 ≤ Q ∧ ∀ n : ℕ, n₁ ≤ n →
    ∃ H : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
      ((∀ C ∈ H, C.Nonempty ∧ C.card ≤ 3) ∧
      (∀ x : Fin n,
        let pos := (H.filter (fun A => (x, true) ∈ A)).card
        let neg := (H.filter (fun E => (x, false) ∈ E)).card
        1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
      ¬ PEqualNP.ProofComplexity.Satisfiable (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
      (∀ C ∈ H, PEqualNP.ProofComplexity.Satisfiable
        (↑(H.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n))))) ∧
      ∃ D : ℕ, 1 ≤ D ∧ n ≤ Q * D ∧
        ¬ PCRefutable (cnfSystem (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) D := by
  classical
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = max b 2 := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 4 * s₀ * w := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hs₀) (by omega)
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 3 * (w + 2) * (1 + w * w) := ⟨_, rfl⟩
  have hApos : 0 < A := by
    rw [hA]
    positivity
  refine ⟨4 * A * K, 2 * A * (n₀ + K + 2 * ((4 * w + 2) * s₀) + 1), ?_, ?_⟩
  · have : 0 < 4 * A * K := by positivity
    omega
  intro n hn
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = n / (2 * A) := ⟨_, rfl⟩
  have hNbig : n₀ + K + 2 * ((4 * w + 2) * s₀) + 1 ≤ N := by
    rw [hN, Nat.le_div_iff_mul_le (by omega)]
    rw [mul_comm]
    exact hn
  obtain ⟨G, hLd, hR, hE⟩ := hG N (by omega)
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = N / K := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by
    rw [hD, Nat.le_div_iff_mul_le hKpos]
    omega
  have hDK : D * K ≤ N := by
    rw [hD]
    exact Nat.div_mul_le_self N K
  have hdeg : 2 * (w * D + 2 * w + 1) ≤ N / s₀ := by
    rw [Nat.le_div_iff_mul_le hs₀]
    have h1 : 4 * (s₀ * w * D) ≤ N := by
      calc 4 * (s₀ * w * D) = D * K := by rw [hK]; ring
        _ ≤ N := hDK
    have e : 2 * (w * D + 2 * w + 1) * s₀ = 2 * (s₀ * w * D) + (4 * w + 2) * s₀ := by ring
    rw [e]
    omega
  have hnr := PEqualNP.ProofComplexity.L046 (N + 1) N G (N / s₀) (w * D + 2 * w) hE hdeg
  have hwid : ∀ C ∈ graphPHP G, C.card ≤ w :=
    fun C hC => le_trans (PEqualNP.ProofComplexity.PhpFinal.graphPHP_width G b hLd C hC) hw.symm.le
  have hnr3 : ¬ PCRefutable (cnfSystem (PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3 (graphPHP G) w)) D :=
    PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3_pc_lower (graphPHP G) w D (by omega) hwid hnr
  have hun3 : ¬ Satisfiable (PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3 (graphPHP G) w) :=
    PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3_unsat _ _
      (PEqualNP.ProofComplexity.ThreeCnfFamily.graphPHP_unsat G (Nat.lt_succ_self N))
  have instF : Fintype ↥(graphPHP G) := Fintype.ofFinite _
  obtain ⟨S, hS, hScard⟩ := to3_finset (graphPHP G) w hwid
  have hFcard : Fintype.card ↥(graphPHP G) ≤ (N + 1) + (N + 1) * b * b :=
    PEqualNP.ProofComplexity.ThreeCnfFamily.card_graphPHP_le G b hLd hR
  have hS3 : ∀ K ∈ S, K.Nonempty ∧ K.card ≤ 3 := by
    intro K hK
    have hK' : K ∈ (↑S : Set (Clause (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))))) :=
      Finset.mem_coe.mpr hK
    rw [hS] at hK'
    exact ⟨to3_nonempty _ _ K hK', PEqualNP.ProofComplexity.Helpers.ThreeCnf.to3_width _ _ K hK'⟩
  have hSun : ¬ Satisfiable (↑S : Set (Clause (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))))) := by
    rw [hS]
    exact hun3
  have hsum : S.sum (fun A₀ => A₀.card) ≤ 3 * S.card := by
    calc S.sum (fun A₀ => A₀.card) ≤ S.sum (fun _ => 3) :=
          Finset.sum_le_sum (fun K hK => (hS3 K hK).2)
      _ = 3 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hocc : S.sum (fun A₀ => A₀.card) ≤ n := by
    have h1 : S.card ≤ ((N + 1) + (N + 1) * b * b) * (w + 2) :=
      le_trans hScard (Nat.mul_le_mul_right _ hFcard)
    have hbb : b * b ≤ w * w := Nat.mul_le_mul hbw hbw
    have h2 : ((N + 1) + (N + 1) * b * b) * (w + 2) ≤ (N + 1) * (1 + w * w) * (w + 2) := by
      apply Nat.mul_le_mul_right
      calc (N + 1) + (N + 1) * b * b = (N + 1) * (1 + b * b) := by ring
        _ ≤ (N + 1) * (1 + w * w) := Nat.mul_le_mul_left _ (by omega)
    have h3 : N * (2 * A) ≤ n := by
      rw [hN]
      exact Nat.div_mul_le_self n (2 * A)
    have h4 : 3 * ((N + 1) * (1 + w * w) * (w + 2)) = A * (N + 1) := by
      rw [hA]
      ring
    have h5 : A * (N + 1) ≤ N * (2 * A) := by
      have h6 : A * 1 ≤ A * N := Nat.mul_le_mul_left A (by omega)
      nlinarith
    calc S.sum (fun A₀ => A₀.card) ≤ 3 * S.card := hsum
      _ ≤ 3 * ((N + 1) * (1 + w * w) * (w + 2)) := Nat.mul_le_mul_left 3 (h1.trans h2)
      _ = A * (N + 1) := h4
      _ ≤ N * (2 * A) := h5
      _ ≤ n := h3
  obtain ⟨F1, hF1, hU1, hsum1, hpc1⟩ := rename_fin S hS3 hSun
  obtain ⟨H, h1, h2, h3, h4, h5⟩ :=
    P210.Exact210.result _ 3 F1 hF1 hU1 n (hsum1.trans hocc)
  refine ⟨H, ⟨fun C hC => ⟨(h1 C hC).1, le_trans (h1 C hC).2 (by norm_num)⟩, h2, h3, h4⟩,
    D, hD1, ?_, ?_⟩
  · have e1 : n < 2 * A * (N + 1) := by
      rw [hN]
      exact Nat.lt_mul_div_succ n (by omega)
    have e2 : N < K * (D + 1) := by
      rw [hD]
      exact Nat.lt_mul_div_succ N hKpos
    have e4 : 2 * A * (N + 1) ≤ 2 * A * (K * (D + 1)) := Nat.mul_le_mul_left _ e2
    have e5 : K * (D + 1) ≤ K * (2 * D) := Nat.mul_le_mul_left _ (by omega)
    have e7 : 2 * A * (K * (D + 1)) ≤ 2 * A * (K * (2 * D)) := Nat.mul_le_mul_left _ e5
    have e6 : 2 * A * (K * (2 * D)) = 4 * A * K * D := by ring
    calc n ≤ 2 * A * (N + 1) := e1.le
      _ ≤ 2 * A * (K * (D + 1)) := e4
      _ ≤ 2 * A * (K * (2 * D)) := e7
      _ = 4 * A * K * D := e6
  · intro hH
    apply hnr3
    rw [← hS]
    exact hpc1 D (h5 D hH)
theorem arith (Q n D k S : ℕ) (hQ : 1 ≤ Q) (hn : (16 * Q) ^ 4 ≤ n) (hD : n ≤ Q * D)
    (hk : 1 ≤ k) (hB : ((8 * Q) ^ 4) ^ k ≤ n) :
    16 * k ≤ D ∧ 12 ≤ D ∧
    (Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k) ≤ (S : ℝ) →
      2 ^ (Nat.sqrt n) ≤ S) := by
  obtain ⟨t, ht⟩ : ∃ t, t = (8 * Q) ^ k := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  have ht4 : t ^ 4 ≤ n := by
    rw [ht, ← pow_mul, mul_comm k 4, pow_mul]
    exact hB
  have hss : s * s ≤ n := by
    rw [hs]
    exact Nat.sqrt_le n
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Nat.sqrt_pos.mpr hn1
  have hkey : 16 * Q * t * s ≤ n := by
    have h4 : (16 * Q * t * s) ^ 4 ≤ n ^ 4 := by
      calc (16 * Q * t * s) ^ 4 = (16 * Q) ^ 4 * t ^ 4 * ((s * s) * (s * s)) := by ring
        _ ≤ n * n * (n * n) := by gcongr
        _ = n ^ 4 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp h4
  have hk2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hkt : k ≤ t := by
    calc k ≤ 2 ^ k := hk2
      _ ≤ (8 * Q) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = t := ht.symm
  have hQt : 16 * Q * k ≤ n := by
    have : 16 * Q * k ≤ 16 * Q * t * s := by
      calc 16 * Q * k ≤ 16 * Q * t := Nat.mul_le_mul_left _ hkt
        _ = 16 * Q * t * 1 := (mul_one _).symm
        _ ≤ 16 * Q * t * s := Nat.mul_le_mul_left _ hs1
    exact this.trans hkey
  have hD16 : 16 * k ≤ D := by
    have : Q * (16 * k) ≤ Q * D := by
      calc Q * (16 * k) = 16 * Q * k := by ring
        _ ≤ n := hQt
        _ ≤ Q * D := hD
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hD12 : 12 ≤ D := by
    have h12 : Q * 12 ≤ n := by
      have : 16 * Q ≤ (16 * Q) ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    exact Nat.le_of_mul_le_mul_left (h12.trans hD) (by omega)
  refine ⟨hD16, hD12, fun hS => ?_⟩
  have hk4 : k * (4 * Q) ^ k ≤ t := by
    calc k * (4 * Q) ^ k ≤ 2 ^ k * (4 * Q) ^ k := Nat.mul_le_mul_right _ hk2
      _ = (2 * (4 * Q)) ^ k := (mul_pow _ _ _).symm
      _ = (8 * Q) ^ k := by ring
      _ = t := ht.symm
  have hnat : s * (16 * Q * (k * (4 * Q) ^ k)) ≤ n := by
    calc s * (16 * Q * (k * (4 * Q) ^ k)) ≤ s * (16 * Q * t) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk4)
      _ = 16 * Q * t * s := by ring
      _ ≤ n := hkey
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hDR : (n : ℝ) ≤ Q * D := by exact_mod_cast hD
  have hnatR : (s : ℝ) * (16 * Q * (k * (4 * Q) ^ k)) ≤ n := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < 16 * Q * (k * (4 * Q) ^ k) := by positivity
  have hx : (s : ℝ) ≤ (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k := by
    have e1 : (s : ℝ) ≤ (n : ℝ) / (16 * Q * (k * (4 * Q) ^ k)) := by
      rw [le_div_iff₀ hpos]
      exact hnatR
    have e2 : (n : ℝ) / (16 * Q * (k * (4 * Q) ^ k)) =
        ((n : ℝ) / (16 * k * Q)) * (1 / (4 * Q)) ^ k := by
      rw [one_div_pow, div_mul_div_comm, mul_one]
      congr 1
      ring
    have e3 : (n : ℝ) / (16 * k * Q) ≤ (D : ℝ) / (16 * k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hDR (le_of_lt (by positivity : (0 : ℝ) < 16 * k))]
    have e4 : (1 / (4 * (Q : ℝ))) ≤ (D : ℝ) / (4 * n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e5 : (1 / (4 * (Q : ℝ))) ^ k ≤ ((D : ℝ) / (4 * n)) ^ k :=
      pow_le_pow_left₀ (by positivity) e4 k
    calc (s : ℝ) ≤ (n : ℝ) / (16 * Q * (k * (4 * Q) ^ k)) := e1
      _ = ((n : ℝ) / (16 * k * Q)) * (1 / (4 * Q)) ^ k := e2
      _ ≤ (D : ℝ) / (16 * k) * ((D : ℝ) / (4 * n)) ^ k :=
          mul_le_mul e3 e5 (by positivity) (by positivity)
  have h2e : (2 : ℝ) ^ s ≤ Real.exp s := by
    have h21 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ s ≤ (Real.exp 1) ^ s := pow_le_pow_left₀ (by norm_num) h21 s
      _ = Real.exp s := by rw [← Real.exp_nat_mul, mul_one]
  have hfinal : ((2 ^ s : ℕ) : ℝ) ≤ (S : ℝ) := by
    push_cast
    calc (2 : ℝ) ^ s ≤ Real.exp s := h2e
      _ ≤ Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k) :=
          Real.exp_le_exp.mpr hx
      _ ≤ S := hS
  rw [← hs]
  exact_mod_cast hfinal
theorem main : ∃ B n₀ : ℕ, 2 ≤ B ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ H : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
    (∀ C ∈ H, C.Nonempty ∧ C.card ≤ 3) ∧
    (∀ x : Fin n,
      let pos := (H.filter (fun A => (x, true) ∈ A)).card
      let neg := (H.filter (fun E => (x, false) ∈ E)).card
      1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
    ¬ PEqualNP.ProofComplexity.Satisfiable (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
    (∀ C ∈ H, PEqualNP.ProofComplexity.Satisfiable
      (↑(H.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) ∧
    ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (Fin n))),
      1 ≤ k → B ^ k ≤ n →
      PEqualNP.ProofComplexity.IsLinKRefutation k (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π →
      2 ^ (Nat.sqrt n) ≤ π.length := by
  obtain ⟨Q, n₁, hQ, hfam⟩ := family
  refine ⟨(8 * Q) ^ 4, max n₁ ((16 * Q) ^ 4), ?_, ?_⟩
  · calc 2 ≤ 8 * Q := by omega
      _ ≤ (8 * Q) ^ 4 := Nat.le_self_pow (by norm_num) _
  · intro n hn
    obtain ⟨H, ⟨h1, h2, h3, h4⟩, D, hD1, hnD, hnr⟩ := hfam n (le_trans (le_max_left _ _) hn)
    refine ⟨H, h1, h2, h3, h4, ?_⟩
    intro k π hk hB hπ
    obtain ⟨h16, h12, hfin⟩ :=
      arith Q n D k π.length hQ (le_trans (le_max_right _ _) hn) hnD hk hB
    apply hfin
    have hgen := PEqualNP.ProofComplexity.LinKAsm.degree_to_size_k
      PEqualNP.ProofComplexity.LinKSim.simulation_refutation
      PEqualNP.ProofComplexity.DegSizeArithK.final_of_assembly_plan
    have hb := hgen (Fin n) (↑H) π k 3 D (fun A hA => (h1 A hA).2) hk h16 (by omega) hnr hπ
    rw [Fintype.card_fin] at hb
    exact hb
end Glue211

end PEqualNP.Outside.L_pcx_211_aux

theorem PEqualNP.Outside.L_pcx_211 : ∃ B n₀ : ℕ, 2 ≤ B ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ H : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
    (∀ C ∈ H, C.Nonempty ∧ C.card ≤ 3) ∧
    (∀ x : Fin n,
      let pos := (H.filter (fun A => (x, true) ∈ A)).card
      let neg := (H.filter (fun E => (x, false) ∈ E)).card
      1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
    ¬ PEqualNP.ProofComplexity.Satisfiable (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
    (∀ C ∈ H, PEqualNP.ProofComplexity.Satisfiable
      (↑(H.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) ∧
    ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (Fin n))),
      1 ≤ k → B ^ k ≤ n →
      PEqualNP.ProofComplexity.IsLinKRefutation k (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π →
      2 ^ (Nat.sqrt n) ≤ π.length :=
  PEqualNP.Outside.L_pcx_211_aux.Glue211.main
