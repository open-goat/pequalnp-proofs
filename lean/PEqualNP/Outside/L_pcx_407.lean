import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_407_aux

namespace InlinePC

namespace Helpers

open PEqualNP.ProofComplexity

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

section

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

end

end Helpers


theorem L043_inline : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

theorem L049_inline : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB

end InlinePC


open PEqualNP.Expanders PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

noncomputable section

section BoolZ2AndSyndrome

def boolToZ2 (b : Bool) : ZMod 2 := (b.toNat : ZMod 2)

def z2ToBool (a : ZMod 2) : Bool := decide (a = 1)

lemma z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases z2_cases a with rfl | rfl <;> decide

lemma z2_mul_self (a : ZMod 2) : a * a = a := by
  rcases z2_cases a with rfl | rfl <;> decide

lemma boolToZ2_z2ToBool (a : ZMod 2) : boolToZ2 (z2ToBool a) = a := by
  rcases z2_cases a with rfl | rfl <;> decide

lemma z2ToBool_boolToZ2 (b : Bool) : z2ToBool (boolToZ2 b) = b := by
  cases b <;> decide

lemma boolToZ2_not (b : Bool) : boolToZ2 (!b) = boolToZ2 b + 1 := by
  cases b <;> decide

lemma boolToZ2_injective : Function.Injective boolToZ2 := by
  intro a b h
  have := congrArg z2ToBool h
  rwa [z2ToBool_boolToZ2, z2ToBool_boolToZ2] at this

lemma boolToZ2_mod2 (l : List Bool) :
    boolToZ2 (decide (l.count true % 2 = 0)) = 1 + (l.map boolToZ2).sum := by
  induction l with
  | nil => decide
  | cons b tl ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons]
    cases b
    · simp only [boolToZ2, Bool.toNat_false, Nat.cast_zero, zero_add]
      exact ih
    · simp only [beq_self_eq_true, ↓reduceIte, boolToZ2, Bool.toNat_true, Nat.cast_one]
      have hpar : decide ((tl.count true + 1) % 2 = 0) = !decide (tl.count true % 2 = 0) := by
        have hmod : tl.count true % 2 = 0 ∨ tl.count true % 2 = 1 := by omega
        rcases hmod with h0 | h1
        · have : (tl.count true + 1) % 2 = 1 := by omega
          simp [h0, this]
        · have : (tl.count true + 1) % 2 = 0 := by omega
          simp [h1, this]
      rw [hpar, show ((!(decide (tl.count true % 2 = 0))).toNat : ZMod 2) =
          boolToZ2 (!decide (tl.count true % 2 = 0)) from rfl, boolToZ2_not, ih]
      ring

open Classical

def xToZ2 {V : Type} (x : V → Bool) : V → ZMod 2 := fun v => boolToZ2 (x v)

def z2ToX {V : Type} (z : V → ZMod 2) : V → Bool := fun v => z2ToBool (z v)

lemma z2ToX_xToZ2 {V : Type} (x : V → Bool) : z2ToX (xToZ2 x) = x := by
  funext v
  exact z2ToBool_boolToZ2 (x v)

lemma xToZ2_z2ToX {V : Type} (z : V → ZMod 2) : xToZ2 (z2ToX z) = z := by
  funext v
  exact boolToZ2_z2ToBool (z v)

lemma xToZ2_update {V : Type} [DecidableEq V] (x : V → Bool) (v : V) :
    xToZ2 (Function.update x v (!(x v))) = xToZ2 x + (fun u => if u = v then (1 : ZMod 2) else 0) := by
  funext u
  by_cases huv : u = v
  · subst huv
    simp [xToZ2, boolToZ2_not]
  · simp [xToZ2, huv]

lemma z2ToX_add_unit {V : Type} [DecidableEq V] (z : V → ZMod 2) (v : V) :
    z2ToX (z + fun u => if u = v then (1 : ZMod 2) else 0) =
      Function.update (z2ToX z) v (!(z2ToX z v)) := by
  have h1 := xToZ2_update (z2ToX z) v
  rw [xToZ2_z2ToX] at h1
  have h2 := congrArg z2ToX h1.symm
  rwa [z2ToX_xToZ2] at h2

abbrev Aff (V : Type) : Type := (V → ZMod 2) × ZMod 2

def evalAff {V : Type} [Fintype V] (ℓ : Aff V) (z : V → ZMod 2) : ZMod 2 :=
  (∑ v : V, ℓ.1 v * z v) + ℓ.2

def affLin {V : Type} [Fintype V] (ℓ : Aff V) : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun z := ∑ v : V, ℓ.1 v * z v
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => by ring

lemma evalAff_eq_zero_iff {V : Type} [Fintype V] (ℓ : Aff V) (z : V → ZMod 2) :
    evalAff ℓ z = 0 ↔ affLin ℓ z = ℓ.2 := by
  constructor
  · intro h
    have h1 : affLin ℓ z + ℓ.2 = 0 := h
    have h2 : affLin ℓ z = affLin ℓ z + (ℓ.2 + ℓ.2) := by rw [z2_add_self, add_zero]
    rw [← add_assoc, h1, zero_add] at h2
    exact h2
  · intro h
    change affLin ℓ z + ℓ.2 = 0
    rw [h, z2_add_self]

lemma evalAff_single {V : Type} [Fintype V] [DecidableEq V] (v : V) (c : ZMod 2) (z : V → ZMod 2) :
    evalAff (Pi.single v (1 : ZMod 2), c) z = z v + c := by
  unfold evalAff
  congr 1
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ huv; simp [Pi.single_eq_of_ne huv]
  · intro h; exact absurd (Finset.mem_univ v) h

lemma powerset_sum_pow {V : Type*} [DecidableEq V] (P : Finset V) (R : ℝ) :
    ∑ D ∈ P.powerset, R ^ D.card = (R + 1) ^ P.card := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert a P ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union, Finset.card_insert_of_notMem ha, pow_succ']
    · rw [Finset.sum_image]
      · have h2 : (∑ D ∈ P.powerset, R ^ (insert a D).card) = R * ∑ D ∈ P.powerset, R ^ D.card := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun D hD => ?_
          have hna : a ∉ D := fun h => ha (Finset.mem_powerset.mp hD h)
          rw [Finset.card_insert_of_notMem hna, pow_succ']
        rw [h2, ih]
        ring
      · intro D₁ hD₁ D₂ hD₂ heq
        have h1 : a ∉ D₁ := fun h => ha (Finset.mem_powerset.mp hD₁ h)
        have h2 : a ∉ D₂ := fun h => ha (Finset.mem_powerset.mp hD₂ h)
        ext x
        by_cases hx : x = a
        · subst hx; simp [h1, h2]
        · have := Finset.ext_iff.mp heq x
          simpa [hx] using this
    · rw [Finset.disjoint_left]
      intro s hs1 hs2
      obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hs2
      exact ha (Finset.mem_powerset.mp hs1 (Finset.mem_insert_self a D))

lemma smooth_flip_set {V : Type} [DecidableEq V] (R : ℕ) (μ : (V → ZMod 2) → ℝ)
    (hμsm : ∀ z v, μ z ≤ (R : ℝ) * μ (z + fun u => if u = v then (1 : ZMod 2) else 0))
    (D : Finset V) (z : V → ZMod 2) :
    μ (z + fun u => if u ∈ D then (1 : ZMod 2) else 0) ≤ (R : ℝ) ^ D.card * μ z := by
  induction D using Finset.induction_on with
  | empty =>
    have h0 : (z + fun _ => (0 : ZMod 2)) = z := by funext u; simp
    simp [h0]
  | insert a D ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ']
    have hsplit : (z + fun u => if u ∈ insert a D then (1 : ZMod 2) else 0) +
        (fun u => if u = a then (1 : ZMod 2) else 0) =
        z + fun u => if u ∈ D then (1 : ZMod 2) else 0 := by
      funext u
      by_cases hua : u = a
      · subst hua
        simp [ha, add_assoc, z2_add_self]
      · simp [hua]
    have hstep := hμsm (z + fun u => if u ∈ insert a D then (1 : ZMod 2) else 0) a
    rw [hsplit] at hstep
    exact hstep.trans ((mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg R)).trans (by rw [mul_assoc]))

lemma exists_pivot_set {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}
    (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H) :
    ∃ P : Finset V, P.card = r ∧
      Function.Bijective (fun d : (P → ZMod 2) => H (fun v => if hv : v ∈ P then d ⟨v, hv⟩ else 0)) := by
  let u : V → (Fin r → ZMod 2) := fun v => H (Pi.single v (1 : ZMod 2))
  have hspan_top : Submodule.span (ZMod 2) (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := hH y
    have hz : z = ∑ v : V, z v • Pi.single v (1 : ZMod 2) := by
      funext w
      simp [Finset.sum_apply, Pi.single_apply]
    change H z ∈ Submodule.span (ZMod 2) (Set.range u)
    rw [hz, map_sum]
    refine Submodule.sum_mem _ fun v _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  have hstep : ∀ k : ℕ, k ≤ r →
      ∃ P : Finset V, P.card = k ∧
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (u '' (P : Set V))) = k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, rfl, ?_⟩
      simp
    | succ k ih =>
      intro hk
      obtain ⟨P, hPcard, hPfr⟩ := ih (by omega)
      have hne_top : Submodule.span (ZMod 2) (u '' (P : Set V)) ≠ ⊤ := by
        intro htop
        rw [htop, finrank_top, Module.finrank_pi, Fintype.card_fin] at hPfr
        omega
      have hex_v : ∃ v : V, u v ∉ Submodule.span (ZMod 2) (u '' (P : Set V)) := by
        by_contra hall
        push Not at hall
        apply hne_top
        rw [eq_top_iff, ← hspan_top]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨v, rfl⟩
        exact hall v
      obtain ⟨v, hv⟩ := hex_v
      have hvnotP : v ∉ P := fun hmem => hv (Submodule.subset_span ⟨v, hmem, rfl⟩)
      refine ⟨insert v P, by rw [Finset.card_insert_of_notMem hvnotP, hPcard], ?_⟩
      have himg : u '' ((insert v P : Finset V) : Set V) = insert (u v) (u '' (P : Set V)) := by
        simp [Set.image_insert_eq]
      rw [himg, Submodule.span_insert]
      have hdisj : Disjoint (Submodule.span (ZMod 2) {u v}) (Submodule.span (ZMod 2) (u '' (P : Set V))) := by
        rw [Submodule.disjoint_def]
        intro x hx1 hx2
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
        rcases z2_cases c with rfl | rfl
        · simp
        · simp only [one_smul] at hx2
          exact absurd hx2 hv
      have hu_ne : u v ≠ 0 := fun h0 => hv (h0 ▸ Submodule.zero_mem _)
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (Submodule.span (ZMod 2) {u v}) (Submodule.span (ZMod 2) (u '' (P : Set V)))
      rw [hdisj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hu_ne, hPfr] at hsup
      omega
  obtain ⟨P, hPcard, hPfr⟩ := hstep r le_rfl
  let Ψ : (P → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := fun d => H (fun v => if hv : v ∈ P then d ⟨v, hv⟩ else 0)
      map_add' := fun d₁ d₂ => by
        rw [← map_add]
        congr 1
        funext v
        by_cases hv : v ∈ P <;> simp [hv]
      map_smul' := fun c d => by
        simp only [RingHom.id_apply, ← map_smul]
        congr 1
        funext v
        by_cases hv : v ∈ P <;> simp [hv] }
  have hrange : LinearMap.range Ψ = Submodule.span (ZMod 2) (u '' (P : Set V)) := by
    apply le_antisymm
    · rintro _ ⟨d, rfl⟩
      have hd : (fun v => if hv : v ∈ P then d ⟨v, hv⟩ else 0) =
          ∑ v ∈ P.attach, d v • Pi.single v.1 (1 : ZMod 2) := by
        funext w
        by_cases hw : w ∈ P
        · rw [dite_eq_left hw, Finset.sum_apply, Finset.sum_eq_single ⟨w, hw⟩]
          · simp
          · intro b _ hne
            have hne1 : w ≠ b.1 := fun h => hne (Subtype.ext h.symm)
            simp [Pi.single_eq_of_ne hne1]
          · intro h; exact absurd (Finset.mem_attach P ⟨w, hw⟩) h
        · rw [dite_eq_right hw, Finset.sum_apply]
          symm
          refine Finset.sum_eq_zero fun b _ => ?_
          have hne1 : w ≠ b.1 := fun h => hw (h ▸ b.2)
          simp [Pi.single_eq_of_ne hne1]
      change H (fun v => if hv : v ∈ P then d ⟨v, hv⟩ else 0) ∈ _
      rw [hd, map_sum]
      refine Submodule.sum_mem _ fun v _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v.1, v.2, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      have hvP : v ∈ P := Finset.mem_coe.mp hv
      refine ⟨fun w => if w.1 = v then 1 else 0, ?_⟩
      change H (fun w => if hw : w ∈ P then (if w = v then 1 else 0) else 0) = H (Pi.single v 1)
      congr 1
      funext w
      by_cases hwv : w = v
      · subst hwv; simp [hvP]
      · by_cases hw : w ∈ P <;> simp [hw, hwv]
  have htop : LinearMap.range Ψ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange, hPfr, Module.finrank_pi, Fintype.card_fin]
  have hsurj : Function.Surjective Ψ := LinearMap.range_eq_top.mp htop
  have hfr_eq : Module.finrank (ZMod 2) (P → ZMod 2) = Module.finrank (ZMod 2) (Fin r → ZMod 2) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, hPcard, Fintype.card_fin]
  have hinj : Function.Injective Ψ := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
    rw [htop, finrank_top] at hrn
    have hker0 : Module.finrank (ZMod 2) (LinearMap.ker Ψ) = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)
  exact ⟨P, hPcard, ⟨hinj, hsurj⟩⟩

lemma syndrome_mass_ineq {V : Type} [Fintype V] [DecidableEq V] {r : ℕ} (R : ℕ)
    (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (y : Fin r → ZMod 2) (μ : (V → ZMod 2) → ℝ)
    (hμ0 : ∀ z, 0 ≤ μ z)
    (hμsm : ∀ z v, μ z ≤ (R : ℝ) * μ (z + fun u => if u = v then (1 : ZMod 2) else 0)) :
    (∑ z : V → ZMod 2, μ z) ≤
      ((R + 1 : ℕ) : ℝ) ^ r * ∑ z ∈ Finset.univ.filter (fun z => H z = y), μ z := by
  obtain ⟨P, hPcard, hPbij⟩ := exists_pivot_set H hH
  let fiber := Finset.univ.filter (fun z : V → ZMod 2 => H z = y)
  let Φ : (V → ZMod 2) × Finset V → (V → ZMod 2) :=
    fun p => p.1 + fun v => if v ∈ p.2 then (1 : ZMod 2) else 0
  have hcover : (Finset.univ : Finset (V → ZMod 2)) ⊆ (fiber ×ˢ P.powerset).image Φ := by
    intro w _
    obtain ⟨d, hd⟩ := hPbij.2 (y + H w)
    let D : Finset V := P.filter (fun v => ∃ hv : v ∈ P, d ⟨v, hv⟩ = 1)
    have hDP : D ⊆ P := Finset.filter_subset _ _
    have hD_eq : (fun v => if v ∈ D then (1 : ZMod 2) else 0) =
        (fun v => if hv : v ∈ P then d ⟨v, hv⟩ else 0) := by
      funext v
      by_cases hv : v ∈ P
      · rw [dite_eq_left hv]
        rcases z2_cases (d ⟨v, hv⟩) with h0 | h1
        · have hvD : v ∉ D := by simp [D, hv, h0]
          simp [hvD, h0]
        · have hvD : v ∈ D := by simp [D, hv, h1]
          simp [hvD, h1]
      · have hvD : v ∉ D := fun h => hv (hDP h)
        simp [hv, hvD]
    let z : V → ZMod 2 := w + fun v => if v ∈ D then (1 : ZMod 2) else 0
    have hz_fib : z ∈ fiber := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change H (w + fun v => if v ∈ D then 1 else 0) = y
      dsimp only at hd
      rw [map_add, hD_eq, hd]
      funext j
      simp [Pi.add_apply, add_comm (y j), ← add_assoc, z2_add_self]
    refine Finset.mem_image.mpr ⟨(z, D), Finset.mem_product.mpr ⟨hz_fib, Finset.mem_powerset.mpr hDP⟩, ?_⟩
    funext v
    change (w v + (if v ∈ D then 1 else 0)) + (if v ∈ D then 1 else 0) = w v
    rw [add_assoc, z2_add_self, add_zero]
  calc (∑ z : V → ZMod 2, μ z)
      ≤ ∑ z ∈ (fiber ×ˢ P.powerset).image Φ, μ z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun z _ _ => hμ0 z)
    _ ≤ ∑ p ∈ fiber ×ˢ P.powerset, μ (Φ p) :=
        Finset.sum_image_le_of_nonneg (fun z _ => hμ0 z)
    _ = ∑ z ∈ fiber, ∑ D ∈ P.powerset, μ (z + fun v => if v ∈ D then (1 : ZMod 2) else 0) :=
        Finset.sum_product _ _ _
    _ ≤ ∑ z ∈ fiber, ∑ D ∈ P.powerset, (R : ℝ) ^ D.card * μ z :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun D _ => smooth_flip_set R μ hμsm D z
    _ = ∑ z ∈ fiber, (∑ D ∈ P.powerset, (R : ℝ) ^ D.card) * μ z := by
        refine Finset.sum_congr rfl fun z _ => (Finset.sum_mul _ _ _).symm
    _ = ((R + 1 : ℕ) : ℝ) ^ r * ∑ z ∈ fiber, μ z := by
        rw [← Finset.mul_sum, powerset_sum_pow, hPcard]
        push_cast
        rfl

lemma syndrome_mass_bound {V : Type} [Fintype V] [DecidableEq V]
    (R h : ℕ) (hR : 1 ≤ R)
    (μ : (V → Bool) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμpos : 0 < ∑ x, μ x)
    (hμsm : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v))))
    (bad : Finset (V → Bool))
    (hacc : (2 : ℝ) ^ h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x)
    (eqs : List (Aff V)) (x₀ : V → Bool)
    (hx₀ : ∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x₀) = 0)
    (hsub : ∀ x : V → Bool, (∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x) = 0) → x ∈ bad) :
    h ≤ Nat.clog 2 (R + 1) * eqs.length := by
  let Lmap : (V → ZMod 2) →ₗ[ZMod 2] (Fin eqs.length → ZMod 2) :=
    LinearMap.pi (fun i => affLin (eqs.get i))
  let Im := LinearMap.range Lmap
  let r := Module.finrank (ZMod 2) Im
  have hr_le : r ≤ eqs.length := by
    calc r ≤ Module.finrank (ZMod 2) (Fin eqs.length → ZMod 2) := Submodule.finrank_le Im
      _ = eqs.length := by rw [Module.finrank_pi, Fintype.card_fin]
  let eIm : Im ≃ₗ[ZMod 2] (Fin r → ZMod 2) := (Module.finBasis (ZMod 2) Im).equivFun
  let Hsurj : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    eIm.toLinearMap.comp Lmap.rangeRestrict
  have hHsurj : Function.Surjective Hsurj :=
    eIm.surjective.comp Lmap.surjective_rangeRestrict
  let μ' : (V → ZMod 2) → ℝ := fun z => μ (z2ToX z)
  have hsum_eq : (∑ z : V → ZMod 2, μ' z) = ∑ x : V → Bool, μ x := by
    refine Finset.sum_bij (fun z _ => z2ToX z)
      (fun _ _ => Finset.mem_univ _)
      (fun z₁ _ z₂ _ heq => by
        have := congrArg xToZ2 heq
        rwa [xToZ2_z2ToX, xToZ2_z2ToX] at this)
      (fun x _ => ⟨xToZ2 x, Finset.mem_univ _, z2ToX_xToZ2 x⟩)
      (fun _ _ => rfl)
  have hμ'sm : ∀ z v, μ' z ≤ (R : ℝ) * μ' (z + fun u => if u = v then (1 : ZMod 2) else 0) := by
    intro z v
    simp only [μ', z2ToX_add_unit]
    exact hμsm (z2ToX z) v
  let y₀ := Hsurj (xToZ2 x₀)
  have hmass := syndrome_mass_ineq R Hsurj hHsurj y₀ μ' (fun z => hμ0 (z2ToX z)) hμ'sm
  let fiber := Finset.univ.filter (fun z : V → ZMod 2 => Hsurj z = y₀)
  have hfib_le_bad : (∑ z ∈ fiber, μ' z) ≤ ∑ x ∈ bad, μ x := by
    have hbij : (∑ z ∈ fiber, μ' z) = ∑ x ∈ fiber.image z2ToX, μ x := by
      rw [Finset.sum_image]
      intro z₁ _ z₂ _ heq
      have := congrArg xToZ2 heq
      rwa [xToZ2_z2ToX, xToZ2_z2ToX] at this
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hμ0 x)
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hHz : Hsurj z = y₀ := (Finset.mem_filter.mp hz).2
    have hLz : Lmap z = Lmap (xToZ2 x₀) := by
      have h1 : Lmap.rangeRestrict z = Lmap.rangeRestrict (xToZ2 x₀) := eIm.injective hHz
      exact congrArg Subtype.val h1
    apply hsub
    intro ℓ hℓ
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hℓ
    rw [xToZ2_z2ToX, evalAff_eq_zero_iff]
    have hi : Lmap z i = Lmap (xToZ2 x₀) i := congrFun hLz i
    have h0 := (evalAff_eq_zero_iff (eqs.get i) (xToZ2 x₀)).mp (hx₀ (eqs.get i) (List.get_mem eqs i))
    exact hi.trans h0
  have htotal_le : (∑ x : V → Bool, μ x) ≤ ((R + 1 : ℕ) : ℝ) ^ r * ∑ x ∈ bad, μ x := by
    rw [← hsum_eq]
    exact hmass.trans (mul_le_mul_of_nonneg_left hfib_le_bad (by positivity))
  have hbad_pos : 0 < ∑ x ∈ bad, μ x := by
    by_contra hle0
    push Not at hle0
    have h0 : ∑ x ∈ bad, μ x = 0 := le_antisymm hle0 (Finset.sum_nonneg fun x _ => hμ0 x)
    rw [h0, mul_zero] at htotal_le
    linarith
  have hpow_le : (2 : ℝ) ^ h ≤ ((R + 1 : ℕ) : ℝ) ^ r := by
    have h1 : (2 : ℝ) ^ h * (∑ x ∈ bad, μ x) ≤ ((R + 1 : ℕ) : ℝ) ^ r * (∑ x ∈ bad, μ x) :=
      hacc.trans htotal_le
    exact le_of_mul_le_mul_right h1 hbad_pos
  have hclog : R + 1 ≤ 2 ^ Nat.clog 2 (R + 1) := Nat.le_pow_clog (by omega) (R + 1)
  have hpow_le2 : (2 : ℝ) ^ h ≤ (2 : ℝ) ^ (Nat.clog 2 (R + 1) * r) := by
    calc (2 : ℝ) ^ h ≤ ((R + 1 : ℕ) : ℝ) ^ r := hpow_le
      _ ≤ ((2 ^ Nat.clog 2 (R + 1) : ℕ) : ℝ) ^ r := by
          gcongr
      _ = (2 : ℝ) ^ (Nat.clog 2 (R + 1) * r) := by
          push_cast
          rw [← pow_mul]
  have hnat : 2 ^ h ≤ 2 ^ (Nat.clog 2 (R + 1) * r) := by exact_mod_cast hpow_le2
  have hle_r : h ≤ Nat.clog 2 (R + 1) * r := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hnat
  exact hle_r.trans (Nat.mul_le_mul_left _ hr_le)

end BoolZ2AndSyndrome

open Classical

section LinearCoords

lemma exists_inj_coords {b : ℕ} (U : Submodule (ZMod 2) (Fin b → ZMod 2)) :
    ∃ J : Finset (Fin b), J.card ≤ Module.finrank (ZMod 2) U ∧
      ∀ u ∈ U, (∀ j ∈ J, u j = 0) → u = 0 := by
  suffices ∀ k : ℕ, ∀ U : Submodule (ZMod 2) (Fin b → ZMod 2),
      Module.finrank (ZMod 2) U ≤ k →
      ∃ J : Finset (Fin b), J.card ≤ k ∧ ∀ u ∈ U, (∀ j ∈ J, u j = 0) → u = 0 by
    exact this (Module.finrank (ZMod 2) U) U le_rfl
  intro k
  induction k with
  | zero =>
    intro U hU
    have hbot : U = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hU)
    refine ⟨∅, by simp, fun u hu _ => ?_⟩
    rwa [hbot, Submodule.mem_bot] at hu
  | succ k ih =>
    intro U hU
    by_cases hbot : U = ⊥
    · refine ⟨∅, by simp, fun u hu _ => ?_⟩
      rwa [hbot, Submodule.mem_bot] at hu
    · have hex : ∃ u ∈ U, u ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [Submodule.eq_bot_iff]
        exact hall
      obtain ⟨u₀, hu₀U, hu₀ne⟩ := hex
      have hexj : ∃ j : Fin b, u₀ j ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hu₀ne
        funext j
        exact hall j
      obtain ⟨j₀, hj₀⟩ := hexj
      let proj : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj j₀
      let U' : Submodule (ZMod 2) (Fin b → ZMod 2) := U ⊓ LinearMap.ker proj
      have hU'le : Module.finrank (ZMod 2) U' ≤ k := by
        have hrn := LinearMap.finrank_range_add_finrank_ker (proj.domRestrict U)
        have hrange_pos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (proj.domRestrict U)) := by
          have hne : LinearMap.range (proj.domRestrict U) ≠ ⊥ := by
            intro hrb
            have hmem : proj u₀ ∈ LinearMap.range (proj.domRestrict U) := ⟨⟨u₀, hu₀U⟩, rfl⟩
            rw [hrb, Submodule.mem_bot] at hmem
            exact hj₀ hmem
          have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range (proj.domRestrict U)) := by
            by_contra h0
            have h0' : Module.finrank (ZMod 2) (LinearMap.range (proj.domRestrict U)) = 0 := by omega
            exact hne (Submodule.finrank_eq_zero.mp h0')
          omega
        have hker_eq : Module.finrank (ZMod 2) (LinearMap.ker (proj.domRestrict U)) =
            Module.finrank (ZMod 2) U' := by
          let e : LinearMap.ker (proj.domRestrict U) ≃ₗ[ZMod 2] U' :=
            { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
              invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact e.finrank_eq
        omega
      obtain ⟨J', hJ'card, hJ'inj⟩ := ih U' hU'le
      refine ⟨insert j₀ J', (Finset.card_insert_le _ _).trans (by omega), fun u huU hzero => ?_⟩
      have huU' : u ∈ U' := ⟨huU, hzero j₀ (Finset.mem_insert_self _ _)⟩
      exact hJ'inj u huU' (fun j hj => hzero j (Finset.mem_insert_of_mem hj))

lemma flat_bddAbove {b : ℕ} (S : Finset (Fin b → ZMod 2)) :
    BddAbove {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
      Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S} := by
  refine ⟨b, ?_⟩
  rintro k ⟨U, _, rfl, _⟩
  calc Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (Fin b → ZMod 2) := Submodule.finrank_le U
    _ = b := by rw [Module.finrank_pi, Fintype.card_fin]

lemma flat_ge_of_affine {b : ℕ} (S : Finset (Fin b → ZMod 2))
    (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2)
    (hU : ∀ u ∈ U, y + u ∈ S) :
    Module.finrank (ZMod 2) U ≤
      sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
        Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S} :=
  le_csSup (flat_bddAbove S) ⟨U, y, rfl, hU⟩

lemma exists_flat_witness {b : ℕ} (S : Finset (Fin b → ZMod 2)) (hS : S.Nonempty) :
    ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
      Module.finrank (ZMod 2) U =
        sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
          Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S} ∧
      ∀ u ∈ U, y + u ∈ S := by
  obtain ⟨y₀, hy₀⟩ := hS
  have hne : {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
      Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}.Nonempty := by
    refine ⟨0, ⊥, y₀, finrank_bot _ _, fun u hu => ?_⟩
    rw [(Submodule.mem_bot (ZMod 2)).mp hu, add_zero]
    exact hy₀
  exact Nat.sSup_mem hne (flat_bddAbove S)

end LinearCoords

section PCHelpers

open MvPolynomial

def affPoly {V : Type} [Fintype V] (ℓ : Aff V) : MvPolynomial V (ZMod 2) :=
  (∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v) + MvPolynomial.C ℓ.2

lemma affPoly_eval {V : Type} [Fintype V] (ℓ : Aff V) (z : V → ZMod 2) :
    MvPolynomial.eval z (affPoly ℓ) = evalAff ℓ z := by
  simp [affPoly, evalAff, map_add, map_sum, map_mul]

lemma totalDegree_sum_le {V : Type} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial V (ZMod 2)) (d : ℕ) (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma affPoly_totalDegree_le {V : Type} [Fintype V] (ℓ : Aff V) :
    (affPoly ℓ).totalDegree ≤ 1 := by
  unfold affPoly
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine totalDegree_sum_le Finset.univ _ 1 fun v _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · simp [MvPolynomial.totalDegree_C]

lemma affPoly_flip {V : Type} [Fintype V] (ℓ : Aff V) :
    affPoly (ℓ.1, ℓ.2 + 1) = 1 + affPoly ℓ := by
  unfold affPoly
  rw [map_add, map_one]
  ring

lemma pc_mono {V : Type} {F₁ F₂ : Set (MvPolynomial V (ZMod 2))} {B₁ B₂ : ℕ}
    (hF : F₁ ⊆ F₂) (hB : B₁ ≤ B₂) {p : MvPolynomial V (ZMod 2)}
    (hp : PCDerivable F₁ B₁ p) : PCDerivable F₂ B₂ p := by
  induction hp with
  | ax h hdeg => exact PCDerivable.ax (hF h) (hdeg.trans hB)
  | zero => exact PCDerivable.zero
  | add _ _ ih1 ih2 => exact PCDerivable.add ih1 ih2
  | mulX j _ hdeg ih => exact PCDerivable.mulX j ih (hdeg.trans hB)

lemma pc_deg_le {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable F B p) : p.totalDegree ≤ B := by
  induction hp with
  | ax _ hdeg => exact hdeg
  | zero => simp
  | add _ _ ih1 ih2 => exact (MvPolynomial.totalDegree_add _ _).trans (max_le ih1 ih2)
  | mulX _ _ hdeg _ => exact hdeg

lemma pc_sum {V : Type} {ι : Type*} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (s : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PCDerivable.add (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma pc_mul_C {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (c : ZMod 2) {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable F B p) :
    PCDerivable F B (MvPolynomial.C c * p) := by
  rcases z2_cases c with rfl | rfl
  · simp [PCDerivable.zero]
  · simpa using hp

lemma pc_mul_aff {V : Type} [Fintype V] {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (ℓ : Aff V) {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable F B p) :
    PCDerivable F (B + 1) (affPoly ℓ * p) := by
  have hpdeg : p.totalDegree ≤ B := pc_deg_le hp
  have hexpand : affPoly ℓ * p =
      (∑ v : V, MvPolynomial.C (ℓ.1 v) * (MvPolynomial.X v * p)) + MvPolynomial.C ℓ.2 * p := by
    unfold affPoly
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun v _ => by ring
  rw [hexpand]
  refine PCDerivable.add (pc_sum Finset.univ _ fun v _ => ?_) (pc_mul_C ℓ.2 (pc_mono subset_rfl (by omega) hp))
  refine pc_mul_C (ℓ.1 v) (PCDerivable.mulX v (pc_mono subset_rfl (by omega) hp) ?_)
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X]; omega)

lemma mvpoly_add_self {V : Type} (p : MvPolynomial V (ZMod 2)) : p + p = 0 := by
  have h2 : (2 : MvPolynomial V (ZMod 2)) = 0 := by
    have h := map_ofNat (MvPolynomial.C : ZMod 2 →+* MvPolynomial V (ZMod 2)) 2
    rw [← h]
    have h2z : (2 : ZMod 2) = 0 := rfl
    rw [h2z, map_zero]
  calc p + p = 2 * p := by ring
    _ = 0 := by rw [h2, zero_mul]

lemma mvpoly_sq_add {V : Type} (p q : MvPolynomial V (ZMod 2)) :
    (p + q) * (p + q) = p * p + q * q := by
  have h : (p + q) * (p + q) = p * p + (p * q + p * q) + q * q := by ring
  rw [h, mvpoly_add_self, add_zero]

lemma mvpoly_sq_sum {V : Type} {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial V (ZMod 2)) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, mvpoly_sq_add, ih]

lemma pc_aff_bool {V : Type} [Fintype V] {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hB : 2 ≤ B) (ℓ : Aff V) :
    PCDerivable F B (affPoly ℓ * (1 + affPoly ℓ)) := by
  have heq : affPoly ℓ * (1 + affPoly ℓ) =
      ∑ v : V, MvPolynomial.C (ℓ.1 v) * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) := by
    have h1 : affPoly ℓ * (1 + affPoly ℓ) = affPoly ℓ * affPoly ℓ + affPoly ℓ := by ring
    rw [h1]
    unfold affPoly
    rw [mvpoly_sq_add, mvpoly_sq_sum]
    have hc : (MvPolynomial.C ℓ.2 : MvPolynomial V (ZMod 2)) * MvPolynomial.C ℓ.2 + MvPolynomial.C ℓ.2 = 0 := by
      rw [← map_mul, z2_mul_self, mvpoly_add_self]
    have hsum : (∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v * (MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v)) +
        (∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v) =
        ∑ v : V, MvPolynomial.C (ℓ.1 v) * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hv : (MvPolynomial.C (ℓ.1 v) : MvPolynomial V (ZMod 2)) * MvPolynomial.C (ℓ.1 v) = MvPolynomial.C (ℓ.1 v) := by
        rw [← map_mul, z2_mul_self]
      calc MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v * (MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v) +
            MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v
          = (MvPolynomial.C (ℓ.1 v) * MvPolynomial.C (ℓ.1 v)) * (MvPolynomial.X v * MvPolynomial.X v) +
            MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v := by ring
        _ = MvPolynomial.C (ℓ.1 v) * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) := by
            rw [hv]; ring
    calc ((∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v * (MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v)) +
            MvPolynomial.C ℓ.2 * MvPolynomial.C ℓ.2) +
          ((∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v) + MvPolynomial.C ℓ.2)
        = ((∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v * (MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v)) +
            (∑ v : V, MvPolynomial.C (ℓ.1 v) * MvPolynomial.X v)) +
          (MvPolynomial.C ℓ.2 * MvPolynomial.C ℓ.2 + MvPolynomial.C ℓ.2) := by ring
      _ = ∑ v : V, MvPolynomial.C (ℓ.1 v) * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v) := by
          rw [hsum, hc, add_zero]
  rw [heq]
  refine pc_sum Finset.univ _ fun v _ => pc_mul_C (ℓ.1 v) (PCDerivable.ax (hbool v) ?_)
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]; omega
  · simp [MvPolynomial.totalDegree_X]; omega

lemma pc_deduct {V : Type} [Fintype V] {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hB : 1 ≤ B) (ℓ : Aff V) {p : MvPolynomial V (ZMod 2)}
    (hp : PCDerivable (F ∪ {affPoly ℓ}) B p) :
    PCDerivable F (B + 1) ((1 + affPoly ℓ) * p) := by
  induction hp with
  | ax h hdeg =>
    rcases h with hF | hEq
    · rw [← affPoly_flip]
      exact pc_mul_aff (ℓ.1, ℓ.2 + 1) (PCDerivable.ax hF hdeg)
    · rw [Set.mem_singleton_iff] at hEq
      subst hEq
      have hcomm : (1 + affPoly ℓ) * affPoly ℓ = affPoly ℓ * (1 + affPoly ℓ) := mul_comm _ _
      rw [hcomm]
      exact pc_aff_bool hbool (by omega) ℓ
  | zero =>
    rw [mul_zero]
    exact PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [mul_add]
    exact PCDerivable.add ih1 ih2
  | @mulX j q _ hdeg ih =>
    have hcomm : (1 + affPoly ℓ) * (MvPolynomial.X j * q) =
        MvPolynomial.X j * ((1 + affPoly ℓ) * q) := by ring
    rw [hcomm]
    refine PCDerivable.mulX j ih ?_
    rw [← hcomm]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (1 + affPoly ℓ).totalDegree ≤ 1 := by
      rw [← affPoly_flip]
      exact affPoly_totalDegree_le _
    omega

lemma pc_branch {V : Type} [Fintype V] {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hB : 1 ≤ B) (ℓ : Aff V)
    (h0 : PCRefutable (F ∪ {affPoly ℓ}) B)
    (h1 : PCRefutable (F ∪ {affPoly (ℓ.1, ℓ.2 + 1)}) B) :
    PCRefutable F (B + 1) := by
  have hd0 : PCDerivable F (B + 1) (1 + affPoly ℓ) := by
    simpa using pc_deduct hbool hB ℓ h0
  have hd1 : PCDerivable F (B + 1) (affPoly ℓ) := by
    have h := pc_deduct hbool hB (ℓ.1, ℓ.2 + 1) h1
    have hflip : 1 + affPoly (ℓ.1, ℓ.2 + 1) = affPoly ℓ := by
      rw [affPoly_flip, ← add_assoc, mvpoly_add_self, zero_add]
    simpa [hflip] using h
  have hsum := PCDerivable.add hd0 hd1
  have h1eq : (1 + affPoly ℓ) + affPoly ℓ = (1 : MvPolynomial V (ZMod 2)) := by
    rw [add_assoc, mvpoly_add_self, add_zero]
  rwa [h1eq] at hsum

lemma pc_unsat_aff {V : Type} [Fintype V] {F : Set (MvPolynomial V (ZMod 2))}
    (E : List (Aff V))
    (hE : ∀ ℓ ∈ E, affPoly ℓ ∈ F)
    (hunsat : ¬ ∃ z : V → ZMod 2, ∀ ℓ ∈ E, evalAff ℓ z = 0) :
    PCRefutable F 1 := by
  let Φ : (V → ZMod 2) →ₗ[ZMod 2] (Fin E.length → ZMod 2) :=
    LinearMap.pi (fun i => affLin (E.get i))
  let rhs : Fin E.length → ZMod 2 := fun i => (E.get i).2
  have hnotmem : rhs ∉ LinearMap.range Φ := by
    rintro ⟨z, hz⟩
    apply hunsat
    refine ⟨z, fun ℓ hℓ => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hℓ
    rw [evalAff_eq_zero_iff]
    exact congrFun hz i
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.range Φ)
  let pQ : (Fin E.length → ZMod 2) →ₗ[ZMod 2] Q := Submodule.projectionOnto Q (LinearMap.range Φ) hQ.symm
  let q₀ : Q := pQ rhs
  have hq₀ne : q₀ ≠ 0 := by
    intro h0
    have hmem : rhs ∈ LinearMap.range Φ :=
      (Submodule.projectionOnto_apply_eq_zero_iff hQ.symm).mp h0
    exact hnotmem hmem
  let Lq : Submodule (ZMod 2) Q := Submodule.span (ZMod 2) {q₀}
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl Lq
  let pL : Q →ₗ[ZMod 2] Lq := Submodule.projectionOnto Lq Q' hQ'
  have hfrL : Module.finrank (ZMod 2) Lq = 1 := finrank_span_singleton hq₀ne
  let coord : Lq →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => if x = 0 then 0 else 1
      map_add' := fun x y => by
        obtain ⟨cx, hcx⟩ := Submodule.mem_span_singleton.mp x.2
        obtain ⟨cy, hcy⟩ := Submodule.mem_span_singleton.mp y.2
        have hx : x = cx • ⟨q₀, Submodule.subset_span (Set.mem_singleton _)⟩ := Subtype.ext hcx.symm
        have hy : y = cy • ⟨q₀, Submodule.subset_span (Set.mem_singleton _)⟩ := Subtype.ext hcy.symm
        have hne : (⟨q₀, Submodule.subset_span (Set.mem_singleton _)⟩ : Lq) ≠ 0 :=
          fun h => hq₀ne (congrArg Subtype.val h)
        rcases z2_cases cx with rfl | rfl <;> rcases z2_cases cy with rfl | rfl
        · simp [hx, hy]
        · simp [hx, hy, hne]
        · simp [hx, hy, hne]
        · have hq00 : q₀ + q₀ = 0 := by
            rw [← one_smul (ZMod 2) q₀, ← add_smul, z2_add_self, zero_smul]
          have hsum0 : x + y = 0 := Subtype.ext (by
            simp only [Submodule.coe_add, ZeroMemClass.coe_zero]
            rw [hx, hy]
            simpa using hq00)
          rw [hsum0, hx, hy]
          simp [hne, z2_add_self]
      map_smul' := fun c x => by
        rcases z2_cases c with rfl | rfl
        · simp
        · simp }
  let α : (Fin E.length → ZMod 2) →ₗ[ZMod 2] ZMod 2 := coord.comp (pL.comp pQ)
  have hα_range : ∀ u ∈ LinearMap.range Φ, α u = 0 := by
    intro u hu
    have h1 : pQ u = 0 := Submodule.projectionOnto_apply_right hQ.symm ⟨u, hu⟩
    simp [α, h1]
  have hα_rhs : α rhs = 1 := by
    have h1 : pL q₀ = ⟨q₀, Submodule.subset_span (Set.mem_singleton _)⟩ :=
      Submodule.projectionOnto_apply_left hQ' ⟨q₀, Submodule.subset_span (Set.mem_singleton _)⟩
    have hne : (⟨q₀, Submodule.subset_span (Set.mem_singleton _)⟩ : Lq) ≠ 0 :=
      fun h => hq₀ne (congrArg Subtype.val h)
    change coord (pL q₀) = 1
    rw [h1]
    simp [coord, hne]
  let c : Fin E.length → ZMod 2 := fun i => α (Pi.single i 1)
  have hα_apply : ∀ w : Fin E.length → ZMod 2, α w = ∑ i : Fin E.length, c i * w i := by
    intro w
    have hw : w = ∑ i : Fin E.length, w i • Pi.single i (1 : ZMod 2) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hlin_zero : ∀ v : V, ∑ i : Fin E.length, c i * (E.get i).1 v = 0 := by
    intro v
    have h1 : α (Φ (Pi.single v 1)) = 0 := hα_range _ ⟨Pi.single v 1, rfl⟩
    rw [hα_apply] at h1
    simpa [Φ, affLin, Pi.single_apply] using h1
  have hconst_one : ∑ i : Fin E.length, c i * (E.get i).2 = 1 := by
    have h1 := hα_rhs
    rw [hα_apply] at h1
    exact h1
  have hpoly_one : ∑ i : Fin E.length, MvPolynomial.C (c i) * affPoly (E.get i) =
      (1 : MvPolynomial V (ZMod 2)) := by
    simp only [affPoly, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hfirst : (∑ v : V, ∑ i : Fin E.length, MvPolynomial.C (c i) * (MvPolynomial.C ((E.get i).1 v) * MvPolynomial.X v)) = 0 := by
      refine Finset.sum_eq_zero fun v _ => ?_
      have h2 : (∑ i : Fin E.length, MvPolynomial.C (c i) * (MvPolynomial.C ((E.get i).1 v) * MvPolynomial.X v)) =
          MvPolynomial.C (∑ i : Fin E.length, c i * (E.get i).1 v) * MvPolynomial.X v := by
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
      rw [h2, hlin_zero v, map_zero, zero_mul]
    have hsecond : (∑ i : Fin E.length, (MvPolynomial.C (c i) : MvPolynomial V (ZMod 2)) * MvPolynomial.C (E.get i).2) = 1 := by
      have h2 : (∑ i : Fin E.length, (MvPolynomial.C (c i) : MvPolynomial V (ZMod 2)) * MvPolynomial.C (E.get i).2) =
          MvPolynomial.C (∑ i : Fin E.length, c i * (E.get i).2) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm
      rw [h2, hconst_one, map_one]
    rw [hfirst, hsecond, zero_add]
  unfold PCRefutable
  rw [← hpoly_one]
  refine pc_sum Finset.univ _ fun i _ => pc_mul_C (c i) ?_
  exact PCDerivable.ax (hE (E.get i) (List.get_mem E i)) (affPoly_totalDegree_le _)

lemma clausePoly_totalDegree_le {V : Type} (C : Clause V) :
    (clausePoly C).totalDegree ≤ C.card := by
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | insert l C hl ih =>
    unfold clausePoly
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hdeg1 : (if l.2 = true then (1 : MvPolynomial V (ZMod 2)) + MvPolynomial.X l.1 else MvPolynomial.X l.1).totalDegree ≤ 1 := by
      split_ifs
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · simp
        · simp [MvPolynomial.totalDegree_X]
      · simp [MvPolynomial.totalDegree_X]
    change _ + (clausePoly C).totalDegree ≤ _
    omega

lemma pc_clause_falsified {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (C : Clause V) (hCF : clausePoly C ∈ F) (hCB : C.card ≤ B) (hB1 : 1 ≤ B)
    (hlits : ∀ l ∈ C, affPoly (Pi.single l.1 1, if l.2 = true then 0 else 1) ∈ F) :
    PCRefutable F B := by
  have hprod : ∀ D : Clause V, (∀ l ∈ D, affPoly (Pi.single l.1 1, if l.2 = true then 0 else 1) ∈ F) →
      PCDerivable F (max 1 D.card) (clausePoly D + 1) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      simp [clausePoly, mvpoly_add_self, PCDerivable.zero]
    | insert l D hl ih =>
      intro hD
      unfold clausePoly
      rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
      let f : MvPolynomial V (ZMod 2) := if l.2 = true then 1 + MvPolynomial.X l.1 else MvPolynomial.X l.1
      have hf_aff : f = affPoly (Pi.single l.1 1, if l.2 = true then 1 else 0) := by
        unfold affPoly f
        have hsum : (∑ v : V, MvPolynomial.C ((Pi.single l.1 (1 : ZMod 2)) v) * MvPolynomial.X v) =
            MvPolynomial.X l.1 := by
          rw [Finset.sum_eq_single l.1]
          · simp
          · intro v _ hv; simp [Pi.single_eq_of_ne hv]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum]
        cases l.2 <;> simp [add_comm]
      have hf1_aff : f + 1 = affPoly (Pi.single l.1 1, if l.2 = true then 0 else 1) := by
        rw [hf_aff, add_comm, ← affPoly_flip]
        cases l.2
        · simp [affPoly]
        · simp [affPoly, z2_add_self]
      have hstep : f * clausePoly D + 1 = f * (clausePoly D + 1) + (f + 1) := by
        have hff : f + f = 0 := mvpoly_add_self f
        calc f * clausePoly D + 1 = f * clausePoly D + (f + f) + 1 := by rw [hff, add_zero]
          _ = f * (clausePoly D + 1) + (f + 1) := by ring
      change PCDerivable F _ (f * clausePoly D + 1)
      rw [hstep]
      have h1 : PCDerivable F (max 1 D.card + 1) (f * (clausePoly D + 1)) := by
        rw [hf_aff]
        exact pc_mul_aff _ (ih fun l' hl' => hD l' (Finset.mem_insert_of_mem hl'))
      have h2 : PCDerivable F 1 (f + 1) := by
        rw [hf1_aff]
        exact PCDerivable.ax (hD l (Finset.mem_insert_self _ _)) (affPoly_totalDegree_le _)
      by_cases hD0 : D.card = 0
      · have hDempty : D = ∅ := Finset.card_eq_zero.mp hD0
        subst hDempty
        simp only [clausePoly, Finset.prod_empty, mul_one, Finset.card_empty, max_self] at hstep ⊢
        rw [← hstep]
        exact h2
      · have hle1 : max 1 D.card + 1 ≤ max 1 (D.card + 1) := by omega
        have hle2 : 1 ≤ max 1 (D.card + 1) := by omega
        exact PCDerivable.add (pc_mono subset_rfl hle1 h1) (pc_mono subset_rfl hle2 h2)
  have hder1 : PCDerivable F B (clausePoly C + 1) :=
    pc_mono subset_rfl (max_le hB1 hCB) (hprod C hlits)
  have hder2 : PCDerivable F B (clausePoly C) :=
    PCDerivable.ax hCF ((clausePoly_totalDegree_le C).trans hCB)
  have hsum := PCDerivable.add hder2 hder1
  have h1 : clausePoly C + (clausePoly C + 1) = (1 : MvPolynomial V (ZMod 2)) := by
    rw [← add_assoc, mvpoly_add_self, zero_add]
  rwa [h1] at hsum

lemma pc_of_cover {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (MvPolynomial V (ZMod 2))}
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (b' : ℕ) (hb' : 1 ≤ b')
    (U : Finset (Clause V))
    (hUF : ∀ C ∈ U, clausePoly C ∈ F ∧ C.card ≤ b')
    (E : List (Aff V))
    (hcov : ∀ z : V → ZMod 2, (∀ ℓ ∈ E, evalAff ℓ z = 0) →
      ∃ C ∈ U, ¬ ClauseSat (z2ToX z) C) :
    PCRefutable (F ∪ {p | ∃ ℓ ∈ E, p = affPoly ℓ}) (b' * U.card + b') := by
  let varsU : Finset V := U.biUnion (fun C => C.image Prod.fst)
  have hvars_card : varsU.card ≤ b' * U.card := by
    calc varsU.card ≤ ∑ C ∈ U, (C.image Prod.fst).card := Finset.card_biUnion_le
      _ ≤ ∑ C ∈ U, C.card := Finset.sum_le_sum fun C _ => Finset.card_image_le
      _ ≤ ∑ _C ∈ U, b' := Finset.sum_le_sum fun C hC => (hUF C hC).2
      _ = U.card * b' := by simp
      _ = b' * U.card := Nat.mul_comm _ _
  have hgen : ∀ (S : Finset V) (E' : List (Aff V)),
      (∀ z : V → ZMod 2, (∀ ℓ ∈ E', evalAff ℓ z = 0) → ∃ C ∈ U, ¬ ClauseSat (z2ToX z) C) →
      (∀ v ∈ varsU, v ∉ S →
        (Pi.single v (1 : ZMod 2), (0 : ZMod 2)) ∈ E' ∨
        (Pi.single v (1 : ZMod 2), (1 : ZMod 2)) ∈ E') →
      PCRefutable (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) (S.card + b') := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro E' hcov' hfix
      simp only [Finset.card_empty, zero_add]
      by_cases hsat : ∃ z : V → ZMod 2, ∀ ℓ ∈ E', evalAff ℓ z = 0
      · obtain ⟨z₀, hz₀⟩ := hsat
        obtain ⟨C, hCU, hCfalse⟩ := hcov' z₀ hz₀
        refine pc_clause_falsified C (Or.inl (hUF C hCU).1) (hUF C hCU).2 hb' ?_
        intro l hlC
        right
        have hv : l.1 ∈ varsU := Finset.mem_biUnion.mpr ⟨C, hCU, Finset.mem_image.mpr ⟨l, hlC, rfl⟩⟩
        have hnotl : z2ToX z₀ l.1 ≠ l.2 := fun heq => hCfalse ⟨l, hlC, heq⟩
        rcases hfix l.1 hv (Finset.notMem_empty _) with h0 | h1
        · have hz0 : z₀ l.1 = 0 := by
            have := hz₀ _ h0
            simpa [evalAff, Pi.single_apply] using this
          have hl2 : l.2 = true := by
            have hzx : z2ToX z₀ l.1 = false := by simp [z2ToX, z2ToBool, hz0]
            cases hl : l.2 <;> simp_all
          exact ⟨(Pi.single l.1 1, 0), h0, by simp [hl2]⟩
        · have hz1 : z₀ l.1 = 1 := by
            have := hz₀ _ h1
            have : z₀ l.1 + 1 = 0 := by simpa [evalAff, Pi.single_apply] using this
            rcases z2_cases (z₀ l.1) with h | h <;> simp_all
          have hl2 : l.2 = false := by
            have hzx : z2ToX z₀ l.1 = true := by simp [z2ToX, z2ToBool, hz1]
            cases hl : l.2 <;> simp_all
          exact ⟨(Pi.single l.1 1, 1), h1, by simp [hl2]⟩
      · exact pc_mono subset_rfl hb' (pc_unsat_aff E' (fun ℓ hℓ => Or.inr ⟨ℓ, hℓ, rfl⟩) hsat)
    | insert v S hv ih =>
      intro E' hcov' hfix
      rw [Finset.card_insert_of_notMem hv]
      have h0 : PCRefutable ((F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪
          {affPoly (Pi.single v (1 : ZMod 2), (0 : ZMod 2))}) (S.card + b') := by
        have hset : (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪ {affPoly (Pi.single v 1, 0)} =
            F ∪ {p | ∃ ℓ ∈ (Pi.single v 1, 0) :: E', p = affPoly ℓ} := by
          ext p; simp [or_comm, or_left_comm]
        rw [hset]
        refine ih ((Pi.single v 1, 0) :: E') (fun z hz => hcov' z fun ℓ hℓ => hz ℓ (List.mem_cons_of_mem _ hℓ)) ?_
        intro u hu huS
        by_cases huv : u = v
        · subst huv; left; exact List.mem_cons_self
        · have huin : u ∉ insert v S := by simp [huv, huS]
          rcases hfix u hu huin with h | h
          · left; exact List.mem_cons_of_mem _ h
          · right; exact List.mem_cons_of_mem _ h
      have h1 : PCRefutable ((F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪
          {affPoly (Pi.single v (1 : ZMod 2), (0 : ZMod 2) + 1)}) (S.card + b') := by
        have hset : (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪ {affPoly (Pi.single v 1, 0 + 1)} =
            F ∪ {p | ∃ ℓ ∈ (Pi.single v 1, 1) :: E', p = affPoly ℓ} := by
          ext p; simp [or_comm, or_left_comm]
        rw [hset]
        refine ih ((Pi.single v 1, 1) :: E') (fun z hz => hcov' z fun ℓ hℓ => hz ℓ (List.mem_cons_of_mem _ hℓ)) ?_
        intro u hu huS
        by_cases huv : u = v
        · subst huv; right; exact List.mem_cons_self
        · have huin : u ∉ insert v S := by simp [huv, huS]
          rcases hfix u hu huin with h | h
          · left; exact List.mem_cons_of_mem _ h
          · right; exact List.mem_cons_of_mem _ h
      exact pc_mono subset_rfl (by omega)
        (pc_branch (fun u => Or.inl (hbool u)) (by omega) (Pi.single v 1, 0) h0 h1)
  exact pc_mono subset_rfl (by omega) (hgen varsU E hcov (fun v hv hnv => absurd hv hnv))

end PCHelpers

section CircuitAffineAndLowerBound

def inBits {V : Type} [Fintype V] (x : V → Bool) : List Bool :=
  [false, true] ++ List.ofFn (fun i : Fin (Fintype.card V) => x ((Fintype.equivFin V).symm i))

lemma inBits_length {V : Type} [Fintype V] (x : V → Bool) :
    (inBits x).length = 2 + Fintype.card V := by
  simp [inBits]; omega

def wiresOf (gs : List Gate) (inp : List Bool) : List Bool :=
  ({ gates := gs, output := 0 } : Circuit).wires inp

lemma wiresOf_nil (inp : List Bool) : wiresOf [] inp = inp := rfl

lemma wiresOf_append_one (gs : List Gate) (g : Gate) (inp : List Bool) :
    wiresOf (gs ++ [g]) inp =
      wiresOf gs inp ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)] := by
  simp [wiresOf, Circuit.wires]

lemma wiresOf_append (gs₁ gs₂ : List Gate) (inp : List Bool) :
    wiresOf (gs₁ ++ gs₂) inp = wiresOf gs₂ (wiresOf gs₁ inp) := by
  simp [wiresOf, Circuit.wires, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf_nil]
  | append_singleton gs g ih =>
    rw [wiresOf_append_one, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton]
    omega

lemma wiresOf_prefix_getD (gs₁ gs₂ : List Gate) (inp : List Bool) (i : ℕ)
    (hi : i < inp.length + gs₁.length) :
    (wiresOf (gs₁ ++ gs₂) inp).getD i false = (wiresOf gs₁ inp).getD i false := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    rw [← List.append_assoc, wiresOf_append_one]
    have hlen : i < (wiresOf (gs₁ ++ gs₂) inp).length := by
      rw [wiresOf_length, List.length_append]; omega
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
      List.getElem_append_left hlen, ← List.getD_eq_getElem _ _ hlen]
    exact ih

lemma wiresOf_last_getD (gs : List Gate) (g : Gate) (inp : List Bool) :
    (wiresOf (gs ++ [g]) inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false) := by
  rw [wiresOf_append_one]
  have hlen : (wiresOf gs inp).length = inp.length + gs.length := wiresOf_length gs inp
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_singleton, hlen]; omega)]
  have h1 : (wiresOf gs inp ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)])[inp.length + gs.length]'(by
      rw [List.length_append, List.length_singleton, hlen]; omega) =
      ([g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)])[inp.length + gs.length - (wiresOf gs inp).length]'(by
      rw [hlen]; simp) := by
    apply List.getElem_append_right
    omega
  rw [h1]
  simp [hlen]

def inputAffs (V : Type) [Fintype V] [DecidableEq V] : List (Aff V) :=
  [(0, 0), (0, 1)] ++ List.ofFn (fun i : Fin (Fintype.card V) =>
    (Pi.single ((Fintype.equivFin V).symm i) (1 : ZMod 2), (0 : ZMod 2)))

lemma inputAffs_length (V : Type) [Fintype V] [DecidableEq V] :
    (inputAffs V).length = 2 + Fintype.card V := by
  simp [inputAffs]; omega

lemma inputAffs_match {V : Type} [Fintype V] [DecidableEq V] (x : V → Bool) (i : ℕ)
    (hi : i < 2 + Fintype.card V) :
    boolToZ2 ((inBits x).getD i false) = evalAff ((inputAffs V).getD i (0, 0)) (xToZ2 x) := by
  match i with
  | 0 => simp [inBits, inputAffs, evalAff, boolToZ2]
  | 1 => simp [inBits, inputAffs, evalAff, boolToZ2]
  | k + 2 =>
    have hk : k < Fintype.card V := by omega
    have h1 : (inBits x).getD (k + 2) false = x ((Fintype.equivFin V).symm ⟨k, hk⟩) := by
      unfold inBits
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    have h2 : (inputAffs V).getD (k + 2) (0, 0) =
        (Pi.single ((Fintype.equivFin V).symm ⟨k, hk⟩) (1 : ZMod 2), (0 : ZMod 2)) := by
      unfold inputAffs
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    rw [h1, h2]
    simp [evalAff, xToZ2, Pi.single_apply]

def gateValid (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)

def countAndOr (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))

lemma countAndOr_nil : countAndOr [] = 0 := rfl

lemma countAndOr_cons (g : Gate) (gs : List Gate) :
    countAndOr (g :: gs) = countAndOr gs + if g.op = .and ∨ g.op = .or then 1 else 0 := by
  unfold countAndOr
  rw [List.countP_cons]
  by_cases h : g.op = .and ∨ g.op = .or <;> simp [h]

lemma countAndOr_append_one (gs : List Gate) (g : Gate) :
    countAndOr (gs ++ [g]) = countAndOr gs + if g.op = .and ∨ g.op = .or then 1 else 0 := by
  unfold countAndOr
  rw [List.countP_append, List.countP_cons, List.countP_nil, zero_add]
  by_cases h : g.op = .and ∨ g.op = .or <;> simp [h]

def notAff {V : Type} (ℓ : Aff V) : Aff V := (ℓ.1, ℓ.2 + 1)

def mod2Aff {V : Type} (ls : List (Aff V)) : Aff V :=
  (fun v => (ls.map (fun ℓ => ℓ.1 v)).sum, 1 + (ls.map Prod.snd).sum)

lemma evalAff_notAff {V : Type} [Fintype V] (ℓ : Aff V) (z : V → ZMod 2) :
    evalAff (notAff ℓ) z = evalAff ℓ z + 1 := by
  simp [evalAff, notAff, add_assoc]

lemma evalAff_mod2Aff {V : Type} [Fintype V] (ls : List (Aff V)) (z : V → ZMod 2) :
    evalAff (mod2Aff ls) z = 1 + (ls.map (fun ℓ => evalAff ℓ z)).sum := by
  induction ls with
  | nil => simp [evalAff, mod2Aff]
  | cons ℓ tl ih =>
    simp only [mod2Aff, evalAff, List.map_cons, List.sum_cons] at ih ⊢
    have hsum : (∑ v : V, (ℓ.1 v + (tl.map fun ℓ' => ℓ'.1 v).sum) * z v) =
        (∑ v : V, ℓ.1 v * z v) + ∑ v : V, (tl.map fun ℓ' => ℓ'.1 v).sum * z v := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [hsum]
    calc ((∑ v : V, ℓ.1 v * z v) + ∑ v : V, (tl.map fun ℓ' => ℓ'.1 v).sum * z v) +
          (1 + (ℓ.2 + (tl.map Prod.snd).sum))
        = (∑ v : V, ℓ.1 v * z v) + ℓ.2 +
          ((∑ v : V, (tl.map fun ℓ' => ℓ'.1 v).sum * z v) + (1 + (tl.map Prod.snd).sum)) := by ring
      _ = (∑ v : V, ℓ.1 v * z v) + ℓ.2 + (1 + (tl.map fun ℓ' => (∑ v : V, ℓ'.1 v * z v) + ℓ'.2).sum) := by
          rw [ih]
      _ = 1 + (((∑ v : V, ℓ.1 v * z v) + ℓ.2) +
          (tl.map fun ℓ' => (∑ v : V, ℓ'.1 v * z v) + ℓ'.2).sum) := by ring

lemma eval_not_gate {V : Type} [Fintype V] (ws : List Bool) (waff : List (Aff V)) (z : V → ZMod 2)
    (u : ℕ) (hu : boolToZ2 (ws.getD u false) = evalAff (waff.getD u (0, 0)) z) :
    boolToZ2 (GateOp.eval .not ([u].map fun i => ws.getD i false)) =
      evalAff (notAff (waff.getD u (0, 0))) z := by
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  rw [boolToZ2_not, hu, evalAff_notAff]

lemma eval_mod2_gate {V : Type} [Fintype V] (ws : List Bool) (waff : List (Aff V)) (z : V → ZMod 2)
    (ins : List ℕ) (hins : ∀ i ∈ ins, boolToZ2 (ws.getD i false) = evalAff (waff.getD i (0, 0)) z) :
    boolToZ2 (GateOp.eval (.mod 2) (ins.map fun i => ws.getD i false)) =
      evalAff (mod2Aff (ins.map fun i => waff.getD i (0, 0))) z := by
  simp only [GateOp.eval]
  rw [boolToZ2_mod2, evalAff_mod2Aff, List.map_map, List.map_map]
  congr 1
  have hmap : ins.map (boolToZ2 ∘ fun i => ws.getD i false) =
      ins.map ((fun ℓ => evalAff ℓ z) ∘ fun i => waff.getD i (0, 0)) := by
    refine List.map_congr_left fun i hi => hins i hi
  rw [hmap]

lemma eval_and_gate_zero {V : Type} [Fintype V] (ws : List Bool) (z : V → ZMod 2)
    (u v : ℕ) (hu : boolToZ2 (ws.getD u false) = 0) :
    boolToZ2 (GateOp.eval .and ([u, v].map fun i => ws.getD i false)) = evalAff (0, 0) z := by
  have huf : ws.getD u false = false := boolToZ2_injective hu
  have hev : evalAff (0, 0) z = 0 := by simp [evalAff]
  rw [hev]
  simp only [List.map_cons, List.map_nil, GateOp.eval, huf, List.all_cons, List.all_nil, id_eq,
    Bool.false_and]
  rfl

lemma eval_and_gate_one {V : Type} [Fintype V] (ws : List Bool) (waff : List (Aff V)) (z : V → ZMod 2)
    (u v : ℕ) (hu : boolToZ2 (ws.getD u false) = 1)
    (hv : boolToZ2 (ws.getD v false) = evalAff (waff.getD v (0, 0)) z) :
    boolToZ2 (GateOp.eval .and ([u, v].map fun i => ws.getD i false)) =
      evalAff (waff.getD v (0, 0)) z := by
  have hut : ws.getD u false = true := boolToZ2_injective hu
  simp only [List.map_cons, List.map_nil, GateOp.eval, hut, List.all_cons, List.all_nil, id_eq,
    Bool.true_and, Bool.and_true]
  exact hv

lemma eval_or_gate_zero {V : Type} [Fintype V] (ws : List Bool) (waff : List (Aff V)) (z : V → ZMod 2)
    (u v : ℕ) (hu : boolToZ2 (ws.getD u false) = 0)
    (hv : boolToZ2 (ws.getD v false) = evalAff (waff.getD v (0, 0)) z) :
    boolToZ2 (GateOp.eval .or ([u, v].map fun i => ws.getD i false)) =
      evalAff (waff.getD v (0, 0)) z := by
  have huf : ws.getD u false = false := boolToZ2_injective hu
  simp only [List.map_cons, List.map_nil, GateOp.eval, huf, List.any_cons, List.any_nil, id_eq,
    Bool.false_or, Bool.or_false]
  exact hv

lemma eval_or_gate_one {V : Type} [Fintype V] (ws : List Bool) (z : V → ZMod 2)
    (u v : ℕ) (hu : boolToZ2 (ws.getD u false) = 1) :
    boolToZ2 (GateOp.eval .or ([u, v].map fun i => ws.getD i false)) = evalAff (0, 1) z := by
  have hut : ws.getD u false = true := boolToZ2_injective hu
  have hev : evalAff (0, 1) z = 1 := by simp [evalAff]
  rw [hev]
  simp only [List.map_cons, List.map_nil, GateOp.eval, hut, List.any_cons, List.any_nil, id_eq,
    Bool.true_or]
  rfl

lemma circuit_slice_at_point {V : Type} [Fintype V] [DecidableEq V]
    (gs : List Gate)
    (hrb : ReadsBack (2 + Fintype.card V) ⟨gs, 0⟩)
    (hval : ∀ g ∈ gs, gateValid g)
    (x₀ : V → Bool) :
    ∃ (eqs : List (Aff V)) (waff : List (Aff V)),
      eqs.length ≤ countAndOr gs ∧
      waff.length = 2 + Fintype.card V + gs.length ∧
      (∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x₀) = 0) ∧
      (∀ x : V → Bool, (∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x) = 0) →
        ∀ i < 2 + Fintype.card V + gs.length,
          boolToZ2 ((wiresOf gs (inBits x)).getD i false) = evalAff (waff.getD i (0, 0)) (xToZ2 x)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], inputAffs V, by simp, by simp [inputAffs_length], by simp, ?_⟩
    intro x _ i hi
    simpa [wiresOf_nil] using inputAffs_match x i hi
  | append_singleton gs g ih =>
    have hrb_prev : ReadsBack (2 + Fintype.card V) ⟨gs, 0⟩ := by
      intro j hj i hi
      dsimp only at hj
      have hj' : j < (gs ++ [g]).length := by rw [List.length_append, List.length_singleton]; omega
      have h1 := hrb j hj'
      have hg_eq : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt
        dsimp only
        rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj', List.getElem_append_left hj]
      rw [hg_eq] at h1
      exact h1 i hi
    have hrb_last : ∀ i ∈ g.inputs, i < 2 + Fintype.card V + gs.length := by
      intro i hi
      have h1 := hrb gs.length (by simp)
      have hg_eq : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        simp [gateAt]
      rw [hg_eq] at h1
      exact h1 i hi
    obtain ⟨eqs, waff, heqs_len, hwaff_len, hx₀, hmatch⟩ :=
      ih hrb_prev (fun g' hg' => hval g' (List.mem_append_left _ hg'))
    have hgval : gateValid g := hval g (List.mem_append_right _ List.mem_cons_self)
    have hstep_append : ∀ (newAff : Aff V) (extraEqs : List (Aff V)),
        (∀ ℓ ∈ extraEqs, evalAff ℓ (xToZ2 x₀) = 0) →
        (∀ x : V → Bool, (∀ ℓ ∈ extraEqs ++ eqs, evalAff ℓ (xToZ2 x) = 0) →
          boolToZ2 (g.op.eval (g.inputs.map fun i => (wiresOf gs (inBits x)).getD i false)) =
            evalAff newAff (xToZ2 x)) →
        extraEqs.length ≤ (if g.op = .and ∨ g.op = .or then 1 else 0) →
        ∃ (eqs' : List (Aff V)) (waff' : List (Aff V)),
          eqs'.length ≤ countAndOr (gs ++ [g]) ∧
          waff'.length = 2 + Fintype.card V + (gs ++ [g]).length ∧
          (∀ ℓ ∈ eqs', evalAff ℓ (xToZ2 x₀) = 0) ∧
          (∀ x : V → Bool, (∀ ℓ ∈ eqs', evalAff ℓ (xToZ2 x) = 0) →
            ∀ i < 2 + Fintype.card V + (gs ++ [g]).length,
              boolToZ2 ((wiresOf (gs ++ [g]) (inBits x)).getD i false) =
                evalAff (waff'.getD i (0, 0)) (xToZ2 x)) := by
      intro newAff extraEqs hex₀ hexmatch hexlen
      refine ⟨extraEqs ++ eqs, waff ++ [newAff], ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, countAndOr_append_one]; omega
      · rw [List.length_append, List.length_singleton, hwaff_len, List.length_append,
          List.length_singleton]; omega
      · intro ℓ hℓ
        rcases List.mem_append.mp hℓ with h1 | h2
        · exact hex₀ ℓ h1
        · exact hx₀ ℓ h2
      · intro x hx i hi
        rw [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < 2 + Fintype.card V + gs.length
        · have hprev := wiresOf_prefix_getD gs [g] (inBits x) i (by rw [inBits_length]; exact hlt)
          rw [hprev]
          have hw : (waff ++ [newAff]).getD i (0, 0) = waff.getD i (0, 0) := by
            rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hwaff_len]; omega),
              List.getElem_append_left (by omega), ← List.getD_eq_getElem _ _ (by omega)]
          rw [hw]
          exact hmatch x (fun ℓ hℓ => hx ℓ (List.mem_append_right _ hℓ)) i hlt
        · have hieq : i = 2 + Fintype.card V + gs.length := by omega
          subst hieq
          have hlast := wiresOf_last_getD gs g (inBits x)
          rw [inBits_length] at hlast
          rw [hlast]
          have hw : (waff ++ [newAff]).getD (2 + Fintype.card V + gs.length) (0, 0) = newAff := by
            rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hwaff_len]; simp)]
            have h1 : (waff ++ [newAff])[2 + Fintype.card V + gs.length]'(by
                rw [List.length_append, hwaff_len]; simp) =
                ([newAff])[2 + Fintype.card V + gs.length - waff.length]'(by rw [hwaff_len]; simp) :=
              List.getElem_append_right (by omega)
            rw [h1]; simp [hwaff_len]
          rw [hw]
          exact hexmatch x hx
    rcases hgval with ⟨hor, hlen2⟩ | hmod2 | ⟨hnot, hlen1⟩
    · obtain ⟨u, v, huv⟩ : ∃ u v, g.inputs = [u, v] := by
        cases h1 : g.inputs with
        | nil => simp [h1] at hlen2
        | cons u tl =>
          cases h2 : tl with
          | nil => simp [h1, h2] at hlen2
          | cons v tl2 =>
            cases tl2 with
            | nil => exact ⟨u, v, rfl⟩
            | cons _ _ => simp [h1, h2] at hlen2
      have hu_lt : u < 2 + Fintype.card V + gs.length := hrb_last u (by rw [huv]; simp)
      have hv_lt : v < 2 + Fintype.card V + gs.length := hrb_last v (by rw [huv]; simp)
      let ℓu := waff.getD u (0, 0)
      let val_u := evalAff ℓu (xToZ2 x₀)
      let eq_u : Aff V := (ℓu.1, ℓu.2 + val_u)
      have heq_x0 : evalAff eq_u (xToZ2 x₀) = 0 := by
        change (∑ a : V, ℓu.1 a * xToZ2 x₀ a) + (ℓu.2 + val_u) = 0
        rw [← add_assoc]
        exact z2_add_self val_u
      have heq_val : ∀ x : V → Bool, (∀ ℓ ∈ eq_u :: eqs, evalAff ℓ (xToZ2 x) = 0) →
          boolToZ2 ((wiresOf gs (inBits x)).getD u false) = val_u := by
        intro x hx
        rw [hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) u hu_lt]
        have h0 : evalAff eq_u (xToZ2 x) = 0 := hx eq_u List.mem_cons_self
        have h1 : evalAff ℓu (xToZ2 x) + val_u = 0 := by
          simpa [eq_u, evalAff, add_assoc] using h0
        have h2 : evalAff ℓu (xToZ2 x) = evalAff ℓu (xToZ2 x) + (val_u + val_u) := by
          rw [z2_add_self, add_zero]
        rw [← add_assoc, h1, zero_add] at h2
        exact h2
      rcases hor with hand | hor'
      · rcases z2_cases val_u with hval0 | hval1
        · refine hstep_append (0, 0) [eq_u] (by simp [heq_x0]) (fun x hx => ?_) (by rw [hand]; simp)
          rw [hand, huv]
          exact eval_and_gate_zero _ _ u v ((heq_val x hx).trans hval0)
        · refine hstep_append (waff.getD v (0, 0)) [eq_u] (by simp [heq_x0]) (fun x hx => ?_) (by rw [hand]; simp)
          rw [hand, huv]
          exact eval_and_gate_one _ waff _ u v ((heq_val x hx).trans hval1)
            (hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) v hv_lt)
      · rcases z2_cases val_u with hval0 | hval1
        · refine hstep_append (waff.getD v (0, 0)) [eq_u] (by simp [heq_x0]) (fun x hx => ?_) (by rw [hor']; simp)
          rw [hor', huv]
          exact eval_or_gate_zero _ waff _ u v ((heq_val x hx).trans hval0)
            (hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) v hv_lt)
        · refine hstep_append (0, 1) [eq_u] (by simp [heq_x0]) (fun x hx => ?_) (by rw [hor']; simp)
          rw [hor', huv]
          exact eval_or_gate_one _ _ u v ((heq_val x hx).trans hval1)
    · refine hstep_append (mod2Aff (g.inputs.map fun i => waff.getD i (0, 0))) [] (by simp)
        (fun x hx => ?_) (by simp)
      rw [hmod2]
      exact eval_mod2_gate _ waff _ g.inputs (fun i hi => hmatch x hx i (hrb_last i hi))
    · obtain ⟨u, hu⟩ : ∃ u, g.inputs = [u] := by
        cases h1 : g.inputs with
        | nil => simp [h1] at hlen1
        | cons u tl =>
          cases tl with
          | nil => exact ⟨u, rfl⟩
          | cons _ _ => simp [h1] at hlen1
      have hu_lt : u < 2 + Fintype.card V + gs.length := hrb_last u (by rw [hu]; simp)
      refine hstep_append (notAff (waff.getD u (0, 0))) [] (by simp) (fun x hx => ?_) (by simp)
      rw [hnot, hu]
      exact eval_not_gate _ waff _ u (hmatch x hx u hu_lt)

lemma pc_of_flat_branch {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (MvPolynomial V (ZMod 2))}
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (b b' M : ℕ) (hb' : 1 ≤ b')
    (msgAff : Fin b → Aff V)
    (out : (Fin b → ZMod 2) → Finset (Clause V))
    (hU : ∀ y : Fin b → ZMod 2, ∀ C ∈ out y, clausePoly C ∈ F ∧ C.card ≤ b')
    (E : List (Aff V))
    (J : Finset (Fin b))
    (hconst : ∀ z₁ z₂ : V → ZMod 2,
      (∀ ℓ ∈ E, evalAff ℓ z₁ = 0) → (∀ ℓ ∈ E, evalAff ℓ z₂ = 0) →
      (∀ j ∈ J, evalAff (msgAff j) z₁ = evalAff (msgAff j) z₂) →
      (fun j => evalAff (msgAff j) z₁) = (fun j => evalAff (msgAff j) z₂))
    (hcap : ∀ z : V → ZMod 2, (∀ ℓ ∈ E, evalAff ℓ z = 0) →
      (out (fun j => evalAff (msgAff j) z)).card ≤ M)
    (hcov : ∀ z : V → ZMod 2, (∀ ℓ ∈ E, evalAff ℓ z = 0) →
      ∃ C ∈ out (fun j => evalAff (msgAff j) z), ¬ ClauseSat (z2ToX z) C) :
    PCRefutable (F ∪ {p | ∃ ℓ ∈ E, p = affPoly ℓ}) (J.card + (b' * M + b')) := by
  have hgen : ∀ (J' : Finset (Fin b)) (E' : List (Aff V)),
      (∀ ℓ ∈ E, ℓ ∈ E') →
      (∀ j ∈ J, j ∉ J' → ∃ c : ZMod 2, ((msgAff j).1, (msgAff j).2 + c) ∈ E') →
      PCRefutable (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) (J'.card + (b' * M + b')) := by
    intro J'
    induction J' using Finset.induction_on with
    | empty =>
      intro E' hEE' hfix
      simp only [Finset.card_empty, zero_add]
      by_cases hsat : ∃ z : V → ZMod 2, ∀ ℓ ∈ E', evalAff ℓ z = 0
      · obtain ⟨z₀, hz₀⟩ := hsat
        let y₀ : Fin b → ZMod 2 := fun j => evalAff (msgAff j) z₀
        have hz₀E : ∀ ℓ ∈ E, evalAff ℓ z₀ = 0 := fun ℓ hℓ => hz₀ ℓ (hEE' ℓ hℓ)
        have hM : (out y₀).card ≤ M := hcap z₀ hz₀E
        have hcov' : ∀ z : V → ZMod 2, (∀ ℓ ∈ E', evalAff ℓ z = 0) →
            ∃ C ∈ out y₀, ¬ ClauseSat (z2ToX z) C := by
          intro z hz
          have hzE : ∀ ℓ ∈ E, evalAff ℓ z = 0 := fun ℓ hℓ => hz ℓ (hEE' ℓ hℓ)
          have hyeq : (fun j => evalAff (msgAff j) z) = y₀ := by
            refine hconst z z₀ hzE hz₀E fun j hj => ?_
            obtain ⟨c, hc⟩ := hfix j hj (Finset.notMem_empty _)
            have h1 : evalAff (msgAff j) z + c = 0 := by simpa [evalAff, add_assoc] using hz _ hc
            have h2 : evalAff (msgAff j) z₀ + c = 0 := by simpa [evalAff, add_assoc] using hz₀ _ hc
            have h3 : evalAff (msgAff j) z + evalAff (msgAff j) z₀ = 0 := by
              have hc0 : c + c = 0 := z2_add_self c
              calc evalAff (msgAff j) z + evalAff (msgAff j) z₀
                  = evalAff (msgAff j) z + evalAff (msgAff j) z₀ + (c + c) := by rw [hc0, add_zero]
                _ = (evalAff (msgAff j) z + c) + (evalAff (msgAff j) z₀ + c) := by ring
                _ = 0 := by rw [h1, h2, add_zero]
            rcases z2_cases (evalAff (msgAff j) z) with ha | ha <;>
              rcases z2_cases (evalAff (msgAff j) z₀) with hb | hb <;> simp_all
          rw [← hyeq]
          exact hcov z hzE
        have hpc := pc_of_cover hbool b' hb' (out y₀) (hU y₀) E' hcov'
        exact pc_mono subset_rfl (by nlinarith) hpc
      · exact pc_mono subset_rfl (by omega)
          (pc_unsat_aff E' (fun ℓ hℓ => Or.inr ⟨ℓ, hℓ, rfl⟩) hsat)
    | insert j J' hj ih =>
      intro E' hEE' hfix
      rw [Finset.card_insert_of_notMem hj]
      have h0 : PCRefutable ((F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪ {affPoly (msgAff j)})
          (J'.card + (b' * M + b')) := by
        have hset : (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪ {affPoly (msgAff j)} =
            F ∪ {p | ∃ ℓ ∈ msgAff j :: E', p = affPoly ℓ} := by
          ext p; simp [or_left_comm]
        rw [hset]
        refine ih (msgAff j :: E') (fun ℓ hℓ => List.mem_cons_of_mem _ (hEE' ℓ hℓ)) ?_
        intro j' hj' hj'not
        by_cases heq : j' = j
        · subst heq
          refine ⟨0, ?_⟩
          simp
        · have hj'in : j' ∉ insert j J' := by simp [heq, hj'not]
          obtain ⟨c, hc⟩ := hfix j' hj' hj'in
          exact ⟨c, List.mem_cons_of_mem _ hc⟩
      have h1 : PCRefutable ((F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪
          {affPoly ((msgAff j).1, (msgAff j).2 + 1)})
          (J'.card + (b' * M + b')) := by
        have hset : (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) ∪ {affPoly ((msgAff j).1, (msgAff j).2 + 1)} =
            F ∪ {p | ∃ ℓ ∈ ((msgAff j).1, (msgAff j).2 + 1) :: E', p = affPoly ℓ} := by
          ext p; simp [or_comm, or_left_comm]
        rw [hset]
        refine ih (((msgAff j).1, (msgAff j).2 + 1) :: E')
          (fun ℓ hℓ => List.mem_cons_of_mem _ (hEE' ℓ hℓ)) ?_
        intro j' hj' hj'not
        by_cases heq : j' = j
        · subst heq
          exact ⟨1, List.mem_cons_self⟩
        · have hj'in : j' ∉ insert j J' := by simp [heq, hj'not]
          obtain ⟨c, hc⟩ := hfix j' hj' hj'in
          exact ⟨c, List.mem_cons_of_mem _ hc⟩
      exact pc_mono subset_rfl (by omega)
        (pc_branch (fun u => Or.inl (hbool u)) (by omega) (msgAff j) h0 h1)
  exact hgen J E (fun _ h => h) (fun j hj hnj => absurd hj hnj)

lemma pc_of_circuit_exact {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (MvPolynomial V (ZMod 2))}
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (b b' M flat : ℕ) (hb' : 1 ≤ b')
    (S : Finset (Fin b → ZMod 2))
    (hflat : ∀ (U : Submodule (ZMod 2) (Fin b → ZMod 2)) (y : Fin b → ZMod 2),
      (∀ u ∈ U, y + u ∈ S) → Module.finrank (ZMod 2) U ≤ flat)
    (H : Circuit) (pick : Fin b → Fin (2 + Fintype.card V + H.size))
    (out : (Fin b → ZMod 2) → Finset (Clause V))
    (hrb : ReadsBack (2 + Fintype.card V) H)
    (hval : ∀ g ∈ H.gates, gateValid g)
    (hU : ∀ y : Fin b → ZMod 2, ∀ C ∈ out y, clausePoly C ∈ F ∧ C.card ≤ b')
    (hcap : ∀ y ∈ S, (out y).card ≤ M)
    (hmsgS : ∀ x : V → Bool, (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)) ∈ S)
    (hexact : ∀ x : V → Bool,
      ∃ C ∈ out (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)),
        ¬ ClauseSat x C) :
    PCRefutable F (countAndOr H.gates + flat + b' * M + b') := by
  have hrec : ∀ (gs₂ gs₁ : List Gate), gs₁ ++ gs₂ = H.gates →
      ∀ (E : List (Aff V)) (waff : List (Aff V)),
        waff.length = 2 + Fintype.card V + gs₁.length →
        (∀ x : V → Bool, (∀ ℓ ∈ E, evalAff ℓ (xToZ2 x) = 0) →
          ∀ i < 2 + Fintype.card V + gs₁.length,
            boolToZ2 ((wiresOf gs₁ (inBits x)).getD i false) = evalAff (waff.getD i (0, 0)) (xToZ2 x)) →
        PCRefutable (F ∪ {p | ∃ ℓ ∈ E, p = affPoly ℓ}) (countAndOr gs₂ + flat + b' * M + b') := by
    intro gs₂
    induction gs₂ with
    | nil =>
      intro gs₁ hgs E waff hwaff hmatch
      rw [List.append_nil] at hgs
      subst hgs
      simp only [countAndOr_nil, zero_add]
      by_cases hsat : ∃ z : V → ZMod 2, ∀ ℓ ∈ E, evalAff ℓ z = 0
      · obtain ⟨z₀, hz₀⟩ := hsat
        let msgAff : Fin b → Aff V := fun j => waff.getD (pick j).val (0, 0)
        have hmsg_eq : ∀ z : V → ZMod 2, (∀ ℓ ∈ E, evalAff ℓ z = 0) →
            (fun j => evalAff (msgAff j) z) =
              (fun j => boolToZ2 ((H.wires (inBits (z2ToX z))).getD (pick j).val false)) := by
          intro z hz
          funext j
          have hz' : ∀ ℓ ∈ E, evalAff ℓ (xToZ2 (z2ToX z)) = 0 := by
            simpa [xToZ2_z2ToX] using hz
          have hm := hmatch (z2ToX z) hz' (pick j).val (pick j).isLt
          rw [xToZ2_z2ToX] at hm
          exact hm.symm
        let Wlin : Submodule (ZMod 2) (V → ZMod 2) :=
          { carrier := {v | ∀ ℓ ∈ E, affLin ℓ v = 0}, add_mem' := fun ha hb ℓ hℓ => by rw [map_add, ha ℓ hℓ, hb ℓ hℓ, add_zero]
            zero_mem' := fun ℓ _ => map_zero _
            smul_mem' := fun c _ ha ℓ hℓ => by rw [map_smul, ha ℓ hℓ, smul_zero] }
        let Φ : Wlin →ₗ[ZMod 2] (Fin b → ZMod 2) :=
          (LinearMap.pi (fun j => affLin (msgAff j))).domRestrict Wlin
        let U : Submodule (ZMod 2) (Fin b → ZMod 2) := LinearMap.range Φ
        let y₀ : Fin b → ZMod 2 := fun j => evalAff (msgAff j) z₀
        have hUS : ∀ u ∈ U, y₀ + u ∈ S := by
          rintro _ ⟨⟨v, hv⟩, rfl⟩
          have hz' : ∀ ℓ ∈ E, evalAff ℓ (z₀ + v) = 0 := by
            intro ℓ hℓ
            rw [evalAff_eq_zero_iff, map_add, hv ℓ hℓ, add_zero]
            exact (evalAff_eq_zero_iff ℓ z₀).mp (hz₀ ℓ hℓ)
          have hyeq : y₀ + Φ ⟨v, hv⟩ = fun j => evalAff (msgAff j) (z₀ + v) := by
            funext j
            change (affLin (msgAff j) z₀ + (msgAff j).2) + affLin (msgAff j) v =
              affLin (msgAff j) (z₀ + v) + (msgAff j).2
            rw [map_add]
            ring
          rw [hyeq, hmsg_eq (z₀ + v) hz']
          exact hmsgS (z2ToX (z₀ + v))
        have hdim_le : Module.finrank (ZMod 2) U ≤ flat := hflat U y₀ hUS
        obtain ⟨J, hJcard, hJinj⟩ := exists_inj_coords U
        have hpc := pc_of_flat_branch hbool b b' M hb' msgAff out hU E J
          (fun z₁ z₂ hz₁ hz₂ hJeq => by
            have hdiff : z₁ + z₂ ∈ Wlin := by
              intro ℓ hℓ
              rw [map_add, (evalAff_eq_zero_iff ℓ z₁).mp (hz₁ ℓ hℓ),
                (evalAff_eq_zero_iff ℓ z₂).mp (hz₂ ℓ hℓ), z2_add_self]
            have hmemU : Φ ⟨z₁ + z₂, hdiff⟩ ∈ U := ⟨⟨z₁ + z₂, hdiff⟩, rfl⟩
            have hzeroJ : ∀ j ∈ J, Φ ⟨z₁ + z₂, hdiff⟩ j = 0 := by
              intro j hj
              change affLin (msgAff j) (z₁ + z₂) = 0
              rw [map_add]
              have heq := hJeq j hj
              have h1 : affLin (msgAff j) z₁ + (msgAff j).2 = affLin (msgAff j) z₂ + (msgAff j).2 := heq
              have h2 : affLin (msgAff j) z₁ = affLin (msgAff j) z₂ := add_right_cancel h1
              rw [h2, z2_add_self]
            have hΦ0 : Φ ⟨z₁ + z₂, hdiff⟩ = 0 := hJinj _ hmemU hzeroJ
            funext j
            have hj0 : affLin (msgAff j) (z₁ + z₂) = 0 := congrFun hΦ0 j
            rw [map_add] at hj0
            have hlin : affLin (msgAff j) z₁ = affLin (msgAff j) z₂ := by
              have h := congrArg (fun t => t + affLin (msgAff j) z₂) hj0
              simpa [add_assoc, z2_add_self] using h
            change affLin (msgAff j) z₁ + (msgAff j).2 = affLin (msgAff j) z₂ + (msgAff j).2
            rw [hlin])
          (fun z hz => by
            rw [hmsg_eq z hz]
            exact hcap _ (hmsgS (z2ToX z)))
          (fun z hz => by
            rw [hmsg_eq z hz]
            exact hexact (z2ToX z))
        exact pc_mono subset_rfl (by omega) hpc
      · exact pc_mono subset_rfl (by omega)
          (pc_unsat_aff E (fun ℓ hℓ => Or.inr ⟨ℓ, hℓ, rfl⟩) hsat)
    | cons g gs₂ ih =>
      intro gs₁ hgs E waff hwaff hmatch
      have hgs' : (gs₁ ++ [g]) ++ gs₂ = H.gates := by simp [hgs]
      have hrb_g : ∀ i ∈ g.inputs, i < 2 + Fintype.card V + gs₁.length := by
        intro i hi
        have hj : gs₁.length < H.gates.length := by rw [← hgs]; simp
        have h1 := hrb gs₁.length hj
        have hgat : gateAt H gs₁.length = g := by
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hj]
          simp [← hgs]
        rw [hgat] at h1
        exact h1 i hi
      have hgval : gateValid g := hval g (by rw [← hgs]; simp)
      have hlift : ∀ (newAff : Aff V) (E' : List (Aff V)),
          (∀ ℓ ∈ E, ℓ ∈ E') →
          (∀ x : V → Bool, (∀ ℓ ∈ E', evalAff ℓ (xToZ2 x) = 0) →
            boolToZ2 (g.op.eval (g.inputs.map fun i => (wiresOf gs₁ (inBits x)).getD i false)) =
              evalAff newAff (xToZ2 x)) →
          PCRefutable (F ∪ {p | ∃ ℓ ∈ E', p = affPoly ℓ}) (countAndOr gs₂ + flat + b' * M + b') := by
        intro newAff E' hEE' hnew
        refine ih (gs₁ ++ [g]) hgs' E' (waff ++ [newAff])
          (by rw [List.length_append, List.length_singleton, hwaff, List.length_append,
            List.length_singleton]; omega) ?_
        intro x hx i hi
        rw [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < 2 + Fintype.card V + gs₁.length
        · rw [wiresOf_prefix_getD gs₁ [g] (inBits x) i (by rw [inBits_length]; exact hlt)]
          have hw : (waff ++ [newAff]).getD i (0, 0) = waff.getD i (0, 0) := by
            rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hwaff]; omega),
              List.getElem_append_left (by omega), ← List.getD_eq_getElem _ _ (by omega)]
          rw [hw]
          exact hmatch x (fun ℓ hℓ => hx ℓ (hEE' ℓ hℓ)) i hlt
        · have hieq : i = 2 + Fintype.card V + gs₁.length := by omega
          subst hieq
          have hlast := wiresOf_last_getD gs₁ g (inBits x)
          rw [inBits_length] at hlast
          rw [hlast]
          have hw : (waff ++ [newAff]).getD (2 + Fintype.card V + gs₁.length) (0, 0) = newAff := by
            rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hwaff]; simp)]
            have h1 : (waff ++ [newAff])[2 + Fintype.card V + gs₁.length]'(by
                rw [List.length_append, hwaff]; simp) =
                ([newAff])[2 + Fintype.card V + gs₁.length - waff.length]'(by rw [hwaff]; simp) :=
              List.getElem_append_right (by omega)
            rw [h1]; simp [hwaff]
          rw [hw]
          exact hnew x hx
      rw [countAndOr_cons]
      rcases hgval with ⟨hor, hlen2⟩ | hmod2 | ⟨hnot, hlen1⟩
      · obtain ⟨u, v, huv⟩ : ∃ u v, g.inputs = [u, v] := by
          cases h1 : g.inputs with
          | nil => simp [h1] at hlen2
          | cons u tl =>
            cases h2 : tl with
            | nil => simp [h1, h2] at hlen2
            | cons v tl2 =>
              cases tl2 with
              | nil => exact ⟨u, v, rfl⟩
              | cons _ _ => simp [h1, h2] at hlen2
        have hu_lt : u < 2 + Fintype.card V + gs₁.length := hrb_g u (by rw [huv]; simp)
        have hv_lt : v < 2 + Fintype.card V + gs₁.length := hrb_g v (by rw [huv]; simp)
        let ℓu := waff.getD u (0, 0)
        have hif : (if g.op = .and ∨ g.op = .or then 1 else 0) = 1 := by simp [hor]
        rw [hif]
        have hdeg_eq : countAndOr gs₂ + 1 + flat + b' * M + b' =
            (countAndOr gs₂ + flat + b' * M + b') + 1 := by omega
        rw [hdeg_eq]
        have hset0 : (F ∪ {p | ∃ ℓ ∈ E, p = affPoly ℓ}) ∪ {affPoly ℓu} =
            F ∪ {p | ∃ ℓ ∈ ℓu :: E, p = affPoly ℓ} := by
          ext p; simp [or_comm, or_left_comm]
        have hset1 : (F ∪ {p | ∃ ℓ ∈ E, p = affPoly ℓ}) ∪ {affPoly (ℓu.1, ℓu.2 + 1)} =
            F ∪ {p | ∃ ℓ ∈ (ℓu.1, ℓu.2 + 1) :: E, p = affPoly ℓ} := by
          ext p; simp [or_comm, or_left_comm]
        have hu0 : ∀ x : V → Bool, (∀ ℓ ∈ ℓu :: E, evalAff ℓ (xToZ2 x) = 0) →
            boolToZ2 ((wiresOf gs₁ (inBits x)).getD u false) = 0 := by
          intro x hx
          rw [hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) u hu_lt]
          exact hx ℓu List.mem_cons_self
        have hu1 : ∀ x : V → Bool, (∀ ℓ ∈ (ℓu.1, ℓu.2 + 1) :: E, evalAff ℓ (xToZ2 x) = 0) →
            boolToZ2 ((wiresOf gs₁ (inBits x)).getD u false) = 1 := by
          intro x hx
          rw [hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) u hu_lt]
          have h0 : evalAff ℓu (xToZ2 x) + 1 = 0 := by
            simpa [evalAff, add_assoc] using hx (ℓu.1, ℓu.2 + 1) List.mem_cons_self
          rcases z2_cases (evalAff ℓu (xToZ2 x)) with h | h
          · rw [h, zero_add] at h0; exact absurd h0 one_ne_zero
          · exact h
        rcases hor with hand | hor'
        · refine pc_branch (fun w => Or.inl (hbool w)) (by omega) ℓu ?_ ?_
          · rw [hset0]
            refine hlift (0, 0) (ℓu :: E) (fun _ h => List.mem_cons_of_mem _ h) fun x hx => ?_
            rw [hand, huv]
            exact eval_and_gate_zero _ _ u v (hu0 x hx)
          · rw [hset1]
            refine hlift (waff.getD v (0, 0)) ((ℓu.1, ℓu.2 + 1) :: E)
              (fun _ h => List.mem_cons_of_mem _ h) fun x hx => ?_
            rw [hand, huv]
            exact eval_and_gate_one _ waff _ u v (hu1 x hx)
              (hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) v hv_lt)
        · refine pc_branch (fun w => Or.inl (hbool w)) (by omega) ℓu ?_ ?_
          · rw [hset0]
            refine hlift (waff.getD v (0, 0)) (ℓu :: E) (fun _ h => List.mem_cons_of_mem _ h) fun x hx => ?_
            rw [hor', huv]
            exact eval_or_gate_zero _ waff _ u v (hu0 x hx)
              (hmatch x (fun ℓ hℓ => hx ℓ (List.mem_cons_of_mem _ hℓ)) v hv_lt)
          · rw [hset1]
            refine hlift (0, 1) ((ℓu.1, ℓu.2 + 1) :: E)
              (fun _ h => List.mem_cons_of_mem _ h) fun x hx => ?_
            rw [hor', huv]
            exact eval_or_gate_one _ _ u v (hu1 x hx)
      · have hif : (if g.op = .and ∨ g.op = .or then 1 else 0) = 0 := by simp [hmod2]
        rw [hif, add_zero]
        refine hlift (mod2Aff (g.inputs.map fun i => waff.getD i (0, 0))) E (fun _ h => h) fun x hx => ?_
        rw [hmod2]
        exact eval_mod2_gate _ waff _ g.inputs (fun i hi => hmatch x hx i (hrb_g i hi))
      · obtain ⟨u, hu⟩ : ∃ u, g.inputs = [u] := by
          cases h1 : g.inputs with
          | nil => simp [h1] at hlen1
          | cons u tl =>
            cases tl with
            | nil => exact ⟨u, rfl⟩
            | cons _ _ => simp [h1] at hlen1
        have hu_lt : u < 2 + Fintype.card V + gs₁.length := hrb_g u (by rw [hu]; simp)
        have hif : (if g.op = .and ∨ g.op = .or then 1 else 0) = 0 := by simp [hnot]
        rw [hif, add_zero]
        refine hlift (notAff (waff.getD u (0, 0))) E (fun _ h => h) fun x hx => ?_
        rw [hnot, hu]
        exact eval_not_gate _ waff _ u (hmatch x hx u hu_lt)
  have h0 := hrec H.gates [] rfl [] (inputAffs V) (by simp [inputAffs_length])
    (fun x _ i hi => by simpa [wiresOf_nil] using inputAffs_match x i hi)
  have hF : F ∪ {p | ∃ ℓ ∈ ([] : List (Aff V)), p = affPoly ℓ} = F := by ext p; simp
  rwa [hF] at h0

lemma funGraphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hLd : LeftDegLe G b)
    (C : Clause (GEdge G)) (hC : C ∈ funGraphPHP G) : C.card ≤ max 2 b := by
  rcases hC with (⟨i, rfl⟩ | ⟨e, e', _, _, rfl⟩) | ⟨e, e', _, _, rfl⟩
  · let Sp : Clause (GEdge G) := Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)
    have hinj : Set.InjOn (fun l : Literal (GEdge G) => l.1.1.2) (Sp : Set _) := by
      rintro ⟨⟨⟨i₁, j₁⟩, h₁⟩, b₁⟩ hm₁ ⟨⟨⟨i₂, j₂⟩, h₂⟩, b₂⟩ hm₂ heq
      simp only [Finset.mem_coe, Sp, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
      dsimp only at heq
      subst heq
      rcases hm₁ with ⟨rfl, rfl⟩
      rcases hm₂ with ⟨rfl, rfl⟩
      rfl
    have hsub : Sp.image (fun l => l.1.1.2) ⊆ G i := by
      intro j hj
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
      have h1 := (Finset.mem_filter.mp hl).2.1
      rw [← h1]
      exact l.1.2
    change Sp.card ≤ max 2 b
    calc Sp.card = (Sp.image (fun l => l.1.1.2)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (G i).card := Finset.card_le_card hsub
      _ ≤ b := hLd i
      _ ≤ max 2 b := le_max_right 2 b
  · exact (Finset.card_le_two).trans (le_max_left 2 b)
  · exact (Finset.card_le_two).trans (le_max_left 2 b)

lemma lower_bound_main (n b s₀ : ℕ) (hs₀ : 0 < s₀) (hn : s₀ ≤ n)
    (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b)
    (hExp : IsBdryExpander G (n / s₀) 2)
    (C : ℕ) (hC : 3 * s₀ * (max 2 b) ^ 2 ≤ C)
    (b_bits T h R : ℕ) (S : Finset (Fin b_bits → ZMod 2)) (cap : (Fin b_bits → ZMod 2) → ℕ)
    (hR : 1 ≤ R) (hS : S.Nonempty) (hcap1 : ∀ y ∈ S, 1 ≤ cap y)
    (H : Circuit) (pick : Fin b_bits → Fin (2 + Fintype.card (GEdge G) + H.size))
    (out : (Fin b_bits → ZMod 2) → Finset (Clause (GEdge G)))
    (hrb : ReadsBack (2 + Fintype.card (GEdge G)) H)
    (hval : ∀ g ∈ H.gates, gateValid g)
    (hT : countAndOr H.gates ≤ T)
    (hout : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ funGraphPHP G)
    (hmsgS : ∀ x : GEdge G → Bool,
      (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)) ∈ S)
    (μ : (GEdge G → Bool) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμpos : 0 < ∑ x, μ x)
    (hμsm : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v))))
    (hacc : (2 : ℝ) ^ h *
      (∑ x ∈ Finset.univ.filter (fun x : GEdge G → Bool =>
        @decide (∀ cl ∈ out (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)),
          ClauseSat x cl) (Classical.propDecidable _)), μ x) ≤ ∑ x, μ x) :
    let flat := sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b_bits → ZMod 2)) (y : Fin b_bits → ZMod 2),
      Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}
    let B := min (∑ y ∈ S, cap y) (T + S.sup cap + flat)
    let L := Nat.clog 2 (R + 1)
    min (n * L) h ≤ C * L * B := by
  intro flat B L
  let V := GEdge G
  let b' := max 2 b
  let M := S.sup cap
  let msg : (V → Bool) → (Fin b_bits → ZMod 2) :=
    fun x j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)
  let bad : Finset (V → Bool) := Finset.univ.filter (fun x : V → Bool =>
    @decide (∀ cl ∈ out (msg x), ClauseSat x cl) (Classical.propDecidable _))
  have hb'2 : 2 ≤ b' := le_max_left 2 b
  have hLd' : LeftDegLe G b' := fun i => (hLd i).trans (le_max_right 2 b)
  have hs1 : 1 ≤ n / s₀ := Nat.div_pos hn hs₀
  have hM1 : 1 ≤ M := by
    obtain ⟨y₀, hy₀⟩ := hS
    exact (hcap1 y₀ hy₀).trans (Finset.le_sup (f := cap) hy₀)
  have hsum1 : 1 ≤ ∑ y ∈ S, cap y := by
    obtain ⟨y₀, hy₀⟩ := hS
    exact (hcap1 y₀ hy₀).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy₀)
  have hL_ge : 1 ≤ L := by
    have h2 : 1 < R + 1 := by omega
    exact Nat.clog_pos (by omega) h2
  have hbound1 : min (n * L) h ≤ C * L * ∑ y ∈ S, cap y := by
    let U : Finset (Clause V) := S.biUnion out
    have hUcard : U.card ≤ ∑ y ∈ S, cap y :=
      (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun y hy => (hout y hy).1)
    by_cases hsat : ∃ x₀ : V → Bool, ∀ cl ∈ U, ClauseSat x₀ cl
    · obtain ⟨x₀, hx₀⟩ := hsat
      let eqs : List (Aff V) := U.toList.map (fun cl =>
        if h : ∃ l ∈ cl, x₀ l.1 = l.2 then
          let l := h.choose
          (Pi.single l.1 (1 : ZMod 2), if x₀ l.1 then 1 else 0)
        else (0, 0))
      have heqs_x0 : ∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x₀) = 0 := by
        intro ℓ hℓ
        obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hℓ
        have hclU : cl ∈ U := Finset.mem_toList.mp hcl
        have hclsat : ∃ l ∈ cl, x₀ l.1 = l.2 := hx₀ cl hclU
        rw [dite_eq_left hclsat]
        dsimp only
        rw [evalAff_single]
        cases hxl : x₀ hclsat.choose.1
        · simp [xToZ2, boolToZ2, hxl]
        · simp [xToZ2, boolToZ2, hxl, z2_add_self]
      have heqs_bad : ∀ x : V → Bool, (∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x) = 0) → x ∈ bad := by
        intro x hx
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        intro cl hcl
        have hclU : cl ∈ U := Finset.mem_biUnion.mpr ⟨msg x, hmsgS x, hcl⟩
        have hclsat : ∃ l ∈ cl, x₀ l.1 = l.2 := hx₀ cl hclU
        let l := hclsat.choose
        have hl : l ∈ cl ∧ x₀ l.1 = l.2 := hclsat.choose_spec
        have hmem : (Pi.single l.1 (1 : ZMod 2), if x₀ l.1 then 1 else 0) ∈ eqs := by
          refine List.mem_map.mpr ⟨cl, Finset.mem_toList.mpr hclU, ?_⟩
          rw [dite_eq_left hclsat]
        have h0 := hx _ hmem
        rw [evalAff_single] at h0
        have hxeq : x l.1 = x₀ l.1 := by
          cases hx0l : x₀ l.1
          · have h1 : boolToZ2 (x l.1) = 0 := by simpa [xToZ2, hx0l] using h0
            exact boolToZ2_injective h1
          · have h1 : boolToZ2 (x l.1) + 1 = 0 := by simpa [xToZ2, hx0l] using h0
            cases hx1 : x l.1
            · rw [hx1] at h1; exact absurd h1 one_ne_zero
            · rfl
        exact ⟨l, hl.1, hxeq.trans hl.2⟩
      have hh := syndrome_mass_bound R h hR μ hμ0 hμpos hμsm bad hacc eqs x₀ heqs_x0 heqs_bad
      have hlen : eqs.length = U.card := by simp [eqs]
      rw [hlen] at hh
      have h1 : h ≤ L * ∑ y ∈ S, cap y := hh.trans (Nat.mul_le_mul_left L hUcard)
      have hC1 : 1 ≤ C := by
        have hpos : 1 ≤ 3 * s₀ * b' ^ 2 := by
          have : 1 ≤ b' ^ 2 := Nat.one_le_pow _ _ (by omega)
          exact Nat.mul_pos (Nat.mul_pos (by omega) hs₀) this
        exact hpos.trans hC
      calc min (n * L) h ≤ h := min_le_right _ _
        _ ≤ L * ∑ y ∈ S, cap y := h1
        _ = 1 * L * ∑ y ∈ S, cap y := by ring
        _ ≤ C * L * ∑ y ∈ S, cap y := by gcongr
    · have hUF : ∀ cl ∈ U, clausePoly cl ∈ cnfSystem (funGraphPHP G) ∧ cl.card ≤ b' := by
        intro cl hcl
        obtain ⟨y, hyS, hcly⟩ := Finset.mem_biUnion.mp hcl
        have hclF : cl ∈ funGraphPHP G := (hout y hyS).2 cl hcly
        exact ⟨Or.inr ⟨cl, hclF, rfl⟩, funGraphPHP_width G b hLd cl hclF⟩
      have hpc := pc_of_cover (F := cnfSystem (funGraphPHP G)) (fun v => Or.inl ⟨v, rfl⟩)
        b' (by omega) U hUF [] (fun z _ => by
          by_contra hall
          push Not at hall
          exact hsat ⟨z2ToX z, hall⟩)
      have hFempty : cnfSystem (funGraphPHP G) ∪ {p | ∃ ℓ ∈ ([] : List (Aff V)), p = affPoly ℓ} =
          cnfSystem (funGraphPHP G) := by ext p; simp
      rw [hFempty] at hpc
      have hnotpc : ¬ (b' * (b' * U.card + b') ≤ n / s₀) := fun hle =>
        PEqualNP.Outside.L_pcx_407_aux.InlinePC.L049_inline (n + 1) n G (n / s₀) b' (b' * U.card + b') hExp hLd' hs1 hle hpc
      have hdiv : n / s₀ < b' * (b' * U.card + b') := by omega
      have hn_le : n ≤ C * ∑ y ∈ S, cap y := by
        have h1 : n < s₀ * (b' * (b' * U.card + b')) := by
          have h := Nat.lt_mul_of_div_lt hdiv hs₀
          rwa [Nat.mul_comm] at h
        have h2 : b' * (b' * U.card + b') ≤ 2 * b' ^ 2 * ∑ y ∈ S, cap y := by
          have hUc : U.card + 1 ≤ 2 * ∑ y ∈ S, cap y := by omega
          calc b' * (b' * U.card + b') = b' ^ 2 * (U.card + 1) := by ring
            _ ≤ b' ^ 2 * (2 * ∑ y ∈ S, cap y) := Nat.mul_le_mul_left _ hUc
            _ = 2 * b' ^ 2 * ∑ y ∈ S, cap y := by ring
        have h3 : n ≤ (2 * s₀ * b' ^ 2) * ∑ y ∈ S, cap y := by
          have h4 := (le_of_lt h1).trans (Nat.mul_le_mul_left s₀ h2)
          calc n ≤ s₀ * (2 * b' ^ 2 * ∑ y ∈ S, cap y) := h4
            _ = (2 * s₀ * b' ^ 2) * ∑ y ∈ S, cap y := by ring
        have h23 : 2 * s₀ * b' ^ 2 ≤ C := by
          have : 2 * s₀ * b' ^ 2 ≤ 3 * s₀ * b' ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
          exact this.trans hC
        exact h3.trans (Nat.mul_le_mul_right _ h23)
      calc min (n * L) h ≤ n * L := min_le_left _ _
        _ ≤ (C * ∑ y ∈ S, cap y) * L := Nat.mul_le_mul_right L hn_le
        _ = C * L * ∑ y ∈ S, cap y := by ring
  have hbound2 : min (n * L) h ≤ C * L * (T + M + flat) := by
    by_cases hbad_ne : bad.Nonempty
    · obtain ⟨x₀, hx₀bad⟩ := hbad_ne
      obtain ⟨eqs1, waff, heqs1_len, hwaff_len, hx₀1, hmatch⟩ :=
        circuit_slice_at_point H.gates hrb hval x₀
      let msgAff : Fin b_bits → Aff V := fun j => waff.getD (pick j).val (0, 0)
      let Wlin : Submodule (ZMod 2) (V → ZMod 2) :=
        { carrier := {v | ∀ ℓ ∈ eqs1, affLin ℓ v = 0}, add_mem' := fun ha hb ℓ hℓ => by rw [map_add, ha ℓ hℓ, hb ℓ hℓ, add_zero]
          zero_mem' := fun ℓ _ => map_zero _
          smul_mem' := fun c _ ha ℓ hℓ => by rw [map_smul, ha ℓ hℓ, smul_zero] }
      let Φ : Wlin →ₗ[ZMod 2] (Fin b_bits → ZMod 2) :=
        (LinearMap.pi (fun j => affLin (msgAff j))).domRestrict Wlin
      let U : Submodule (ZMod 2) (Fin b_bits → ZMod 2) := LinearMap.range Φ
      let y₀ : Fin b_bits → ZMod 2 := msg x₀
      have hmsg_eq : ∀ x : V → Bool, (∀ ℓ ∈ eqs1, evalAff ℓ (xToZ2 x) = 0) →
          msg x = fun j => evalAff (msgAff j) (xToZ2 x) := by
        intro x hx
        funext j
        exact hmatch x hx (pick j).val (pick j).isLt
      have hUS : ∀ u ∈ U, y₀ + u ∈ S := by
        rintro _ ⟨⟨v, hv⟩, rfl⟩
        let x' := z2ToX (xToZ2 x₀ + v)
        have hx' : ∀ ℓ ∈ eqs1, evalAff ℓ (xToZ2 x') = 0 := by
          intro ℓ hℓ
          rw [xToZ2_z2ToX, evalAff_eq_zero_iff, map_add, hv ℓ hℓ, add_zero]
          exact (evalAff_eq_zero_iff ℓ (xToZ2 x₀)).mp (hx₀1 ℓ hℓ)
        have hyeq : y₀ + Φ ⟨v, hv⟩ = msg x' := by
          change msg x₀ + Φ ⟨v, hv⟩ = msg x'
          rw [hmsg_eq x' hx', hmsg_eq x₀ hx₀1]
          funext j
          change (affLin (msgAff j) (xToZ2 x₀) + (msgAff j).2) + affLin (msgAff j) v =
            affLin (msgAff j) (xToZ2 x') + (msgAff j).2
          rw [xToZ2_z2ToX, map_add]
          ring
        rw [hyeq]
        exact hmsgS x'
      have hdim_le : Module.finrank (ZMod 2) U ≤ flat := flat_ge_of_affine S U y₀ hUS
      obtain ⟨J, hJcard, hJinj⟩ := exists_inj_coords U
      let eqs2 : List (Aff V) := J.toList.map (fun j =>
        ((msgAff j).1, (msgAff j).2 + y₀ j))
      have hx₀sat : ∀ cl ∈ out y₀, ClauseSat x₀ cl := by
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx₀bad
        exact hx₀bad
      let eqs3 : List (Aff V) := (out y₀).toList.map (fun cl =>
        if hcl : ∃ l ∈ cl, x₀ l.1 = l.2 then
          let l := hcl.choose
          (Pi.single l.1 (1 : ZMod 2), if x₀ l.1 then 1 else 0)
        else (0, 0))
      let eqs := eqs1 ++ eqs2 ++ eqs3
      have heqs_x0 : ∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x₀) = 0 := by
        intro ℓ hℓ
        rcases List.mem_append.mp hℓ with h12 | h3
        · rcases List.mem_append.mp h12 with h1 | h2
          · exact hx₀1 ℓ h1
          · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h2
            have hyj : evalAff (msgAff j) (xToZ2 x₀) = y₀ j := (congrFun (hmsg_eq x₀ hx₀1) j).symm
            change (∑ v : V, (msgAff j).1 v * xToZ2 x₀ v) + ((msgAff j).2 + y₀ j) = 0
            rw [← add_assoc]
            change evalAff (msgAff j) (xToZ2 x₀) + y₀ j = 0
            rw [hyj, z2_add_self]
        · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp h3
          have hclsat : ∃ l ∈ cl, x₀ l.1 = l.2 := hx₀sat cl (Finset.mem_toList.mp hcl)
          rw [dite_eq_left hclsat]
          dsimp only
          rw [evalAff_single]
          cases hxl : x₀ hclsat.choose.1
          · simp [xToZ2, boolToZ2, hxl]
          · simp [xToZ2, boolToZ2, hxl, z2_add_self]
      have heqs_bad : ∀ x : V → Bool, (∀ ℓ ∈ eqs, evalAff ℓ (xToZ2 x) = 0) → x ∈ bad := by
        intro x hx
        have hx1 : ∀ ℓ ∈ eqs1, evalAff ℓ (xToZ2 x) = 0 :=
          fun ℓ hℓ => hx ℓ (List.mem_append_left _ (List.mem_append_left _ hℓ))
        have hmsg_const : msg x = y₀ := by
          have hdiff : xToZ2 x + xToZ2 x₀ ∈ Wlin := by
            intro ℓ hℓ
            rw [map_add, (evalAff_eq_zero_iff ℓ _).mp (hx1 ℓ hℓ),
              (evalAff_eq_zero_iff ℓ _).mp (hx₀1 ℓ hℓ), z2_add_self]
          have hΦ0 : Φ ⟨xToZ2 x + xToZ2 x₀, hdiff⟩ = 0 := by
            refine hJinj _ ⟨⟨xToZ2 x + xToZ2 x₀, hdiff⟩, rfl⟩ fun j hj => ?_
            have hmem2 : ((msgAff j).1, (msgAff j).2 + y₀ j) ∈ eqs2 :=
              List.mem_map.mpr ⟨j, Finset.mem_toList.mpr hj, rfl⟩
            have h0 := hx _ (List.mem_append_left _ (List.mem_append_right _ hmem2))
            have h1 : evalAff (msgAff j) (xToZ2 x) + y₀ j = 0 := by
              simpa [evalAff, add_assoc] using h0
            have hyj : evalAff (msgAff j) (xToZ2 x₀) = y₀ j := (congrFun (hmsg_eq x₀ hx₀1) j).symm
            change affLin (msgAff j) (xToZ2 x + xToZ2 x₀) = 0
            rw [map_add]
            have h2 : affLin (msgAff j) (xToZ2 x) + (msgAff j).2 + (affLin (msgAff j) (xToZ2 x₀) + (msgAff j).2) = 0 := by
              rw [← hyj] at h1; exact h1
            have hc0 : (msgAff j).2 + (msgAff j).2 = 0 := z2_add_self _
            calc affLin (msgAff j) (xToZ2 x) + affLin (msgAff j) (xToZ2 x₀)
                = affLin (msgAff j) (xToZ2 x) + affLin (msgAff j) (xToZ2 x₀) + ((msgAff j).2 + (msgAff j).2) := by
                  rw [hc0, add_zero]
              _ = affLin (msgAff j) (xToZ2 x) + (msgAff j).2 + (affLin (msgAff j) (xToZ2 x₀) + (msgAff j).2) := by
                  ring
              _ = 0 := h2
          change msg x = msg x₀
          rw [hmsg_eq x hx1, hmsg_eq x₀ hx₀1]
          funext j
          have hj0 : affLin (msgAff j) (xToZ2 x) + affLin (msgAff j) (xToZ2 x₀) = 0 := by
            have := congrFun hΦ0 j
            simpa [Φ, map_add] using this
          have hlin : affLin (msgAff j) (xToZ2 x) = affLin (msgAff j) (xToZ2 x₀) := by
            have h := congrArg (fun t => t + affLin (msgAff j) (xToZ2 x₀)) hj0
            simpa [add_assoc, z2_add_self] using h
          change affLin (msgAff j) (xToZ2 x) + (msgAff j).2 =
            affLin (msgAff j) (xToZ2 x₀) + (msgAff j).2
          rw [hlin]
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        intro cl hcl
        rw [hmsg_const] at hcl
        have hclsat : ∃ l ∈ cl, x₀ l.1 = l.2 := hx₀sat cl hcl
        let l := hclsat.choose
        have hl : l ∈ cl ∧ x₀ l.1 = l.2 := hclsat.choose_spec
        have hmem3 : (Pi.single l.1 (1 : ZMod 2), if x₀ l.1 then 1 else 0) ∈ eqs3 := by
          refine List.mem_map.mpr ⟨cl, Finset.mem_toList.mpr hcl, ?_⟩
          rw [dite_eq_left hclsat]
        have h0 := hx _ (List.mem_append_right _ hmem3)
        rw [evalAff_single] at h0
        have hxeq : x l.1 = x₀ l.1 := by
          cases hx0l : x₀ l.1
          · have h1 : boolToZ2 (x l.1) = 0 := by simpa [xToZ2, hx0l] using h0
            exact boolToZ2_injective h1
          · have h1 : boolToZ2 (x l.1) + 1 = 0 := by simpa [xToZ2, hx0l] using h0
            cases hx1' : x l.1
            · rw [hx1'] at h1; exact absurd h1 one_ne_zero
            · rfl
        exact ⟨l, hl.1, hxeq.trans hl.2⟩
      have hh := syndrome_mass_bound R h hR μ hμ0 hμpos hμsm bad hacc eqs x₀ heqs_x0 heqs_bad
      have hlen_le : eqs.length ≤ T + M + flat := by
        have hl1 : eqs1.length ≤ T := heqs1_len.trans hT
        have hl2 : eqs2.length ≤ flat := by
          have : eqs2.length = J.card := by simp [eqs2]
          omega
        have hl3 : eqs3.length ≤ M := by
          have : eqs3.length = (out y₀).card := by simp [eqs3]
          have h1 : (out y₀).card ≤ cap y₀ := (hout y₀ (hmsgS x₀)).1
          have h2 : cap y₀ ≤ M := Finset.le_sup (f := cap) (hmsgS x₀)
          omega
        simp only [eqs, List.length_append]
        omega
      have hC1 : 1 ≤ C := by
        have hpos : 1 ≤ 3 * s₀ * b' ^ 2 := by
          have : 1 ≤ b' ^ 2 := Nat.one_le_pow _ _ (by omega)
          exact Nat.mul_pos (Nat.mul_pos (by omega) hs₀) this
        exact hpos.trans hC
      calc min (n * L) h ≤ h := min_le_right _ _
        _ ≤ L * eqs.length := hh
        _ ≤ L * (T + M + flat) := Nat.mul_le_mul_left L hlen_le
        _ = 1 * L * (T + M + flat) := by ring
        _ ≤ C * L * (T + M + flat) := by gcongr
    ·
      have hexact : ∀ x : V → Bool, ∃ cl ∈ out (msg x), ¬ ClauseSat x cl := by
        intro x
        by_contra hall
        push Not at hall
        apply hbad_ne
        exact ⟨x, by simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]; exact hall⟩
      let out' : (Fin b_bits → ZMod 2) → Finset (Clause V) := fun y => if y ∈ S then out y else ∅
      have hpc := pc_of_circuit_exact (F := cnfSystem (funGraphPHP G)) (fun v => Or.inl ⟨v, rfl⟩)
        b_bits b' M flat (by omega) S (fun U y hUS => flat_ge_of_affine S U y hUS)
        H pick out' hrb hval
        (fun y cl hcl => by
          by_cases hy : y ∈ S
          · simp only [out', hy, ↓reduceIte] at hcl
            have hclF := (hout y hy).2 cl hcl
            exact ⟨Or.inr ⟨cl, hclF, rfl⟩, funGraphPHP_width G b hLd cl hclF⟩
          · simp [out', hy] at hcl)
        (fun y hy => by
          simp only [out', hy, ↓reduceIte]
          exact (hout y hy).1.trans (Finset.le_sup (f := cap) hy))
        hmsgS
        (fun x => by
          have hy := hmsgS x
          simp only [out', hy, ↓reduceIte]
          exact hexact x)
      have hpc' : PCRefutable (cnfSystem (funGraphPHP G)) (T + flat + b' * M + b') :=
        pc_mono subset_rfl (by omega) hpc
      have hnotpc : ¬ (b' * (T + flat + b' * M + b') ≤ n / s₀) := fun hle =>
        PEqualNP.Outside.L_pcx_407_aux.InlinePC.L049_inline (n + 1) n G (n / s₀) b' (T + flat + b' * M + b')
          hExp hLd' hs1 hle hpc'
      have hdiv : n / s₀ < b' * (T + flat + b' * M + b') := by omega
      have hn_le : n ≤ C * (T + M + flat) := by
        have h1 : n < s₀ * (b' * (T + flat + b' * M + b')) := by
          have h := Nat.lt_mul_of_div_lt hdiv hs₀
          rwa [Nat.mul_comm] at h
        have h2 : T + flat + b' * M + b' ≤ 2 * b' * (T + M + flat) := by
          have hTf : T + flat ≤ b' * (T + flat) := Nat.le_mul_of_pos_left _ (by omega)
          have hbM : b' * M + b' ≤ 2 * b' * M := by
            calc b' * M + b' = b' * (M + 1) := by ring
              _ ≤ b' * (2 * M) := Nat.mul_le_mul_left _ (by omega)
              _ = 2 * b' * M := by ring
          calc T + flat + b' * M + b' = (T + flat) + (b' * M + b') := by ring
            _ ≤ b' * (T + flat) + 2 * b' * M := Nat.add_le_add hTf hbM
            _ ≤ 2 * b' * (T + flat) + 2 * b' * M :=
                Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
            _ = 2 * b' * (T + M + flat) := by ring
        have h3 : n ≤ (2 * s₀ * b' ^ 2) * (T + M + flat) := by
          have h4 := (le_of_lt h1).trans (Nat.mul_le_mul_left s₀ (Nat.mul_le_mul_left b' h2))
          calc n ≤ s₀ * (b' * (2 * b' * (T + M + flat))) := h4
            _ = (2 * s₀ * b' ^ 2) * (T + M + flat) := by ring
        have h23 : 2 * s₀ * b' ^ 2 ≤ C := by
          have : 2 * s₀ * b' ^ 2 ≤ 3 * s₀ * b' ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
          exact this.trans hC
        exact h3.trans (Nat.mul_le_mul_right _ h23)
      calc min (n * L) h ≤ n * L := min_le_left _ _
        _ ≤ (C * (T + M + flat)) * L := Nat.mul_le_mul_right L hn_le
        _ = C * L * (T + M + flat) := by ring
  by_cases hmin : ∑ y ∈ S, cap y ≤ T + M + flat
  · have hBeq : B = ∑ y ∈ S, cap y := min_eq_left hmin
    rw [hBeq]
    exact hbound1
  · have hBeq : B = T + M + flat := min_eq_right (le_of_not_ge hmin)
    rw [hBeq]
    exact hbound2

end CircuitAffineAndLowerBound

section UpperBound

def pigeonClause {m N : ℕ} (G : BipGraph m N) (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

lemma pigeonClause_mem {m N : ℕ} (G : BipGraph m N) (i : Fin m) :
    pigeonClause G i ∈ funGraphPHP G :=
  Or.inl (Or.inl ⟨i, rfl⟩)

lemma funGraphPHP_unsat {m N : ℕ} (G : BipGraph m N) (hNm : N < m) :
    ¬ Satisfiable (funGraphPHP G) := by
  rintro ⟨a, ha⟩
  have hex : ∀ i : Fin m, ∃ j : Fin N, ∃ hj : j ∈ G i, a ⟨(i, j), hj⟩ = true := by
    intro i
    obtain ⟨l, hl, htrue⟩ := ha (pigeonClause G i) (pigeonClause_mem G i)
    simp only [pigeonClause, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases l with ⟨⟨⟨i', j⟩, hj⟩, b⟩
    dsimp only at hl htrue
    rcases hl with ⟨rfl, rfl⟩
    exact ⟨j, hj, htrue⟩
  let f : Fin m → Fin N := fun i => (hex i).choose
  have hf_inj : Function.Injective f := by
    intro i₁ i₂ heq
    by_contra hne
    have h1 := (hex i₁).choose_spec
    have h2 := (hex i₂).choose_spec
    let e₁ : GEdge G := ⟨(i₁, f i₁), h1.choose⟩
    let e₂ : GEdge G := ⟨(i₂, f i₂), h2.choose⟩
    have hcl : ({(e₁, false), (e₂, false)} : Clause (GEdge G)) ∈ funGraphPHP G :=
      Or.inl (Or.inr ⟨e₁, e₂, heq, hne, rfl⟩)
    obtain ⟨l, hl, hsat⟩ := ha _ hcl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have := h1.choose_spec
      simp [e₁] at hsat
      rw [this] at hsat
      exact Bool.noConfusion hsat
    · have := h2.choose_spec
      simp [e₂] at hsat
      rw [this] at hsat
      exact Bool.noConfusion hsat
  have hcard := Fintype.card_le_of_injective f hf_inj
  simp only [Fintype.card_fin] at hcard
  omega

lemma card_gedge_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hLd : LeftDegLe G b) :
    Fintype.card (GEdge G) ≤ b * m := by
  let S : Finset (Fin m × Fin N) := Finset.univ.filter (fun p => p.2 ∈ G p.1)
  have hcard : Fintype.card (GEdge G) = S.card := by
    rw [Fintype.card_subtype]
  rw [hcard]
  have hsub : S ⊆ (Finset.univ : Finset (Fin m)).biUnion (fun i => (G i).image (fun j => (i, j))) := by
    intro p hp
    have hmem : p.2 ∈ G p.1 := (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, hmem, rfl⟩⟩
  calc S.card ≤ ((Finset.univ : Finset (Fin m)).biUnion (fun i => (G i).image (fun j => (i, j)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin m, ((G i).image (fun j => (i, j))).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => Finset.card_image_le
    _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum fun i _ => hLd i
    _ = m * b := by simp
    _ = b * m := Nat.mul_comm _ _

lemma funGraphPHP_finset {n b : ℕ} (hn : 1 ≤ n) (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b) (hRd : RightDegLe G b) :
    ∃ Ffin : Finset (Clause (GEdge G)),
      (∀ C, C ∈ Ffin ↔ C ∈ funGraphPHP G) ∧ Ffin.card ≤ (3 * (max 2 b) ^ 2 + 2) * n := by
  let b' := max 2 b
  let Fp : Finset (Clause (GEdge G)) := Finset.univ.image (pigeonClause G)
  let edgesAtR (j : Fin n) : Finset (GEdge G) := Finset.univ.filter (fun e => e.1.2 = j)
  let edgesAtL (i : Fin (n + 1)) : Finset (GEdge G) := Finset.univ.filter (fun e => e.1.1 = i)
  let Fh : Finset (Clause (GEdge G)) :=
    (Finset.univ : Finset (Fin n)).biUnion (fun j =>
      ((edgesAtR j ×ˢ edgesAtR j).filter (fun p => p.1.1.1 ≠ p.2.1.1)).image
        (fun p => ({(p.1, false), (p.2, false)} : Clause (GEdge G))))
  let Ff : Finset (Clause (GEdge G)) :=
    (Finset.univ : Finset (Fin (n + 1))).biUnion (fun i =>
      ((edgesAtL i ×ˢ edgesAtL i).filter (fun p => p.1.1.2 ≠ p.2.1.2)).image
        (fun p => ({(p.1, false), (p.2, false)} : Clause (GEdge G))))
  refine ⟨Fp ∪ Fh ∪ Ff, ?_, ?_⟩
  · intro C
    constructor
    · intro hC
      simp only [Finset.mem_union] at hC
      rcases hC with (h1 | h2) | h3
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
        exact pigeonClause_mem G i
      · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp h2
        obtain ⟨⟨e₁, e₂⟩, hp, rfl⟩ := Finset.mem_image.mp hj
        simp only [Finset.mem_filter, Finset.mem_product, edgesAtR, Finset.mem_univ, true_and] at hp
        exact Or.inl (Or.inr ⟨e₁, e₂, hp.1.1.trans hp.1.2.symm, hp.2, rfl⟩)
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h3
        obtain ⟨⟨e₁, e₂⟩, hp, rfl⟩ := Finset.mem_image.mp hi
        simp only [Finset.mem_filter, Finset.mem_product, edgesAtL, Finset.mem_univ, true_and] at hp
        exact Or.inr ⟨e₁, e₂, hp.1.1.trans hp.1.2.symm, hp.2, rfl⟩
    · intro hC
      simp only [Finset.mem_union]
      rcases hC with (⟨i, rfl⟩ | ⟨e₁, e₂, hj, hne, rfl⟩) | ⟨e₁, e₂, hi, hne, rfl⟩
      · left; left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · left; right
        refine Finset.mem_biUnion.mpr ⟨e₁.1.2, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨(e₁, e₂), ?_, rfl⟩⟩
        simp [edgesAtR, hj, hne]
      · right
        refine Finset.mem_biUnion.mpr ⟨e₁.1.1, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨(e₁, e₂), ?_, rfl⟩⟩
        simp [edgesAtL, hi, hne]
  · have hFp : Fp.card ≤ n + 1 :=
      (Finset.card_image_le).trans (by simp)
    have hcardR : ∀ j : Fin n, (edgesAtR j).card ≤ b := by
      intro j
      have hinj : Set.InjOn (fun e : GEdge G => e.1.1) (edgesAtR j : Set (GEdge G)) := by
        rintro ⟨⟨i₁, j₁⟩, h₁⟩ hm₁ ⟨⟨i₂, j₂⟩, h₂⟩ hm₂ heq
        simp only [Finset.mem_coe, edgesAtR, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
        dsimp only at heq
        subst heq; subst hm₁; subst hm₂; rfl
      have hsub : (edgesAtR j).image (fun e => e.1.1) ⊆ rightNbrs G j := by
        intro i hi
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
        have hej : e.1.2 = j := (Finset.mem_filter.mp he).2
        rw [rightNbrs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hej ▸ e.2⟩
      calc (edgesAtR j).card = ((edgesAtR j).image (fun e => e.1.1)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (rightNbrs G j).card := Finset.card_le_card hsub
        _ ≤ b := hRd j
    have hcardL : ∀ i : Fin (n + 1), (edgesAtL i).card ≤ b := by
      intro i
      have hinj : Set.InjOn (fun e : GEdge G => e.1.2) (edgesAtL i : Set (GEdge G)) := by
        rintro ⟨⟨i₁, j₁⟩, h₁⟩ hm₁ ⟨⟨i₂, j₂⟩, h₂⟩ hm₂ heq
        simp only [Finset.mem_coe, edgesAtL, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
        dsimp only at heq
        subst heq; subst hm₁; subst hm₂; rfl
      have hsub : (edgesAtL i).image (fun e => e.1.2) ⊆ G i := by
        intro j hj
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
        have hei : e.1.1 = i := (Finset.mem_filter.mp he).2
        exact hei ▸ e.2
      calc (edgesAtL i).card = ((edgesAtL i).image (fun e => e.1.2)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (G i).card := Finset.card_le_card hsub
        _ ≤ b := hLd i
    have hFh : Fh.card ≤ n * b ^ 2 := by
      calc Fh.card ≤ ∑ j : Fin n, (((edgesAtR j ×ˢ edgesAtR j).filter _).image _).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ j : Fin n, (edgesAtR j ×ˢ edgesAtR j).card :=
            Finset.sum_le_sum fun j _ => (Finset.card_image_le).trans (Finset.card_filter_le _ _)
        _ ≤ ∑ _j : Fin n, b ^ 2 := Finset.sum_le_sum fun j _ => by
            rw [Finset.card_product, sq]
            exact Nat.mul_le_mul (hcardR j) (hcardR j)
        _ = n * b ^ 2 := by simp
    have hFf : Ff.card ≤ (n + 1) * b ^ 2 := by
      calc Ff.card ≤ ∑ i : Fin (n + 1), (((edgesAtL i ×ˢ edgesAtL i).filter _).image _).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ i : Fin (n + 1), (edgesAtL i ×ˢ edgesAtL i).card :=
            Finset.sum_le_sum fun i _ => (Finset.card_image_le).trans (Finset.card_filter_le _ _)
        _ ≤ ∑ _i : Fin (n + 1), b ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Finset.card_product, sq]
            exact Nat.mul_le_mul (hcardL i) (hcardL i)
        _ = (n + 1) * b ^ 2 := by simp
    have hbb' : b ≤ b' := le_max_right 2 b
    have hsq : b ^ 2 ≤ b' ^ 2 := Nat.pow_le_pow_left hbb' 2
    have hunion : (Fp ∪ Fh ∪ Ff).card ≤ Fp.card + Fh.card + Ff.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    change (Fp ∪ Fh ∪ Ff).card ≤ (3 * b' ^ 2 + 2) * n
    nlinarith

lemma smooth_step_disjoint {V : Type} [Fintype V] [DecidableEq V]
    (R b' : ℕ) (μ : (V → Bool) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x)
    (hμsm : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v))))
    (E : Finset V) (hE : E.card ≤ b')
    (Q : (V → Bool) → Prop)
    (hQ : ∀ x x' : V → Bool, (∀ v ∉ E, x v = x' v) → (Q x ↔ Q x')) :
    let A_Q := Finset.univ.filter (fun x => @decide (Q x) (Classical.propDecidable _))
    let A_hit := Finset.univ.filter (fun x =>
      @decide (Q x ∧ ∃ v ∈ E, x v = true) (Classical.propDecidable _))
    ∑ x ∈ A_hit, μ x ≤ (1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') * ∑ x ∈ A_Q, μ x := by
  intro A_Q A_hit
  let A_zero := A_Q \ A_hit
  have hsub : A_hit ⊆ A_Q := by
    intro x hx
    simp only [A_hit, A_Q, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx ⊢
    exact hx.1
  have hflip_bool : ∀ (D : Finset V) (y : V → Bool),
      μ (fun v => if v ∈ D then !(y v) else y v) ≤ (R : ℝ) ^ D.card * μ y := by
    intro D y
    let μ' : (V → ZMod 2) → ℝ := fun z => μ (z2ToX z)
    have hμ'sm : ∀ z v, μ' z ≤ (R : ℝ) * μ' (z + fun u => if u = v then (1 : ZMod 2) else 0) := by
      intro z v
      simp only [μ', z2ToX_add_unit]
      exact hμsm (z2ToX z) v
    have h1 := smooth_flip_set R μ' hμ'sm D (xToZ2 y)
    have harg : z2ToX (xToZ2 y + fun u => if u ∈ D then (1 : ZMod 2) else 0) =
        (fun v => if v ∈ D then !(y v) else y v) := by
      funext v
      by_cases hv : v ∈ D
      · simp only [z2ToX, Pi.add_apply, xToZ2, hv, ↓reduceIte]
        rw [← boolToZ2_not, z2ToBool_boolToZ2]
      · simp only [z2ToX, Pi.add_apply, xToZ2, hv, ↓reduceIte, add_zero, z2ToBool_boolToZ2]
    simpa [μ', harg, z2ToX_xToZ2] using h1
  let Φ : (V → Bool) × Finset V → (V → Bool) :=
    fun p => fun v => if v ∈ p.2 then !(p.1 v) else p.1 v
  have hcover : A_Q ⊆ (A_zero ×ˢ E.powerset).image Φ := by
    intro x hx
    let D : Finset V := E.filter (fun v => x v = true)
    let y : V → Bool := fun v => if v ∈ E then false else x v
    have hyQ : Q y := by
      simp only [A_Q, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx
      exact (hQ x y fun v hv => by simp [y, hv]).mp hx
    have hy0 : y ∈ A_zero := by
      rw [Finset.mem_sdiff]
      refine ⟨by simp only [A_Q, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]; exact hyQ, ?_⟩
      intro hyhit
      simp only [A_hit, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hyhit
      obtain ⟨_, v, hvE, hvt⟩ := hyhit
      simp [y, hvE] at hvt
    refine Finset.mem_image.mpr ⟨(y, D),
      Finset.mem_product.mpr ⟨hy0, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩, ?_⟩
    funext v
    by_cases hvE : v ∈ E
    · cases hxv : x v
      · simp [Φ, D, y, hvE, hxv]
      · simp [Φ, D, y, hvE, hxv]
    · have hvD : v ∉ D := fun h => hvE (Finset.mem_filter.mp h).1
      simp [Φ, y, hvE, hvD]
  have hsum_le : ∑ x ∈ A_Q, μ x ≤ ((R + 1 : ℕ) : ℝ) ^ b' * ∑ y ∈ A_zero, μ y := by
    calc ∑ x ∈ A_Q, μ x
        ≤ ∑ x ∈ (A_zero ×ˢ E.powerset).image Φ, μ x :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun x _ _ => hμ0 x)
      _ ≤ ∑ p ∈ A_zero ×ˢ E.powerset, μ (Φ p) :=
          Finset.sum_image_le_of_nonneg (fun x _ => hμ0 x)
      _ = ∑ y ∈ A_zero, ∑ D ∈ E.powerset, μ (fun v => if v ∈ D then !(y v) else y v) :=
          Finset.sum_product _ _ _
      _ ≤ ∑ y ∈ A_zero, ∑ D ∈ E.powerset, (R : ℝ) ^ D.card * μ y :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun D _ => hflip_bool D y
      _ = ∑ y ∈ A_zero, (∑ D ∈ E.powerset, (R : ℝ) ^ D.card) * μ y := by
          refine Finset.sum_congr rfl fun y _ => (Finset.sum_mul _ _ _).symm
      _ = ((R + 1 : ℕ) : ℝ) ^ E.card * ∑ y ∈ A_zero, μ y := by
          rw [← Finset.mul_sum, powerset_sum_pow]
          push_cast
          rfl
      _ ≤ ((R + 1 : ℕ) : ℝ) ^ b' * ∑ y ∈ A_zero, μ y := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun y _ => hμ0 y)
          exact pow_le_pow_right₀ (by norm_cast; omega) hE
  have hsplit : ∑ y ∈ A_zero, μ y = (∑ x ∈ A_Q, μ x) - ∑ x ∈ A_hit, μ x := by
    have h1 := Finset.sum_sdiff hsub (f := μ)
    linarith
  rw [hsplit] at hsum_le
  have hpos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) ^ b' := by positivity
  have hmul : ((R + 1 : ℕ) : ℝ) ^ b' * ∑ x ∈ A_hit, μ x ≤
      (((R + 1 : ℕ) : ℝ) ^ b' - 1) * ∑ x ∈ A_Q, μ x := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hpos)
  rw [mul_div_cancel_left₀ _ (ne_of_gt hpos)] at hdiv
  calc ∑ x ∈ A_hit, μ x ≤ ((((R + 1 : ℕ) : ℝ) ^ b' - 1) * ∑ x ∈ A_Q, μ x) / ((R + 1 : ℕ) : ℝ) ^ b' := hdiv
    _ = (1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') * ∑ x ∈ A_Q, μ x := by
        field_simp [ne_of_gt hpos]

lemma bernoulli_half (N : ℕ) (hN : 1 ≤ N) :
    (1 - 1 / (N : ℝ)) ^ N ≤ (1 / 2 : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h1 : (1 - 1 / (N : ℝ)) * (1 + 1 / (N : ℝ)) ≤ 1 := by
    have hsq : 0 ≤ (1 / (N : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  have hnonneg : 0 ≤ 1 - 1 / (N : ℝ) := by
    have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [sub_nonneg, div_le_one hNpos]
    exact hle
  have hmul_pow : (1 - 1 / (N : ℝ)) ^ N * (1 + 1 / (N : ℝ)) ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg hnonneg (by positivity)) h1
  have hbern : (2 : ℝ) ≤ (1 + 1 / (N : ℝ)) ^ N := by
    have hge : (-2 : ℝ) ≤ 1 / (N : ℝ) := by
      have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
    have hb := one_add_mul_le_pow hge N
    have hN1 : (N : ℝ) * (1 / (N : ℝ)) = 1 := mul_one_div_cancel (ne_of_gt hNpos)
    linarith
  have hpos2 : (0 : ℝ) < (1 + 1 / (N : ℝ)) ^ N := by positivity
  have h2 : (1 - 1 / (N : ℝ)) ^ N * 2 ≤ 1 := by
    calc (1 - 1 / (N : ℝ)) ^ N * 2
        ≤ (1 - 1 / (N : ℝ)) ^ N * (1 + 1 / (N : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left hbern (pow_nonneg hnonneg N)
      _ ≤ 1 := hmul_pow
  linarith

lemma disjoint_pigeon_mass_bound {n b h R : ℕ}
    (G : BipGraph (n + 1) n) (hLd : LeftDegLe G b)
    (b' : ℕ) (hb' : b ≤ b')
    (hm : (R + 1) ^ b' * h ≤ n + 1)
    (μ : (GEdge G → Bool) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x)
    (hμsm : ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v)))) :
    let m := (R + 1) ^ b' * h
    let S_all := Finset.univ.filter (fun x : GEdge G → Bool =>
      @decide (∀ t : Fin m, ClauseSat x (pigeonClause G ⟨t.val, lt_of_lt_of_le t.isLt hm⟩))
        (Classical.propDecidable _))
    (2 : ℝ) ^ h * ∑ x ∈ S_all, μ x ≤ ∑ x, μ x := by
  intro m S_all
  have hstep : ∀ k : ℕ, (hk : k ≤ n + 1) →
      ∑ x ∈ Finset.univ.filter (fun x : GEdge G → Bool =>
        @decide (∀ t : Fin k, ClauseSat x (pigeonClause G ⟨t.val, lt_of_lt_of_le t.isLt hk⟩))
          (Classical.propDecidable _)), μ x ≤
      (1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') ^ k * ∑ x, μ x := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      let E_k : Finset (GEdge G) := Finset.univ.filter (fun e => e.1.1 = ⟨k, by omega⟩)
      have hEk_card : E_k.card ≤ b' := by
        have hinj : Set.InjOn (fun e : GEdge G => e.1.2) (E_k : Set (GEdge G)) := by
          rintro ⟨⟨i₁, j₁⟩, h₁⟩ hm₁ ⟨⟨i₂, j₂⟩, h₂⟩ hm₂ heq
          simp only [Finset.mem_coe, E_k, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
          dsimp only at heq
          subst heq; subst hm₁; subst hm₂; rfl
        have hsub : E_k.image (fun e => e.1.2) ⊆ G ⟨k, by omega⟩ := by
          intro j hj
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
          have h1 : e.1.1 = ⟨k, by omega⟩ := (Finset.mem_filter.mp he).2
          exact h1 ▸ e.2
        calc E_k.card = (E_k.image (fun e => e.1.2)).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (G ⟨k, by omega⟩).card := Finset.card_le_card hsub
          _ ≤ b := hLd _
          _ ≤ b' := hb'
      let Q : (GEdge G → Bool) → Prop :=
        fun x => ∀ t : Fin k, ClauseSat x (pigeonClause G ⟨t.val, by omega⟩)
      have hQ_ind : ∀ x x' : GEdge G → Bool, (∀ v ∉ E_k, x v = x' v) → (Q x ↔ Q x') := by
        intro x x' hxx'
        constructor <;> intro hQ t <;> obtain ⟨l, hl, hsat⟩ := hQ t
        · have hlE : l.1 ∉ E_k := by
            intro hin
            have h1 : l.1.1.1 = ⟨t.val, by omega⟩ := (Finset.mem_filter.mp hl).2.1
            have h2 : l.1.1.1 = ⟨k, by omega⟩ := (Finset.mem_filter.mp hin).2
            have hv := congrArg (fun p : Fin (n + 1) => p.val) (h1.symm.trans h2)
            dsimp only at hv
            omega
          exact ⟨l, hl, (hxx' l.1 hlE).symm.trans hsat⟩
        · have hlE : l.1 ∉ E_k := by
            intro hin
            have h1 : l.1.1.1 = ⟨t.val, by omega⟩ := (Finset.mem_filter.mp hl).2.1
            have h2 : l.1.1.1 = ⟨k, by omega⟩ := (Finset.mem_filter.mp hin).2
            have hv := congrArg (fun p : Fin (n + 1) => p.val) (h1.symm.trans h2)
            dsimp only at hv
            omega
          exact ⟨l, hl, (hxx' l.1 hlE).trans hsat⟩
      have hfilt_eq : Finset.univ.filter (fun x : GEdge G → Bool =>
            @decide (∀ t : Fin (k + 1), ClauseSat x (pigeonClause G ⟨t.val, lt_of_lt_of_le t.isLt hk⟩))
              (Classical.propDecidable _)) =
          Finset.univ.filter (fun x : GEdge G → Bool =>
            @decide (Q x ∧ ∃ v ∈ E_k, x v = true) (Classical.propDecidable _)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        constructor
        · intro hall
          refine ⟨fun t => hall ⟨t.val, by omega⟩, ?_⟩
          obtain ⟨l, hl, hsat⟩ := hall ⟨k, by omega⟩
          simp only [pigeonClause, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          refine ⟨l.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl.1⟩, ?_⟩
          rw [hsat, hl.2]
        · rintro ⟨hQx, v, hvE, hvt⟩ t
          by_cases hlt : t.val < k
          · exact hQx ⟨t.val, hlt⟩
          · have hteq : t.val = k := by omega
            refine ⟨(v, true), ?_, hvt⟩
            simp only [pigeonClause, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            have h1 : v.1.1 = ⟨k, by omega⟩ := (Finset.mem_filter.mp hvE).2
            exact h1.trans (Fin.ext (by dsimp only; exact hteq.symm))
      rw [hfilt_eq]
      have hsm := smooth_step_disjoint R b' μ hμ0 hμsm E_k hEk_card Q hQ_ind
      have hnonneg : 0 ≤ 1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b' := by
        have hge1 : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ b' := by
          have : 1 ≤ (R + 1) ^ b' := Nat.one_le_pow _ _ (by omega)
          exact_mod_cast this
        have hpos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) ^ b' := by positivity
        rw [sub_nonneg, div_le_one hpos]
        exact hge1
      calc _ ≤ (1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') * ∑ x ∈ Finset.univ.filter (fun x =>
                @decide (Q x) (Classical.propDecidable _)), μ x := hsm
        _ ≤ (1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') *
              ((1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') ^ k * ∑ x, μ x) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hnonneg
        _ = (1 - 1 / ((R + 1 : ℕ) : ℝ) ^ b') ^ (k + 1) * ∑ x, μ x := by
            rw [pow_succ', mul_assoc]
  have hbound := hstep m hm
  let N := (R + 1) ^ b'
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hbern := bernoulli_half N hN1
  have hpow : (1 - 1 / (N : ℝ)) ^ (N * h) ≤ (1 / 2 : ℝ) ^ h := by
    rw [pow_mul]
    have hnn : 0 ≤ 1 - 1 / (N : ℝ) := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      rw [sub_nonneg, div_le_one hNpos]; exact hle
    exact pow_le_pow_left₀ (pow_nonneg hnn N) hbern h
  have hcast : ((R + 1 : ℕ) : ℝ) ^ b' = (N : ℝ) := by simp [N]
  rw [hcast] at hbound
  have hle : ∑ x ∈ S_all, μ x ≤ (1 / 2 : ℝ) ^ h * ∑ x, μ x :=
    hbound.trans (mul_le_mul_of_nonneg_right hpow (Finset.sum_nonneg fun x _ => hμ0 x))
  calc (2 : ℝ) ^ h * ∑ x ∈ S_all, μ x
      ≤ (2 : ℝ) ^ h * ((1 / 2 : ℝ) ^ h * ∑ x, μ x) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ((2 : ℝ) * (1 / 2 : ℝ)) ^ h * ∑ x, μ x := by rw [← mul_assoc, ← mul_pow]
    _ = ∑ x, μ x := by norm_num

structure CState (V : Type) [Fintype V] where
  gs : List Gate
  hrb : ReadsBack (2 + Fintype.card V) ⟨gs, 0⟩
  hval : ∀ g ∈ gs, gateValid g

def CState.empty (V : Type) [Fintype V] : CState V :=
  ⟨[], fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ hg => by simp at hg⟩

def CState.push {V : Type} [Fintype V] (st : CState V) (g : Gate)
    (hgval : gateValid g) (hins : ∀ i ∈ g.inputs, i < 2 + Fintype.card V + st.gs.length) :
    CState V where
  gs := st.gs ++ [g]
  hrb := by
    intro j hj i hi
    dsimp only at hj
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < st.gs.length
    · have hj' : j < (st.gs ++ [g]).length := by rw [List.length_append, List.length_singleton]; omega
      have hgat : gateAt ⟨st.gs ++ [g], 0⟩ j = gateAt ⟨st.gs, 0⟩ j := by
        unfold gateAt
        dsimp only
        rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hj', List.getElem_append_left hlt]
      rw [hgat] at hi
      exact st.hrb j hlt i hi
    · have hjeq : j = st.gs.length := by omega
      subst hjeq
      have hgat : gateAt ⟨st.gs ++ [g], 0⟩ st.gs.length = g := by
        simp [gateAt]
      rw [hgat] at hi
      exact hins i hi
  hval := by
    intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact st.hval g' h1
    · simp only [List.mem_singleton] at h2
      subst h2
      exact hgval

def CExt {V : Type} [Fintype V] (st₁ st₂ : CState V) : Prop :=
  ∃ extra : List Gate, st₂.gs = st₁.gs ++ extra

lemma CExt.refl {V : Type} [Fintype V] (st : CState V) : CExt st st :=
  ⟨[], by simp⟩

lemma CExt.trans {V : Type} [Fintype V] {s₁ s₂ s₃ : CState V}
    (h12 : CExt s₁ s₂) (h23 : CExt s₂ s₃) : CExt s₁ s₃ := by
  obtain ⟨e1, he1⟩ := h12
  obtain ⟨e2, he2⟩ := h23
  exact ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩

lemma CExt.push {V : Type} [Fintype V] (st : CState V) (g : Gate)
    (hgval : gateValid g) (hins : ∀ i ∈ g.inputs, i < 2 + Fintype.card V + st.gs.length) :
    CExt st (st.push g hgval hins) :=
  ⟨[g], rfl⟩

lemma CExt.len_le {V : Type} [Fintype V] {s₁ s₂ : CState V} (h : CExt s₁ s₂) :
    s₁.gs.length ≤ s₂.gs.length := by
  obtain ⟨e, he⟩ := h
  rw [he, List.length_append]
  omega

lemma CExt.wire_eq {V : Type} [Fintype V] {s₁ s₂ : CState V} (h : CExt s₁ s₂)
    (x : V → Bool) (i : ℕ) (hi : i < 2 + Fintype.card V + s₁.gs.length) :
    (wiresOf s₂.gs (inBits x)).getD i false = (wiresOf s₁.gs (inBits x)).getD i false := by
  obtain ⟨e, he⟩ := h
  rw [he]
  exact wiresOf_prefix_getD s₁.gs e (inBits x) i (by rw [inBits_length]; exact hi)

lemma push_wire_eval {V : Type} [Fintype V] (st : CState V) (g : Gate)
    (hgval : gateValid g) (hins : ∀ i ∈ g.inputs, i < 2 + Fintype.card V + st.gs.length)
    (x : V → Bool) :
    (wiresOf (st.push g hgval hins).gs (inBits x)).getD (2 + Fintype.card V + st.gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf st.gs (inBits x)).getD i false) := by
  have h := wiresOf_last_getD st.gs g (inBits x)
  rwa [inBits_length] at h

lemma inBits_getD_var {V : Type} [Fintype V] (x : V → Bool) (v : V) :
    (inBits x).getD (2 + (Fintype.equivFin V v).val) false = x v := by
  have hlt : 2 + (Fintype.equivFin V v).val < (inBits x).length := by
    rw [inBits_length]
    have := (Fintype.equivFin V v).isLt
    omega
  rw [List.getD_eq_getElem _ _ hlt]
  have hlen2 : ([false, true] : List Bool).length = 2 := rfl
  have h2 : (inBits x)[2 + (Fintype.equivFin V v).val]'hlt =
      (List.ofFn (fun i : Fin (Fintype.card V) => x ((Fintype.equivFin V).symm i)))[2 + (Fintype.equivFin V v).val - 2]'(by simp) := by
    unfold inBits
    exact List.getElem_append_right (by omega)
  rw [h2]
  simp

lemma wire_var_eq {V : Type} [Fintype V] (st : CState V) (x : V → Bool) (v : V) :
    (wiresOf st.gs (inBits x)).getD (2 + (Fintype.equivFin V v).val) false = x v := by
  have h := CExt.wire_eq (s₁ := CState.empty V) (s₂ := st) ⟨st.gs, rfl⟩ x
    (2 + (Fintype.equivFin V v).val) (by
      have := (Fintype.equivFin V v).isLt
      simp only [CState.empty, List.length_nil, add_zero]
      omega)
  rw [h]
  exact inBits_getD_var x v

lemma wire_false_eq {V : Type} [Fintype V] (st : CState V) (x : V → Bool) :
    (wiresOf st.gs (inBits x)).getD 0 false = false := by
  have h := CExt.wire_eq (s₁ := CState.empty V) (s₂ := st) ⟨st.gs, rfl⟩ x 0
    (by simp only [CState.empty, List.length_nil, add_zero]; omega)
  rw [h]
  rfl

lemma wire_true_eq {V : Type} [Fintype V] (st : CState V) (x : V → Bool) :
    (wiresOf st.gs (inBits x)).getD 1 false = true := by
  have h := CExt.wire_eq (s₁ := CState.empty V) (s₂ := st) ⟨st.gs, rfl⟩ x 1
    (by simp only [CState.empty, List.length_nil, add_zero]; omega)
  rw [h]
  rfl

lemma build_const_circuit {V : Type} [Fintype V] {b_bits : ℕ} (y₀ : Fin b_bits → ZMod 2) :
    ∃ (st : CState V) (pick : Fin b_bits → Fin (2 + Fintype.card V + st.gs.length)),
      countAndOr st.gs = 0 ∧
      ∀ x : V → Bool, (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)) = y₀ := by
  refine ⟨CState.empty V, fun j => ⟨if y₀ j = 1 then 1 else 0, by split_ifs <;> (simp only [CState.empty, List.length_nil, add_zero]; omega)⟩, rfl, ?_⟩
  intro x
  funext j
  rcases z2_cases (y₀ j) with h0 | h1
  · simp [h0, CState.empty, wiresOf_nil, inBits, boolToZ2]
  · simp [h1, CState.empty, wiresOf_nil, inBits, boolToZ2]

lemma build_parity_wire {V : Type} [Fintype V] (st : CState V) (ins : List ℕ)
    (hins : ∀ i ∈ ins, i < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (w : ℕ),
      CExt st st' ∧ w < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs = countAndOr st.gs ∧
      ∀ x : V → Bool,
        boolToZ2 ((wiresOf st'.gs (inBits x)).getD w false) =
          (ins.map fun i => boolToZ2 ((wiresOf st.gs (inBits x)).getD i false)).sum := by
  let g1 : Gate := ⟨.mod 2, ins⟩
  let st1 := st.push g1 (Or.inr (Or.inl rfl)) hins
  let w1 := 2 + Fintype.card V + st.gs.length
  let g2 : Gate := ⟨.not, [w1]⟩
  have hw1_lt : w1 < 2 + Fintype.card V + st1.gs.length := by
    simp [st1, CState.push, w1]
  let st2 := st1.push g2 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (fun i hi => by simp [g2] at hi; subst hi; exact hw1_lt)
  let w2 := 2 + Fintype.card V + st1.gs.length
  refine ⟨st2, w2, (CExt.push st _ _ _).trans (CExt.push st1 _ _ _),
    by simp [st2, CState.push, w2], ?_, ?_⟩
  · dsimp only [st2, st1, CState.push]
    rw [countAndOr_append_one, countAndOr_append_one]
    simp [g1, g2]
  · intro x
    have h2 := push_wire_eval st1 g2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (fun i hi => by simp [g2] at hi; subst hi; exact hw1_lt) x
    have h1 := push_wire_eval st g1 (Or.inr (Or.inl rfl)) hins x
    change boolToZ2 ((wiresOf st2.gs (inBits x)).getD w2 false) = _
    rw [h2]
    simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [boolToZ2_not, h1]
    simp only [g1, GateOp.eval]
    rw [boolToZ2_mod2, List.map_map]
    have hadd : (1 + (ins.map (boolToZ2 ∘ fun i => (wiresOf st.gs (inBits x)).getD i false)).sum) + 1 =
        (ins.map (fun i => boolToZ2 ((wiresOf st.gs (inBits x)).getD i false))).sum := by
      have h11 : (1 : ZMod 2) + 1 = 0 := z2_add_self 1
      calc (1 + (ins.map (boolToZ2 ∘ fun i => (wiresOf st.gs (inBits x)).getD i false)).sum) + 1
          = (1 + 1) + (ins.map (boolToZ2 ∘ fun i => (wiresOf st.gs (inBits x)).getD i false)).sum := by ring
        _ = (ins.map (fun i => boolToZ2 ((wiresOf st.gs (inBits x)).getD i false))).sum := by
            rw [h11, zero_add]; rfl
    exact hadd

lemma build_multi_parity {V : Type} [Fintype V] {b_bits : ℕ} (st : CState V)
    (ins : Fin b_bits → List ℕ)
    (hins : ∀ j : Fin b_bits, ∀ i ∈ ins j, i < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (pick : Fin b_bits → Fin (2 + Fintype.card V + st'.gs.length)),
      CExt st st' ∧ countAndOr st'.gs = countAndOr st.gs ∧
      ∀ x : V → Bool, ∀ j : Fin b_bits,
        boolToZ2 ((wiresOf st'.gs (inBits x)).getD (pick j).val false) =
          ((ins j).map fun i => boolToZ2 ((wiresOf st.gs (inBits x)).getD i false)).sum := by
  have hrec : ∀ k : ℕ, (hk : k ≤ b_bits) →
      ∃ (st' : CState V) (pick : Fin k → Fin (2 + Fintype.card V + st'.gs.length)),
        CExt st st' ∧ countAndOr st'.gs = countAndOr st.gs ∧
        ∀ x : V → Bool, ∀ j : Fin k,
          boolToZ2 ((wiresOf st'.gs (inBits x)).getD (pick j).val false) =
            ((ins ⟨j.val, lt_of_lt_of_le j.isLt hk⟩).map fun i =>
              boolToZ2 ((wiresOf st.gs (inBits x)).getD i false)).sum := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨st, Fin.elim0, CExt.refl st, rfl, fun _ j => j.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨st1, pick1, hext1, hcnt1, hval1⟩ := ih (by omega)
      have hins_k : ∀ i ∈ ins ⟨k, hk⟩, i < 2 + Fintype.card V + st1.gs.length :=
        fun i hi => lt_of_lt_of_le (hins ⟨k, hk⟩ i hi) (by have := hext1.len_le; omega)
      obtain ⟨st2, wk, hext2, hwk_lt, hcnt2, hvalk⟩ := build_parity_wire st1 (ins ⟨k, hk⟩) hins_k
      refine ⟨st2, fun j =>
          if hj : j.val < k then
            ⟨(pick1 ⟨j.val, hj⟩).val, lt_of_lt_of_le (pick1 ⟨j.val, hj⟩).isLt (by have := hext2.len_le; omega)⟩
          else ⟨wk, hwk_lt⟩,
        hext1.trans hext2, hcnt2.trans hcnt1, ?_⟩
      intro x j
      dsimp only
      by_cases hj : j.val < k
      · rw [dite_eq_left hj]
        dsimp only
        rw [hext2.wire_eq x _ (pick1 ⟨j.val, hj⟩).isLt]
        exact hval1 x ⟨j.val, hj⟩
      · rw [dite_eq_right hj]
        dsimp only
        have hjeq : (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin b_bits) = ⟨k, hk⟩ :=
          Fin.ext (by dsimp only; have := j.isLt; omega)
        rw [hjeq, hvalk x]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        rw [hext1.wire_eq x i (hins ⟨k, hk⟩ i hi)]
  obtain ⟨st', pick, hext, hcnt, hval⟩ := hrec b_bits le_rfl
  exact ⟨st', pick, hext, hcnt, fun x j => hval x j⟩

lemma build_affine_circuit {V : Type} [Fintype V] {b_bits m : ℕ}
    (y₀ : Fin b_bits → ZMod 2)
    (vars : Fin m → V)
    (L : Fin m → (Fin b_bits → ZMod 2)) :
    ∃ (st : CState V) (pick : Fin b_bits → Fin (2 + Fintype.card V + st.gs.length)),
      countAndOr st.gs = 0 ∧
      ∀ x : V → Bool,
        (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)) =
          y₀ + ∑ t : Fin m, boolToZ2 (x (vars t)) • L t := by
  let ins : Fin b_bits → List ℕ := fun j =>
    (if y₀ j = 1 then [1] else []) ++
    ((List.finRange m).filter (fun t => decide (L t j = 1))).map
      (fun t => 2 + (Fintype.equivFin V (vars t)).val)
  have hins : ∀ j : Fin b_bits, ∀ i ∈ ins j, i < 2 + Fintype.card V + (CState.empty V).gs.length := by
    intro j i hi
    simp only [ins, List.mem_append, List.mem_map, CState.empty, List.length_nil, add_zero] at hi ⊢
    rcases hi with h1 | ⟨t, _, rfl⟩
    · split_ifs at h1 with hy
      · simp at h1; omega
      · simp at h1
    · have := (Fintype.equivFin V (vars t)).isLt; omega
  obtain ⟨st', pick, _, hcnt, hval⟩ := build_multi_parity (CState.empty V) ins hins
  refine ⟨st', pick, hcnt, fun x => ?_⟩
  funext j
  rw [hval x j]
  simp only [ins, List.map_append, List.sum_append, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  have hconst : ((if y₀ j = 1 then [1] else []).map fun i =>
      boolToZ2 ((wiresOf (CState.empty V).gs (inBits x)).getD i false)).sum = y₀ j := by
    rcases z2_cases (y₀ j) with h0 | h1
    · simp [h0]
    · rw [h1]
      simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [wire_true_eq]
      rfl
  have hlin : ((((List.finRange m).filter (fun t => decide (L t j = 1))).map
      (fun t => 2 + (Fintype.equivFin V (vars t)).val)).map
      (fun i => boolToZ2 ((wiresOf (CState.empty V).gs (inBits x)).getD i false))).sum =
      ∑ t : Fin m, boolToZ2 (x (vars t)) * L t j := by
    rw [List.map_map]
    have hmap : (((List.finRange m).filter (fun t => decide (L t j = 1))).map
        ((fun i => boolToZ2 ((wiresOf (CState.empty V).gs (inBits x)).getD i false)) ∘
          fun t => 2 + (Fintype.equivFin V (vars t)).val)) =
        ((List.finRange m).filter (fun t => decide (L t j = 1))).map (fun t => boolToZ2 (x (vars t))) := by
      refine List.map_congr_left fun t _ => ?_
      dsimp only [Function.comp_apply]
      rw [wire_var_eq]
    rw [hmap]
    have hsum_gen : ∀ l : List (Fin m),
        ((l.filter (fun t => decide (L t j = 1))).map (fun t => boolToZ2 (x (vars t)))).sum =
        (l.map (fun t => boolToZ2 (x (vars t)) * L t j)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons t tl ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        rcases z2_cases (L t j) with h0 | h1
        · simp [h0, ih]
        · simp [h1, ih]
    rw [hsum_gen]
    have hfin : ((List.finRange m).map (fun t => boolToZ2 (x (vars t)) * L t j)).sum =
        ∑ t : Fin m, boolToZ2 (x (vars t)) * L t j := by
      rw [← Fin.sum_univ_def]
    exact hfin
  rw [hconst, hlin]

lemma build_not_wire {V : Type} [Fintype V] (st : CState V) (w : ℕ)
    (hw : w < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs = countAndOr st.gs ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false =
        !((wiresOf st.gs (inBits x)).getD w false) := by
  let g : Gate := ⟨.not, [w]⟩
  let st' := st.push g (Or.inr (Or.inr ⟨rfl, rfl⟩)) (fun i hi => by simp [g] at hi; subst hi; exact hw)
  refine ⟨st', 2 + Fintype.card V + st.gs.length, CExt.push st _ _ _,
    by simp [st', CState.push], by simp [st', CState.push, g, countAndOr_append_one], ?_⟩
  intro x
  have h := push_wire_eval st g (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (fun i hi => by simp [g] at hi; subst hi; exact hw) x
  dsimp only [st']
  rw [h]
  simp [g, GateOp.eval]

lemma build_and_wire {V : Type} [Fintype V] (st : CState V) (w₁ w₂ : ℕ)
    (hw₁ : w₁ < 2 + Fintype.card V + st.gs.length)
    (hw₂ : w₂ < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs = countAndOr st.gs + 1 ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false =
        ((wiresOf st.gs (inBits x)).getD w₁ false && (wiresOf st.gs (inBits x)).getD w₂ false) := by
  let g : Gate := ⟨.and, [w₁, w₂]⟩
  let st' := st.push g (Or.inl ⟨Or.inl rfl, rfl⟩)
    (fun i hi => by simp [g] at hi; rcases hi with rfl | rfl <;> assumption)
  refine ⟨st', 2 + Fintype.card V + st.gs.length, CExt.push st _ _ _,
    by simp [st', CState.push], by simp [st', CState.push, g, countAndOr_append_one], ?_⟩
  intro x
  have h := push_wire_eval st g (Or.inl ⟨Or.inl rfl, rfl⟩)
    (fun i hi => by simp [g] at hi; rcases hi with rfl | rfl <;> assumption) x
  dsimp only [st']
  rw [h]
  simp [g, GateOp.eval]

lemma build_or_wire {V : Type} [Fintype V] (st : CState V) (w₁ w₂ : ℕ)
    (hw₁ : w₁ < 2 + Fintype.card V + st.gs.length)
    (hw₂ : w₂ < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs = countAndOr st.gs + 1 ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false =
        ((wiresOf st.gs (inBits x)).getD w₁ false || (wiresOf st.gs (inBits x)).getD w₂ false) := by
  let g : Gate := ⟨.or, [w₁, w₂]⟩
  let st' := st.push g (Or.inl ⟨Or.inr rfl, rfl⟩)
    (fun i hi => by simp [g] at hi; rcases hi with rfl | rfl <;> assumption)
  refine ⟨st', 2 + Fintype.card V + st.gs.length, CExt.push st _ _ _,
    by simp [st', CState.push], by simp [st', CState.push, g, countAndOr_append_one], ?_⟩
  intro x
  have h := push_wire_eval st g (Or.inl ⟨Or.inr rfl, rfl⟩)
    (fun i hi => by simp [g] at hi; rcases hi with rfl | rfl <;> assumption) x
  dsimp only [st']
  rw [h]
  simp [g, GateOp.eval]

lemma build_and_list {V : Type} [Fintype V] (st : CState V) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs ≤ countAndOr st.gs + ws.length ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false =
        (ws.all fun w => (wiresOf st.gs (inBits x)).getD w false) := by
  induction ws generalizing st with
  | nil =>
    refine ⟨st, 1, CExt.refl st, by omega, by simp, fun x => by rw [wire_true_eq]; rfl⟩
  | cons w tl ih =>
    obtain ⟨st1, w1, hext1, hw1_lt, hcnt1, hval1⟩ :=
      ih st (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    have hw_lt : w < 2 + Fintype.card V + st1.gs.length :=
      lt_of_lt_of_le (hws w List.mem_cons_self) (by have := hext1.len_le; omega)
    obtain ⟨st2, w2, hext2, hw2_lt, hcnt2, hval2⟩ := build_and_wire st1 w w1 hw_lt hw1_lt
    refine ⟨st2, w2, hext1.trans hext2, hw2_lt, by simp only [List.length_cons]; omega, fun x => ?_⟩
    rw [hval2 x, hext1.wire_eq x w (hws w List.mem_cons_self), hval1 x]
    simp

lemma build_or_list {V : Type} [Fintype V] (st : CState V) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < 2 + Fintype.card V + st.gs.length) :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs ≤ countAndOr st.gs + ws.length ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false =
        (ws.any fun w => (wiresOf st.gs (inBits x)).getD w false) := by
  induction ws generalizing st with
  | nil =>
    refine ⟨st, 0, CExt.refl st, by omega, by simp, fun x => by rw [wire_false_eq]; rfl⟩
  | cons w tl ih =>
    obtain ⟨st1, w1, hext1, hw1_lt, hcnt1, hval1⟩ :=
      ih st (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    have hw_lt : w < 2 + Fintype.card V + st1.gs.length :=
      lt_of_lt_of_le (hws w List.mem_cons_self) (by have := hext1.len_le; omega)
    obtain ⟨st2, w2, hext2, hw2_lt, hcnt2, hval2⟩ := build_or_wire st1 w w1 hw_lt hw1_lt
    refine ⟨st2, w2, hext1.trans hext2, hw2_lt, by simp only [List.length_cons]; omega, fun x => ?_⟩
    rw [hval2 x, hext1.wire_eq x w (hws w List.mem_cons_self), hval1 x]
    simp

lemma build_clause_false {V : Type} [Fintype V] (st : CState V) (cl : Clause V) :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs ≤ countAndOr st.gs + cl.card ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false = true ↔ ¬ ClauseSat x cl := by
  have hlits : ∀ ls : List (Literal V),
      ∃ (st1 : CState V) (ws : List ℕ),
        CExt st st1 ∧ ws.length = ls.length ∧
        (∀ w ∈ ws, w < 2 + Fintype.card V + st1.gs.length) ∧
        countAndOr st1.gs = countAndOr st.gs ∧
        ∀ x : V → Bool,
          (ws.all fun w => (wiresOf st1.gs (inBits x)).getD w false) = true ↔
            ∀ l ∈ ls, x l.1 ≠ l.2 := by
    intro ls
    induction ls with
    | nil =>
      exact ⟨st, [], CExt.refl st, rfl, fun _ h => by simp at h, rfl, fun _ => by simp⟩
    | cons l tl ih =>
      obtain ⟨st1, ws, hext1, hlen1, hws1, hcnt1, hval1⟩ := ih
      let wvar := 2 + (Fintype.equivFin V l.1).val
      have hwvar_lt : wvar < 2 + Fintype.card V + st1.gs.length := by
        have := (Fintype.equivFin V l.1).isLt; omega
      cases hl2 : l.2
      · refine ⟨st1, wvar :: ws, hext1, by simp [hlen1], ?_, hcnt1, fun x => ?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | h
          · exact hwvar_lt
          · exact hws1 u h
        · simp only [wvar, List.all_cons, Bool.and_eq_true, wire_var_eq, hval1 x]
          constructor
          · rintro ⟨hx, htl⟩ l' hl'
            rcases List.mem_cons.mp hl' with rfl | h
            · rw [hx, hl2]; exact Bool.noConfusion
            · exact htl l' h
          · intro hall
            have h0 := hall l List.mem_cons_self
            rw [hl2] at h0
            refine ⟨by cases hx : x l.1 with | false => exact absurd hx h0 | true => rfl,
              fun l' hl' => hall l' (List.mem_cons_of_mem _ hl')⟩
      · obtain ⟨st2, wn, hext2, hwn_lt, hcnt2, hvaln⟩ := build_not_wire st1 wvar hwvar_lt
        refine ⟨st2, wn :: ws, hext1.trans hext2, by simp [hlen1], ?_, hcnt2.trans hcnt1, fun x => ?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | h
          · exact hwn_lt
          · exact lt_of_lt_of_le (hws1 u h) (by have := hext2.len_le; omega)
        · simp only [wvar, List.all_cons, Bool.and_eq_true, hvaln x, wire_var_eq]
          have hall_eq : (ws.all fun w => (wiresOf st2.gs (inBits x)).getD w false) =
              (ws.all fun w => (wiresOf st1.gs (inBits x)).getD w false) := by
            clear hval1 hlen1
            induction ws with
            | nil => rfl
            | cons u us ihu =>
              simp only [List.all_cons]
              rw [hext2.wire_eq x u (hws1 u List.mem_cons_self),
                ihu (fun w hw => hws1 w (List.mem_cons_of_mem _ hw))]
          rw [hall_eq, hval1 x]
          constructor
          · rintro ⟨hx, htl⟩ l' hl'
            rcases List.mem_cons.mp hl' with rfl | h
            · rw [hl2]; cases hxv : x l'.1 with
              | false => exact Bool.noConfusion
              | true => rw [hxv] at hx; exact Bool.noConfusion hx
            · exact htl l' h
          · intro hall
            have h0 := hall l List.mem_cons_self
            rw [hl2] at h0
            refine ⟨by cases hx : x l.1 with | false => rfl | true => exact absurd hx h0,
              fun l' hl' => hall l' (List.mem_cons_of_mem _ hl')⟩
  obtain ⟨st1, ws, hext1, hlen1, hws1, hcnt1, hval1⟩ := hlits cl.toList
  obtain ⟨st2, w2, hext2, hw2_lt, hcnt2, hval2⟩ := build_and_list st1 ws hws1
  refine ⟨st2, w2, hext1.trans hext2, hw2_lt, ?_, fun x => ?_⟩
  · have : ws.length = cl.card := by rw [hlen1, Finset.length_toList]
    omega
  · rw [hval2 x, hval1 x]
    unfold ClauseSat
    push Not
    constructor
    · intro h l hl; exact h l (Finset.mem_toList.mpr hl)
    · intro h l hl; exact h l (Finset.mem_toList.mp hl)

lemma build_bucket_hit {V : Type} [Fintype V] (st : CState V) (b' : ℕ)
    (cls : List (Clause V)) (hwidth : ∀ cl ∈ cls, cl.card ≤ b') :
    ∃ (st' : CState V) (w' : ℕ),
      CExt st st' ∧ w' < 2 + Fintype.card V + st'.gs.length ∧
      countAndOr st'.gs ≤ countAndOr st.gs + (b' + 1) * cls.length ∧
      ∀ x : V → Bool, (wiresOf st'.gs (inBits x)).getD w' false = true ↔
        ∃ cl ∈ cls, ¬ ClauseSat x cl := by
  have hcls : ∀ ls : List (Clause V), (∀ cl ∈ ls, cl.card ≤ b') →
      ∃ (st1 : CState V) (ws : List ℕ),
        CExt st st1 ∧ ws.length = ls.length ∧
        (∀ w ∈ ws, w < 2 + Fintype.card V + st1.gs.length) ∧
        countAndOr st1.gs ≤ countAndOr st.gs + b' * ls.length ∧
        ∀ x : V → Bool,
          (ws.any fun w => (wiresOf st1.gs (inBits x)).getD w false) = true ↔
            ∃ cl ∈ ls, ¬ ClauseSat x cl := by
    intro ls
    induction ls with
    | nil =>
      intro _
      exact ⟨st, [], CExt.refl st, rfl, fun _ h => by simp at h, by simp, fun _ => by simp⟩
    | cons cl tl ih =>
      intro hw
      obtain ⟨st1, ws, hext1, hlen1, hws1, hcnt1, hval1⟩ :=
        ih (fun c hc => hw c (List.mem_cons_of_mem _ hc))
      obtain ⟨st2, wcl, hext2, hwcl_lt, hcnt2, hvalcl⟩ := build_clause_false st1 cl
      have hcl_le : cl.card ≤ b' := hw cl List.mem_cons_self
      refine ⟨st2, wcl :: ws, hext1.trans hext2, by simp [hlen1], ?_, ?_, fun x => ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | h
        · exact hwcl_lt
        · exact lt_of_lt_of_le (hws1 u h) (by have := hext2.len_le; omega)
      · simp only [List.length_cons]
        nlinarith
      · simp only [List.any_cons, Bool.or_eq_true, hvalcl x]
        have hany : (ws.any fun w => (wiresOf st2.gs (inBits x)).getD w false) =
            (ws.any fun w => (wiresOf st1.gs (inBits x)).getD w false) := by
          clear hval1 hlen1
          induction ws with
          | nil => rfl
          | cons u us ihu =>
            simp only [List.any_cons]
            rw [hext2.wire_eq x u (hws1 u List.mem_cons_self),
              ihu (fun w hw' => hws1 w (List.mem_cons_of_mem _ hw'))]
        rw [hany, hval1 x]
        simp
  obtain ⟨st1, ws, hext1, hlen1, hws1, hcnt1, hval1⟩ := hcls cls hwidth
  obtain ⟨st2, w2, hext2, hw2_lt, hcnt2, hval2⟩ := build_or_list st1 ws hws1
  refine ⟨st2, w2, hext1.trans hext2, hw2_lt, ?_, fun x => ?_⟩
  · nlinarith
  · rw [hval2 x, hval1 x]

lemma build_bucket_search_circuit {V : Type} [Fintype V] {b_bits : ℕ}
    (b' : ℕ) (y_fb : Fin b_bits → ZMod 2)
    (buckets : List ((Fin b_bits → ZMod 2) × List (Clause V)))
    (hwidth : ∀ p ∈ buckets, ∀ cl ∈ p.2, cl.card ≤ b') :
    ∃ (st : CState V) (pick : Fin b_bits → Fin (2 + Fintype.card V + st.gs.length)),
      countAndOr st.gs ≤ (b' + 1) * (buckets.map (fun p => p.2.length)).sum + 2 * buckets.length ∧
      ∀ x : V → Bool,
        let y := fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)
        (∃ p ∈ buckets, y = p.1 ∧ ∃ cl ∈ p.2, ¬ ClauseSat x cl) ∨
        (y = y_fb ∧ ∀ p ∈ buckets, ∀ cl ∈ p.2, ClauseSat x cl) := by
  have hprio : ∀ (bs : List ((Fin b_bits → ZMod 2) × List (Clause V))),
      (∀ p ∈ bs, ∀ cl ∈ p.2, cl.card ≤ b') →
      ∃ (st : CState V) (found : ℕ) (sels : List (ℕ × (Fin b_bits → ZMod 2))),
        found < 2 + Fintype.card V + st.gs.length ∧
        (∀ s ∈ sels, s.1 < 2 + Fintype.card V + st.gs.length) ∧
        countAndOr st.gs ≤ (b' + 1) * (bs.map (fun p => p.2.length)).sum + 2 * bs.length ∧
        ∀ x : V → Bool,
          ((wiresOf st.gs (inBits x)).getD found false = true ↔
            ∃ p ∈ bs, ∃ cl ∈ p.2, ¬ ClauseSat x cl) ∧
          (∀ s ∈ sels, (wiresOf st.gs (inBits x)).getD s.1 false = true →
            ∃ p ∈ bs, s.2 = p.1 ∧ ∃ cl ∈ p.2, ¬ ClauseSat x cl) ∧
          ((wiresOf st.gs (inBits x)).getD found false = true →
            (sels.map fun s => (wiresOf st.gs (inBits x)).getD s.1 false).count true = 1) ∧
          ((wiresOf st.gs (inBits x)).getD found false = false →
            ∀ s ∈ sels, (wiresOf st.gs (inBits x)).getD s.1 false = false) := by
    intro bs
    induction bs with
    | nil =>
      intro _
      refine ⟨CState.empty V, 0, [], by simp only [CState.empty, List.length_nil, add_zero]; omega,
        fun _ h => by simp at h, by simp [CState.empty, countAndOr_nil], fun x => ?_⟩
      refine ⟨?_, fun _ h => by simp at h, ?_, fun _ _ h => by simp at h⟩
      · rw [wire_false_eq]; simp
      · intro h; rw [wire_false_eq] at h; exact Bool.noConfusion h
    | cons p tl ih =>
      intro hw
      obtain ⟨st1, found1, sels1, hfound1_lt, hsels1_lt, hcnt1, hinv1⟩ :=
        ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      obtain ⟨st2, whit, hext2, hwhit_lt, hcnt2, hvalhit⟩ :=
        build_bucket_hit st1 b' p.2 (hw p List.mem_cons_self)
      have hfound1_lt2 : found1 < 2 + Fintype.card V + st2.gs.length :=
        lt_of_lt_of_le hfound1_lt (by have := hext2.len_le; omega)
      obtain ⟨st3, wnotf, hext3, hwnotf_lt, hcnt3, hvalnotf⟩ :=
        build_not_wire st2 found1 hfound1_lt2
      have hwhit_lt3 : whit < 2 + Fintype.card V + st3.gs.length :=
        lt_of_lt_of_le hwhit_lt (by have := hext3.len_le; omega)
      obtain ⟨st4, wsel, hext4, hwsel_lt, hcnt4, hvalsel⟩ :=
        build_and_wire st3 whit wnotf hwhit_lt3 hwnotf_lt
      have hfound1_lt4 : found1 < 2 + Fintype.card V + st4.gs.length :=
        lt_of_lt_of_le hfound1_lt2 (by have := (hext3.trans hext4).len_le; omega)
      have hwhit_lt4 : whit < 2 + Fintype.card V + st4.gs.length :=
        lt_of_lt_of_le hwhit_lt3 (by have := hext4.len_le; omega)
      obtain ⟨st5, wfound, hext5, hwfound_lt, hcnt5, hvalfound⟩ :=
        build_or_wire st4 found1 whit hfound1_lt4 hwhit_lt4
      have hext15 : CExt st1 st5 := hext2.trans (hext3.trans (hext4.trans hext5))
      have hext25 : CExt st2 st5 := hext3.trans (hext4.trans hext5)
      have hwsel_lt5 : wsel < 2 + Fintype.card V + st5.gs.length :=
        lt_of_lt_of_le hwsel_lt (by have := hext5.len_le; omega)
      refine ⟨st5, wfound, (wsel, p.1) :: sels1, hwfound_lt, ?_, ?_, fun x => ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · exact hwsel_lt5
        · exact lt_of_lt_of_le (hsels1_lt s hs') (by have := hext15.len_le; omega)
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
      · obtain ⟨hf1, hsel1, hcnt1_t, hzero1⟩ := hinv1 x
        have hfound5 : (wiresOf st5.gs (inBits x)).getD wfound false =
            ((wiresOf st1.gs (inBits x)).getD found1 false ||
             (wiresOf st2.gs (inBits x)).getD whit false) := by
          rw [hvalfound x, (hext2.trans (hext3.trans hext4)).wire_eq x found1 hfound1_lt,
            (hext3.trans hext4).wire_eq x whit hwhit_lt]
        have hsel5 : (wiresOf st5.gs (inBits x)).getD wsel false =
            ((wiresOf st2.gs (inBits x)).getD whit false &&
             !((wiresOf st1.gs (inBits x)).getD found1 false)) := by
          rw [hext5.wire_eq x wsel hwsel_lt, hvalsel x, hext3.wire_eq x whit hwhit_lt,
            hvalnotf x, hext2.wire_eq x found1 hfound1_lt]
        have hsels_eq : (sels1.map fun s => (wiresOf st5.gs (inBits x)).getD s.1 false) =
            (sels1.map fun s => (wiresOf st1.gs (inBits x)).getD s.1 false) := by
          refine List.map_congr_left fun s hs => hext15.wire_eq x s.1 (hsels1_lt s hs)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hfound5, Bool.or_eq_true, hf1, hvalhit x]
          simp [or_comm]
        · intro s hs hst
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsel5, Bool.and_eq_true] at hst
            exact ⟨p, List.mem_cons_self, rfl, (hvalhit x).mp hst.1⟩
          · rw [hext15.wire_eq x s.1 (hsels1_lt s hs')] at hst
            obtain ⟨q, hq, hsq, hcl⟩ := hsel1 s hs' hst
            exact ⟨q, List.mem_cons_of_mem _ hq, hsq, hcl⟩
        · intro hf_true
          rw [List.map_cons, List.count_cons, hsels_eq, hsel5]
          cases hf1v : (wiresOf st1.gs (inBits x)).getD found1 false
          · rw [hfound5, hf1v, Bool.false_or] at hf_true
            have h0 : (sels1.map fun s => (wiresOf st1.gs (inBits x)).getD s.1 false).count true = 0 := by
              rw [List.count_eq_zero]
              intro hmem
              obtain ⟨s, hs, hst⟩ := List.mem_map.mp hmem
              have := hzero1 hf1v s hs
              rw [this] at hst
              exact Bool.noConfusion hst
            rw [hf_true, h0]
            rfl
          · rw [hcnt1_t hf1v]
            simp
        · intro hf_false s hs
          rw [hfound5, Bool.or_eq_false_iff] at hf_false
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsel5, hf_false.2]; rfl
          · rw [hext15.wire_eq x s.1 (hsels1_lt s hs')]
            exact hzero1 hf_false.1 s hs'
  obtain ⟨st1, found, sels, hfound_lt, hsels_lt, hcnt1, hinv⟩ := hprio buckets hwidth
  obtain ⟨st2, wfb, hext2, hwfb_lt, hcnt2, hvalfb⟩ := build_not_wire st1 found hfound_lt
  let allSels : List (ℕ × (Fin b_bits → ZMod 2)) := (wfb, y_fb) :: sels
  have hall_lt : ∀ s ∈ allSels, s.1 < 2 + Fintype.card V + st2.gs.length := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact hwfb_lt
    · exact lt_of_lt_of_le (hsels_lt s hs') (by have := hext2.len_le; omega)
  let ins : Fin b_bits → List ℕ := fun j =>
    (allSels.filter (fun s => decide (s.2 j = 1))).map Prod.fst
  have hins : ∀ j : Fin b_bits, ∀ i ∈ ins j, i < 2 + Fintype.card V + st2.gs.length := by
    intro j i hi
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
    exact hall_lt s (List.mem_filter.mp hs).1
  obtain ⟨st3, pick, hext3, hcnt3, hval3⟩ := build_multi_parity st2 ins hins
  refine ⟨st3, pick, by omega, fun x => ?_⟩
  obtain ⟨hfound, hsel_ok, hcnt_one, hzero_all⟩ := hinv x
  have hsum_sel : ∀ (w_true : ℕ) (y_true : Fin b_bits → ZMod 2),
      (w_true, y_true) ∈ allSels →
      (wiresOf st2.gs (inBits x)).getD w_true false = true →
      (allSels.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 1 →
      (fun j => boolToZ2 ((wiresOf st3.gs (inBits x)).getD (pick j).val false)) = y_true := by
    intro w_true y_true hmem ht hcnt_eq
    funext j
    rw [hval3 x j]
    have hones : ∀ (ls : List (ℕ × (Fin b_bits → ZMod 2))),
        (ls.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 0 →
        (((ls.filter (fun s => decide (s.2 j = 1))).map Prod.fst).map
          (fun i => boolToZ2 ((wiresOf st2.gs (inBits x)).getD i false))).sum = 0 := by
      intro ls h0
      induction ls with
      | nil => simp
      | cons s tl ih =>
        simp only [List.map_cons, List.count_cons] at h0
        have hsf : (wiresOf st2.gs (inBits x)).getD s.1 false = false := by
          cases hv : (wiresOf st2.gs (inBits x)).getD s.1 false
          · rfl
          · rw [hv] at h0; simp at h0
        have htl0 : (tl.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 0 := by
          rw [hsf] at h0; simpa using h0
        simp only [List.filter_cons]
        split_ifs
        · simp only [List.map_cons, List.sum_cons]
          rw [hsf, ih htl0]
          rfl
        · exact ih htl0
    have huniq : ∀ (ls : List (ℕ × (Fin b_bits → ZMod 2))),
        (w_true, y_true) ∈ ls →
        (ls.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 1 →
        (((ls.filter (fun s => decide (s.2 j = 1))).map Prod.fst).map
          (fun i => boolToZ2 ((wiresOf st2.gs (inBits x)).getD i false))).sum = y_true j := by
      intro ls
      induction ls with
      | nil => intro h; simp at h
      | cons s tl ih =>
        intro hm hc
        simp only [List.map_cons, List.count_cons] at hc
        rcases List.mem_cons.mp hm with rfl | hm'
        · simp only [ht, beq_self_eq_true, ↓reduceIte] at hc
          have htl0 : (tl.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 0 := by omega
          simp only [List.filter_cons]
          rcases z2_cases (y_true j) with h0 | h1
          · have hdec : decide (y_true j = 1) = false := decide_eq_false (by rw [h0]; exact zero_ne_one)
            rw [hdec, h0]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hones tl htl0
          · have hdec : decide (y_true j = 1) = true := decide_eq_true h1
            rw [hdec]
            simp only [↓reduceIte, List.map_cons, List.sum_cons]
            rw [ht, hones tl htl0, h1]
            rfl
        · cases hsv : (wiresOf st2.gs (inBits x)).getD s.1 false
          · simp only [hsv] at hc
            have hc' : (tl.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 1 := hc
            simp only [List.filter_cons]
            split_ifs
            · simp only [List.map_cons, List.sum_cons]
              rw [hsv, ih hm' hc']
              simp [boolToZ2]
            · exact ih hm' hc'
          · exfalso
            simp only [hsv, beq_self_eq_true, ↓reduceIte] at hc
            have htl0 : (tl.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 0 := by omega
            have hmem_t : true ∈ tl.map (fun s => (wiresOf st2.gs (inBits x)).getD s.1 false) :=
              List.mem_map.mpr ⟨(w_true, y_true), hm', ht⟩
            have hpos := List.count_pos_iff.mpr hmem_t
            omega
    exact huniq allSels hmem hcnt_eq
  have hsels2 : (sels.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false) =
      (sels.map fun s => (wiresOf st1.gs (inBits x)).getD s.1 false) :=
    List.map_congr_left fun s hs => hext2.wire_eq x s.1 (hsels_lt s hs)
  cases hfv : (wiresOf st1.gs (inBits x)).getD found false
  · right
    have hwfbt : (wiresOf st2.gs (inBits x)).getD wfb false = true := by rw [hvalfb x, hfv]; rfl
    have hcnt0 : (sels.map fun s => (wiresOf st1.gs (inBits x)).getD s.1 false).count true = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      obtain ⟨s, hs, hst⟩ := List.mem_map.mp hmem
      have := hzero_all hfv s hs
      rw [this] at hst
      exact Bool.noConfusion hst
    have hall1 : (allSels.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 1 := by
      simp only [allSels, List.map_cons, List.count_cons, hsels2, hwfbt, hcnt0]
      rfl
    refine ⟨hsum_sel wfb y_fb List.mem_cons_self hwfbt hall1, ?_⟩
    intro p hp cl hcl
    by_contra hnsat
    have hft : (wiresOf st1.gs (inBits x)).getD found false = true := hfound.mpr ⟨p, hp, cl, hcl, hnsat⟩
    rw [hfv] at hft
    exact Bool.noConfusion hft
  · left
    have hwfbf : (wiresOf st2.gs (inBits x)).getD wfb false = false := by rw [hvalfb x, hfv]; rfl
    have hcnt1' : (sels.map fun s => (wiresOf st1.gs (inBits x)).getD s.1 false).count true = 1 := hcnt_one hfv
    have hall1 : (allSels.map fun s => (wiresOf st2.gs (inBits x)).getD s.1 false).count true = 1 := by
      simp only [allSels, List.map_cons, List.count_cons, hsels2, hwfbf, hcnt1']
      rfl
    have hmem_t : true ∈ sels.map (fun s => (wiresOf st1.gs (inBits x)).getD s.1 false) :=
      List.count_pos_iff.mp (by omega)
    obtain ⟨s, hs, hst⟩ := List.mem_map.mp hmem_t
    have hst2 : (wiresOf st2.gs (inBits x)).getD s.1 false = true := by
      rw [hext2.wire_eq x s.1 (hsels_lt s hs)]; exact hst
    have hy_eq := hsum_sel s.1 s.2 (List.mem_cons_of_mem _ hs) hst2 hall1
    obtain ⟨p, hp, hsp, hcl⟩ := hsel_ok s hs hst
    exact ⟨p, hp, hy_eq.trans hsp, hcl⟩

lemma pack_buckets {Y V : Type} [DecidableEq Y]
    (ys : List Y) (hnd : ys.Nodup) (cap : Y → ℕ)
    (cls : List (Clause V)) (hlen : cls.length ≤ (ys.map cap).sum) :
    ∃ buckets : List (Y × List (Clause V)),
      (buckets.map Prod.fst).Nodup ∧
      (∀ p ∈ buckets, p.1 ∈ ys ∧ 1 ≤ p.2.length ∧ p.2.length ≤ cap p.1) ∧
      (∀ cl ∈ cls, ∃ p ∈ buckets, cl ∈ p.2) ∧
      (∀ p ∈ buckets, ∀ cl ∈ p.2, cl ∈ cls) ∧
      (buckets.map (fun p => p.2.length)).sum = cls.length := by
  induction ys generalizing cls with
  | nil =>
    simp only [List.map_nil, List.sum_nil] at hlen
    have hnil : cls = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil
    exact ⟨[], List.nodup_nil, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, rfl⟩
  | cons y tl ih =>
    simp only [List.map_cons, List.sum_cons] at hlen
    rw [List.nodup_cons] at hnd
    let chunk := cls.take (cap y)
    let rest := cls.drop (cap y)
    have hrest_le : rest.length ≤ (tl.map cap).sum := by
      simp only [rest, List.length_drop]; omega
    obtain ⟨bs, hbs_nd, hbs_ok, hbs_cov, hbs_sub, hbs_sum⟩ := ih hnd.2 rest hrest_le
    by_cases hchunk : chunk.length = 0
    · have hrest_eq : rest = cls := by
        have : cap y = 0 ∨ cls.length = 0 := by
          simp only [chunk, List.length_take] at hchunk; omega
        rcases this with h0 | h0
        · simp [rest, h0]
        · have hnil : cls = [] := List.eq_nil_of_length_eq_zero h0
          simp [rest, hnil]
      refine ⟨bs, hbs_nd, fun p hp => ⟨List.mem_cons_of_mem _ (hbs_ok p hp).1, (hbs_ok p hp).2⟩,
        fun cl hcl => hbs_cov cl (hrest_eq ▸ hcl),
        fun p hp cl hcl => hrest_eq ▸ hbs_sub p hp cl hcl,
        by rw [hbs_sum, hrest_eq]⟩
    · refine ⟨(y, chunk) :: bs, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hin => ?_, hbs_nd⟩
        obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hin
        dsimp only at hp1
        exact hnd.1 (hp1 ▸ (hbs_ok p hp).1)
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨List.mem_cons_self, by change 1 ≤ chunk.length; omega, by simp [chunk]⟩
        · exact ⟨List.mem_cons_of_mem _ (hbs_ok p hp').1, (hbs_ok p hp').2⟩
      · intro cl hcl
        have hsplit : cls = chunk ++ rest := (List.take_append_drop (cap y) cls).symm
        rw [hsplit] at hcl
        rcases List.mem_append.mp hcl with h1 | h2
        · exact ⟨(y, chunk), List.mem_cons_self, h1⟩
        · obtain ⟨p, hp, hclp⟩ := hbs_cov cl h2
          exact ⟨p, List.mem_cons_of_mem _ hp, hclp⟩
      · intro p hp cl hcl
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact List.mem_of_mem_take hcl
        · exact List.mem_of_mem_drop (hbs_sub p hp' cl hcl)
      · simp only [List.map_cons, List.sum_cons, hbs_sum, chunk, rest, List.length_take,
          List.length_drop]
        omega

lemma solve_clause_list {V : Type} [Fintype V] [DecidableEq V]
    {b_bits b' T : ℕ}
    (Fset : Set (Clause V))
    (S : Finset (Fin b_bits → ZMod 2)) (cap : (Fin b_bits → ZMod 2) → ℕ)
    (hS : S.Nonempty) (hcap1 : ∀ y ∈ S, 1 ≤ cap y)
    (cls : List (Clause V))
    (hclsF : ∀ cl ∈ cls, cl ∈ Fset)
    (hclsW : ∀ cl ∈ cls, cl.card ≤ b')
    (usedVars : Finset V)
    (hused : ∀ cl ∈ cls, ∀ l ∈ cl, l.1 ∈ usedVars)
    (hsum_cap : cls.length ≤ ∑ y ∈ S, cap y)
    (hbudget : cls.length ≤ S.sup cap ∨
      usedVars.card ≤ sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b_bits → ZMod 2))
        (y : Fin b_bits → ZMod 2), Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S} ∨
      (b' + 3) * cls.length ≤ T) :
    ∃ (H : Circuit) (pick : Fin b_bits → Fin (2 + Fintype.card V + H.size))
      (out : (Fin b_bits → ZMod 2) → Finset (Clause V)),
      ReadsBack (2 + Fintype.card V) H ∧
      (∀ g ∈ H.gates, gateValid g) ∧
      countAndOr H.gates ≤ T ∧
      (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ Fset) ∧
      (∀ x : V → Bool, (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)) ∈ S) ∧
      (∀ x : V → Bool,
        (∀ cl ∈ out (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)), ClauseSat x cl) →
        ∀ cl ∈ cls, ClauseSat x cl) := by
  rcases hbudget with hM | hFlat | hT
  ·
    obtain ⟨y₀, hy₀S, hy₀cap⟩ : ∃ y ∈ S, cls.length ≤ cap y := by
      by_cases h0 : cls.length = 0
      · obtain ⟨y₀, hy₀⟩ := hS
        exact ⟨y₀, hy₀, by omega⟩
      · obtain ⟨y₀, hy₀, hmax⟩ := Finset.exists_mem_eq_sup S hS cap
        exact ⟨y₀, hy₀, by rw [← hmax]; exact hM⟩
    obtain ⟨st, pick, hcnt, hmsg⟩ := build_const_circuit (V := V) y₀
    let out : (Fin b_bits → ZMod 2) → Finset (Clause V) := fun y => if y = y₀ then cls.toFinset else ∅
    refine ⟨⟨st.gs, 0⟩, pick, out, st.hrb, st.hval, by dsimp only; rw [hcnt]; omega, ?_, ?_, ?_⟩
    · intro y _
      by_cases hy : y = y₀
      · subst hy
        simp only [out, ↓reduceIte]
        exact ⟨(List.toFinset_card_le cls).trans hy₀cap, fun cl hcl => hclsF cl (List.mem_toFinset.mp hcl)⟩
      · simp [out, hy]
    · intro x
      change (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)) ∈ S
      rw [hmsg x]
      exact hy₀S
    · intro x hsat cl hcl
      change ∀ cl ∈ out (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)),
        ClauseSat x cl at hsat
      rw [hmsg x] at hsat
      exact hsat cl (by simp [out, hcl])
  ·
    obtain ⟨U, y₀, hUfr, hUS⟩ := exists_flat_witness S hS
    let m := usedVars.card
    have hm_le : m ≤ Module.finrank (ZMod 2) U := by rw [hUfr]; exact hFlat
    let bU := Module.finBasis (ZMod 2) U
    let vars : Fin m → V := fun t => (usedVars.equivFin.symm t).1
    let L : Fin m → (Fin b_bits → ZMod 2) := fun t => (bU ⟨t.val, lt_of_lt_of_le t.isLt hm_le⟩ : Fin b_bits → ZMod 2)
    obtain ⟨st, pick, hcnt, hmsg⟩ := build_affine_circuit y₀ vars L
    have hinj : ∀ x₁ x₂ : V → Bool,
        (y₀ + ∑ t : Fin m, boolToZ2 (x₁ (vars t)) • L t) =
        (y₀ + ∑ t : Fin m, boolToZ2 (x₂ (vars t)) • L t) →
        ∀ v ∈ usedVars, x₁ v = x₂ v := by
      intro x₁ x₂ heq v hv
      have hsum : ∑ t : Fin m, boolToZ2 (x₁ (vars t)) • L t =
          ∑ t : Fin m, boolToZ2 (x₂ (vars t)) • L t := add_left_cancel heq
      have hsubU : ∑ t : Fin m, (boolToZ2 (x₁ (vars t)) + boolToZ2 (x₂ (vars t))) •
          bU ⟨t.val, lt_of_lt_of_le t.isLt hm_le⟩ = 0 := by
        apply Subtype.ext
        simp only [add_smul, Finset.sum_add_distrib, Submodule.coe_add, Submodule.coe_sum,
          Submodule.coe_smul, ZeroMemClass.coe_zero]
        change (∑ t : Fin m, boolToZ2 (x₁ (vars t)) • L t) +
          (∑ t : Fin m, boolToZ2 (x₂ (vars t)) • L t) = 0
        rw [hsum]
        funext j
        simp [Pi.add_apply, z2_add_self]
      have hcoeff : ∀ t : Fin m, boolToZ2 (x₁ (vars t)) + boolToZ2 (x₂ (vars t)) = 0 := by
        let coeff : Fin (Module.finrank (ZMod 2) U) → ZMod 2 := fun k =>
          if hk : k.val < m then boolToZ2 (x₁ (vars ⟨k.val, hk⟩)) + boolToZ2 (x₂ (vars ⟨k.val, hk⟩)) else 0
        have hfull : ∑ k : Fin (Module.finrank (ZMod 2) U), coeff k • bU k = 0 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin (Module.finrank (ZMod 2) U) => k.val < m)]
          have h2 : ∑ k ∈ Finset.univ.filter (fun k : Fin (Module.finrank (ZMod 2) U) => ¬ k.val < m),
              coeff k • bU k = 0 := Finset.sum_eq_zero fun k hk => by
            have hge : ¬ k.val < m := (Finset.mem_filter.mp hk).2
            simp [coeff, hge]
          rw [h2, add_zero]
          have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin (Module.finrank (ZMod 2) U) => k.val < m),
              coeff k • bU k =
              ∑ t : Fin m, (boolToZ2 (x₁ (vars t)) + boolToZ2 (x₂ (vars t))) •
                bU ⟨t.val, lt_of_lt_of_le t.isLt hm_le⟩ := by
            refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => Fin.ext (congrArg (fun t : Fin m => t.val) h))
              (fun t _ => ⟨⟨t.val, lt_of_lt_of_le t.isLt hm_le⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, rfl⟩)
              (fun k hk => by
                have hlt : k.val < m := (Finset.mem_filter.mp hk).2
                simp [coeff, hlt])
          rw [h1, hsubU]
        intro t
        have hlin := Fintype.linearIndependent_iff.mp bU.linearIndependent coeff hfull
          ⟨t.val, lt_of_lt_of_le t.isLt hm_le⟩
        simpa [coeff, t.isLt] using hlin
      let t₀ : Fin m := usedVars.equivFin ⟨v, hv⟩
      have hvt : vars t₀ = v := by simp [vars, t₀]
      have h0 := hcoeff t₀
      rw [hvt] at h0
      have hbe : boolToZ2 (x₁ v) = boolToZ2 (x₂ v) := by
        rcases z2_cases (boolToZ2 (x₁ v)) with ha | ha <;>
          rcases z2_cases (boolToZ2 (x₂ v)) with hb | hb <;> simp_all
      exact boolToZ2_injective hbe
    let msgFn : (V → Bool) → (Fin b_bits → ZMod 2) :=
      fun x => y₀ + ∑ t : Fin m, boolToZ2 (x (vars t)) • L t
    let out : (Fin b_bits → ZMod 2) → Finset (Clause V) := fun y =>
      if h : ∃ x : V → Bool, msgFn x = y ∧ ∃ cl ∈ cls, ¬ ClauseSat x cl then
        {h.choose_spec.2.choose}
      else ∅
    refine ⟨⟨st.gs, 0⟩, pick, out, st.hrb, st.hval, by dsimp only; rw [hcnt]; omega, ?_, ?_, ?_⟩
    · intro y hyS
      by_cases hex : ∃ x : V → Bool, msgFn x = y ∧ ∃ cl ∈ cls, ¬ ClauseSat x cl
      · simp only [out, hex, ↓reduceDIte]
        refine ⟨by simp [hcap1 y hyS], fun cl hcl => ?_⟩
        simp only [Finset.mem_singleton] at hcl
        subst hcl
        exact hclsF _ hex.choose_spec.2.choose_spec.1
      · simp [out, hex]
    · intro x
      change (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)) ∈ S
      rw [hmsg x]
      refine hUS _ (Submodule.sum_mem U fun t _ => Submodule.smul_mem U _ ?_)
      exact (bU ⟨t.val, lt_of_lt_of_le t.isLt hm_le⟩).2
    · intro x hsat cl hcl
      change ∀ cl ∈ out (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)),
        ClauseSat x cl at hsat
      rw [hmsg x] at hsat
      by_contra hnsat
      have hex : ∃ x' : V → Bool, msgFn x' = msgFn x ∧ ∃ c ∈ cls, ¬ ClauseSat x' c :=
        ⟨x, rfl, cl, hcl, hnsat⟩
      let x' := hex.choose
      have hx'eq : msgFn x' = msgFn x := hex.choose_spec.1
      let cl' := hex.choose_spec.2.choose
      have hcl' : cl' ∈ cls ∧ ¬ ClauseSat x' cl' := hex.choose_spec.2.choose_spec
      have hmem : cl' ∈ out (msgFn x) := by simp [out, hex, cl']
      have hsat' : ClauseSat x cl' := hsat cl' hmem
      obtain ⟨l, hlcl', hxl⟩ := hsat'
      have hxv : x' l.1 = x l.1 := hinj x' x hx'eq l.1 (hused cl' hcl'.1 l hlcl')
      exact hcl'.2 ⟨l, hlcl', hxv.trans hxl⟩
  ·
    have hsum_list : (S.toList.map cap).sum = ∑ y ∈ S, cap y := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    obtain ⟨buckets, hnd, hbok, hbcov, hbsub, hbsum⟩ :=
      pack_buckets S.toList (Finset.nodup_toList S) cap cls (by rw [hsum_list]; exact hsum_cap)
    obtain ⟨y_fb, hy_fb⟩ := hS
    obtain ⟨st, pick, hcnt, hspec⟩ :=
      build_bucket_search_circuit b' y_fb buckets (fun p hp cl hcl => hclsW cl (hbsub p hp cl hcl))
    have hblen : buckets.length ≤ cls.length := by
      have h1 : buckets.length ≤ (buckets.map fun p => p.2.length).sum := by
        have hge : ∀ l : List ((Fin b_bits → ZMod 2) × List (Clause V)),
            (∀ p ∈ l, 1 ≤ p.2.length) → l.length ≤ (l.map fun p => p.2.length).sum := by
          intro l
          induction l with
          | nil => intro _; simp
          | cons p tl ih =>
            intro h
            simp only [List.length_cons, List.map_cons, List.sum_cons]
            have h1 := h p List.mem_cons_self
            have h2 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
            omega
        exact hge buckets (fun p hp => (hbok p hp).2.1)
      omega
    let out : (Fin b_bits → ZMod 2) → Finset (Clause V) := fun y =>
      if h : ∃ p ∈ buckets, p.1 = y then h.choose.2.toFinset else ∅
    have hout_eq : ∀ p ∈ buckets, out p.1 = p.2.toFinset := by
      intro p hp
      have hex : ∃ q ∈ buckets, q.1 = p.1 := ⟨p, hp, rfl⟩
      simp only [out, hex, ↓reduceDIte]
      have hq := hex.choose_spec
      have hpeq : hex.choose = p := by
        have hidx : ∀ (l : List ((Fin b_bits → ZMod 2) × List (Clause V))),
            (l.map Prod.fst).Nodup → ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a = b := by
          intro l
          induction l with
          | nil => intro _ _ ha; simp at ha
          | cons hd tl ih =>
            intro hnd' a ha b hb hab
            rw [List.map_cons, List.nodup_cons] at hnd'
            rcases List.mem_cons.mp ha with rfl | ha' <;>
              rcases List.mem_cons.mp hb with rfl | hb'
            · rfl
            · exfalso; exact hnd'.1 (List.mem_map.mpr ⟨b, hb', hab.symm⟩)
            · exfalso; exact hnd'.1 (List.mem_map.mpr ⟨a, ha', hab⟩)
            · exact ih hnd'.2 a ha' b hb' hab
        exact hidx buckets hnd hex.choose hq.1 p hp hq.2
      rw [hpeq]
    refine ⟨⟨st.gs, 0⟩, pick, out, st.hrb, st.hval, by dsimp only; rw [hbsum] at hcnt; nlinarith, ?_, ?_, ?_⟩
    · intro y _
      by_cases hex : ∃ p ∈ buckets, p.1 = y
      · simp only [out, hex, ↓reduceDIte]
        have hp := hex.choose_spec
        refine ⟨(List.toFinset_card_le _).trans (by
          have h2 := (hbok _ hp.1).2.2
          rwa [hp.2] at h2), fun cl hcl => ?_⟩
        exact hclsF cl (hbsub _ hp.1 cl (List.mem_toFinset.mp hcl))
      · simp only [out, hex, ↓reduceDIte]
        exact ⟨Nat.zero_le _, by simp⟩
    · intro x
      rcases hspec x with ⟨p, hp, hy, _⟩ | ⟨hy, _⟩
      · change (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)) ∈ S
        rw [hy]
        exact Finset.mem_toList.mp (hbok p hp).1
      · change (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)) ∈ S
        rw [hy]
        exact hy_fb
    · intro x hsat cl hcl
      rcases hspec x with ⟨p, hp, hy, cl', hcl', hnsat⟩ | ⟨_, hall⟩
      · exfalso
        change ∀ c ∈ out (fun j => boolToZ2 ((wiresOf st.gs (inBits x)).getD (pick j).val false)),
          ClauseSat x c at hsat
        rw [hy, hout_eq p hp] at hsat
        exact hnsat (hsat cl' (List.mem_toFinset.mpr hcl'))
      · obtain ⟨p, hp, hclp⟩ := hbcov cl hcl
        exact hall p hp cl hclp

lemma upper_bound_main (n b : ℕ) (hn : 1 ≤ n)
    (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b) (hRd : RightDegLe G b)
    (C : ℕ)
    (hCb' : max 2 b ≤ C)
    (hC0 : 3 * ((max 2 b + 3) * (3 * (max 2 b) ^ 2 + 2) + 2 * max 2 b) ≤ C)
    (b_bits T h R : ℕ) (S : Finset (Fin b_bits → ZMod 2)) (cap : (Fin b_bits → ZMod 2) → ℕ)
    (hR : 1 ≤ R) (hS : S.Nonempty) (hcap1 : ∀ y ∈ S, 1 ≤ cap y)
    (hB : C * min n ((R + 1) ^ C * h) ≤
      min (∑ y ∈ S, cap y) (T + S.sup cap + sSup {k : ℕ |
        ∃ (U : Submodule (ZMod 2) (Fin b_bits → ZMod 2)) (y : Fin b_bits → ZMod 2),
          Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S})) :
    ∃ (H : Circuit) (pick : Fin b_bits → Fin (2 + Fintype.card (GEdge G) + H.size))
      (out : (Fin b_bits → ZMod 2) → Finset (Clause (GEdge G))),
      ReadsBack (2 + Fintype.card (GEdge G)) H ∧
      (∀ g ∈ H.gates, gateValid g) ∧
      countAndOr H.gates ≤ T ∧
      (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ funGraphPHP G) ∧
      (∀ x : GEdge G → Bool, (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)) ∈ S) ∧
      ∀ μ : (GEdge G → Bool) → ℝ,
        ((∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧
          ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v)))) →
        (2 : ℝ) ^ h *
          (∑ x ∈ Finset.univ.filter (fun x : GEdge G → Bool =>
            @decide (∀ cl ∈ out (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)),
              ClauseSat x cl) (Classical.propDecidable _)), μ x) ≤ ∑ x, μ x := by
  let b' := max 2 b
  let flat := sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) (Fin b_bits → ZMod 2)) (y : Fin b_bits → ZMod 2),
    Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}
  have hBsum : C * min n ((R + 1) ^ C * h) ≤ ∑ y ∈ S, cap y := hB.trans (min_le_left _ _)
  have hB3 : C * min n ((R + 1) ^ C * h) ≤ T + S.sup cap + flat := hB.trans (min_le_right _ _)
  by_cases hcase : n ≤ (R + 1) ^ C * h
  ·
    rw [min_eq_left hcase] at hBsum hB3
    obtain ⟨Ffin, hFmem, hFcard⟩ := funGraphPHP_finset hn G hLd hRd
    let C₀ := (b' + 3) * (3 * b' ^ 2 + 2) + 2 * b'
    have hC0_def : C₀ = (b' + 3) * (3 * b' ^ 2 + 2) + 2 * b' := rfl
    have hb'2 : 2 ≤ b' := le_max_left 2 b
    have hC3 : 3 * C₀ ≤ C := hC0
    have hcls_len : Ffin.toList.length ≤ (3 * b' ^ 2 + 2) * n := by
      rw [Finset.length_toList]; exact hFcard
    have hcardV : (Finset.univ : Finset (GEdge G)).card ≤ 2 * b' * n := by
      rw [Finset.card_univ]
      have h1 := card_gedge_le G b hLd
      have hb_le : b ≤ b' := le_max_right 2 b
      nlinarith
    have hC0_ge1 : (3 * b' ^ 2 + 2) * n ≤ C₀ * n := by
      have : 3 * b' ^ 2 + 2 ≤ C₀ := by nlinarith
      exact Nat.mul_le_mul_right n this
    have hC0_ge2 : 2 * b' * n ≤ C₀ * n := by
      have : 2 * b' ≤ C₀ := by nlinarith
      exact Nat.mul_le_mul_right n this
    have hC0_ge3 : (b' + 3) * ((3 * b' ^ 2 + 2) * n) ≤ C₀ * n := by
      have : (b' + 3) * (3 * b' ^ 2 + 2) ≤ C₀ := by nlinarith
      calc (b' + 3) * ((3 * b' ^ 2 + 2) * n) = ((b' + 3) * (3 * b' ^ 2 + 2)) * n := by ring
        _ ≤ C₀ * n := Nat.mul_le_mul_right n this
    have hbudget : Ffin.toList.length ≤ S.sup cap ∨
        (Finset.univ : Finset (GEdge G)).card ≤ flat ∨
        (b' + 3) * Ffin.toList.length ≤ T := by
      have h3 : 3 * (C₀ * n) ≤ T + S.sup cap + flat := by nlinarith
      by_cases h1 : C₀ * n ≤ S.sup cap
      · left; omega
      · by_cases h2 : C₀ * n ≤ flat
        · right; left; omega
        · right; right
          have hTge : C₀ * n ≤ T := by omega
          have hmul : (b' + 3) * Ffin.toList.length ≤ (b' + 3) * ((3 * b' ^ 2 + 2) * n) :=
            Nat.mul_le_mul_left _ hcls_len
          omega
    obtain ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, hsolve⟩ :=
      solve_clause_list (funGraphPHP G) S cap hS hcap1 Ffin.toList
        (fun cl hcl => (hFmem cl).mp (Finset.mem_toList.mp hcl))
        (fun cl hcl => funGraphPHP_width G b hLd cl ((hFmem cl).mp (Finset.mem_toList.mp hcl)))
        Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
        (by
          have : C₀ * n ≤ C * n := Nat.mul_le_mul_right n (by omega)
          omega) hbudget
    refine ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, fun μ hμ => ?_⟩
    have hemp : Finset.univ.filter (fun x : GEdge G → Bool =>
        @decide (∀ cl ∈ out (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)),
          ClauseSat x cl) (Classical.propDecidable _)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx
      have hsat_all : Satisfies x (funGraphPHP G) := fun cl hcl =>
        hsolve x hx cl (Finset.mem_toList.mpr ((hFmem cl).mpr hcl))
      exact funGraphPHP_unsat G (by omega) ⟨x, hsat_all⟩
    rw [hemp, Finset.sum_empty, mul_zero]
    exact le_of_lt hμ.2.1
  ·
    push Not at hcase
    rw [min_eq_right (le_of_lt hcase)] at hBsum hB3
    let m := (R + 1) ^ b' * h
    have hm_le_pow : m ≤ (R + 1) ^ C * h :=
      Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by omega) hCb')
    have hm_le_n : m ≤ n + 1 := by omega
    let cls : List (Clause (GEdge G)) :=
      (List.finRange m).map (fun t => pigeonClause G ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩)
    let usedVars : Finset (GEdge G) :=
      Finset.univ.filter (fun e : GEdge G => e.1.1.val < m)
    have hused_card : usedVars.card ≤ b' * m := by
      have hsub : usedVars ⊆ (Finset.univ : Finset (Fin m)).biUnion
          (fun t => Finset.univ.filter (fun e : GEdge G => e.1.1 = ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩)) := by
        intro e he
        have hlt : e.1.1.val < m := (Finset.mem_filter.mp he).2
        refine Finset.mem_biUnion.mpr ⟨⟨e.1.1.val, hlt⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext rfl⟩⟩
      calc usedVars.card
          ≤ ∑ t : Fin m, (Finset.univ.filter (fun e : GEdge G =>
              e.1.1 = ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩)).card :=
            (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        _ ≤ ∑ _t : Fin m, b' := Finset.sum_le_sum fun t _ => by
            let E_t := Finset.univ.filter (fun e : GEdge G =>
              e.1.1 = ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩)
            have hinj : Set.InjOn (fun e : GEdge G => e.1.2) (E_t : Set (GEdge G)) := by
              rintro ⟨⟨i₁, j₁⟩, h₁⟩ hm₁ ⟨⟨i₂, j₂⟩, h₂⟩ hm₂ heq
              simp only [Finset.mem_coe, E_t, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
              dsimp only at heq
              subst heq; subst hm₁; subst hm₂; rfl
            have hsub' : E_t.image (fun e => e.1.2) ⊆ G ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩ := by
              intro j hj
              obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
              have h1 : e.1.1 = ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩ := (Finset.mem_filter.mp he).2
              exact h1 ▸ e.2
            calc E_t.card = (E_t.image (fun e => e.1.2)).card := (Finset.card_image_of_injOn hinj).symm
              _ ≤ (G _).card := Finset.card_le_card hsub'
              _ ≤ b := hLd _
              _ ≤ b' := le_max_right 2 b
        _ = m * b' := by simp
        _ = b' * m := Nat.mul_comm _ _
    have hcls_len : cls.length = m := by simp [cls]
    have hC_ge : 3 * (b' + 3) ≤ C := by
      have hb'2 : 2 ≤ b' := le_max_left 2 b
      have h1 : 3 * (b' + 3) ≤ 3 * ((b' + 3) * (3 * b' ^ 2 + 2) + 2 * b') := by
        have hpos : 1 ≤ 3 * b' ^ 2 + 2 := by omega
        have hmul : b' + 3 ≤ (b' + 3) * (3 * b' ^ 2 + 2) := Nat.le_mul_of_pos_right _ hpos
        omega
      exact h1.trans hC0
    have hbudget : cls.length ≤ S.sup cap ∨ usedVars.card ≤ flat ∨ (b' + 3) * cls.length ≤ T := by
      have h3 : 3 * ((b' + 3) * m) ≤ T + S.sup cap + flat := by
        have h1 : (3 * (b' + 3)) * m ≤ C * m := Nat.mul_le_mul_right m hC_ge
        have h2 : C * m ≤ C * ((R + 1) ^ C * h) := Nat.mul_le_mul_left C hm_le_pow
        have h4 : 3 * ((b' + 3) * m) = (3 * (b' + 3)) * m := by ring
        omega
      by_cases h1 : (b' + 3) * m ≤ S.sup cap
      · left
        have hle : m ≤ (b' + 3) * m := Nat.le_mul_of_pos_left m (by omega)
        rw [hcls_len]; omega
      · by_cases h2 : (b' + 3) * m ≤ flat
        · right; left
          have hle : b' * m ≤ (b' + 3) * m := Nat.mul_le_mul_right m (by omega)
          omega
        · right; right; rw [hcls_len]; omega
    obtain ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, hsolve⟩ :=
      solve_clause_list (funGraphPHP G) S cap hS hcap1 cls
        (fun cl hcl => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hcl
          exact pigeonClause_mem G _)
        (fun cl hcl => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hcl
          exact funGraphPHP_width G b hLd _ (pigeonClause_mem G _))
        usedVars
        (fun cl hcl l hl => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hcl
          have h1 : l.1.1.1 = ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩ := (Finset.mem_filter.mp hl).2.1
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [h1]; exact t.isLt)
        (by
          rw [hcls_len]
          have hC1 : 1 ≤ C := by omega
          have h1 : m ≤ C * m := Nat.le_mul_of_pos_left m hC1
          have h2 : C * m ≤ C * ((R + 1) ^ C * h) := Nat.mul_le_mul_left C hm_le_pow
          omega) hbudget
    refine ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, fun μ hμ => ?_⟩
    have hsub_bad : Finset.univ.filter (fun x : GEdge G → Bool =>
          @decide (∀ cl ∈ out (fun j => boolToZ2 ((H.wires (inBits x)).getD (pick j).val false)),
            ClauseSat x cl) (Classical.propDecidable _)) ⊆
        Finset.univ.filter (fun x : GEdge G → Bool =>
          @decide (∀ t : Fin m, ClauseSat x (pigeonClause G ⟨t.val, lt_of_lt_of_le t.isLt hm_le_n⟩))
            (Classical.propDecidable _)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx ⊢
      intro t
      exact hsolve x hx _ (List.mem_map.mpr ⟨t, List.mem_finRange t, rfl⟩)
    have hmass := disjoint_pigeon_mass_bound G hLd b' (le_max_right 2 b) hm_le_n μ hμ.1 hμ.2.2
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub_bad (fun x _ _ => hμ.1 x)
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hmass

end UpperBound

end

end PEqualNP.Outside.L_pcx_407_aux

theorem PEqualNP.Outside.L_pcx_407 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let X := V → Bool
    let e := Fintype.card V
    let F := PEqualNP.Expanders.funGraphPHP G
    ∀ (b T h R : ℕ) (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ),
      1 ≤ R → S.Nonempty → (∀ y ∈ S, 1 ≤ cap y) →
      let Y := Fin b → ZMod 2
      let flat := sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) Y) (y : Y),
        Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}
      let B := min (∑ y ∈ S, cap y) (T + S.sup cap + flat)
      let L := Nat.clog 2 (R+1)
      let smooth := fun μ : X → ℝ => (∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧
        ∀ x v, μ x ≤ (R : ℝ) * μ (Function.update x v (!(x v)))
      let possible := fun (allSources : Bool) => ∃ (H : PEqualNP.CircuitLowerBounds.Circuit)
          (pick : Fin b → Fin (2+e+H.size)) (out : Y → Finset (PEqualNP.ProofComplexity.Clause V)),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+e) H ∧
        (∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
        H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ T ∧
        (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F) ∧
        let msg := fun (x : X) (j : Fin b) =>
          let ws := H.wires ([false,true] ++ List.ofFn (fun i : Fin e => x ((Fintype.equivFin V).symm i)))
          ((ws.getD (pick j).val false).toNat : ZMod 2)
        (∀ x : X, msg x ∈ S) ∧
        let bad := Finset.univ.filter (fun x : X =>
          @decide (∀ cl ∈ out (msg x), PEqualNP.ProofComplexity.ClauseSat x cl) (Classical.propDecidable _))
        let accurate := fun μ : X → ℝ => (2 : ℝ)^h * (∑ x ∈ bad, μ x) ≤ ∑ x, μ x
        if allSources then (∀ μ, smooth μ → accurate μ) else (∃ μ, smooth μ ∧ accurate μ)
      (possible false → min (n*L) h ≤ C*L*B) ∧
      (C * min n ((R+1)^C*h) ≤ B → possible true)) := by
  obtain ⟨b, s₀, n₀_0, hs₀, hL043⟩ := PEqualNP.Outside.L_pcx_407_aux.InlinePC.L043_inline
  let b' := max 2 b
  let C₀ := (b' + 3) * (3 * b' ^ 2 + 2) + 2 * b'
  let C := max (3 * s₀ * b' ^ 2) (3 * C₀)
  let n₀ := max n₀_0 (max s₀ 1)
  have hC2 : 2 ≤ C := by
    have : 2 ≤ b' := le_max_left 2 b
    have : 3 * C₀ ≤ C := le_max_right _ _
    omega
  refine ⟨C, n₀, hC2, fun n hn => ?_⟩
  obtain ⟨G, hLd, hRd, hExp⟩ := hL043 n (le_trans (le_max_left _ _) hn)
  have hbC : b ≤ C := by
    have : b ≤ b' := le_max_right 2 b
    have : 3 * C₀ ≤ C := le_max_right _ _
    omega
  refine ⟨G, fun i => (hLd i).trans hbC, fun j => (hRd j).trans hbC, ?_⟩
  intro V X e F b_bits T h R S cap hR hS hcap1 Y flat B L smooth possible
  constructor
  · rintro ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, μ, ⟨hμ0, hμpos, hμsm⟩, hacc⟩
    exact PEqualNP.Outside.L_pcx_407_aux.lower_bound_main n b s₀ hs₀
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
      G hLd hExp C (le_max_left _ _) b_bits T h R S cap hR hS hcap1 H pick out
      hrb hval hT hout hmsgS μ hμ0 hμpos hμsm hacc
  · intro hB
    obtain ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, hall⟩ :=
      PEqualNP.Outside.L_pcx_407_aux.upper_bound_main n b
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
        G hLd hRd C
        (by have : 3 * C₀ ≤ C := le_max_right _ _; omega)
        (le_max_right _ _)
        b_bits T h R S cap hR hS hcap1 hB
    exact ⟨H, pick, out, hrb, hval, hT, hout, hmsgS, hall⟩
