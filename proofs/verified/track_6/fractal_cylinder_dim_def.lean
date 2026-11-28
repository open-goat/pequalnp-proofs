-- Track 6: Intermediate Ordinal-Fractal Cut Number System (𝓘_cut)
-- Verified leaf: Fractal cylinder dimension and survival measure.
--
-- Defines the cylinder survival measure (3/4)^k which models
-- finite bit-reservoir exhaustion across nested 2^k-adic cuts.
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

noncomputable def cylinderSurvivalMeasure (k : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ k

-- The cylinder survival measure strictly decreases with depth k.
theorem cylinderSurvivalMeasure_decreasing (k : ℕ) :
    cylinderSurvivalMeasure (k + 1) < cylinderSurvivalMeasure k := by
  have h : (3 / 4 : ℝ) > 0 := by norm_num
  have h₂ : (3 / 4 : ℝ) < 1 := by norm_num
  calc
    cylinderSurvivalMeasure (k + 1) = (3 / 4 : ℝ) ^ (k + 1) := rfl
    _ = (3 / 4 : ℝ) ^ k * (3 / 4 : ℝ) := by
      rw [pow_succ]
      <;> ring
    _ < (3 / 4 : ℝ) ^ k * 1 := by
      gcongr
      <;> norm_num
    _ = (3 / 4 : ℝ) ^ k := by ring
    _ = cylinderSurvivalMeasure k := rfl
