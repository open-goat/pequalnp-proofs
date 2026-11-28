-- Track 6: Intermediate Ordinal-Fractal Cut Number System (𝓘_cut)
-- Verified leaf: CutCardinalityMode definition and basic properties.
--
-- Tri-modal cardinality classification for elements of 𝓘_cut:
--   - decidableCollapsible: constructive ordinal layers bijective to ω
--   - undecidableModelSensitive: cardinal status independent of base axioms
--   - dualInternalExternal: cardinal internally, not externally
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Ordinal

inductive CutCardinalityMode where
  | decidableCollapsible
  | undecidableModelSensitive
  | dualInternalExternal

-- Every CutCardinalityMode is one of the three constructors.
theorem cut_cardinality_mode_cases (m : CutCardinalityMode) :
    m = CutCardinalityMode.decidableCollapsible ∨
    m = CutCardinalityMode.undecidableModelSensitive ∨
    m = CutCardinalityMode.dualInternalExternal := by
  cases m with
  | decidableCollapsible => exact Or.inl rfl
  | undecidableModelSensitive => exact Or.inr (Or.inl rfl)
  | dualInternalExternal => exact Or.inr (Or.inr rfl)
