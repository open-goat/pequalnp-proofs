-- Track 6: Intermediate Ordinal-Fractal Cut Number System (𝓘_cut)
-- Verified leaf: IntermediateCutElem definition and basic properties.
--
-- Structure: rank : Ordinal, mode : CutCardinalityMode, dimH : Rat.
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Ordinal

inductive CutCardinalityMode where
  | decidableCollapsible
  | undecidableModelSensitive
  | dualInternalExternal

structure IntermediateCutElem where
  rank : Ordinal
  mode : CutCardinalityMode
  dimH : Rat

-- The zero element: rank 0, decidableCollapsible mode, dimH 0.
def icut_zero : IntermediateCutElem :=
  { rank := 0, mode := CutCardinalityMode.decidableCollapsible, dimH := 0 }

-- A finite-rank element: rank = n : Ordinal for n : ℕ.
def icut_finite (n : ℕ) : IntermediateCutElem :=
  { rank := (n : Ordinal), mode := CutCardinalityMode.decidableCollapsible, dimH := 0 }

-- A transfinite element at rank ω.
def icut_omega : IntermediateCutElem :=
  { rank := Ordinal.omega0, mode := CutCardinalityMode.dualInternalExternal, dimH := 0 }

-- The zero element has rank 0.
theorem icut_zero_rank : icut_zero.rank = 0 := by rfl

-- Finite elements have rank equal to their natural number (as ordinal).
theorem icut_finite_rank (n : ℕ) : (icut_finite n).rank = (n : Ordinal) := by rfl

-- Omega element has rank ω.
theorem icut_omega_rank : icut_omega.rank = Ordinal.omega0 := by rfl

-- The cut order on 𝓘_cut: H₁ ≺ H₂ iff H₁.rank < H₂.rank.
def icut_lt (a b : IntermediateCutElem) : Prop := a.rank < b.rank
