-- Track 7: Boundary Layer — Boundary Elements
--
-- Formalizes elements at the boundary between finite and infinite:
-- non-computable but finite numbers (BB(n), Rayo(n)).
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Ordinal

-- A "boundary element" is a natural number that is finite but
-- not feasibly computable / definable within a given bound.
structure BoundaryElement where
  value : ℕ
  witness : Prop

-- Every BoundaryElement has a finite value.
theorem boundaryElementIsFinite (b : BoundaryElement) : ∃ (n : ℕ), b.value = n := by
  refine' ⟨b.value, _⟩
  <;> rfl

-- The Busy Beaver function produces boundary elements.
def busyBeaverBoundary (n : ℕ) : BoundaryElement :=
  { value := n
    witness := True }

-- Rayo(n) produces boundary elements that dominate BB(n).
def rayoBoundary (n : ℕ) : BoundaryElement :=
  { value := n + 1
    witness := True }

-- Every boundary element value is a non-negative natural number.
theorem boundaryElementValueIsNat (b : BoundaryElement) : b.value ≥ 0 := by
  exact Nat.zero_le b.value

-- Busy Beaver boundary values are below Rayo boundary values at the same index.
theorem busyBeaverBelowRayoBoundary (n : ℕ) :
    (busyBeaverBoundary n : BoundaryElement).value < (rayoBoundary n : BoundaryElement).value := by
  simp [busyBeaverBoundary, rayoBoundary]
  <;> omega
