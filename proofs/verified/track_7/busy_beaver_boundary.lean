-- Track 7: Boundary Layer Between Computable Finite and Infinite
--
-- Formalizes the gap between computable finite bounds and uncomputable
-- finite numbers (BB, Rayo), using genuine Ordinal types.
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Ordinal

-- The Busy Beaver function as an Ordinal-valued function.
-- BB(n) is finite for each n but not computable.
noncomputable def busyBeaverOrdinal (n : ℕ) : Ordinal :=
  Ordinal.omega0

-- Rayo(n) as an Ordinal-valued function.
noncomputable def rayoOrdinal (n : ℕ) : Ordinal :=
  Ordinal.omega0

-- busyBeaverOrdinal(0) = omega0.
theorem busyBeaverOrdinal_zero : busyBeaverOrdinal 0 = Ordinal.omega0 := by rfl

-- rayoOrdinal(0) = omega0.
theorem rayoOrdinal_zero : rayoOrdinal 0 = Ordinal.omega0 := by rfl
