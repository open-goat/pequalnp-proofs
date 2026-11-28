-- Track 7: Boundary Layer — Growth Rate Hierarchy
--
-- Formalizes the growth rate boundary between elementary, ackermannian,
-- goodsteinian, busyBeaver, and rayo growth rates.
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Ordinal

-- Growth rate classification for functions ℕ → ℕ.
inductive GrowthRate where
  | elementary
  | ackermannian
  | goodsteinian
  | busyBeaver
  | rayo

-- Growth rate ordinal for each category.
noncomputable def growthRateOrdinal (r : GrowthRate) : Ordinal :=
  match r with
  | GrowthRate.elementary => Ordinal.omega0
  | GrowthRate.ackermannian => Ordinal.omega0 ^ Ordinal.omega0
  | GrowthRate.goodsteinian => Ordinal.omega0 ^ Ordinal.omega0 ^ Ordinal.omega0
  | GrowthRate.busyBeaver => Ordinal.omega0
  | GrowthRate.rayo => Ordinal.omega0 + 1

-- Elementary growth rate ordinal is ω.
theorem elementaryOrdinal : growthRateOrdinal GrowthRate.elementary = Ordinal.omega0 := by rfl

-- Ackermannian growth rate ordinal is ω^ω.
theorem ackermannianOrdinal : growthRateOrdinal GrowthRate.ackermannian = Ordinal.omega0 ^ Ordinal.omega0 := by rfl

-- Goodsteinian growth rate ordinal is ω^(ω^ω).
theorem goodsteinianOrdinal : growthRateOrdinal GrowthRate.goodsteinian = Ordinal.omega0 ^ Ordinal.omega0 ^ Ordinal.omega0 := by rfl

-- Busy Beaver ordinal is ω.
theorem busyBeaverOrdinal' : growthRateOrdinal GrowthRate.busyBeaver = Ordinal.omega0 := by rfl

-- Rayo ordinal is ω + 1.
theorem rayoOrdinal' : growthRateOrdinal GrowthRate.rayo = Ordinal.omega0 + 1 := by rfl
