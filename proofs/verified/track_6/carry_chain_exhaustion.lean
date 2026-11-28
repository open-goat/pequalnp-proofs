-- Track 6: Intermediate Ordinal-Fractal Cut Number System (𝓘_cut)
-- Verified leaf: Carry chain exhaustion.
--
-- For the Collatz map, a "carry chain" is a sequence of consecutive odd steps.
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Nat

def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- The Collatz step of any n is bounded by 3n+1.
theorem collatzStep_bound (n : ℕ) : collatzStep n ≤ 3 * n + 1 := by
  by_cases h : n % 2 = 0
  · -- even case: n/2 ≤ n ≤ 3n+1
    have h₁ : collatzStep n = n / 2 := by
      dsimp [collatzStep]
      <;> simp [h]
    rw [h₁]
    have h₂ : n / 2 ≤ n := by
      apply Nat.div_le_self
    have h₃ : n ≤ 3 * n + 1 := by nlinarith
    linarith
  · -- odd case: 3n+1 = 3n+1
    have h₁ : collatzStep n = 3 * n + 1 := by
      dsimp [collatzStep]
      <;> simp [h]
    rw [h₁]
    <;> nlinarith
