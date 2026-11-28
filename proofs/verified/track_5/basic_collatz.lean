-- Track 5: Computable Collatz Beaver bounds — basic verified facts.
-- Self-contained leaf file (matches blueprint/Target.lean semantics).
-- Proven directly as part of the bootstrap; zero `sorry`s.

import Mathlib

def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatzIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

-- The step of a positive number is always positive.
theorem collatzStep_pos (n : ℕ) : 0 < n → 0 < collatzStep n := by
  intro hn
  by_cases h : n % 2 = 0
  · -- even branch: n > 0 and even => n >= 2 => n / 2 > 0
    have h1 : collatzStep n = n / 2 := by
      dsimp [collatzStep]
      <;> simp [h]
    rw [h1]
    have h2 : 2 <= n := by
      by_contra h3
      have h4 : n <= 1 := by omega
      have h5 : n = 0 ∨ n = 1 := by omega
      rcases h5 with (rfl | rfl)
      · exfalso; linarith
      · norm_num at h <;> contradiction
    have h3 : 1 <= n / 2 := by
      by_contra h4
      have h5 : n / 2 = 0 := by
        have h6 : n / 2 < 1 := by linarith
        omega
      have h6 : n < 2 := by
        have h7 : n / 2 = 0 := h5
        have h8 : n < 2 := by
          rw [Nat.div_eq_zero_iff_lt] at h7 <;> norm_num at h7 ⊢ <;> omega
        exact h8
      linarith
    linarith
  · -- odd branch: 3 * n + 1 > 0
    have h1 : collatzStep n = 3 * n + 1 := by
      dsimp [collatzStep]
      <;> simp [h]
    rw [h1]
    have h2 : 0 < 3 * n + 1 := by
      have h3 : 0 < n := hn
      nlinarith
    linarith

-- An even positive step strictly decreases.
theorem collatzStep_even_decrease (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    collatzStep n < n := by
  have h1 : collatzStep n = n / 2 := by
    dsimp [collatzStep]
    <;> simp [he]
  rw [h1]
  have h2 : 1 < n := by
    by_contra h3
    have h4 : n <= 1 := by omega
    have h5 : n = 0 ∨ n = 1 := by omega
    rcases h5 with (rfl | rfl)
    · exfalso; linarith
    · norm_num at he <;> contradiction
  have h3 : n / 2 < n := by
    apply Nat.div_lt_self
    <;> norm_num
    <;> linarith [h2]
  exact h3

-- Zero iterations return the input unchanged.
theorem collatzIter_zero (n : ℕ) : collatzIter 0 n = n := by
  rfl

-- collatzStep 1 = 4.
theorem collatzStep_one : collatzStep 1 = 4 := by
  norm_num [collatzStep]
