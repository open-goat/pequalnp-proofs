-- Track 6: Intermediate Ordinal-Fractal Cut Number System (𝓘_cut)
-- Verified leaf: Consecutive ν₂(3n+1)=1 bound for Mersenne numbers.
--
-- Zero `sorry`. No forbidden axioms.

import Mathlib

open Nat

def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- For k ≥ 2: 3(2^k-1)+1 = 3·2^k - 2 = 2(3·2^(k-1)-1).
theorem mersenne_half (k : ℕ) (hk : 2 ≤ k) :
    (3 * (2 ^ k - 1) + 1) / 2 = 3 * 2 ^ (k - 1) - 1 := by
  have h₁ : k ≥ 1 := by omega
  have h₂ : 2 ^ k ≥ 4 := by
    have h₃ : ∀ n : ℕ, n ≥ 2 → 2 ^ n ≥ 4 := by
      intro n hn
      induction' hn with n hn IH
      · norm_num
      · cases n with
        | zero => contradiction
        | succ n =>
          simp_all [pow_succ]
          <;> nlinarith
    exact h₃ k hk
  
  have h₃ : 3 * (2 ^ k - 1) + 1 = 3 * 2 ^ k - 2 := by
    have h₄ : 2 ^ k - 1 + 1 = 2 ^ k := by omega
    have h₅ : 3 * (2 ^ k - 1) = 3 * 2 ^ k - 3 := by
      have h₆ : 3 ≤ 3 * 2 ^ k := by nlinarith
      have h₆ : 3 * (2 ^ k - 1) + 3 = 3 * 2 ^ k := by
        have h₇ : 3 * (2 ^ k - 1) + 3 = 3 * ((2 ^ k - 1) + 1) := by ring
        rw [h₇]
        <;> rw [h₄]
        <;> ring
      omega
    calc
      3 * (2 ^ k - 1) + 1 = (3 * 2 ^ k - 3) + 1 := by rw [h₅]
      _ = 3 * 2 ^ k - 2 := by omega
      _ = 3 * 2 ^ k - 2 := by rfl

  rw [h₃]
  have h₄ : 3 * 2 ^ k - 2 = 2 * (3 * 2 ^ (k - 1) - 1) := by
    have h₅ : k - 1 + 1 = k := by omega
    have h₅ : 2 ^ k = 2 * 2 ^ (k - 1) := by
      have h₆ : k = (k - 1) + 1 := by omega
      rw [h₆]
      simp [pow_add, pow_one, mul_comm]
      <;> ring_nf
    calc
      3 * 2 ^ k - 2 = 3 * (2 * 2 ^ (k - 1)) - 2 := by rw [h₅]
      _ = 6 * 2 ^ (k - 1) - 2 := by ring
      _ = 2 * (3 * 2 ^ (k - 1) - 1) := by
        have h₆ : 3 * 2 ^ (k - 1) ≥ 1 := by
          have h₇ : k - 1 ≥ 1 := by omega
          have h₈ : 2 ^ (k - 1) ≥ 2 := by
            have h₉ : ∀ n : ℕ, n ≥ 1 → 2 ^ n ≥ 2 := by
              intro n hn
              induction' hn with n hn IH
              · norm_num
              · cases n with
                | zero => contradiction
                | succ n =>
                  simp_all [pow_succ]
                  <;> nlinarith
            exact h₉ (k - 1) h₇
          nlinarith
        have h₇ : 2 * (3 * 2 ^ (k - 1) - 1) = 6 * 2 ^ (k - 1) - 2 := by
          have h₈ : 1 ≤ 3 * 2 ^ (k - 1) := by nlinarith
          omega
        linarith

  rw [h₄]
  -- Show (2 * X) / 2 = X where X = 3 * 2^(k-1) - 1 ≥ 1
  have h₅ : 3 * 2 ^ (k - 1) - 1 ≥ 1 := by
    have h₆ : k - 1 ≥ 1 := by omega
    have h₇ : 2 ^ (k - 1) ≥ 2 := by
      have h₈ : ∀ n : ℕ, n ≥ 1 → 2 ^ n ≥ 2 := by
        intro n hn
        induction' hn with n hn IH
        · norm_num
        · cases n with
          | zero => contradiction
          | succ n =>
            simp_all [pow_succ]
            <;> nlinarith
      exact h₈ (k - 1) h₆
    nlinarith
  have h₆ : (2 * (3 * 2 ^ (k - 1) - 1)) / 2 = 3 * 2 ^ (k - 1) - 1 := by
    have h₇ : 2 ∣ 2 * (3 * 2 ^ (k - 1) - 1) := by
      use (3 * 2 ^ (k - 1) - 1)
      <;> ring_nf
    have h₈ : (2 * (3 * 2 ^ (k - 1) - 1)) / 2 = 3 * 2 ^ (k - 1) - 1 := by
      rw [Nat.div_eq_of_eq_mul_left (show 0 < 2 by norm_num)]
      <;>
      (try
        {
          use (3 * 2 ^ (k - 1) - 1)
          <;> ring_nf
        })
      <;>
      (try
        {
          omega
        })
    exact h₈
  exact h₆
