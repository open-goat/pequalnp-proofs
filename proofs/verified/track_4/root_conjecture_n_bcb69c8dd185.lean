import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem root_conjecture_n (n : ℕ) : n ≥ 0 := by
  linarith