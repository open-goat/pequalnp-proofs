import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-7750`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_7750_2 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → x1.size ≤ (123 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → x1.size ≤ (123 : ℕ) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → x1.size ≤ (123 : ℕ) → ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true)) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
