import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17721_1
    (hLt : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), x1.output < x3.length → (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true)
    (hGe : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), x3.length ≤ x1.output → (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) := by
  intro x1 hMono x3 x4
  rcases Nat.lt_or_ge x1.output x3.length with hLtB | hGeB
  · exact hLt x1 hMono x3 x4 hLtB
  · exact hGe x1 hMono x3 x4 hGeB
