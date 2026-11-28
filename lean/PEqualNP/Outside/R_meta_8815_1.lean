import PEqualNP.Defs

-- A perfect matching forces any vertex cover to meet at least n edges
-- with distinct vertices. The first step gives the resulting gate bound.
-- The second step is an accounting inequality for a binary circuit.
theorem PEqualNP.Outside.R_meta_8815_1
    (hMatchingFloor :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        0 < n →
        (∀ (a a' b b' : Fin n), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        (∀ a : Fin n, (a, σ a) ∈ E) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        (∀ z : Fin (n + n) → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + n) C z =
            Decidable.decide (∃ (a b : Fin n),
              (a, b) ∈ E ∧ z (Fin.castAdd n a) = true ∧ z (Fin.natAdd n b) = true)) →
        E.card + n ≤ C.size + 1)
    (hWireBudget :
      ∀ (inputs : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 inputs C →
        (∃ z : Fin inputs → Bool,
          PEqualNP.MetaComplexity.circuitFun inputs C z = true) →
        let refs := C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
        C.size + 1 ≤ inputs + (refs.length - refs.toFinset.card)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →       (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →         PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →           (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →             have x10 : List ℕ := x4.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x4.gates;             x2.card ≤ x1 + (x10.length - x10.toFinset.card) := by
  intro n E σ C hn hC4 hMatching hAO hFun
  -- The all-true assignment activates the edge at the first matching
  -- vertex. Thus the output cannot be a missing wire.
  let a : Fin n := ⟨0, hn⟩
  let allTrue : Fin (n + n) → Bool := fun _ => true
  have hActive : PEqualNP.MetaComplexity.circuitFun (n + n) C allTrue = true := by
    rw [hFun]
    exact decide_eq_true ⟨a, σ a, hMatching a, rfl, rfl⟩
  have hOutputLive : ∃ z : Fin (n + n) → Bool,
      PEqualNP.MetaComplexity.circuitFun (n + n) C z = true :=
    ⟨allTrue, hActive⟩
  have hFloor : E.card + n ≤ C.size + 1 :=
    hMatchingFloor n E σ C hn hC4 hMatching hAO hFun
  -- Each gate contributes two operand occurrences and the output
  -- contributes one occurrence. Distinct references can only be
  -- primary inputs or existing gate outputs.
  let refs := C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
  have hWires : C.size + 1 ≤ (n + n) + (refs.length - refs.toFinset.card) :=
    hWireBudget (n + n) C hAO hOutputLive
  change E.card ≤ n + (refs.length - refs.toFinset.card)
  have hCombined : E.card + n ≤ (n + n) + (refs.length - refs.toFinset.card) :=
    hFloor.trans hWires
  omega
