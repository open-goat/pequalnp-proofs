import PEqualNP.Defs
-- Submitted via OpenAI Codex by gpt-6.2-astra.
-- A shared circuit for the twelve nonzero lines feeds both operands of the final AND.
-- The six-gate extension forms the zero-line point disjunction and the two branches.
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_7261_801
  (extendPrefix : ∀ (C : Circuit), IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    C.output < 26+C.size → C.output ≠ 13 →
    ∃ (D : Circuit) (j a b : Nat), D.size = C.size+6 ∧ IsAO2 26 D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.output = 26+j ∧
      D.gates[j]? = some ⟨.and,[a,b]⟩ ∧
      ∀ x : Fin 26 → Bool,
        wireValue D 26 x a = (wireValue C 26 x C.output || x 0 || x 1 || x 3 || x 9) ∧
        wireValue D 26 x b = (wireValue C 26 x C.output || x 13))
  (synthesis :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4;
    ∃ C : Circuit, C.size ≤ 58 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      C.output < 26+C.size ∧ C.output ≠ 13 ∧
      (∀ p l : Fin 13, l ≠ 0 → x1 p l → wireValue C 26 (fun (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) C.output = true) ∧
      ∀ (t : Bool) (S : Finset (Fin 13)), S.card ≤ 3 → wireValue C 26 (x2 t S) C.output = false) :
  let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Bool) (x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (x2 x7 x8) (if x2 x7 x8 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  intro rel tests
  obtain ⟨C, cost, eligible, distinct, output, nz, positive, negative⟩ := synthesis
  obtain ⟨D,j,a,b,size,legal,distinctD,index,gate,branches⟩ := extendPrefix C eligible distinct output nz
  refine ⟨D,j,a,b,by omega,legal,distinctD,index,gate,?_,?_⟩
  · intro p l inc row
    obtain ⟨left,right⟩ := branches row
    by_cases h : l=0
    · subst l
      have hp : p=0 ∨ p=1 ∨ p=3 ∨ p=9 := by simpa [rel] using inc
      rcases hp with rfl | rfl | rfl | rfl <;> rw [left,right]
      all_goals
        have yes : row 13 = true := by dsimp only [row]; decide
        first
          | have pt : row 0 = true := by dsimp only [row]; decide
            simp [pt,yes]
          | have pt : row 1 = true := by dsimp only [row]; decide
            simp [pt,yes]
          | have pt : row 3 = true := by dsimp only [row]; decide
            simp [pt,yes]
          | have pt : row 9 = true := by dsimp only [row]; decide
            simp [pt,yes]
    · have ok := positive p l h inc
      change wireValue C 26 row C.output = true at ok
      simp [left,right,ok]
  · intro t S card
    have noEdge (p l : Fin 13) (inc : rel p l) :
        tests t S (Fin.castAdd 13 p) = true → tests t S (Fin.natAdd 13 l) = true → False := by
      intro hp hl
      cases t <;> simp only [tests, Bool.false_eq_true, ite_false, ite_true,
        Fin.append_left, Fin.append_right, decide_eq_true_eq] at hp hl
      · exact hp l hl inc
      · exact hl p hp inc
    obtain ⟨left,right⟩ := branches (tests t S)
    have off := negative t S card
    change wireValue C 26 (tests t S) C.output = false at off
    by_cases h : tests t S 13 = true
    · have gone (p : Fin 13) (hp : rel p 0) : tests t S (Fin.castAdd 13 p) = false := by
        apply Bool.eq_false_iff.mpr
        intro on
        exact noEdge p 0 hp on h
      have g0 : tests t S 0=false := gone 0 (by decide)
      have g1 : tests t S 1=false := gone 1 (by decide)
      have g3 : tests t S 3=false := gone 3 (by decide)
      have g9 : tests t S 9=false := gone 9 (by decide)
      simp [h,left,off,g0,g1,g3,g9]
    · simp [h,right,off]
