import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_18874_2
    (hMinOr : ∀ D : Circuit, IsAO2 25 D → (∀ x3 : Fin 25 → Bool, D.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) → (∀ E : Circuit, IsAO2 25 E → (∀ x3 : Fin 25 → Bool, E.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) → D.size ≤ E.size) → D.output + 1 = 25 + D.size → (gateAt D (D.size - 1)).op = GateOp.or → 58 ≤ D.size)
    (hMinAnd : ∀ D : Circuit, IsAO2 25 D → (∀ x3 : Fin 25 → Bool, D.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) → (∀ E : Circuit, IsAO2 25 E → (∀ x3 : Fin 25 → Bool, E.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) → D.size ≤ E.size) → D.output + 1 = 25 + D.size → (gateAt D (D.size - 1)).op = GateOp.and → 58 ≤ D.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (25 : ℕ) x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size) := by
  intro C hAO hComp
  classical
  let P : ℕ → Prop := fun s =>
    ∃ D : Circuit, IsAO2 25 D ∧ D.size = s ∧ (∀ x3 : Fin 25 → Bool, D.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true)
  have hex : ∃ s, P s := ⟨C.size, C, hAO, rfl, hComp⟩
  obtain ⟨D, hDAO, hDs, hDComp⟩ := Nat.find_spec hex
  have hDmin : ∀ E : Circuit, IsAO2 25 E → (∀ x3 : Fin 25 → Bool, E.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) → D.size ≤ E.size := by
    intro E hE hEc
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hE, rfl, hEc⟩
  have hDleC : D.size ≤ C.size := hDmin C hAO hComp
  let stp : List Bool → Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFoldLen : ∀ (l : List Gate) (xs : List Bool), (l.foldl stp xs).length = xs.length + l.length := by
    intro l xs
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hstepLen : ∀ w : List Bool, (stp w g).length = w.length + 1 := fun w => by simp [stp]
      rw [hstepLen, ih, List.length_append, List.length_singleton]
      omega
  have hPres : ∀ (l : List Gate) (xs : List Bool) (w : ℕ), w < xs.length → (l.foldl stp xs).getD w false = xs.getD w false := by
    intro l xs w hw
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only [stp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hFoldLen]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have hOutGe : 25 ≤ D.output := by
    by_contra ho_lt
    have ho : D.output < 25 := Nat.lt_of_not_ge ho_lt
    let x : Fin 25 → Bool := fun z => decide (z.val = D.output)
    have hEvalT : D.eval (List.ofFn x) = true := by
      unfold Circuit.eval Circuit.wires
      change (D.gates.foldl stp (List.ofFn x)).getD D.output false = true
      rw [hPres D.gates (List.ofFn x) D.output (by simp [ho])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ho]), Option.getD_some, List.getElem_ofFn]
      simp [x]
    obtain ⟨p, l, _, hp, hl⟩ := (hDComp x).mp hEvalT
    simp only [x, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at hp hl
    have hplt : p.val < 12 := p.isLt
    omega
  have hOutLt : D.output < 25 + D.gates.length := by
    by_contra ho_ge
    have ho : 25 + D.gates.length ≤ D.output := Nat.le_of_not_lt ho_ge
    let x : Fin 25 → Bool := fun z => decide (z = Fin.castAdd 13 (0 : Fin 12) ∨ z = Fin.natAdd 12 (1 : Fin 13))
    have hEvalF : D.eval (List.ofFn x) = false := by
      unfold Circuit.eval Circuit.wires
      change (D.gates.foldl stp (List.ofFn x)).getD D.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hFoldLen, List.length_ofFn]; omega)]
      rfl
    have hEvalT : D.eval (List.ofFn x) = true :=
      (hDComp x).mpr ⟨(0 : Fin 12), (1 : Fin 13), Or.inl rfl, by simp [x], by simp [x]⟩
    rw [hEvalF] at hEvalT
    simp at hEvalT
  let k : ℕ := D.output - 25 + 1
  have hk_le : k ≤ D.gates.length := by omega
  let E : Circuit := ⟨D.gates.take k, D.output⟩
  have hE_ao : IsAO2 25 E := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact hDAO.1 g (List.mem_of_mem_take hg)
    · intro j hj i hi
      have hjk : j < k := by simp only [E, List.length_take] at hj; omega
      have hjD : j < D.gates.length := by omega
      have hg_eq : gateAt E j = gateAt D j := by
        unfold gateAt
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        have hcat := List.take_append_drop k D.gates
        have hget : E.gates[j]? = D.gates[j]? := by
          change (D.gates.take k)[j]? = D.gates[j]?
          conv_rhs => rw [← hcat]
          rw [List.getElem?_append_left (by rw [List.length_take]; omega)]
        rw [hget]
      rw [hg_eq] at hi
      exact hDAO.2.1 j hjD i hi
    · intro g hg
      exact hDAO.2.2 g (List.mem_of_mem_take hg)
  have hE_eq : ∀ x : Fin 25 → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x) := by
    intro x
    unfold Circuit.eval Circuit.wires
    change (E.gates.foldl stp (List.ofFn x)).getD D.output false =
      (D.gates.foldl stp (List.ofFn x)).getD D.output false
    have hcat := List.take_append_drop k D.gates
    have hElen : ((D.gates.take k).foldl stp (List.ofFn x)).length = 25 + k := by
      rw [hFoldLen, List.length_ofFn, List.length_take]
      omega
    conv_rhs => rw [← hcat, List.foldl_append]
    exact (hPres (D.gates.drop k) ((D.gates.take k).foldl stp (List.ofFn x)) D.output (by rw [hElen]; omega)).symm
  have hEComp : (∀ x3 : Fin 25 → Bool, E.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin (12 + 1)) ∨ x4.succ = x5 + (3 : Fin (12 + 1)) ∨ x4.succ = x5 + (9 : Fin (12 + 1))) ∧ x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) := by
    intro x
    rw [hE_eq x]
    exact hDComp x
  have hD_le_E : D.size ≤ E.size := hDmin E hE_ao hEComp
  have hOutLast : D.output + 1 = 25 + D.size := by
    have hEs : E.size = k := by change (D.gates.take k).length = k; rw [List.length_take]; omega
    have hDs2 : D.size = D.gates.length := rfl
    have hk_def : k = D.output - 25 + 1 := rfl
    omega
  have hDs2 : D.size = D.gates.length := rfl
  have hPos : 0 < D.size := by omega
  have hLastMem : gateAt D (D.size - 1) ∈ D.gates := by
    unfold gateAt
    have hlt : D.size - 1 < D.gates.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  have h58D : 58 ≤ D.size := by
    rcases hDAO.1 _ hLastMem with hAnd | hOr
    · exact hMinAnd D hDAO hDComp hDmin hOutLast hAnd
    · exact hMinOr D hDAO hDComp hDmin hOutLast hOr
  omega
