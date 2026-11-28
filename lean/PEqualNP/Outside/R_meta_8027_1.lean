import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8027_1
    (hMonotone :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        x2.Colorable (2 : ℕ) →
        (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (0 : ℕ) ∨ (x2.neighborSet x5).ncard = (3 : ℕ)) →
        (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (8 : ℕ) ≤ x7.length) →
        (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) →
        PEqualNP.MetaComplexity.Monotone2 C →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        (∀ (x8 : Fin x1 → Bool), C.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) →
        x2.edgeSet.ncard + x2.support.ncard / (2 : ℕ) ≤ C.size + (1 : ℕ))
    (hHasNot :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        x2.Colorable (2 : ℕ) →
        (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (0 : ℕ) ∨ (x2.neighborSet x5).ncard = (3 : ℕ)) →
        (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (8 : ℕ) ≤ x7.length) →
        (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        (∀ (x8 : Fin x1 → Bool), C.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) →
        x2.edgeSet.ncard + x2.support.ncard / (2 : ℕ) ≤ C.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (0 : ℕ) ∨ (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → x2.edgeSet.ncard + x2.support.ncard / (2 : ℕ) ≤ x9 + (1 : ℕ) := by
  classical
  intro n G f hCol hDeg hGirth7 hEdge hSpec s hHas
  obtain ⟨C, hF2, hCs, hCeval⟩ := hHas
  have hCspec : ∀ (x : Fin n → Bool),
      C.eval (List.ofFn x) = Bool.true ↔ ∃ (a b : Fin n), G.Adj a b ∧ x a = Bool.true ∧ x b = Bool.true := by
    intro x
    rw [hCeval x]
    exact hSpec x
  have hFin2Trans : ∀ a b d : Fin 2, a ≠ b → b ≠ d → a = d := by decide
  have hGirth8 : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 8 ≤ w.length := by
    intro v w hw
    have h7 := hGirth7 v w hw
    obtain ⟨c⟩ := hCol
    have hParity : ∀ {u z : Fin n} (p : G.Walk u z),
        (p.length % 2 = 0 ∧ c u = c z) ∨ (p.length % 2 = 1 ∧ c u ≠ c z) := by
      intro u z p
      induction p with
      | nil => exact Or.inl ⟨rfl, rfl⟩
      | @cons u' v' z' hadj q ih =>
        have hne : c u' ≠ c v' := c.valid hadj
        rcases ih with ⟨heven, heq⟩ | ⟨hodd, hneq⟩
        · refine Or.inr ⟨?_, ?_⟩
          · simp only [SimpleGraph.Walk.length_cons]; omega
          · rw [← heq]; exact hne
        · refine Or.inl ⟨?_, ?_⟩
          · simp only [SimpleGraph.Walk.length_cons]; omega
          · exact hFin2Trans (c u') (c v') (c z') hne hneq
    rcases hParity w with ⟨heven, _⟩ | ⟨_, hneq⟩
    · omega
    · exact False.elim (hneq rfl)
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [List.length_append, List.length_singleton]
      omega
  have hfold_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
      j < init.length →
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).getD j false =
      init.getD j false := by
    intro gs
    induction gs with
    | nil => intro init j _; rfl
    | cons hd tl ih =>
      intro init j hj
      simp only [List.foldl_cons]
      rw [ih _ j (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hj
  have houtGe : n ≤ C.output := by
    by_contra hlt
    have hlt : C.output < n := Nat.lt_of_not_ge hlt
    let v0 : Fin n := ⟨C.output, hlt⟩
    let x : Fin n → Bool := fun i => decide (i = v0)
    have ht : C.eval (List.ofFn x) = true := by
      have h1 := hfold_pref C.gates (List.ofFn x) C.output (by simp only [List.length_ofFn]; exact hlt)
      change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = true
      rw [h1, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have heq : (⟨C.output, hlt⟩ : Fin n) = v0 := rfl
      simp only [x, heq, decide_true]
    obtain ⟨a, b, hab, ha, hb⟩ := (hCspec x).mp ht
    simp only [x, decide_eq_true_eq] at ha hb
    rw [ha, hb] at hab
    exact G.ne_of_adj hab rfl
  have houtLt : C.output < n + C.size := by
    by_contra hge
    have hge : n + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨a, b, hab⟩ := hEdge
    let x : Fin n → Bool := fun i => decide (i = a ∨ i = b)
    have ht : C.eval (List.ofFn x) = true :=
      (hCspec x).mpr ⟨a, b, hab, by simp [x], by simp [x]⟩
    change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = true at ht
    have hlen : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).length = n + C.size := by
      rw [hfold_len, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at ht
    exact Bool.noConfusion ht
  have hBound : G.edgeSet.ncard + G.support.ncard / 2 ≤ C.size + 1 := by
    by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
    · exact hHasNot n G C hCol hDeg hGirth8 hEdge hF2 hnot ⟨houtGe, houtLt⟩ hCspec
    · have hMono : PEqualNP.MetaComplexity.Monotone2 C := by
        intro g hg
        have hf := hF2 g hg
        refine ⟨?_, hf.2⟩
        have hmem := hf.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hA | hO | hN
        · exact Or.inl hA
        · exact Or.inr hO
        · exact False.elim (hnot ⟨g, hg, hN⟩)
      exact hMonotone n G C hCol hDeg hGirth8 hEdge hMono ⟨houtGe, houtLt⟩ hCspec
  omega
