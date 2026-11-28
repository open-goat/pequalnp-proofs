import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17603_7
    (hLow : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x1 → (∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x4 → x1.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) → (64 : ℕ) ≤ x1.size)
    (hHigh : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x1 → (∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x4 → x1.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) → (64 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2 = [(0 : ℕ), (1 : ℕ)] ∨ x2 = [(13 : ℕ), (14 : ℕ)] →     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Bool) =>       have x7 : List Bool := PEqualNP.GenericRejection.incidenceInput x4 x5;       x1.eval (x7 ++ [x2.any fun (x8 : ℕ) => x7.getD x8 Bool.false] ++ [x6]);     PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 → (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x4 {x7} {x8} (if x2 = [(0 : ℕ), (1 : ℕ)] then Decidable.decide (x8 = (0 : Fin (13 : ℕ)) ∧ (x7 = (0 : Fin (13 : ℕ)) ∨ x7 = (1 : Fin (13 : ℕ)))) else Decidable.decide (x7 = (1 : Fin (13 : ℕ)) ∧ (x8 = (0 : Fin (13 : ℕ)) ∨ x8 = (1 : Fin (13 : ℕ))))) = Bool.true) → (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x4 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) Bool.false = Bool.false) → (62 : ℕ) ≤ x1.size) := by
  have hGen : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C → (∀ (p l : Fin (13 : ℕ)), p ∈ PEqualNP.HeptadCover.singerLines3 l → C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = Bool.true) → (∀ (Q : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q → C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = Bool.false) → (64 : ℕ) ≤ C.size := by
    intro C hm hr hp hq
    have hright : PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C :=
      fun l p hpl => hp p l hpl
    by_cases hd : PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) C (1 : ℕ)
    · exact hLow C hm hright hq hd
    · exact hHigh C hm hr hright hq hd
  intro C ins hins x4 hmono hrb hpos hneg
  have dInc : ∀ X Y : Finset (Fin 13), PEqualNP.GenericRejection.incidenceInput X Y =
      (List.ofFn fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn fun l : Fin 13 => decide (l ∈ Y) :=
    fun _ _ => rfl
  have dSize : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  have dGateAt : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.MetaComplexity.NestedCover.gateAt D j =
      D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := fun _ _ => rfl
  have dEval : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool), D.eval x =
      (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
        D.output false := fun _ _ => rfl
  have dOr : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := fun _ => rfl
  have dAnd : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := fun _ => rfl
  have dMiss : ∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q =
      Finset.univ.filter (fun l => Disjoint (PEqualNP.HeptadCover.singerLines3 l) Q) := fun _ => rfl
  have hP : ∀ (X Y : Finset (Fin 13)) (i : Fin 13),
      (PEqualNP.GenericRejection.incidenceInput X Y).getD (i : ℕ) false = decide (i ∈ X) := by
    intro X Y i
    fin_cases i <;> simp [dInc]
  have hL : ∀ (X Y : Finset (Fin 13)) (i : Fin 13),
      (PEqualNP.GenericRejection.incidenceInput X Y).getD (13 + (i : ℕ)) false = decide (i ∈ Y) := by
    intro X Y i
    fin_cases i <;> simp [dInc]
  have hlen : ∀ (X Y : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y; simp [dInc]
  have hbuild : ∀ a b c : ℕ, a < 26 → b < 26 → c < 26 →
      let D : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ ::
          ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [c, 26]⟩ :: C.gates, C.output⟩
      D.size = C.size + 2 ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D ∧
        ∀ x : List Bool, x.length = 26 → D.eval x =
          C.eval (x ++ [x.getD a false || x.getD b false] ++
            [x.getD c false && (x.getD a false || x.getD b false)]) := by
    intro a b c ha hb hc D
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [D, dSize]
    · intro g hg
      simp only [D, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp
      · simp
      · exact hmono g hg
    · intro j hj i hi
      rcases j with _ | _ | k
      · simp [D, dGateAt] at hi
        omega
      · simp [D, dGateAt] at hi
        omega
      · have hk : k < C.gates.length := by simp [D] at hj; omega
        have := hrb k hk i (by simpa [D, dGateAt] using hi)
        omega
    · intro x hx
      rw [dEval, dEval]
      simp only [D, List.foldl_cons]
      congr 2
      simp [dOr, dAnd, List.getD_eq_getElem?_getD,
        List.getElem?_append_left, List.getElem?_append_right, hx, ha, hb, hc]
  have l00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have l10 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have l11 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 1 := by decide
  have notMiss : ∀ (Q : Finset (Fin 13)) (l p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l → p ∈ Q →
      l ∉ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q := by
    intro Q l p hpl hpQ hm
    rw [dMiss, Finset.mem_filter] at hm
    exact Finset.disjoint_left.mp hm.2 hpl hpQ
  rcases hins with rfl | rfl
  · obtain ⟨hsz, hm, hr, hev⟩ := hbuild 0 1 13 (by norm_num) (by norm_num) (by norm_num)
    have h := hGen _ hm hr ?_ ?_
    · omega
    · intro p l hpl
      rw [hev _ (hlen _ _)]
      have := hpos p l hpl
      simp only [x4] at this
      convert this using 4
      · simp
      · have e0 := hP {p} {l} 0; have e1 := hP {p} {l} 1; have e13 := hL {p} {l} 0
        simp only [Fin.val_zero, Fin.val_one, add_zero] at e0 e1 e13
        rw [e0, e1, e13]
        simp [Finset.mem_singleton, eq_comm, and_comm]
    · intro Q hQ
      rw [hev _ (hlen _ _)]
      have := hneg Q hQ
      simp only [x4] at this
      convert this using 4
      · simp
      · have e0 := hP Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) 0
        have e1 := hP Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) 1
        have e13 := hL Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) 0
        simp only [Fin.val_zero, Fin.val_one, add_zero] at e0 e1 e13
        rw [e0, e1, e13]
        by_cases q0 : (0 : Fin 13) ∈ Q
        · simp [notMiss Q 0 0 l00 q0]
        · by_cases q1 : (1 : Fin 13) ∈ Q
          · simp [notMiss Q 0 1 l10 q1]
          · simp [q0, q1]
  · obtain ⟨hsz, hm, hr, hev⟩ := hbuild 13 14 1 (by norm_num) (by norm_num) (by norm_num)
    have h := hGen _ hm hr ?_ ?_
    · omega
    · intro p l hpl
      rw [hev _ (hlen _ _)]
      have := hpos p l hpl
      simp only [x4] at this
      convert this using 4
      · simp
      · have e0 := hL {p} {l} 0; have e1 := hL {p} {l} 1; have e13 := hP {p} {l} 1
        simp only [Fin.val_zero, Fin.val_one, add_zero, Nat.reduceAdd] at e0 e1 e13
        rw [e0, e1, e13]
        simp [Finset.mem_singleton, eq_comm]
    · intro Q hQ
      rw [hev _ (hlen _ _)]
      have := hneg Q hQ
      simp only [x4] at this
      convert this using 4
      · simp
      · have e0 := hL Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) 0
        have e1 := hL Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) 1
        have e13 := hP Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) 1
        simp only [Fin.val_zero, Fin.val_one, add_zero, Nat.reduceAdd] at e0 e1 e13
        rw [e0, e1, e13]
        by_cases q1 : (1 : Fin 13) ∈ Q
        · simp [notMiss Q 0 1 l10 q1, notMiss Q 1 1 l11 q1]
        · simp [q1]
