import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.HeptadCover

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4500000 in
theorem PEqualNP.Outside.R_meta_5987_731
    (trace :
      ∀ (n : ℕ) (C : Circuit) (a b : ℕ), a < n → b < n → a ≠ b → IsAO2 n C →
        let W := fun (x : Fin n → Bool) i => (C.wires (List.ofFn x)).getD i false
        let lo := fun i : Fin n => decide (i.val = a)
        let hi := fun i : Fin n => decide (i.val = a ∨ i.val = b)
        let R := fun u v : ℕ => ∃ (j k : ℕ) (g : Gate),
          v = n+j ∧ C.gates[j]? = some g ∧ (g.inputs=[u,k] ∨ g.inputs=[k,u]) ∧
            (g.op = GateOp.or ∨ W lo k = true)
        W lo C.output = false → W hi C.output = true →
        Relation.ReflTransGen R b C.output ∨
        ∃ (j u v : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs=[u,v] ∧
          W lo u = false ∧ W hi u = true ∧ W lo v = false ∧ W hi v = true ∧
          Relation.ReflTransGen R (n+j) C.output)
    (aliases :
      ∀ C : Circuit, IsAO2 26 C → (∀ g ∈ C.gates,g.inputs.Nodup) → C.size ≤ 64 →
      let W := fun (x : Fin 26 → Bool) i => (C.wires (List.ofFn x)).getD i false
      let low := fun k (i : Fin 26) => decide (i.val=k)
      let high := fun i : Fin 26 => decide (i.val=0 ∨ i.val=13)
      let R := fun k u v : ℕ => ∃ (j w : ℕ) (g : Gate), v=26+j ∧ C.gates[j]?=some g ∧
        (g.inputs=[u,w] ∨ g.inputs=[w,u]) ∧ (g.op=GateOp.or ∨ W (low k) w=true)
      let B := fun k : ℕ => ∃ (j u v : ℕ) (g : Gate), C.gates[j]?=some g ∧ g.op=GateOp.and ∧ g.inputs=[u,v] ∧
        W (low k) u=false ∧ W high u=true ∧ W (low k) v=false ∧ W high v=true ∧
        Relation.ReflTransGen (R k) (26+j) C.output
      (∀ x : Fin 26 → Bool, W x C.output = true ↔ ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      B 0 → B 13 →
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ ∃ S ⊆ Finset.range C.size, 9 ≤ S.card ∧
        ∀ j ∈ S, ∃ i < 26+j, ∀ x : Fin 26 → Bool, x (Fin.castAdd 13 p)=false →
          x (Fin.natAdd 13 l)=false → W x i = W x (26+j)) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       x2.size ≤ (64 : ℕ) →         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →             have x9 : ℕ → Prop := fun (x9 : ℕ) => Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x11 = (26 : ℕ) + x12 ∧ x2.gates[x12]? = Option.some x14 ∧ (x14.inputs = [x10, x13] ∨ x14.inputs = [x13, x10]) ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x15 : Fin (26 : ℕ)) => Decidable.decide (↑x15 = x9)) x13 = Bool.true)) ((13 : ℕ) - x9) x2.output;             x9 (0 : ℕ) ∨ x9 (13 : ℕ) := by
  intro I C valid distinct small W fit separating path
  have incidences : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ I p l := by decide +kernel
  have recognized (x : Fin 26 → Bool) : W x C.output = true ↔
      ∃ p l : Fin 13,p ∈ singerLines3 l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    rw [fit x]
    constructor
    · rintro ⟨p,l,edge,xp,xl⟩
      exact ⟨p,l,(incidences p l).2 edge,xp,xl⟩
    · rintro ⟨p,l,edge,xp,xl⟩
      exact ⟨p,l,(incidences p l).1 edge,xp,xl⟩
  let single (k : ℕ) (x : Fin 26) := decide (x.val=k)
  let both (x : Fin 26) := decide (x.val=0 ∨ x.val=13)
  have pairTrue : W both C.output = true := (fit both).2 ⟨0,0,by decide,by decide,by decide⟩
  have singleton (i : ℕ) (hi : i=0 ∨ i=13) : W (single i) C.output = false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    have absent : ¬∃ p l : Fin 13, I p l ∧ single i (Fin.castAdd 13 p) = true ∧
      single i (Fin.natAdd 13 l) = true := by
      rcases hi with rfl | rfl <;> decide +kernel
    exact absent ((fit (single i)).1 hx)
  rcases trace 26 C 0 13 (by decide) (by decide) (by decide) valid (singleton 0 (.inl rfl)) pairTrue
    with forwards | barrier0
  · exact Or.inl forwards
  have reverseBoth : (fun x : Fin 26 => decide (x.val=13 ∨ x.val=0)) = both := by
    funext x
    simp only [both,or_comm]
  have pairTrue' : W (fun x : Fin 26 => decide (x.val=13 ∨ x.val=0)) C.output = true := by
    rw [reverseBoth]
    exact pairTrue
  rcases trace 26 C 13 0 (by decide) (by decide) (by decide) valid (singleton 13 (.inr rfl)) pairTrue'
    with backwards | barrier13
  · exact Or.inr backwards
  rw [reverseBoth] at barrier13
  obtain ⟨p,l,edge,S,inside,nine,canAlias⟩ := aliases C valid distinct small recognized barrier0 barrier13
  obtain ⟨U,umem,fiftysix,cannot⟩ := separating p l ((incidences p l).1 edge)
  have disjoint : Disjoint S U := Finset.disjoint_left.mpr (by
    intro j inS inU
    obtain ⟨i,hi,equal⟩ := canAlias j inS
    obtain ⟨x,xp,xl,ne⟩ := cannot j inU i hi
    exact ne (equal x xp xl))
  have together : S ∪ U ⊆ Finset.range C.size := Finset.union_subset inside umem
  have count := Finset.card_le_card together
  rw [Finset.card_union_of_disjoint disjoint,Finset.card_range] at count
  omega
