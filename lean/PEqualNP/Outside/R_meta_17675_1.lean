import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.GenericRejection PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_17675_1
    (hCorners :
      let V := Fin 13 ⊕ Fin 13
      let good (S : Finset V) := IsFree (incidences singerLines3) S ∧ S.toRight.card ≤ 3 ∧
        (∀ l : Fin 13, (S.toLeft ∩ singerLines3 l).card ≤ 2) ∧
        ∀ p : Fin 13, {l ∈ S.toRight | p ∈ singerLines3 l}.card ≤ 2
      let edge : V → V → Prop := Sum.elim
        (fun p => Sum.elim (fun _ => False) (fun l => p ∈ singerLines3 l))
        (fun l => Sum.elim (fun p => p ∈ singerLines3 l) (fun _ => False))
      ∀ S : Finset V, S.card ≤ 2 → good S → ∃ a b c d : V,
        edge a b ∧ edge c d ∧ good ({b} ∪ S) ∧ good ({d} ∪ S) ∧
        good ({a,c} ∪ S) ∧ good ({a,d} ∪ S) ∧ good ({b,c} ∪ S))
    (hGate :
      let V := Fin 13 ⊕ Fin 13
      let wire (C : Circuit) (w : ℕ) (T : Finset V) :=
        (C.wires (incidenceInput T.toLeft T.toRight)).getD w false
      ∀ (C : Circuit) (j : ℕ), Monotone2 C → ReadsBack 26 C →
        (¬∃ a b, (gateAt C a).op = .and ∧ (gateAt C b).op = .and ∧ InCone 26 C a b) →
        j < C.size → (gateAt C j).op = .and →
        (∀ T, wire C (26+j) T = true) ∨
          ∃ L R : V → Prop, ∀ T, wire C (26+j) T = true ↔
            (∃ v ∈ T, L v) ∧ (∃ v ∈ T, R v))
    (hLastOr :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (62 : ℕ) ≤ x5.size) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x5.size) := by
  let Vertex := Fin 13 ⊕ Fin 13
  let good (S : Finset Vertex) := IsFree (incidences singerLines3) S ∧ S.toRight.card ≤ 3 ∧
    (∀ l : Fin 13, (S.toLeft ∩ singerLines3 l).card ≤ 2) ∧
    ∀ p : Fin 13, {l ∈ S.toRight | p ∈ singerLines3 l}.card ≤ 2
  let edge : Vertex → Vertex → Prop := Sum.elim
    (fun p => Sum.elim (fun _ => False) (fun l => p ∈ singerLines3 l))
    (fun l => Sum.elim (fun p => p ∈ singerLines3 l) (fun _ => False))
  let wire (C : Circuit) (w : ℕ) (T : Finset Vertex) :=
    (C.wires (incidenceInput T.toLeft T.toRight)).getD w false
  have gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.size) : gateAt C j = C.gates[j] := by
    exact List.getD_eq_getElem _ _ hj
  have legal_of (C : Circuit) (hm : Monotone2 C) (g : Gate) (hg : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    obtain ⟨hh,hlen⟩ := hm g hg
    rcases hh with aa | oo
    · exact ⟨Or.inl aa,hlen⟩
    · exact ⟨Or.inr oo,hlen⟩
  have stepKeep {A B : Type} (append : List A → B → List A)
      (step : ∀ l g, ∃ tail, append l g = l ++ tail) (gs : List B) (p : List A) :
      ∃ tail, gs.foldl append p = p ++ tail := by
    induction gs generalizing p with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih =>
      obtain ⟨a,ha⟩ := step p g
      obtain ⟨b,hb⟩ := ih (append p g)
      refine ⟨a++b,?_⟩
      rw [List.foldl_cons,hb,ha,List.append_assoc]
  let step (p : List Bool) (g : Gate) := p ++ [g.op.eval (g.inputs.map fun i => p.getD i false)]
  have wireFold (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl
  have foldLength (gs : List Gate) (p : List Bool) : (gs.foldl step p).length = p.length + gs.length := by
    induction gs generalizing p with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]
      omega
  have inputLength (T : Finset Vertex) : (incidenceInput T.toLeft T.toRight).length = 26 := by
    change ((List.ofFn fun p : Fin 13 => decide (p ∈ T.toLeft)) ++
      (List.ofFn fun l : Fin 13 => decide (l ∈ T.toRight))).length = 26
    rw [List.length_append,List.length_ofFn,List.length_ofFn]
  have val_big (C : Circuit) (w : ℕ) (T : Finset Vertex) (past : 26+C.gates.length ≤ w) :
      wire C w T = false := by
    unfold wire
    rw [wireFold,List.getD_eq_default _ _ (by rw [foldLength,inputLength]; exact past)]
  have val_input (C : Circuit) (w : ℕ) (T : Finset Vertex) (raw : w < 26) :
      wire C w T = (incidenceInput T.toLeft T.toRight).getD w false := by
    unfold wire
    obtain ⟨extra,eq⟩ := stepKeep step (fun p g => ⟨_,rfl⟩) C.gates
      (incidenceInput T.toLeft T.toRight)
    rw [wireFold,eq,List.getD_append _ _ _ _ (by rw [inputLength]; exact raw)]
  have no_two_covers (S : Finset Vertex) (small : S.card ≤ 2) (clean : good S)
      (L R : Vertex → Prop)
      (coversL : ∀ x y : Vertex, edge x y → L x ∨ L y)
      (coversR : ∀ x y : Vertex, edge x y → R x ∨ R y)
      (reject : ∀ x y : Vertex, good ({x,y} ∪ S) → ¬ (L x ∧ R y)) : False := by
    obtain ⟨a,b,c,d,edgeAB,edgeCD,goodB,goodD,goodAC,goodAD,goodBC⟩ := hCorners S small clean
    rcases coversL a b edgeAB with la | lb
    · rcases coversR c d edgeCD with rc | rd
      · exact reject a c goodAC ⟨la,rc⟩
      · exact reject a d goodAD ⟨la,rd⟩
    · have rbNot : ¬ R b := fun rb => reject b b (by simpa using goodB) ⟨lb,rb⟩
      have ra := (coversR a b edgeAB).resolve_right rbNot
      rcases coversL c d edgeCD with lc | ld
      · exact reject c a (by simpa [Finset.pair_comm] using goodAC) ⟨lc,ra⟩
      · have rdNot : ¬ R d := fun rd => reject d d (by simpa using goodD) ⟨ld,rd⟩
        have rc := (coversR c d edgeCD).resolve_right rdNot
        exact reject b c goodBC ⟨lb,rc⟩
  have impossible_rectangle (S : Finset Vertex) (small : S.card ≤ 2) (clean : good S)
      (F : Finset Vertex → Bool) (L R : Vertex → Prop)
      (factor : ∀ T, F T = true ↔ (∃ x ∈ T, L x) ∧ (∃ x ∈ T, R x))
      (positive : ∀ p l : Fin 13, p ∈ singerLines3 l → F {Sum.inl p, Sum.inr l} = true)
      (negative : ∀ T : Finset Vertex, T.card ≤ 2 → good (T ∪ S) → F T = false) : False := by
    have cover (x y : Vertex) (h : edge x y) : F {x,y} = true := by
      rcases x with p | l <;> rcases y with q | m
      · exact h.elim
      · exact positive p m h
      · rw [Finset.pair_comm]
        exact positive q l h
      · exact h.elim
    have left (x y : Vertex) (h : edge x y) : L x ∨ L y := by
      obtain ⟨u,hu,hL⟩ := ((factor {x,y}).mp (cover x y h)).1
      rcases Finset.mem_insert.mp hu with rfl | h
      · exact Or.inl hL
      · obtain rfl := Finset.mem_singleton.mp h
        exact Or.inr hL
    have right (x y : Vertex) (h : edge x y) : R x ∨ R y := by
      obtain ⟨u,hu,hR⟩ := ((factor {x,y}).mp (cover x y h)).2
      rcases Finset.mem_insert.mp hu with rfl | h
      · exact Or.inl hR
      · obtain rfl := Finset.mem_singleton.mp h
        exact Or.inr hR
    apply no_two_covers S small clean L R left right
    rintro x y goodXY ⟨hx,hy⟩
    have yes := (factor {x,y}).mpr ⟨⟨x,by simp,hx⟩,⟨y,by simp,hy⟩⟩
    rw [negative {x,y} Finset.card_le_two goodXY] at yes
    cases yes
  have no_and_outlet (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack 26 C)
      (flat : ¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j)
      (j : ℕ) (hj : j < C.size) (S : Finset Vertex) (small : S.card ≤ 2) (hS : good S)
      (positive : ∀ p l : Fin 13, p ∈ singerLines3 l → wire C (26+j) {Sum.inl p, Sum.inr l} = true)
      (negative : ∀ T : Finset Vertex, T.card ≤ 2 → good (T ∪ S) → wire C (26+j) T = false) :
      C.gates[j].op ≠ .and := by
    intro hAnd
    have gate : (gateAt C j).op = .and := by simpa only [gateAt_eq C j hj] using hAnd
    rcases hGate C j hm rb flat hj gate with always | ⟨L,R,rectangle⟩
    · have yes := always ∅
      change wire C (26+j) ∅ = true at yes
      rw [negative ∅ (by simp) (by simpa using hS)] at yes
      cases yes
    · exact impossible_rectangle S small hS (wire C (26+j)) L R rectangle positive negative
  have outlets_before_final_and (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack 26 C)
      (flat : ¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j)
      (u v : ℕ)
      (positive : ∀ p l : Fin 13, p ∈ singerLines3 l →
        (wire C u {Sum.inl p, Sum.inr l} && wire C v {Sum.inl p, Sum.inr l}) = true)
      (negative : ∀ T S : Finset Vertex, T.card ≤ 2 → S.card ≤ 2 → good (T ∪ S) →
        (wire C u T && wire C v S) = false)
      (witnesses : ∀ w ∈ [u,v], ∃ S : Finset Vertex, S.card ≤ 2 ∧ good S ∧ wire C w S = true)
      (lastAnd : (gateAt C (C.size-1)).op = .and) :
      u < 26 + (C.size-1) ∧ v < 26 + (C.size-1) := by
    have nonempty : 0 < C.size := by
      by_contra! impossible
      have empty : C.gates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero impossible)
      change (C.gates.getD (C.size-1) ⟨.or,[]⟩).op = .and at lastAnd
      rw [empty] at lastAnd
      cases lastAnd
    have hJ : C.size-1 < C.size := by omega
    rw [gateAt_eq C _ hJ] at lastAnd
    obtain ⟨Su,smallU,goodU,yesU⟩ := witnesses u (by simp)
    obtain ⟨Sv,smallV,goodV,yesV⟩ := witnesses v (by simp)
    have posU (p l : Fin 13) (h : p ∈ singerLines3 l) : wire C u {Sum.inl p,Sum.inr l} = true :=
      (Bool.and_eq_true_iff.mp (positive p l h)).1
    have posV (p l : Fin 13) (h : p ∈ singerLines3 l) : wire C v {Sum.inl p,Sum.inr l} = true :=
      (Bool.and_eq_true_iff.mp (positive p l h)).2
    have negU (T : Finset Vertex) (small : T.card ≤ 2) (h : good (T ∪ Sv)) : wire C u T = false := by
      simpa [yesV] using negative T Sv small smallV h
    have negV (T : Finset Vertex) (small : T.card ≤ 2) (h : good (T ∪ Su)) : wire C v T = false := by
      simpa [yesU] using negative Su T smallU small (Finset.union_comm T Su ▸ h)
    have bounded (w : ℕ) (S : Finset Vertex) (small : S.card ≤ 2) (hS : good S)
        (pos : ∀ p l : Fin 13, p ∈ singerLines3 l → wire C w {Sum.inl p, Sum.inr l} = true)
        (neg : ∀ T : Finset Vertex, T.card ≤ 2 → good (T ∪ S) → wire C w T = false) :
        w < 26 + (C.size-1) := by
      by_contra! hn
      by_cases equal : w = 26 + (C.size-1)
      · subst w
        exact no_and_outlet C hm rb flat _ hJ S small hS pos neg lastAnd
      · have past : 26 + C.gates.length ≤ w := by
          change 26 + C.size ≤ w
          omega
        have inc : (0 : Fin 13) ∈ singerLines3 0 := by decide
        have shown := pos 0 0 inc
        rw [val_big C w _ past] at shown
        cases shown
    exact ⟨bounded u Sv smallV goodV posU negU, bounded v Su smallU goodU posV negV⟩
  let contract (C : Circuit) (u v : ℕ) : Prop :=
    Monotone2 C ∧ ReadsBack 26 C ∧
    (¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) ∧
    (∀ p l : Fin 13, p ∈ singerLines3 l →
      (wire C u {Sum.inl p, Sum.inr l} && wire C v {Sum.inl p,Sum.inr l}) = true) ∧
    (∀ T S : Finset Vertex, T.card ≤ 2 → S.card ≤ 2 → good (T ∪ S) →
      (wire C u T && wire C v S) = false) ∧
    (∀ w ∈ [u,v], ∃ S : Finset Vertex, S.card ≤ 2 ∧ good S ∧ wire C w S = true)
  have not_raw (C : Circuit) (w : ℕ)
      (pos : ∀ p l : Fin 13, p ∈ singerLines3 l → wire C w {Sum.inl p,Sum.inr l} = true) : 26 ≤ w := by
    by_contra! below
    let i : Fin 26 := ⟨w,below⟩
    have p0 := pos 0 0 (by decide)
    have p1 := pos 1 1 (by decide)
    rw [val_input C w _ below] at p0 p1
    have finite : ∀ i : Fin 26,
      let zero : Finset Vertex := {Sum.inl 0,Sum.inr 0}
      let one : Finset Vertex := {Sum.inl 1,Sum.inr 1}
      (incidenceInput zero.toLeft zero.toRight).getD i.val false = true →
      (incidenceInput one.toLeft one.toRight).getD i.val false = true → False := by decide +kernel
    exact finite i p0 p1
  let takeCircuit (C : Circuit) (k : ℕ) : Circuit := ⟨C.gates.take k,C.output⟩
  have gate_prefix (C : Circuit) (k j : ℕ) (hj : j < (takeCircuit C k).size) :
      gateAt (takeCircuit C k) j = gateAt C j := by
    have original : j < C.gates.length := by
      have h := List.length_take_le (l := C.gates) (i := k)
      change j < (C.gates.take k).length at hj
      rw [List.length_take] at hj
      omega
    rw [gateAt_eq _ _ hj,gateAt_eq _ _ original]
    exact List.getElem_take
  have cone_length (C : Circuit) : (cones 26 C).length = C.size := by
    change (C.gates.foldl (coneStep 26) []).length = C.gates.length
    have inductionStep (gs : List Gate) (p : List (List ℕ)) :
        (gs.foldl (coneStep 26) p).length = p.length + gs.length := by
      induction gs generalizing p with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons,ih]
        change (p ++ [_]).length + gs.length = p.length + (g::gs).length
        simp only [List.length_append,List.length_cons,List.length_nil]
        omega
    rw [inductionStep]
    simp
  have prefix_cone (C : Circuit) (k i j : ℕ) (hj : j < (takeCircuit C k).size) :
      InCone 26 (takeCircuit C k) i j ↔ InCone 26 C i j := by
    have factor : cones 26 C = (C.gates.drop k).foldl (coneStep 26) (cones 26 (takeCircuit C k)) := by
      unfold cones takeCircuit
      rw [← List.foldl_append,List.take_append_drop]
    obtain ⟨extra,he⟩ := stepKeep (coneStep 26) (fun p g => ⟨_,rfl⟩) (C.gates.drop k) (cones 26 (takeCircuit C k))
    unfold InCone
    rw [factor,he,List.getD_append _ _ _ _ (by simpa [cone_length] using hj)]
  have prefix_wire (C : Circuit) (k w : ℕ) (T : Finset Vertex) (hw : w < 26+k)
      (hk : k ≤ C.size) : wire (takeCircuit C k) w T = wire C w T := by
    let x := incidenceInput T.toLeft T.toRight
    change ((takeCircuit C k).wires x).getD w false = (C.wires x).getD w false
    rw [wireFold,wireFold]
    change ((C.gates.take k).foldl step x).getD w false = (C.gates.foldl step x).getD w false
    obtain ⟨extra,he⟩ := stepKeep step (fun p g => ⟨_,rfl⟩)
      (C.gates.drop k) ((C.gates.take k).foldl step x)
    have same : C.gates.foldl step x = ((C.gates.take k).foldl step x) ++ extra := by
      rw [← he,← List.foldl_append,List.take_append_drop]
    have hk' : k ≤ C.gates.length := hk
    rw [same,List.getD_append _ _ _ _ (by
      rw [foldLength,List.length_take,Nat.min_eq_left hk']
      change w < (incidenceInput T.toLeft T.toRight).length + k
      rw [inputLength]
      exact hw)]
  have trim_to_last_or (C : Circuit) (u v : ℕ) (h : contract C u v)
      (lastAnd : (gateAt C (C.size-1)).op = .and) :
      ∃ D : Circuit, D.size < C.size ∧ contract D u v ∧ (gateAt D (D.size-1)).op = .or := by
    rcases h with ⟨hm,rb,flat,pos,neg,ws⟩
    have early := outlets_before_final_and C hm rb flat u v pos neg ws lastAnd
    have posU (p l : Fin 13) (hp : p ∈ singerLines3 l) : wire C u {Sum.inl p,Sum.inr l} = true :=
      (Bool.and_eq_true_iff.mp (pos p l hp)).1
    have posV (p l : Fin 13) (hp : p ∈ singerLines3 l) : wire C v {Sum.inl p,Sum.inr l} = true :=
      (Bool.and_eq_true_iff.mp (pos p l hp)).2
    have uraw := not_raw C u posU
    have vraw := not_raw C v posV
    let j := max u v - 26
    let D := takeCircuit C (j+1)
    have maxEq : max u v = 26+j := by dsimp [j]; omega
    have within : j+1 < C.size := by omega
    have prefixLength : j+1 ≤ C.gates.length := Nat.le_of_lt within
    have sizeD : D.size = j+1 := by
      change (C.gates.take (j+1)).length = j+1
      rw [List.length_take,Nat.min_eq_left prefixLength]
    have sameU (T : Finset Vertex) : wire D u T = wire C u T :=
      prefix_wire C (j+1) u T (by omega) (by omega)
    have sameV (T : Finset Vertex) : wire D v T = wire C v T :=
      prefix_wire C (j+1) v T (by omega) (by omega)
    have lastIndex : D.size-1 = j := by omega
    have hJ : j < C.size := by omega
    have hJD : j < D.size := by omega
    have notAnd : C.gates[j].op ≠ .and := by
      rcases le_total u v with uv | vu
      · have j_eq : v = 26+j := (max_eq_right uv).symm.trans maxEq
        obtain ⟨S,small,clean,yes⟩ := ws u (by simp)
        have no (T : Finset Vertex) (hsmall : T.card ≤ 2) (hg : good (T ∪ S)) : wire C v T = false := by
          simpa [yes] using neg S T small hsmall (Finset.union_comm T S ▸ hg)
        exact no_and_outlet C hm rb flat j hJ S small clean (by simpa [← j_eq] using posV)
          (by simpa [← j_eq] using no)
      · have j_eq : u = 26+j := (max_eq_left vu).symm.trans maxEq
        obtain ⟨S,small,clean,yes⟩ := ws v (by simp)
        have no (T : Finset Vertex) (hsmall : T.card ≤ 2) (hg : good (T ∪ S)) : wire C u T = false := by
          simpa [yes] using neg T S hsmall small hg
        exact no_and_outlet C hm rb flat j hJ S small clean (by simpa [← j_eq] using posU)
          (by simpa [← j_eq] using no)
    have lastOr : (gateAt D (D.size-1)).op = .or := by
      rw [lastIndex,gate_prefix C (j+1) j hJD,gateAt_eq C j hJ]
      exact ((legal_of C hm _ (List.getElem_mem hJ)).1).resolve_left notAnd
    refine ⟨D,by omega,?_,lastOr⟩
    refine ⟨fun g hg => hm g (List.mem_of_mem_take hg),?_,?_,?_,?_,?_⟩
    · intro k hk a ha
      rw [gate_prefix C (j+1) k hk] at ha
      have hk' : k < D.size := hk
      have oldIndex : k < C.size := by omega
      exact rb k oldIndex a ha
    · rintro ⟨a,b,ha,hb,hcone⟩
      have inside (t : ℕ) (hop : (gateAt D t).op = .and) : t < D.size := by
        by_contra! outside
        change (D.gates.getD t ⟨.or,[]⟩).op = .and at hop
        rw [List.getD_eq_default _ _ outside] at hop
        cases hop
      have ha' := inside a ha
      have hb' := inside b hb
      exact flat ⟨a,b, gate_prefix C (j+1) a ha' ▸ ha, gate_prefix C (j+1) b hb' ▸ hb,
        (prefix_cone C (j+1) a b hb').mp hcone⟩
    · intro p l hl
      simpa only [sameU,sameV] using pos p l hl
    · intro T S hT hS both
      simpa only [sameU,sameV] using neg T S hT hS both
    · intro w hw
      obtain ⟨S,small,clean,yes⟩ := ws w hw
      refine ⟨S,small,clean,?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · simpa only [sameU] using yes
      · obtain rfl := List.mem_singleton.mp hw
        simpa only [sameV] using yes
  intro lines supports value noNest C u v hm rb flat positive negative witnesses lastAnd
  have h : contract C u v := ⟨hm,rb,flat,positive,negative,witnesses⟩
  obtain ⟨D,smaller,hh,orLast⟩ := trim_to_last_or C u v h lastAnd
  obtain ⟨hmD,rbD,flatD,posD,negD,witnessD⟩ := hh
  have low := hLastOr D u v hmD rbD flatD posD negD witnessD orLast
  omega
