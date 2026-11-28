import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_6752_1
    (hOneLive :
      let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        2 ≤ J.card → 1 ≤ (centreless G C).card + (orN G C \ lam G C).card →
        ∀ V ⊆ U, 3 ≤ V.card →
          (U \ V).card ≤ (J.filter (fun j => Disjoint V (gammaE G C j))).card →
          (∀ j ∈ J, (V ∩ gammaE G C j).card ≠ 1) →
          (∀ e ∈ U, ∃ j ∈ J, e ∈ gammaE G C j) →
          (∃ g ∈ J, V ⊆ gammaE G C g ∧ ∀ j ∈ J, j ≠ g → Disjoint V (gammaE G C j)) →
          V.card ≤ 2 * (centreless G C).card + (J.card - (U \ V).card) + (orN G C \ lam G C).card)
    (hMultiLive :
      let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        2 ≤ J.card → 1 ≤ (centreless G C).card + (orN G C \ lam G C).card →
        ∀ V ⊆ U, 4 ≤ V.card →
          (U \ V).card ≤ (J.filter (fun j => Disjoint V (gammaE G C j))).card →
          2 ≤ (J.filter (fun j => ¬ Disjoint V (gammaE G C j))).card →
          (∀ j ∈ J, (V ∩ gammaE G C j).card ≠ 1) →
          (∀ e ∈ U, ∃ j ∈ J, e ∈ gammaE G C j) →
          V.card ≤ 2 * (centreless G C).card + (J.card - (U \ V).card) + (orN G C \ lam G C).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → ∀ x9 ⊆ x7, x9.Nonempty → (x7 \ x9).card ≤ {x12 ∈ x6 | Disjoint x9 (PEqualNP.TopForm.gammaE x1 x2 x12)}.card → (∀ x13 ∈ x6, (x9 ∩ PEqualNP.TopForm.gammaE x1 x2 x13).card ≠ (1 : ℕ)) → (∀ x14 ∈ x7, ∃ x16 ∈ x6, x14 ∈ PEqualNP.TopForm.gammaE x1 x2 x16) → x9.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x9).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  dsimp only
  intro C hsize hleast htop hJ2 V hVU hVne hdead hno1 hcov
  set G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  set J := junk G C
  set U := Ustar G C
  have hAO : IsAO2 11 C := hleast.1
  have hfun : circuitFun 11 C = graphFun G ∅ := hleast.2.1
  have hmin : ∀ C' : Circuit, IsAO2 11 C' → circuitFun 11 C' = graphFun G ∅ → C.size ≤ C'.size :=
    hleast.2.2
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hstepW_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      change (w ++ [_]).length + gs.length = _
      rw [List.length_append, List.length_singleton, List.length_cons]
      omega
  have hstepW_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepW w g).length := by
        change i < (w ++ [_]).length
        rw [List.length_append, List.length_singleton]
        omega
      rw [ih _ i hlt]
      change (w ++ [_]).getD i false = w.getD i false
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstepW_gate : ∀ (gs : List Gate) (w : List Bool) (k : ℕ), k < gs.length →
      (gs.foldl stepW w).getD (w.length + k) false =
        (gs.getD k ⟨GateOp.or, []⟩).op.eval
          ((gs.getD k ⟨GateOp.or, []⟩).inputs.map fun i =>
            if i < w.length + k then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro w k hk; simp at hk
    | append_singleton gs g ih =>
      intro w k hk
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen := hstepW_len gs w
      rw [List.length_append, List.length_singleton] at hk
      have hkeep : ∀ i < w.length + gs.length,
          (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
        intro i hi
        change (gs.foldl stepW w ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false)]).getD i false = _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rcases Nat.lt_or_ge k gs.length with hlt | hge
      · have hg : (gs ++ [g]).getD k ⟨GateOp.or, []⟩ = gs.getD k ⟨GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [hg, hkeep _ (by omega), ih w k hlt]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [hkeep i (by omega)]
        · rfl
      · have hk' : k = gs.length := by omega
        subst hk'
        have hg : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
          rfl
        rw [hg]
        have heval : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
            g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
          change (gs.foldl stepW w ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false)]).getD (w.length + gs.length) false = _
          rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _), Nat.sub_self]
          rfl
        rw [heval]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [hkeep i hi]
        · have hout : (gs.foldl stepW w).length ≤ i := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hout]
          rfl
  have horSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep 11) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = _
      rw [List.length_append, List.length_singleton, List.length_cons]
      omega
  have horSets_get_and : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ),
      k < gs.length → (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and →
      (gs.foldl (orStep 11) cs).getD (cs.length + k) [] = [cs.length + k] := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro cs k hk; simp at hk
    | append_singleton gs g ih =>
      intro cs k hk hop
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen := horSets_len gs cs
      rw [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k gs.length with hlt | hge
      · have hg : (gs ++ [g]).getD k ⟨GateOp.or, []⟩ = gs.getD k ⟨GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [hg] at hop
        have hkeep : (orStep 11 (gs.foldl (orStep 11) cs) g).getD (cs.length + k) [] =
            (gs.foldl (orStep 11) cs).getD (cs.length + k) [] := by
          change (gs.foldl (orStep 11) cs ++ [_]).getD (cs.length + k) [] = _
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        rw [hkeep]
        exact ih cs k hlt hop
      · have hk' : k = gs.length := by omega
        subst hk'
        have hg : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
          rfl
        rw [hg] at hop
        set s := gs.foldl (orStep 11) cs
        delta orStep
        rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _), Nat.sub_self]
        change s.length :: (if g.op = GateOp.or then _ else []) = [s.length]
        rw [hop]
        rfl
  have horIn_and_empty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      orIn 11 C (11 + j) = ∅ := by
    intro j hj hop
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    delta orIn at hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with heq | ⟨k, hk, hreach, hkor, _⟩
    · have := i.isLt; omega
    · rcases hreach with ⟨_, hmem⟩
      have hsub : 11 + j - 11 = j := by omega
      rw [hsub] at hmem
      have hlist : (orSets 11 C).getD j [] = [j] := by
        have h0 := horSets_get_and C.gates [] j hj hop
        rw [List.length_nil, Nat.zero_add] at h0
        exact h0
      rw [hlist, List.mem_singleton] at hmem
      subst hmem
      rw [hop] at hkor
      cases hkor
  have hActive : 1 ≤ (centreless G C).card + (orN G C \ lam G C).card := by
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    let j := J.max' hJne
    have hjJ : j ∈ J := Finset.max'_mem J hJne
    have hjData : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        ∃ x : Fin 11 → Bool, gateVal 11 C j x = true ∧ graphFun G ∅ x = false := by
      change j ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd 11 G C k) at hjJ
      rw [Finset.mem_filter, Finset.mem_range] at hjJ
      exact ⟨hjJ.1, hjJ.2.1, hjJ.2.2.2⟩
    obtain ⟨hjLt, hjAnd, xdirty, hxdirty_t, hxdirty_f⟩ := hjData
    have hreaders_ne : (readers 11 C j).Nonempty := by
      by_contra hremp
      rw [Finset.not_nonempty_iff_eq_empty] at hremp
      have hnoread : ∀ k < C.gates.length, 11 + j ∉ (gateAt C k).inputs := by
        intro k hk hmem
        have : k ∈ readers 11 C j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hmem⟩
        rw [hremp] at this
        exact Finset.notMem_empty k this
      have hout_ne : C.output ≠ 11 + j := by
        intro heq
        have h1 : circuitFun 11 C xdirty = true := by
          change (C.wires (List.ofFn xdirty)).getD C.output false = true
          rw [heq]
          exact hxdirty_t
        have h2 : circuitFun 11 C xdirty = graphFun G ∅ xdirty := congrFun hfun xdirty
        rw [h1, hxdirty_f] at h2
        cases h2
      have hout_lt : C.output < 11 + C.gates.length := by
        by_contra hge
        have hge' : 11 + C.gates.length ≤ C.output := Nat.le_of_not_lt hge
        have htrue : graphFun G ∅ (pairInput (0 : Fin 11) (9 : Fin 11)) = true := by
          decide
        have hfalse : circuitFun 11 C (pairInput (0 : Fin 11) (9 : Fin 11)) = false := by
          change (C.wires (List.ofFn (pairInput (0 : Fin 11) (9 : Fin 11)))).getD C.output false = false
          have hlen : (C.wires (List.ofFn (pairInput (0 : Fin 11) (9 : Fin 11)))).length =
              11 + C.gates.length := by
            have h0 := hstepW_len C.gates (List.ofFn (pairInput (0 : Fin 11) (9 : Fin 11)))
            rw [List.length_ofFn] at h0
            exact h0
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
        have h2 : circuitFun 11 C (pairInput (0 : Fin 11) (9 : Fin 11)) =
            graphFun G ∅ (pairInput (0 : Fin 11) (9 : Fin 11)) := congrFun hfun _
        rw [hfalse, htrue] at h2
        cases h2
      let shift (w : ℕ) : ℕ := if w < 11 + j then w else w - 1
      let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map shift⟩
      let C' : Circuit := ⟨(C.gates.eraseIdx j).map shiftGate, shift C.output⟩
      have hC'_len : C'.gates.length = C.gates.length - 1 := by
        change ((C.gates.eraseIdx j).map shiftGate).length = C.gates.length - 1
        rw [List.length_map, List.length_eraseIdx_of_lt hjLt]
      have hC'_get : ∀ k < C'.gates.length,
          gateAt C' k = shiftGate (gateAt C (if k < j then k else k + 1)) := by
        intro k hk
        change ((C.gates.eraseIdx j).map shiftGate).getD k ⟨GateOp.or, []⟩ =
          shiftGate (C.gates.getD (if k < j then k else k + 1) ⟨GateOp.or, []⟩)
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
        split_ifs with hkj
        · have hklt : k < C.gates.length := by omega
          rw [List.getElem?_eq_getElem hklt]
          rfl
        · have hklt : k + 1 < C.gates.length := by omega
          rw [List.getElem?_eq_getElem hklt]
          rfl
      have hC'_AO : IsAO2 11 C' := by
        refine ⟨?_, ?_, ?_⟩
        · intro g hg
          change g ∈ (C.gates.eraseIdx j).map shiftGate at hg
          rw [List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
        · intro k hk w hw
          rw [hC'_get k hk] at hw
          change w ∈ (gateAt C (if k < j then k else k + 1)).inputs.map shift at hw
          rw [List.mem_map] at hw
          obtain ⟨w0, hw0, rfl⟩ := hw
          let k0 := if k < j then k else k + 1
          have hk0 : k0 < C.gates.length := by dsimp [k0]; split_ifs <;> omega
          have hw0_lt : w0 < 11 + k0 := hAO.2.1 k0 hk0 w0 hw0
          have hw0_ne : w0 ≠ 11 + j := fun heq => hnoread k0 hk0 (heq ▸ hw0)
          dsimp [shift, k0] at hw0_lt ⊢
          split_ifs at hw0_lt ⊢ <;> omega
        · intro g hg
          change g ∈ (C.gates.eraseIdx j).map shiftGate at hg
          rw [List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          change (g0.inputs.map shift).length = 2
          rw [List.length_map]
          exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)
      have hC'_wires : ∀ (x : Fin 11 → Bool) (w : ℕ), w < 11 + C.gates.length → w ≠ 11 + j →
          (C'.wires (List.ofFn x)).getD (shift w) false = (C.wires (List.ofFn x)).getD w false := by
        intro x w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwlt hwne
          by_cases hwin : w < 11
          · have hsh : shift w = w := by dsimp [shift]; split_ifs <;> omega
            rw [hsh]
            have h1 := hstepW_lt C'.gates (List.ofFn x) w (by rw [List.length_ofFn]; omega)
            have h2 := hstepW_lt C.gates (List.ofFn x) w (by rw [List.length_ofFn]; omega)
            exact h1.trans h2.symm
          · let k0 := w - 11
            have hk0_lt : k0 < C.gates.length := by omega
            have hw_eq : w = 11 + k0 := by omega
            have hk0_ne : k0 ≠ j := by omega
            let k' := if k0 < j then k0 else k0 - 1
            have hk'_lt : k' < C'.gates.length := by dsimp [k']; split_ifs <;> omega
            have hsh : shift w = 11 + k' := by dsimp [shift, k']; split_ifs <;> omega
            have hk'_orig : (if k' < j then k' else k' + 1) = k0 := by
              dsimp [k']; split_ifs <;> omega
            rw [hsh, hw_eq]
            have h1 := hstepW_gate C'.gates (List.ofFn x) k' hk'_lt
            have h2 := hstepW_gate C.gates (List.ofFn x) k0 hk0_lt
            rw [List.length_ofFn] at h1 h2
            change (C'.gates.foldl stepW (List.ofFn x)).getD (11 + k') false =
              (C.gates.foldl stepW (List.ofFn x)).getD (11 + k0) false
            rw [h1, h2]
            have hgat : gateAt C' k' = shiftGate (gateAt C k0) := by
              rw [hC'_get k' hk'_lt, hk'_orig]
            change (gateAt C' k').op.eval ((gateAt C' k').inputs.map fun i =>
                if i < 11 + k' then (C'.gates.foldl stepW (List.ofFn x)).getD i false else false) =
              (gateAt C k0).op.eval ((gateAt C k0).inputs.map fun i =>
                if i < 11 + k0 then (C.gates.foldl stepW (List.ofFn x)).getD i false else false)
            rw [hgat]
            dsimp only [shiftGate]
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hu_lt : u < 11 + k0 := hAO.2.1 k0 hk0_lt u hu
            have hu_ne : u ≠ 11 + j := fun heq => hnoread k0 hk0_lt (heq ▸ hu)
            have hshu_lt : shift u < 11 + k' := by dsimp [shift, k']; split_ifs <;> omega
            change (if shift u < 11 + k' then (C'.gates.foldl stepW (List.ofFn x)).getD (shift u) false else false) =
              (if u < 11 + k0 then (C.gates.foldl stepW (List.ofFn x)).getD u false else false)
            simp only [hshu_lt, hu_lt, ite_true]
            exact ih u (by omega) (by omega) hu_ne
      have hC'_fun : circuitFun 11 C' = graphFun G ∅ := by
        funext x
        rw [← hfun]
        exact hC'_wires x C.output hout_lt hout_ne
      have hle := hmin C' hC'_AO hC'_fun
      change C.gates.length ≤ C'.gates.length at hle
      omega
    obtain ⟨r, hr⟩ := hreaders_ne
    change r ∈ (Finset.range C.gates.length).filter (fun k => 11 + j ∈ (gateAt C k).inputs) at hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrLt, hrIn⟩ := hr
    have hjr : j < r := by
      have hlt := hAO.2.1 r hrLt (11 + j) hrIn
      omega
    have hrlen : (gateAt C r).inputs.length = 2 := by
      have hmem : gateAt C r ∈ C.gates := by
        change C.gates.getD r ⟨GateOp.or, []⟩ ∈ C.gates
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrLt]
        exact List.getElem_mem hrLt
      exact hAO.2.2 (gateAt C r) hmem
    have hopnd : opnd C r 0 = 11 + j ∨ opnd C r 1 = 11 + j := by
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hrlen
      have hmem : 11 + j = a ∨ 11 + j = b := by
        rw [hab] at hrIn
        rw [List.mem_cons, List.mem_singleton] at hrIn
        exact hrIn
      change (gateAt C r).inputs.getD 0 0 = 11 + j ∨ (gateAt C r).inputs.getD 1 0 = 11 + j
      rw [hab]
      rcases hmem with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hrop : (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or := by
      have hmem : gateAt C r ∈ C.gates := by
        change C.gates.getD r ⟨GateOp.or, []⟩ ∈ C.gates
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrLt]
        exact List.getElem_mem hrLt
      exact hAO.1 (gateAt C r) hmem
    rcases hrop with hrAnd | hrOr
    · have hrBelow : BelowF G C r := by
        by_contra hnot
        change ¬ ∀ x : Fin 11 → Bool, gateVal 11 C r x = true → graphFun G ∅ x = true at hnot
        rw [not_forall] at hnot
        obtain ⟨x, hx⟩ := hnot
        rw [not_imp] at hx
        obtain ⟨hxt, hxf⟩ := hx
        have hxf' : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hxf
        have hrJ : r ∈ J := by
          change r ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd 11 G C k)
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hrLt, hrAnd, hrLt, x, hxt, hxf'⟩
        have hle := Finset.le_max' J r hrJ
        omega
      have hrTop : r ∈ tops G C := by
        delta tops gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hrLt, hrAnd, hrBelow⟩
      have hrCentre : r ∈ centreless G C := by
        delta centreless
        rw [Finset.mem_filter]
        refine ⟨hrTop, ?_⟩
        rcases hopnd with h0 | h1
        · left
          delta side
          rw [h0]
          exact horIn_and_empty j hjLt hjAnd
        · right
          delta side
          rw [h1]
          exact horIn_and_empty j hjLt hjAnd
      have hpos : 1 ≤ (centreless G C).card := Finset.card_pos.mpr ⟨r, hrCentre⟩
      omega
    · have hrNotBelow : ¬ BelowF G C r := by
        intro hB
        have hrVal : gateVal 11 C r xdirty = true := by
          change (C.gates.foldl stepW (List.ofFn xdirty)).getD (11 + r) false = true
          have hg := hstepW_gate C.gates (List.ofFn xdirty) r hrLt
          rw [List.length_ofFn] at hg
          rw [hg]
          change (gateAt C r).op.eval ((gateAt C r).inputs.map fun i =>
            if i < 11 + r then (C.gates.foldl stepW (List.ofFn xdirty)).getD i false else false) = true
          rw [hrOr]
          change ((gateAt C r).inputs.map fun i =>
            if i < 11 + r then (C.gates.foldl stepW (List.ofFn xdirty)).getD i false else false).any id = true
          rw [List.any_eq_true]
          refine ⟨true, List.mem_map.mpr ⟨11 + j, hrIn, ?_⟩, rfl⟩
          have hlt : 11 + j < 11 + r := by omega
          simp only [hlt, ite_true]
          exact hxdirty_t
        have hf := hB xdirty hrVal
        rw [hxdirty_f] at hf
        cases hf
      have hrOrN : r ∈ orN G C := by
        delta orN gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hrLt, hrOr, hrNotBelow⟩
      have hrNotLam : r ∉ lam G C := by
        intro hlam
        delta lam at hlam
        rw [Finset.mem_filter] at hlam
        rcases hopnd with h0 | h1
        · rw [h0, horIn_and_empty j hjLt hjAnd] at hlam
          exact Finset.not_nonempty_empty hlam.2.1
        · rw [h1, horIn_and_empty j hjLt hjAnd] at hlam
          exact Finset.not_nonempty_empty hlam.2.2.1
      have hrDiff : r ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hrOrN, hrNotLam⟩
      have hpos : 1 ≤ (orN G C \ lam G C).card := Finset.card_pos.mpr ⟨r, hrDiff⟩
      omega
  let Jdead := J.filter (fun j => Disjoint V (gammaE G C j))
  let Jlive := J.filter (fun j => ¬ Disjoint V (gammaE G C j))
  have hdead' : (U \ V).card ≤ Jdead.card := hdead
  change V.card ≤ 2 * (centreless G C).card + (J.card - (U \ V).card) + (orN G C \ lam G C).card
  have hJsplit : Jdead.card + Jlive.card = J.card :=
    Finset.card_filter_add_card_filter_not (s := J) (fun j => Disjoint V (gammaE G C j))
  have hJlive_pos : 1 ≤ Jlive.card := by
    obtain ⟨e, heV⟩ := hVne
    obtain ⟨j, hjJ, hej⟩ := hcov e (hVU heV)
    have hnotd : ¬ Disjoint V (gammaE G C j) := by
      intro hd
      exact Finset.disjoint_left.mp hd heV hej
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hjJ, hnotd⟩⟩
  have hJlive_le : Jlive.card ≤ J.card - (U \ V).card := by omega
  by_cases h1 : Jlive.card = 1
  · by_cases hV2 : V.card ≤ 2
    · omega
    · obtain ⟨g, hgEq⟩ := Finset.card_eq_one.mp h1
      have hgMem : g ∈ Jlive := hgEq ▸ Finset.mem_singleton_self g
      have hgJ : g ∈ J := (Finset.mem_filter.mp hgMem).1
      have hOther : ∀ j ∈ J, j ≠ g → Disjoint V (gammaE G C j) := by
        intro j hjJ hne
        by_contra hnotd
        have : j ∈ Jlive := Finset.mem_filter.mpr ⟨hjJ, hnotd⟩
        rw [hgEq, Finset.mem_singleton] at this
        exact hne this
      have hVsub : V ⊆ gammaE G C g := by
        intro e heV
        obtain ⟨j, hjJ, hej⟩ := hcov e (hVU heV)
        by_cases hjg : j = g
        · exact hjg ▸ hej
        · exfalso
          exact Finset.disjoint_left.mp (hOther j hjJ hjg) heV hej
      exact hOneLive C hsize hleast htop hJ2 hActive V hVU (by omega) hdead hno1 hcov
        ⟨g, hgJ, hVsub, hOther⟩
  · have hJlive2 : 2 ≤ Jlive.card := by omega
    by_cases hV3 : V.card ≤ 3
    · omega
    · exact hMultiLive C hsize hleast htop hJ2 hActive V hVU (by omega) hdead hJlive2 hno1 hcov
