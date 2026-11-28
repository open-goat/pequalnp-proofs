import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6200_1
    (h1 : ∀ (x1 : Circuit) (x2 : Fin 10 → Fin 10),
      FanInTwo x1 → x1.size ≤ 18 → Function.Injective x2 →
      (List.filter (fun x5 : Gate => x5.inputs.any fun x6 : ℕ =>
        (List.ofFn x2).getD x6 1 == 0) x1.gates).length = 1 →
      ∃ x6 : Fin 10 → Bool,
        x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 0 || x6 2]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
           x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 4 && x6 9 ||
           x6 5 && x6 7 || x6 7 && x6 9 || x6 9 && x6 6 || x6 6 && x6 8 || x6 8 && x6 5))
    (h2 : ∀ (x1 : Circuit) (x2 : Fin 10 → Fin 10),
      FanInTwo x1 → x1.size ≤ 18 → Function.Injective x2 →
      (List.filter (fun x5 : Gate => x5.inputs.any fun x6 : ℕ =>
        (List.ofFn x2).getD x6 1 == 0) x1.gates).length = 2 →
      ∃ x6 : Fin 10 → Bool,
        x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 0 || x6 2]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
           x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 4 && x6 9 ||
           x6 5 && x6 7 || x6 7 && x6 9 || x6 9 && x6 6 || x6 6 && x6 8 || x6 8 && x6 5))
    (h3 : ∀ (x1 : Circuit) (x2 : Fin 10 → Fin 10),
      FanInTwo x1 → x1.size ≤ 18 → Function.Injective x2 →
      (List.filter (fun x5 : Gate => x5.inputs.any fun x6 : ℕ =>
        (List.ofFn x2).getD x6 1 == 0) x1.gates).length = 3 →
      ∃ x6 : Fin 10 → Bool,
        x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 0 || x6 2]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
           x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 4 && x6 9 ||
           x6 5 && x6 7 || x6 7 && x6 9 || x6 9 && x6 6 || x6 6 && x6 8 || x6 8 && x6 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)),
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) →
      (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.any fun (x6 : ℕ) =>
        (List.ofFn x2).getD x6 (1 : Fin (10 : ℕ)) == (0 : Fin (10 : ℕ))) x1.gates).length ≤ (3 : ℕ) →
      ∃ (x6 : Fin (10 : ℕ) → Bool),
        x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠
          (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) ||
           x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) ||
           x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) ||
           x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) ||
           x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) ||
           x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) ||
           x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) ||
           x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  intro C f hF hsz hcnt
  let pet : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  by_cases hinj : Function.Injective f
  · by_cases h0 : (List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
        (List.ofFn f).getD k 1 == 0) C.gates).length = 0
    · have hnone : ∀ g ∈ C.gates, ∀ k ∈ g.inputs, (List.ofFn f).getD k 1 ≠ 0 := by
        intro g hg k hk heq
        have hmem : g ∈ List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
            (List.ofFn f).getD k 1 == 0) C.gates :=
          List.mem_filter.mpr ⟨hg, List.any_eq_true.mpr ⟨k, hk, beq_iff_eq.mpr heq⟩⟩
        have hpos : 0 < (List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
            (List.ofFn f).getD k 1 == 0) C.gates).length := List.length_pos_of_mem hmem
        omega
      let a0 : Fin 10 → Bool := fun u => decide (u = 2 ∨ u = 5)
      let a1 : Fin 10 → Bool := fun u => decide (u = 0 ∨ u = 2 ∨ u = 5)
      let w0 : List Bool := List.ofFn (a0 ∘ f) ++ [a0 0 || a0 2]
      let w1 : List Bool := List.ofFn (a1 ∘ f) ++ [a1 0 || a1 2]
      have hlen : w0.length = 11 ∧ w1.length = 11 := by simp [w0, w1]
      have hor : (a0 0 || a0 2) = (a1 0 || a1 2) := by decide
      have hagree : ∀ k, (List.ofFn f).getD k 1 ≠ 0 → w0.getD k false = w1.getD k false := by
        intro k hk
        by_cases hk10 : k < 10
        · have hfne : f ⟨k, hk10⟩ ≠ 0 := by
            have hlt : k < (List.ofFn f).length := by rw [List.length_ofFn]; exact hk10
            rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn] at hk
            exact hk
          have hlt0 : k < (List.ofFn (a0 ∘ f)).length := by rw [List.length_ofFn]; exact hk10
          have hlt1 : k < (List.ofFn (a1 ∘ f)).length := by rw [List.length_ofFn]; exact hk10
          rw [List.getD_append _ _ _ _ hlt0, List.getD_append _ _ _ _ hlt1,
            List.getD_eq_getElem _ _ hlt0, List.getD_eq_getElem _ _ hlt1,
            List.getElem_ofFn, List.getElem_ofFn]
          simp only [Function.comp_apply, a0, a1, hfne, false_or]
        · by_cases hk10eq : k = 10
          · subst hk10eq
            simp only [w0, w1, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
            simpa using hor
          · rw [List.getD_eq_default w0 false (by rw [hlen.1]; omega),
              List.getD_eq_default w1 false (by rw [hlen.2]; omega)]
      have hfold_lt : ∀ (gs : List Gate) (u : List Bool) (k : ℕ), k < u.length →
          (gs.foldl (fun w g => w ++ [g.op.eval (List.map (fun i => w.getD i false) g.inputs)]) u).getD k false = u.getD k false := by
        intro gs
        induction gs with
        | nil => intro u k _; rfl
        | cons g gs ih =>
          intro u k hk
          simp only [List.foldl_cons]
          rw [ih _ k (by simp; omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      have hfold : ∀ (gs : List Gate) (u0 u1 : List Bool),
          u0.length = u1.length →
          (∀ k, u0.length ≤ k → u0.getD k false = u1.getD k false) →
          (∀ g ∈ gs, ∀ k ∈ g.inputs, u0.getD k false = u1.getD k false) →
          ∀ j, u0.length ≤ j →
            (gs.foldl (fun w g => w ++ [g.op.eval (List.map (fun i => w.getD i false) g.inputs)]) u0).getD j false =
            (gs.foldl (fun w g => w ++ [g.op.eval (List.map (fun i => w.getD i false) g.inputs)]) u1).getD j false := by
        intro gs
        induction gs with
        | nil => intro u0 u1 _ hge _ j hj; exact hge j hj
        | cons g gs ih =>
          intro u0 u1 hlu hge hgs j hj
          simp only [List.foldl_cons]
          have hval : g.op.eval (g.inputs.map fun i => u0.getD i false) =
              g.op.eval (g.inputs.map fun i => u1.getD i false) := by
            congr 1
            apply List.map_congr_left
            intro i hi
            exact hgs g List.mem_cons_self i hi
          let u0' := u0 ++ [g.op.eval (g.inputs.map fun i => u0.getD i false)]
          let u1' := u1 ++ [g.op.eval (g.inputs.map fun i => u1.getD i false)]
          have hlu' : u0'.length = u1'.length := by simp [u0', u1', hlu]
          have hge' : ∀ k, u0'.length ≤ k → u0'.getD k false = u1'.getD k false := by
            intro k hk
            rw [List.getD_eq_default _ _ hk, List.getD_eq_default _ _ (hlu' ▸ hk)]
          have hgs' : ∀ g' ∈ gs, ∀ k ∈ g'.inputs, u0'.getD k false = u1'.getD k false := by
            intro g' hg' k hk
            by_cases hklt : k < u0.length
            · simp only [u0', u1', List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left hklt, List.getElem?_append_left (hlu ▸ hklt)]
              exact hgs g' (List.mem_cons_of_mem _ hg') k hk
            · by_cases hkeq : k = u0.length
              · subst hkeq
                simp only [u0', u1', List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (hlu ▸ le_refl _)]
                simp only [hlu, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                exact hval
              · exact hge' k (by simp [u0']; omega)
          by_cases hjeq : j = u0.length
          · subst hjeq
            rw [hfold_lt gs u0' u0.length (by simp [u0']), hfold_lt gs u1' u0.length (by simp [u1', hlu])]
            simp only [u0', u1', List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (hlu ▸ le_refl _)]
            simp only [hlu, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            exact hval
          · exact ih u0' u1' hlu' hge' hgs' j (by simp [u0']; omega)
      by_cases hout : (List.ofFn f).getD C.output 1 = 0
      · have hout10 : C.output < 10 := by
          by_contra! hge
          have hlen10 : (List.ofFn f).length ≤ C.output := by rw [List.length_ofFn]; exact hge
          rw [List.getD_eq_default _ _ hlen10] at hout
          exact absurd hout (by decide)
        have hfout : f ⟨C.output, hout10⟩ = 0 := by
          have hlt : C.output < (List.ofFn f).length := by rw [List.length_ofFn]; exact hout10
          rw [← List.getElem_ofFn (f := f) (i := C.output) hlt, ← List.getD_eq_getElem _ 1 hlt]
          exact hout
        let b0 : Fin 10 → Bool := fun u => decide (u = 0 ∨ u = 7)
        refine ⟨b0, ?_⟩
        have hev : C.eval (List.ofFn (b0 ∘ f) ++ [b0 0 || b0 2]) = true := by
          change (C.wires (List.ofFn (b0 ∘ f) ++ [b0 0 || b0 2])).getD C.output false = true
          have hfold_lt : ∀ (gs : List Gate) (u : List Bool) (k : ℕ), k < u.length →
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD k false = u.getD k false := by
            intro gs
            induction gs with
            | nil => intro u k _; rfl
            | cons g gs ih =>
              intro u k hk
              simp only [List.foldl_cons]
              rw [ih _ k (by simp; omega)]
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
          dsimp only [Circuit.wires]
          rw [hfold_lt _ _ C.output (by rw [List.length_append, List.length_ofFn]; omega)]
          rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hout10)]
          have hltb : C.output < (List.ofFn (b0 ∘ f)).length := by rw [List.length_ofFn]; exact hout10
          rw [List.getD_eq_getElem _ _ hltb, List.getElem_ofFn]
          change (b0 ∘ f) ⟨C.output, hout10⟩ = true
          simp only [Function.comp_apply, hfout, b0]
          decide
        rw [hev]
        decide
      · have heval : C.eval w0 = C.eval w1 := by
          by_cases h11 : 11 ≤ C.output
          · exact hfold C.gates w0 w1 (by omega)
              (fun k hk => by
                have hk2 : w1.length ≤ k := by rw [hlen.2, ← hlen.1]; exact hk
                rw [List.getD_eq_default w0 false hk, List.getD_eq_default w1 false hk2])
              (fun g hg k hk => hagree k (hnone g hg k hk)) C.output (by omega)
          · have hfold_lt : ∀ (gs : List Gate) (u : List Bool) (k : ℕ), k < u.length →
                (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD k false = u.getD k false := by
              intro gs
              induction gs with
              | nil => intro u k _; rfl
              | cons g gs ih =>
                intro u k hk
                simp only [List.foldl_cons]
                rw [ih _ k (by simp; omega)]
                simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
            change (C.wires w0).getD C.output false = (C.wires w1).getD C.output false
            dsimp only [Circuit.wires]
            rw [hfold_lt C.gates w0 C.output (by rw [hlen.1]; omega),
              hfold_lt C.gates w1 C.output (by rw [hlen.2]; omega)]
            exact hagree C.output hout
        by_cases hc0 : C.eval w0 = pet a0
        · refine ⟨a1, ?_⟩
          have hp0 : pet a0 = false := by decide
          have hp1 : pet a1 = true := by decide
          change C.eval w1 ≠ pet a1
          rw [← heval, hc0, hp0, hp1]
          decide
        · exact ⟨a0, hc0⟩
    · have hpos : 1 ≤ (List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
          (List.ofFn f).getD k 1 == 0) C.gates).length := Nat.pos_of_ne_zero h0
      have hcases : (List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
          (List.ofFn f).getD k 1 == 0) C.gates).length = 1 ∨
        (List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
          (List.ofFn f).getD k 1 == 0) C.gates).length = 2 ∨
        (List.filter (fun g : Gate => g.inputs.any fun k : ℕ =>
          (List.ofFn f).getD k 1 == 0) C.gates).length = 3 := by omega
      rcases hcases with h | h | h
      · exact h1 C f hF hsz hinj h
      · exact h2 C f hF hsz hinj h
      · exact h3 C f hF hsz hinj h
  · have hnsurj : ∃ v : Fin 10, ∀ j : Fin 10, f j ≠ v := by
      by_contra hsurj
      push Not at hsurj
      have hsurj' : Function.Surjective f := hsurj
      exact hinj (Finite.injective_iff_surjective.mpr hsurj')
    obtain ⟨v, hv⟩ := hnsurj
    have pair_diff : ∀ (a0 a1 : Fin 10 → Bool),
        (∀ u, u ≠ v → a0 u = a1 u) → (a0 0 || a0 2) = (a1 0 || a1 2) →
        pet a0 ≠ pet a1 →
        ∃ x6 : Fin 10 → Bool, C.eval (List.ofFn (x6 ∘ f) ++ [x6 0 || x6 2]) ≠ pet x6 := by
      intro a0 a1 ha hor hpet
      have hcomp : a0 ∘ f = a1 ∘ f := funext fun j => ha (f j) (hv j)
      have hev : C.eval (List.ofFn (a0 ∘ f) ++ [a0 0 || a0 2]) =
          C.eval (List.ofFn (a1 ∘ f) ++ [a1 0 || a1 2]) := by
        rw [hcomp, hor]
      by_cases hc : C.eval (List.ofFn (a0 ∘ f) ++ [a0 0 || a0 2]) = pet a0
      · exact ⟨a1, fun h => hpet (hc.symm.trans (hev.trans h))⟩
      · exact ⟨a0, hc⟩
    fin_cases v
    · exact pair_diff (fun u => decide (u = 2 ∨ u = 5)) (fun u => decide (u = 0 ∨ u = 2 ∨ u = 5))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 6)) (fun u => decide (u = 1 ∨ u = 6))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 0 ∨ u = 7)) (fun u => decide (u = 0 ∨ u = 2 ∨ u = 7))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 8)) (fun u => decide (u = 3 ∨ u = 8))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 9)) (fun u => decide (u = 4 ∨ u = 9))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 7)) (fun u => decide (u = 5 ∨ u = 7))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 8)) (fun u => decide (u = 6 ∨ u = 8))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 9)) (fun u => decide (u = 7 ∨ u = 9))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 6)) (fun u => decide (u = 8 ∨ u = 6))
        (by decide) (by decide) (by decide)
    · exact pair_diff (fun u => decide (u = 7)) (fun u => decide (u = 9 ∨ u = 7))
        (by decide) (by decide) (by decide)
