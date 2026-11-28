import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5230_1
    (budget : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsLeastAO G C → TopForm G C → (tops G C).Nonempty →
      (∀ a ∈ tops G C,
        let s : Fin 2 → Finset (Fin 11) := side C a;
        (∀ u ∈ s 0, ∀ v ∈ s 1, G.Adj u v) ∧ ((s 0).card ≤ 1 ∨ (s 1).card ≤ 1)) →
      2 * (tops G C).card + (junk G C).card + (orN G C).card ≤ C.size + 1 ∧
      (starEdges G C).card ≤ (lam G C).card + (tops G C \ centreless G C).card)
    (caseZ0 : ∀ (C : Circuit) (g h : ℕ),
      let G : SimpleGraph (Fin 11) := edgeGraph 11
        (List.map (fun e : ℕ => (e / 11, e % 11))
          [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]);
      IsLeastAO G C → TopForm G C → junk G C = {g, h} → InCone 11 C g h →
      let U : Finset (Sym2 (Fin 11)) := Ustar G C;
      let T : Finset ℕ := tops G C;
      let R : Finset ℕ := orN G C \ lam G C;
      (∀ a ∈ T,
        let s : Fin 2 → Finset (Fin 11) := side C a;
        (∀ u ∈ s 0, ∀ v ∈ s 1, G.Adj u v) ∧ ((s 0).card ≤ 1 ∨ (s 1).card ≤ 1)) →
      (∀ (u v : Fin 11), s(u, v) ∈ U →
        ∃ a ∈ T, ∃ b : Fin 2, ∃ k : ℕ, (k = g ∨ k = h) ∧
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) k ∧ gateVal 11 C k (pairInput u v) = true) →
      4 ≤ U.card →
      (∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ 7 ≤ K.card + U.card ∧ K.card ≤ T.card) →
      centreless G C = ∅ → 0 < R.card →
      T.card + R.card ≤ 4 + U.card → 2 * T.card + (orN G C).card ≤ 20 → 16 ≤ U.card + (lam G C).card + T.card → False)
    (caseZpos : ∀ (C : Circuit) (g h : ℕ),
      let G : SimpleGraph (Fin 11) := edgeGraph 11
        (List.map (fun e : ℕ => (e / 11, e % 11))
          [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]);
      IsLeastAO G C → TopForm G C → junk G C = {g, h} → InCone 11 C g h →
      let U : Finset (Sym2 (Fin 11)) := Ustar G C;
      let Z : Finset ℕ := centreless G C;
      let T : Finset ℕ := tops G C;
      let R : Finset ℕ := orN G C \ lam G C;
      (∀ a ∈ T,
        let s : Fin 2 → Finset (Fin 11) := side C a;
        (∀ u ∈ s 0, ∀ v ∈ s 1, G.Adj u v) ∧ ((s 0).card ≤ 1 ∨ (s 1).card ≤ 1)) →
      (∀ (u v : Fin 11), s(u, v) ∈ U →
        ∃ a ∈ T, ∃ b : Fin 2, ∃ k : ℕ, (k = g ∨ k = h) ∧
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) k ∧ gateVal 11 C k (pairInput u v) = true) →
      4 ≤ U.card →
      (∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ 7 ≤ K.card + U.card ∧ K.card ≤ (T \ Z).card) →
      Z.Nonempty →
      (T \ Z).card + 2 * Z.card + R.card ≤ 4 + U.card →
      2 * T.card + (orN G C).card ≤ 20 → 16 ≤ U.card + (lam G C).card + (T \ Z).card → False) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False := by
  have hC4 : NoFourCycle (edgeGraph 11
      (List.map (fun e : ℕ => (e / 11, e % 11))
        [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97])) := by decide
  have hE16 : 16 ≤ (edgeGraph 11
      (List.map (fun e : ℕ => (e / 11, e % 11))
        [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97])).edgeFinset.card := by decide
  let G₀ : SimpleGraph (Fin 11) := edgeGraph 11
      (List.map (fun e : ℕ => (e / 11, e % 11))
        [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97])
  let I₀ : DecidableRel G₀.Adj := inferInstance
  intro G inst C g h hG hLeast hTF hJunk hCone
  dsimp only
  intro hStars hTrace hSize hU4 K hMinK hK7 hKT hPos hCount
  subst hG
  rcases Subsingleton.elim inst I₀ with rfl
  change 4 ≤ (Ustar G₀ C).card at hU4
  change K.card ≤ (tops G₀ C \ centreless G₀ C).card at hKT
  change 0 < 2 * (centreless G₀ C).card + (orN G₀ C \ lam G₀ C).card at hPos
  change (tops G₀ C \ centreless G₀ C).card + 2 * (centreless G₀ C).card +
      (orN G₀ C \ lam G₀ C).card ≤ C.size + (Ustar G₀ C).card - 17 at hCount
  have hC4' : NoFourCycle G₀ := hC4
  have hUne : (Ustar G₀ C).Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le (by decide) hU4)
  rcases hUne with ⟨e, he⟩
  have hTne : (tops G₀ C).Nonempty := by
    refine Sym2.ind (fun u v hmem => ?_) e he
    rcases hTrace u v hmem with ⟨a, ha, _⟩
    exact ⟨a, ha⟩
  have hInConeLt : ∀ (n : ℕ) (D : Circuit) (i j : ℕ), InCone n D i j → i < j := by
    intro n D i j hij
    have hfold : ∀ (gs : List Gate) (acc : List (List ℕ)),
        (∀ k < acc.length, ∀ m ∈ acc.getD k [], m < k) →
        ∀ k < (gs.foldl (coneStep n) acc).length,
          ∀ m ∈ (gs.foldl (coneStep n) acc).getD k [], m < k := by
      intro gs
      induction gs with
      | nil => intro acc hacc; exact hacc
      | cons gate tail ih =>
        intro acc hacc
        rw [List.foldl_cons]
        apply ih (coneStep n acc gate)
        intro k hk m hm
        unfold coneStep at hk hm
        rw [List.length_append, List.length_singleton] at hk
        by_cases hlt : k < acc.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
            ← List.getD_eq_getElem?_getD] at hm
          exact hacc k hlt m hm
        · have hkeq : k = acc.length := by omega
          subst hkeq
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hm
          rw [List.mem_flatMap] at hm
          rcases hm with ⟨w, hw, hwm⟩
          rw [List.mem_filter] at hw
          have hwbounds := of_decide_eq_true hw.2
          rw [List.mem_cons] at hwm
          rcases hwm with rfl | hwm
          · omega
          · exact Nat.lt_trans (hacc (w - n) (by omega) m hwm) (by omega)
    unfold InCone cones at hij
    by_cases hj : j < (D.gates.foldl (coneStep n) []).length
    · exact hfold D.gates [] (fun _ hk => False.elim (Nat.not_lt_zero _ hk)) j hj i hij
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at hij
      cases hij
  have hgh : g ≠ h := Nat.ne_of_lt (hInConeLt 11 C g h hCone)
  have hJunkCard : (junk G₀ C).card = 2 := by
    rw [hJunk]
    exact Finset.card_pair hgh
  have hB := budget G₀ C hC4' hLeast hTF hTne hStars
  have hB1 := hB.1
  have hB2 := hB.2
  have hOrNBound : 2 * (tops G₀ C).card + (orN G₀ C).card ≤ 20 := by
    rw [hJunkCard] at hB1
    omega
  have h16 : 16 ≤ (Ustar G₀ C).card + (lam G₀ C).card + (tops G₀ C \ centreless G₀ C).card := by
    have hE16' : 16 ≤ G₀.edgeFinset.card := hE16
    have hsub : G₀.edgeFinset ⊆ Ustar G₀ C ∪ starEdges G₀ C := fun x hx =>
      if hxs : x ∈ starEdges G₀ C then Finset.mem_union_right _ hxs
      else Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxs⟩)
    have hSplit : G₀.edgeFinset.card ≤ (Ustar G₀ C).card + (starEdges G₀ C).card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hCount' : (tops G₀ C \ centreless G₀ C).card + 2 * (centreless G₀ C).card +
      (orN G₀ C \ lam G₀ C).card ≤ 4 + (Ustar G₀ C).card := by omega
  have hTrace' : ∀ (u v : Fin 11), s(u, v) ∈ Ustar G₀ C →
      ∃ a ∈ tops G₀ C, ∃ b : Fin 2, ∃ k : ℕ, (k = g ∨ k = h) ∧
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) k ∧ gateVal 11 C k (pairInput u v) = true := by
    intro u v huv
    rcases hTrace u v huv with ⟨a, ha, b, k, hk, h1, h2, h3⟩
    rw [hJunk, Finset.mem_insert, Finset.mem_singleton] at hk
    exact ⟨a, ha, b, k, hk, h1, h2, h3⟩
  by_cases hZ : centreless G₀ C = ∅
  · have hPos0 : 0 < (orN G₀ C \ lam G₀ C).card := by
      rw [hZ, Finset.card_empty, Nat.mul_zero, Nat.zero_add] at hPos
      exact hPos
    have hKT0 : K.card ≤ (tops G₀ C).card := by
      rw [hZ, Finset.sdiff_empty] at hKT
      exact hKT
    have hCount0 : (tops G₀ C).card + (orN G₀ C \ lam G₀ C).card ≤ 4 + (Ustar G₀ C).card := by
      rw [hZ, Finset.sdiff_empty, Finset.card_empty, Nat.mul_zero, Nat.add_zero] at hCount'
      exact hCount'
    have h16_0 : 16 ≤ (Ustar G₀ C).card + (lam G₀ C).card + (tops G₀ C).card := by
      rw [hZ, Finset.sdiff_empty] at h16
      exact h16
    exact caseZ0 C g h hLeast hTF hJunk hCone hStars hTrace' hU4
      ⟨K, hMinK, hK7, hKT0⟩ hZ hPos0 hCount0 hOrNBound h16_0
  · have hZne : (centreless G₀ C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hZ
    exact caseZpos C g h hLeast hTF hJunk hCone hStars hTrace' hU4
      ⟨K, hMinK, hK7, hKT⟩ hZne hCount' hOrNBound h16
