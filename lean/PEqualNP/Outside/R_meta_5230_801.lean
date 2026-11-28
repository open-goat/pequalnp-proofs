import PEqualNP.Defs
-- Submitted via OpenAI Codex by gpt-6.2-astra.
-- The first child uses the small-defect bound of upstream L_meta_18392 for a comparable pair.
-- A violation of the budget forces a positive non-lambda OR count and a charge of at least two.

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5230_801
  (small : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (a b : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map (fun (i : ℕ) => (i/11,i%11))) →
      IsLeastAO G C → TopForm G C → junk G C = {a,b} → InCone 11 C a b →
      let u := (Ustar G C).card
      let c := (centreless G C).card
      let o := (orN G C \ lam G C).card
      4 ≤ u → o=0 ∨ o=1 ∧ c=0 → 2*u ≤ 2*c+2+o)
  (core : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (a b : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map (fun (i : ℕ) => (i/11,i%11))) →
      IsLeastAO G C → TopForm G C → junk G C = {a,b} → InCone 11 C a b →
      let U := Ustar G C
      let Z := centreless G C
      let o := (orN G C \ lam G C).card
      let t := (tops G C \ Z).card
      let p := 2*Z.card+o
      C.size ≤ 21 → 4 ≤ U.card → 0 < o → 2 ≤ p → p+2 < 2*U.card →
      (∀ u v : Fin 11, s(u,v) ∈ U →
        gateVal 11 C a (pairInput u v) || gateVal 11 C b (pairInput u v)) →
      (∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges (U : Set (Sym2 (Fin 11)))) K ∧
        7 ≤ K.card+U.card ∧ K.card ≤ t ∧ t+p ≤ 4+U.card) → False) :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False := by
  intro G inst C a b eqG least top dirty cone U Z R T sides cover sz hu K hK hseven hkt hpos budget
  have low : R.card=0 ∨ R.card=1 ∧ Z.card=0 → 2*U.card ≤ 2*Z.card+2+R.card :=
    small G C a b eqG least top dirty cone hu
  have bound : (T \ Z).card + (2*Z.card+R.card) ≤ 4+U.card := by omega
  have failSmall : ¬ (R.card=0 ∨ R.card=1 ∧ Z.card=0) := by
    intro h
    have := low h
    omega
  have hit : ∀ u v : Fin 11, s(u,v) ∈ U →
      gateVal 11 C a (pairInput u v) || gateVal 11 C b (pairInput u v) := by
    intro u v hv
    obtain ⟨i, hi, k, j, hj, hon, hreach, hed⟩ := cover u v hv
    rw [dirty] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [hed]
  exact core G C a b eqG least top dirty cone sz hu (by omega : 0<R.card)
    (by omega : 2≤2*Z.card+R.card) (by omega : 2*Z.card+R.card+2<2*U.card)
    hit ⟨K,hK,hseven,hkt,bound⟩
