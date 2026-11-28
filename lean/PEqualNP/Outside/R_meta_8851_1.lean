import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8851_1
    (hInputChild :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (X : Finset (Finset (Fin N) × Finset (Fin N))) (g a b : ℕ) (S : Finset (Fin N)),
        have f : Finset (Fin N) → Finset (Fin N) → List Bool := PEqualNP.GenericRejection.incidenceInput;
        have w : ℕ → Finset (Fin N) → Finset (Fin N) → Bool := fun u A B => PEqualNP.CircuitLowerBounds.wireValue C (f A B) u;
        have pts : Fin N → Finset (Fin N) := fun l => (L l).filter fun p => w (N + N + g) {p} {l} = Bool.true;
        (100 : ℕ) < q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        C.output < N + N + C.size →
        (∀ z ∈ X, q < z.2.card ∧ PEqualNP.GenericRejection.IsFalseInput L z.1 z.2) →
        (∀ z1 ∈ X, ∀ z2 ∈ X, z2.1 ⊆ z1.1 → z2.2 ⊆ z1.2 → z2 = z1) →
        (∀ A B : Finset (Fin N), C.eval (f A B) = Bool.true ↔
          PEqualNP.GenericRejection.incidenceFun L A B = Bool.true ∨ ∃ z ∈ X, z.1 ⊆ A ∧ z.2 ⊆ B) →
        g < C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] →
        a < N + N + g →
        b < N + N + g →
        (a < N + N ∨ b < N + N) →
        (100 : ℕ) < S.card →
        Set.InjOn pts ↑S →
        (∀ l ∈ S, (1 : ℕ) < (pts l).card ∧ w (N + N + g) (L l)ᶜ {l} = Bool.false) →
        N * q ≤ (100 : ℕ) * C.size)
    (hGateChildren :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (X : Finset (Finset (Fin N) × Finset (Fin N))) (g a b : ℕ) (S : Finset (Fin N)),
        have f : Finset (Fin N) → Finset (Fin N) → List Bool := PEqualNP.GenericRejection.incidenceInput;
        have w : ℕ → Finset (Fin N) → Finset (Fin N) → Bool := fun u A B => PEqualNP.CircuitLowerBounds.wireValue C (f A B) u;
        have pts : Fin N → Finset (Fin N) := fun l => (L l).filter fun p => w (N + N + g) {p} {l} = Bool.true;
        (100 : ℕ) < q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        C.output < N + N + C.size →
        (∀ z ∈ X, q < z.2.card ∧ PEqualNP.GenericRejection.IsFalseInput L z.1 z.2) →
        (∀ z1 ∈ X, ∀ z2 ∈ X, z2.1 ⊆ z1.1 → z2.2 ⊆ z1.2 → z2 = z1) →
        (∀ A B : Finset (Fin N), C.eval (f A B) = Bool.true ↔
          PEqualNP.GenericRejection.incidenceFun L A B = Bool.true ∨ ∃ z ∈ X, z.1 ⊆ A ∧ z.2 ⊆ B) →
        g < C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] →
        N + N ≤ a →
        a < N + N + g →
        N + N ≤ b →
        b < N + N + g →
        (100 : ℕ) < S.card →
        Set.InjOn pts ↑S →
        (∀ l ∈ S, (1 : ℕ) < (pts l).card ∧ w (N + N + g) (L l)ᶜ {l} = Bool.false) →
        N * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Finset (Fin x2) × Finset (Fin x2))),   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               (∀ x12 ∈ x5, x1 < x12.2.card ∧ PEqualNP.GenericRejection.IsFalseInput x3 x12.1 x12.2) →                 (∀ x13 ∈ x5, ∀ x15 ∈ x5, x15.1 ⊆ x13.1 → x15.2 ⊆ x13.2 → x15 = x13) →                   (∀ (x14 x15 : Finset (Fin x2)), x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.true ↔ PEqualNP.GenericRejection.incidenceFun x3 x14 x15 = Bool.true ∨ ∃ x16 ∈ x5, x16.1 ⊆ x14 ∧ x16.2 ⊆ x15) →                     (∃ x15 < x4.size,                         (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                           ∃ (x16 : Finset (Fin x2)),                             (100 : ℕ) < x16.card ∧                               have x17 : Fin x2 → Finset (Fin x2) := fun (x17 : Fin x2) => {x18 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x18} {x17}) (x2 + x2 + x15) = Bool.true};                               Set.InjOn x17 ↑x16 ∧ ∀ x18 ∈ x16, (1 : ℕ) < (x17 x18).card ∧ x17 x18 ⊆ x3 x18 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x18)ᶜ {x18}) (x2 + x2 + x15) = Bool.false) →                       x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N L C X hq hN hLcard hProj hAO hout hXfalse hXanti hEval hWit
  obtain ⟨g, hglt, hgop, S, hScard, hInj, hSprop⟩ := hWit
  have hgmem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
    change C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hglt]
    exact List.getElem_mem hglt
  have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := hAO.2.2 _ hgmem
  cases hinp : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs with
  | nil => rw [hinp] at hlen2; simp at hlen2
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen2; simp at hlen2
    | cons b tail =>
      cases tail with
      | cons _ _ => rw [hinp] at hlen2; simp at hlen2
      | nil =>
        have ha_lt : a < N + N + g := hAO.2.1 g hglt a (by rw [hinp]; simp)
        have hb_lt : b < N + N + g := hAO.2.1 g hglt b (by rw [hinp]; simp)
        have hpts_eq : ∀ l ∈ S,
            (L l).filter (fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true) =
            Finset.univ.filter (fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true) := by
          intro l hl
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro hp
            exact ⟨(hSprop l hl).2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩), hp⟩
        have hInj' : Set.InjOn (fun l => (L l).filter fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true) ↑S := by
          intro l1 hl1 l2 hl2 heq
          dsimp only at heq
          rw [hpts_eq l1 hl1, hpts_eq l2 hl2] at heq
          exact hInj hl1 hl2 heq
        have hSprop' : ∀ l ∈ S,
            (1 : ℕ) < ((L l).filter fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true).card ∧
            PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput (L l)ᶜ {l}) (N + N + g) = Bool.false := by
          intro l hl
          rw [hpts_eq l hl]
          exact ⟨(hSprop l hl).1, (hSprop l hl).2.2⟩
        by_cases hIn : a < N + N ∨ b < N + N
        · exact hInputChild q N L C X g a b S hq hN hLcard hProj hAO hout hXfalse hXanti hEval hglt hgop hinp ha_lt hb_lt hIn hScard hInj' hSprop'
        · push Not at hIn
          exact hGateChildren q N L C X g a b S hq hN hLcard hProj hAO hout hXfalse hXanti hEval hglt hgop hinp hIn.1 ha_lt hIn.2 hb_lt hScard hInj' hSprop'
