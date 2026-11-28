import PEqualNP.Defs

-- The circuit realization uses the wire lemmas from PR 37076.
-- The bounds for one read on a side use PR 8785. The two-read bound uses L-meta-4344.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_9134_766
    (normalize :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        0 < n → (∀ l, Fintype.card {p : Fin n // I p l} = q + 1) →
        ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
          o < n + n + s →
          (∀ i : Fin n, W i.val = {z | z.1 i = true} ∧ W (n + i.val) = {z | z.2 i = true}) →
          (∀ j < s, ∃ a < n + n + j, ∃ b < n + n + j,
            W (n + n + j) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
          (∀ p l, I p l → ((fun i => decide (i = p)), (fun i => decide (i = l))) ∈ W o) →
          (∀ Y : Fin n → Bool, Fintype.card {l // Y l = true} ≤ q →
            ((fun p => decide (¬ ∃ l, I p l ∧ Y l = true)), Y) ∉ W o) →
          ∃ C : Circuit, C.size ≤ s ∧ (IsAO2 (n + n) C ∧
      (∀ p l, I p l → circuitFun (n + n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) ∧
      (∀ z : Fin (n + n) → Bool, Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
        circuitFun (n + n) C z = false)))
    (countOne :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
        2 ≤ q → n = q ^ 2 + q + 1 → (∀ l, Fintype.card {p : Fin n // I p l} = q + 1) → (∀ (p r : Fin n), p ≠ r → ∃! l : Fin n, I p l ∧ I r l) →
        IsAO2 (n + n) C → (∀ z : Fin (n + n) → Bool, Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
        circuitFun (n + n) C z = false) →
        Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧ (lineSingle C (n + n) (fun i => decide (n ≤ i)) e.1.val (n + e.2.val) = true ∨ lineSingle C (n + n) (fun i => decide (i < n)) e.1.val (n + e.2.val) = true)} ≤ 14 * C.size + n)
    (countTwo :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
        2 ≤ q → (∀ (p r : Fin n), p ≠ r → ∃! l : Fin n, I p l ∧ I r l) → IsAO2 (n + n) C → (∀ z : Fin (n + n) → Bool, Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
        circuitFun (n + n) C z = false) →
        Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧ ([2, 2] ∈ (readVectors C (n + n) [e.1.val, n + e.2.val] 2).getD C.output [])} ≤ 34 * C.size)
    (expose :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        299 ≤ q → n = q ^ 2 + q + 1 → (∀ l, Fintype.card {p : Fin n // I p l} = q + 1) → (∀ (p r : Fin n), p ≠ r → ∃! l : Fin n, I p l ∧ I r l) →
        let Good := fun C : Circuit => (IsAO2 (n + n) C ∧
      (∀ p l, I p l → circuitFun (n + n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) ∧
      (∀ z : Fin (n + n) → Bool, Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
        circuitFun (n + n) C z = false))
        ∀ C : Circuit, Good C → (∀ D, Good D → C.size ≤ D.size) →
          100 * C.size < n * (q + 1) →
          ∃ D : Circuit, Good D ∧ D.size ≤ C.size ∧
            n * (q + 1) ≤ 2 * (Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧ (lineSingle D (n + n) (fun i => decide (n ≤ i)) e.1.val (n + e.2.val) = true ∨ lineSingle D (n + n) (fun i => decide (i < n)) e.1.val (n + e.2.val) = true ∨ [2, 2] ∈ (readVectors D (n + n) [e.1.val, n + e.2.val] 2).getD D.output [])})) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (100 : ℕ) * x13.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11 := by
  intro q n I inst U singleton hq hn hdeg huniq s o M W ho hin hsteps hpos hneg _
  have hgate : ∀ j < s, ∃ a < n + n + j, ∃ b < n + n + j,
      W (n + n + j) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b] := by
    intro j hj
    obtain ⟨a, ha, b, hb, he⟩ := hsteps j hj
    refine ⟨a, ha, b, hb, ?_⟩
    dsimp only at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with h | ⟨h, _⟩
    · rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨C, hs, hC⟩ := normalize q n I (by omega) hdeg s o W ho hin hgate hpos hneg
  by_contra hc
  let Good : Circuit → Prop := fun C => (IsAO2 (n + n) C ∧
      (∀ p l, I p l → circuitFun (n + n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) ∧
      (∀ z : Fin (n + n) → Bool, Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
        circuitFun (n + n) C z = false))
  have he : ∃ k, ∃ D : Circuit, D.size = k ∧ Good D := ⟨C.size, C, rfl, hC⟩
  classical
  obtain ⟨A, hA, hGA⟩ := Nat.find_spec he
  have hmin (B : Circuit) (hB : Good B) : A.size ≤ B.size := by
    rw [hA]
    exact Nat.find_min' he ⟨B, rfl, hB⟩
  have hAs : A.size ≤ s := (hmin C hC).trans hs
  have hsmall : 100 * A.size < n * (q + 1) := by omega
  obtain ⟨D, hD, hDA, hex⟩ := expose q n I hq hn hdeg huniq A hGA hmin hsmall
  let U : Finset (Fin n × Fin n) := ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => I e.1 e.2 ∧ (lineSingle D (n + n) (fun i => decide (n ≤ i)) e.1.val (n + e.2.val) = true ∨
        lineSingle D (n + n) (fun i => decide (i < n)) e.1.val (n + e.2.val) = true)))
  let V : Finset (Fin n × Fin n) := ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => I e.1 e.2 ∧ ([2, 2] ∈ (readVectors D (n + n) [e.1.val, n + e.2.val] 2).getD D.output [])))
  simp only [Fintype.card_subtype] at hex
  have hU : U.card ≤ 14 * D.size + n := by
    simpa only [Fintype.card_subtype] using countOne q n I D (by omega) hn hdeg huniq hD.1 hD.2.2
  have hV : V.card ≤ 34 * D.size := by
    simpa only [Fintype.card_subtype] using countTwo q n I D (by omega) huniq hD.1 hD.2.2
  have hall : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => I e.1 e.2 ∧ (lineSingle D (n + n) (fun i => decide (n ≤ i)) e.1.val (n + e.2.val) = true ∨
        lineSingle D (n + n) (fun i => decide (i < n)) e.1.val (n + e.2.val) = true ∨
        [2, 2] ∈ (readVectors D (n + n) [e.1.val, n + e.2.val] 2).getD D.output []))).card ≤ (U ∪ V).card := by
    apply Finset.card_le_card
    intro e he
    obtain ⟨hI, hL | hP | hT⟩ := (Finset.mem_filter.mp he).2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, Or.inl hL⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, Or.inr hP⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hT⟩)
  have hu := Finset.card_union_le U V
  have hnq := Nat.mul_le_mul_left n (show 300 ≤ q + 1 by omega)
  rw [Nat.mul_comm n 300] at hnq
  omega
