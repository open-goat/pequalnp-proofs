import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8935_1
    (hBicliqueExtract :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        ¬G.IsAcyclic →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ¬PEqualNP.TopForm.BelowF G C j ∧
          ∃ (u1 v1 u2 v2 : Fin n),
            G.Adj u1 v1 ∧ G.Adj u2 v2 ∧ s(u1, v1) ≠ s(u2, v2) ∧
            PEqualNP.ReadK.readsAtMost C n [↑u1, ↑v1] (1 : ℕ) = Bool.false ∧
            PEqualNP.ReadK.readsAtMost C n [↑u2, ↑v2] (1 : ℕ) = Bool.false ∧
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u1 v1) = Bool.true ∧
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u2 v2) = Bool.true) →
        ∃ (k : ℕ) (A B : Fin k → Finset (Fin n)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ u ∈ A i, ∀ v ∈ B i, G.Adj u v) ∧
          (∀ u v, G.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) ∧
          ∑ i : Fin k, ((A i).card + (B i).card) ≤ C.size + (1 : ℕ))
    (hC4BicliqueStar :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A B : Finset (Fin n)),
        PEqualNP.TopForm.NoFourCycle G →
        A.Nonempty →
        B.Nonempty →
        (∀ u ∈ A, ∀ v ∈ B, G.Adj u v) →
        A.card = (1 : ℕ) ∨ B.card = (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro n G _ C hBip hCyc hC4 hLeast hTop hWit
  obtain ⟨k, A, B, hNE, hAdj, hCov, hCost⟩ :=
    hBicliqueExtract n G C hBip hCyc hC4 hLeast hTop hWit
  have hStar : ∀ i : Fin k, (A i).card = 1 ∨ (B i).card = 1 :=
    fun i => hC4BicliqueStar n G (A i) (B i) hC4 (hNE i).1 (hNE i).2 (hAdj i)
  let c : Fin k → Fin n := fun i =>
    if (A i).card = 1 then (hNE i).1.choose else (hNE i).2.choose
  have hcCov : ∀ (i : Fin k) {u v : Fin n}, u ∈ A i → v ∈ B i → c i = u ∨ c i = v := by
    intro i u v hu hv
    by_cases hA : (A i).card = 1
    · left
      have hmem : (hNE i).1.choose ∈ A i := (hNE i).1.choose_spec
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hA
      have h1 : (hNE i).1.choose = a := Finset.mem_singleton.mp (ha ▸ hmem)
      have h2 : u = a := Finset.mem_singleton.mp (ha ▸ hu)
      simp only [c, hA, ↓reduceIte]
      exact h1.trans h2.symm
    · right
      have hB : (B i).card = 1 := (hStar i).resolve_left hA
      have hmem : (hNE i).2.choose ∈ B i := (hNE i).2.choose_spec
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hB
      have h1 : (hNE i).2.choose = b := Finset.mem_singleton.mp (hb ▸ hmem)
      have h2 : v = b := Finset.mem_singleton.mp (hb ▸ hv)
      simp only [c, hA, ↓reduceIte]
      exact h1.trans h2.symm
  let V : Finset (Fin n) := Finset.univ.image c
  have hVC : G.IsVertexCover (V : Set (Fin n)) := by
    intro u v huv
    obtain ⟨i, h1 | h2⟩ := hCov u v huv
    · rcases hcCov i h1.1 h1.2 with rfl | rfl
      · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_univ i)))
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_univ i)))
    · rcases hcCov i h2.1 h2.2 with rfl | rfl
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_univ i)))
      · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_univ i)))
  have hVCard : V.card ≤ k := by
    calc
      V.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  let E : Fin k → Finset (Sym2 (Fin n)) := fun i =>
    (A i ×ˢ B i).image (fun p => s(p.1, p.2))
  have hESub : G.edgeFinset ⊆ Finset.univ.biUnion E := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨i, h1 | h2⟩ := hCov u v huv
      · refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
        exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr h1, rfl⟩
      · refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
        exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr h2, Sym2.eq_swap⟩
  have hECardI : ∀ i : Fin k, (E i).card + 1 ≤ (A i).card + (B i).card := by
    intro i
    have h1 : (E i).card ≤ (A i).card * (B i).card := by
      calc
        (E i).card ≤ (A i ×ˢ B i).card := Finset.card_image_le
        _ = (A i).card * (B i).card := Finset.card_product (A i) (B i)
    rcases hStar i with hA | hB
    · rw [hA] at h1 ⊢
      omega
    · rw [hB] at h1 ⊢
      omega
  have hECard : G.edgeFinset.card ≤ ∑ i : Fin k, (E i).card :=
    (Finset.card_le_card hESub).trans Finset.card_biUnion_le
  have hSumLe : ∑ i : Fin k, ((E i).card + 1) ≤ ∑ i : Fin k, ((A i).card + (B i).card) :=
    Finset.sum_le_sum (fun i _ => hECardI i)
  have hSumSplit : ∑ i : Fin k, ((E i).card + 1) = (∑ i : Fin k, (E i).card) + k := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
  refine ⟨V, hVC, ?_⟩
  omega
