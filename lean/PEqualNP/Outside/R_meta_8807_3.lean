import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8807_3
    (h1 : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (n+n) C →
      (∀ p r, p ≠ r → ∀ l k, p ∈ S l → r ∈ S l → p ∈ S k → r ∈ S k → l = k) →
      ∀ (b : Bool) (U : Fin n → Finset (Fin n)), (∀ l k, U l ⊆ U k ∨ U k ⊆ U l) →
      ∀ E : Finset (Fin n × Fin n),
      let v := fun (l : Fin n) (X : Finset (Fin n)) => PEqualNP.CircuitLowerBounds.wireValue C
        (if b then PEqualNP.GenericRejection.incidenceInput X (U l) else PEqualNP.GenericRejection.incidenceInput (U l) X)
      (∀ e ∈ E, ∃ w, v e.2 (S e.2)ᶜ w = false ∧ v e.2 {e.1} w = true ∧ ∃ t < e.1, v e.2 {t} w = true) →
      E.card ≤ C.size)
    (h2 : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → PEqualNP.TopForm.IsAO2 (n+n) C →
      C.output < n+n+C.size → PEqualNP.GenericRejection.RightOnIncidentPairs S C →
      (∀ l, C.eval (PEqualNP.GenericRejection.incidenceInput (S l)ᶜ {l}) = false) →
      (∀ p : Fin n, C.eval (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin n))) = false) →
      ∀ E : Finset (Fin n × Fin n),
      let v := fun (X Y : Finset (Fin n)) => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y)
      let miss := fun (l : Fin n) => v (S l)ᶜ {l}
      let hard := fun (e : Fin n × Fin n) => ∃ j < C.size, let w := n+n+j
        v {e.1} {e.2} w = true ∧ ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          v {e.1} ∅ a = false ∧ ¬∀ l, miss l a = true → miss l w = true
      (∀ e ∈ E, e.1 ∈ S e.2 ∧ ¬hard e) → E.card ≤ 3*C.size+n)
    (h3 : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let v := fun (X Y : Finset (Fin n)) => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y)
      let miss := fun (l : Fin n) => v (S l)ᶜ {l}
      let hard := fun (e : Fin n × Fin n) => ∃ j < C.size, let w := n+n+j
        v {e.1} {e.2} w = true ∧ ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          v {e.1} ∅ a = false ∧ ¬∀ l, miss l a = true → miss l w = true
      300 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → PEqualNP.TopForm.IsAO2 (n+n) C →
      C.output < n+n+C.size → PEqualNP.GenericRejection.RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S X Y → C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false) →
      ∃ U V : Fin n → Finset (Fin n), (∀ l k, U l ⊆ U k ∨ U k ⊆ U l) ∧
      (∀ p r, V p ⊆ V r ∨ V r ⊆ V p) ∧ ∀ E : Finset (Fin n × Fin n),
      (∀ e ∈ E, let B := U e.2; let D := V e.1; e.1 ∈ S e.2 ∧ hard e ∧
        (∀ w, v (S e.2)ᶜ B w = false → v {e.1} B w = true → ∀ r < e.1, v {r} B w = false) ∧
        (∀ w, v D (Finset.univ.filter (fun l => e.1 ∈ S l))ᶜ w = false →
          v D {e.2} w = true → ∀ t < e.2, v D {t} w = false)) → E.card ≤ 95*C.size) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →                 (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →                   (∃ x13 < x4.size,                       (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                         ∃ (x14 : Finset (Fin x2)),                           (100 : ℕ) < x14.card ∧                             have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};                             Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →                     x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C hq hn hsize join ao hout right reject _
  obtain ⟨U,V,cu,cv,rem⟩ := h3 q n S C hq hn hsize join ao hout right reject
  let v := fun (X Y : Finset (Fin n)) => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y)
  let miss := fun (l : Fin n) => v (S l)ᶜ {l}
  let hard := fun (e : Fin n × Fin n) => ∃ j < C.size, let w := n+n+j
    v {e.1} {e.2} w = true ∧ ∀ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      v {e.1} ∅ a = false ∧ ¬∀ l, miss l a = true → miss l w = true
  let T (p : Fin n) := Finset.univ.filter fun l => p ∈ S l
  let P (e : Fin n × Fin n) := let B := U e.2; ∃ w, v (S e.2)ᶜ B w = false ∧ v {e.1} B w = true ∧ ∃ r < e.1, v {r} B w = true
  let L (e : Fin n × Fin n) := let D := V e.1; ∃ w, v D (T e.1)ᶜ w = false ∧ v D {e.2} w = true ∧ ∃ t < e.2, v D {t} w = true
  let F := Finset.univ.biUnion fun l : Fin n => (S l).image fun p => (p,l)
  have flags (e : Fin n × Fin n) : e ∈ F ↔ e.1 ∈ S e.2 := by cases e; simp [F]
  have count : F.card = n*(q+1) := by
    dsimp only [F]
    rw [Finset.card_biUnion]
    · have inj (l : Fin n) : Function.Injective (fun p : Fin n => (p,l)) := fun _ _ h => congrArg Prod.fst h
      simp [Finset.card_image_of_injective _ (inj _),hsize]
    · intro i _ j _ ne
      apply Finset.disjoint_left.mpr
      intro x h k
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨r,_,eq⟩ := Finset.mem_image.mp k
      exact ne (congrArg Prod.snd eq).symm
  let A := F.filter P
  let G := F \ A
  let H := G.filter L
  let R := G \ H
  have ca : A.card ≤ C.size := h1 n S C ao (fun p r ne _ _ a b c d => (join p r ne).unique ⟨a,b⟩ ⟨c,d⟩)
    true U cu A (fun _ h => (Finset.mem_filter.mp h).2)
  have du (i j : Fin n) (ne : i ≠ j) (p r : Fin n) (a : i ∈ T p) (b : j ∈ T p)
      (c : i ∈ T r) (d : j ∈ T r) : p = r := by
    by_contra nr
    apply ne
    exact (join p r nr).unique ⟨(Finset.mem_filter.mp a).2,(Finset.mem_filter.mp c).2⟩
      ⟨(Finset.mem_filter.mp b).2,(Finset.mem_filter.mp d).2⟩
  have ch := h1 n T C ao du false V cv (H.image Prod.swap) (by
    intro e h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp ha).2)
  rw [Finset.card_image_of_injective _ Prod.swap_injective] at ch
  have cr : R.card ≤ 98*C.size+n := by
    let M := R.filter hard
    let Q := R.filter (fun e => ¬hard e)
    have cheap : Q.card ≤ 3*C.size+n := by
      apply h2 n S C join ao hout right
      · intro l
        apply reject
        · simp; omega
        · intro k hk
          obtain rfl := Finset.mem_singleton.mp hk
          exact disjoint_compl_right
      · intro p
        apply reject
        · simp
        · intro k hk; simp at hk
      · intro e he
        obtain ⟨r,g⟩ := Finset.mem_filter.mp he
        exact ⟨(flags e).mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp r).1).1,g⟩
    have cost : M.card ≤ 95*C.size := by
      apply rem
      intro e hm
      obtain ⟨hr,harder⟩ := Finset.mem_filter.mp hm
      obtain ⟨hg,nh⟩ := Finset.mem_sdiff.mp hr
      obtain ⟨hf,na⟩ := Finset.mem_sdiff.mp hg
      refine ⟨(flags _).mp hf,harder, ?_, ?_⟩
      · intro w cold hot r lt
        cases h : v {r} (U e.2) w with
        | false => exact h
        | true => exact (na (Finset.mem_filter.mpr ⟨hf,w,cold,hot,r,lt,h⟩)).elim
      · intro w cold hot r lt
        cases h : v (V e.1) {r} w with
        | false => exact h
        | true => exact (nh (Finset.mem_filter.mpr ⟨hg,w,cold,hot,r,lt,h⟩)).elim
    have size : M.card + Q.card = R.card := Finset.card_filter_add_card_filter_not _
    omega
  have top : G.card + A.card = F.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
  have mid : R.card + H.card = G.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
  rw [Nat.mul_add,Nat.mul_one] at count
  omega
