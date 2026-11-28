import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53160

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

-- ============================================================================
-- Helper decidability and input definitions
-- ============================================================================

private def decEqGateOp : DecidableEq GateOp
  | .and, .and => isTrue rfl
  | .or, .or => isTrue rfl
  | .not, .not => isTrue rfl
  | .mod m, .mod n =>
    if h : m = n then isTrue (by rw [h]) else isFalse (fun h' => h (GateOp.mod.inj h'))
  | .maj, .maj => isTrue rfl
  | .and, .or | .and, .not | .and, .mod _ | .and, .maj
  | .or, .and | .or, .not | .or, .mod _ | .or, .maj
  | .not, .and | .not, .or | .not, .mod _ | .not, .maj
  | .mod _, .and | .mod _, .or | .mod _, .not | .mod _, .maj
  | .maj, .and | .maj, .or | .maj, .not | .maj, .mod _ => isFalse (fun h => by cases h)

private instance : DecidableEq GateOp := decEqGateOp

private noncomputable def mkInput (n : Nat) (k : Fin (n + 1)) : List Bool :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  List.ofFn (fun i : Fin n => decide (i.val < k.val)) ++ [false, true]

private lemma mkInput_length (n : Nat) (k : Fin (n + 1)) :
    (mkInput n k).length = n + 2 := by
  unfold mkInput; simp

private lemma mkInput_getD_lt (n : Nat) (k : Fin (n + 1)) (i : Nat) (hi : i < n) :
    (mkInput n k).getD i false = decide (i < k.val) := by
  unfold mkInput
  have hlen : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j.val < k.val))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hi),
      List.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  by_cases h : i < k.val <;> simp [h]

private lemma mkInput_getD_false (n : Nat) (k : Fin (n + 1)) :
    (mkInput n k).getD n false = false := by
  unfold mkInput
  have hlen : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j.val < k.val))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

private lemma mkInput_getD_true (n : Nat) (k : Fin (n + 1)) :
    (mkInput n k).getD (n + 1) false = true := by
  unfold mkInput
  have hlen : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j.val < k.val))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen]
  have hsub : n + 1 - n = 1 := by omega
  rw [hsub]; rfl

-- ============================================================================
-- Circuit wires step lemmas and monotone chain convexity for NOT vectors
-- ============================================================================

private lemma wires_length_aux (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma wires_getD_lt_aux (gs : List Gate) (acc : List Bool) (w : Nat) (hw : w < acc.length) :
    (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).getD w false =
      acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]

private lemma wires_getD_input (C : Circuit) (inp : List Bool) (w : Nat) (hw : w < inp.length) :
    (C.wires inp).getD w false = inp.getD w false :=
  wires_getD_lt_aux C.gates inp w hw

private lemma wires_getD_gate {M : Nat} (C : Circuit) (hRB : ReadsBack M C) (inp : List Bool)
    (hinp : inp.length = M) (j : Nat) (hj : j < C.gates.length) :
    (C.wires inp).getD (M + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires inp).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1; exact h1
  let stepFn : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let pre := (C.gates.take j).foldl stepFn inp
  have hpre_len : pre.length = M + j := by
    rw [wires_length_aux, hinp, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hw_eq : C.wires inp =
      (C.gates.drop (j + 1)).foldl stepFn
        (pre ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => pre.getD i false)]) := by
    change C.gates.foldl stepFn inp = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  have hget_j : (C.wires inp).getD (M + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pre.getD i false) := by
    rw [hw_eq, wires_getD_lt_aux _ _ _ (by rw [List.length_append, hpre_len]; simp)]
    rw [← hpre_len, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]; rfl
  rw [hget_j]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < M + j := hRB j hj i (by rwa [hgate])
  symm
  rw [hw_eq, wires_getD_lt_aux _ _ _ (by rw [List.length_append, hpre_len]; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]

private def notIdxs (C : Circuit) : List Nat :=
  (List.range C.size).filter (fun idx => decide ((gateAt C idx).op = GateOp.not))

private lemma length_filter_range_eq_list_filter (gs : List Gate) (p : Gate → Bool) :
    ((List.range gs.length).filter (fun idx => p (gs.getD idx ⟨GateOp.or, []⟩))).length =
      (gs.filter p).length := by
  have hmap : gs = (List.range gs.length).map (fun idx => gs.getD idx ⟨GateOp.or, []⟩) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 _
      simp [List.getD_eq_getElem?_getD, hi1]
  conv_rhs => rw [hmap]
  rw [List.filter_map, List.length_map]
  rfl

private lemma notIdxs_length (C : Circuit) : (notIdxs C).length = notCount C := by
  unfold notIdxs notCount gateAt Circuit.size
  rw [length_filter_range_eq_list_filter C.gates (fun g => decide (g.op = GateOp.not))]
  congr 1
  apply List.filter_congr
  intro g _
  exact decide_eq_decide.mpr Iff.rfl

private lemma mem_notIdxs_iff (C : Circuit) (idx : Nat) :
    idx ∈ notIdxs C ↔ idx < C.gates.length ∧ (gateAt C idx).op = GateOp.not := by
  unfold notIdxs Circuit.size
  simp [List.mem_filter, List.mem_range]

private def listLe (l1 l2 : List Bool) : Prop :=
  l1.length = l2.length ∧ ∀ i, i < l1.length → l1.getD i false = true → l2.getD i false = true

private lemma mkInput_listLe {n : Nat} {k1 k2 : Fin (n + 1)} (h : k1 ≤ k2) :
    listLe (mkInput n k1) (mkInput n k2) := by
  refine ⟨by rw [mkInput_length, mkInput_length], ?_⟩
  intro i hi ht
  rw [mkInput_length] at hi
  by_cases hin : i < n
  · rw [mkInput_getD_lt n k1 i hin] at ht
    rw [mkInput_getD_lt n k2 i hin]
    have h1 : i < k1.val := by simpa using ht
    have h2 : k1.val ≤ k2.val := h
    simp; omega
  · have : i = n ∨ i = n + 1 := by omega
    rcases this with rfl | rfl
    · rw [mkInput_getD_false] at ht; cases ht
    · rw [mkInput_getD_true]

private def notVec (C : Circuit) (M : Nat) (inp : List Bool) : Fin (notIdxs C).length → Bool :=
  fun j => (C.wires inp).getD (M + (notIdxs C)[j]) false

private lemma wires_mono_of_notVec_eq {M : Nat} (C : Circuit) (hF2 : FanInTwo C) (hRB : ReadsBack M C)
    (inp1 inp2 : List Bool) (h1 : inp1.length = M) (h2 : inp2.length = M)
    (hle : listLe inp1 inp2) (hnv : notVec C M inp1 = notVec C M inp2) :
    ∀ w, w < M + C.size → (C.wires inp1).getD w false = true → (C.wires inp2).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwM : w < M
    · rw [wires_getD_input C _ w (by omega)] at htrue ⊢
      exact hle.2 w (by omega) htrue
    · have hidx : w - M < C.gates.length := by unfold Circuit.size at hw; omega
      have hmem_g : gateAt C (w - M) ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem?_getD, hidx, getElem?_pos, Option.getD_some]
        exact List.getElem_mem hidx
      have hop := (hF2 _ hmem_g).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have hw_eq : w = M + (w - M) := by omega
      rcases hop with hand | hor | hnot
      · rw [hw_eq, wires_getD_gate C hRB inp1 h1 (w - M) hidx, hand] at htrue
        rw [hw_eq, wires_getD_gate C hRB inp2 h2 (w - M) hidx, hand]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] at htrue ⊢
        intro a ha
        have halt : a < w := by have := hRB (w - M) hidx a ha; omega
        exact ih a halt (by omega) (htrue a ha)
      · rw [hw_eq, wires_getD_gate C hRB inp1 h1 (w - M) hidx, hor] at htrue
        rw [hw_eq, wires_getD_gate C hRB inp2 h2 (w - M) hidx, hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrue ⊢
        rcases htrue with ⟨_, ⟨a, ha, rfl⟩, hat⟩
        have halt : a < w := by have := hRB (w - M) hidx a ha; omega
        exact ⟨true, ⟨a, ha, ih a halt (by omega) hat⟩, rfl⟩
      · have hmem : w - M ∈ notIdxs C := (mem_notIdxs_iff C (w - M)).mpr ⟨hidx, hnot⟩
        rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hjeq⟩
        have hnvj := congrFun hnv ⟨j, hj⟩
        simp only [notVec, Fin.getElem_fin, hjeq, ← hw_eq] at hnvj
        rwa [← hnvj]

private lemma wires_sandwich_and_notVec_eq {M : Nat} (C : Circuit) (hF2 : FanInTwo C)
    (hRB : ReadsBack M C) (inp1 inp2 inp3 : List Bool)
    (h1 : inp1.length = M) (h2 : inp2.length = M) (h3 : inp3.length = M)
    (h12 : listLe inp1 inp2) (h23 : listLe inp2 inp3)
    (hnv13 : notVec C M inp1 = notVec C M inp3) :
    (∀ w, w < M + C.size →
      ((C.wires inp1).getD w false = true → (C.wires inp2).getD w false = true) ∧
      ((C.wires inp2).getD w false = true → (C.wires inp3).getD w false = true)) ∧
    notVec C M inp2 = notVec C M inp1 := by
  have hmain : ∀ w, w < M + C.size →
      ((C.wires inp1).getD w false = true → (C.wires inp2).getD w false = true) ∧
      ((C.wires inp2).getD w false = true → (C.wires inp3).getD w false = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwM : w < M
      · constructor
        · intro ht
          rw [wires_getD_input C _ w (by omega)] at ht ⊢
          exact h12.2 w (by omega) ht
        · intro ht
          rw [wires_getD_input C _ w (by omega)] at ht ⊢
          exact h23.2 w (by omega) ht
      · have hidx : w - M < C.gates.length := by unfold Circuit.size at hw; omega
        have hmem_g : gateAt C (w - M) ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem?_getD, hidx, getElem?_pos, Option.getD_some]
          exact List.getElem_mem hidx
        have hop := (hF2 _ hmem_g).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hw_eq : w = M + (w - M) := by omega
        rcases hop with hand | hor | hnot
        · constructor
          · intro ht
            rw [hw_eq, wires_getD_gate C hRB inp1 h1 (w - M) hidx, hand] at ht
            rw [hw_eq, wires_getD_gate C hRB inp2 h2 (w - M) hidx, hand]
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
              and_imp, forall_apply_eq_imp_iff₂] at ht ⊢
            intro a ha
            have halt : a < w := by have := hRB (w - M) hidx a ha; omega
            exact (ih a halt (by omega)).1 (ht a ha)
          · intro ht
            rw [hw_eq, wires_getD_gate C hRB inp2 h2 (w - M) hidx, hand] at ht
            rw [hw_eq, wires_getD_gate C hRB inp3 h3 (w - M) hidx, hand]
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
              and_imp, forall_apply_eq_imp_iff₂] at ht ⊢
            intro a ha
            have halt : a < w := by have := hRB (w - M) hidx a ha; omega
            exact (ih a halt (by omega)).2 (ht a ha)
        · constructor
          · intro ht
            rw [hw_eq, wires_getD_gate C hRB inp1 h1 (w - M) hidx, hor] at ht
            rw [hw_eq, wires_getD_gate C hRB inp2 h2 (w - M) hidx, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
            rcases ht with ⟨_, ⟨a, ha, rfl⟩, hat⟩
            have halt : a < w := by have := hRB (w - M) hidx a ha; omega
            exact ⟨true, ⟨a, ha, (ih a halt (by omega)).1 hat⟩, rfl⟩
          · intro ht
            rw [hw_eq, wires_getD_gate C hRB inp2 h2 (w - M) hidx, hor] at ht
            rw [hw_eq, wires_getD_gate C hRB inp3 h3 (w - M) hidx, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
            rcases ht with ⟨_, ⟨a, ha, rfl⟩, hat⟩
            have halt : a < w := by have := hRB (w - M) hidx a ha; omega
            exact ⟨true, ⟨a, ha, (ih a halt (by omega)).2 hat⟩, rfl⟩
        · have hmem : w - M ∈ notIdxs C := (mem_notIdxs_iff C (w - M)).mpr ⟨hidx, hnot⟩
          rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hjeq⟩
          have hnvj := congrFun hnv13 ⟨j, hj⟩
          simp only [notVec, Fin.getElem_fin, hjeq, ← hw_eq] at hnvj
          have heq12 : (C.wires inp1).getD w false = (C.wires inp2).getD w false := by
            rw [hw_eq,
                wires_getD_gate C hRB inp1 h1 (w - M) hidx,
                wires_getD_gate C hRB inp2 h2 (w - M) hidx]
            rw [hw_eq,
                wires_getD_gate C hRB inp1 h1 (w - M) hidx,
                wires_getD_gate C hRB inp3 h3 (w - M) hidx] at hnvj
            cases hg : (gateAt C (w - M)).inputs with
            | nil => rw [hnot]; rfl
            | cons u rest =>
              have hu : u < w := by have := hRB (w - M) hidx u (by rw [hg]; simp); omega
              rw [hnot, hg] at hnvj
              rw [hnot]
              simp only [GateOp.eval, List.map_cons, List.headD_cons] at hnvj ⊢
              have hu12 := (ih u hu (by omega)).1
              have hu23 := (ih u hu (by omega)).2
              cases h1u : (C.wires inp1).getD u false <;>
              cases h2u : (C.wires inp2).getD u false <;>
              cases h3u : (C.wires inp3).getD u false
              · rfl
              · rfl
              · rw [h2u, h3u] at hu23; cases hu23 rfl
              · rw [h1u, h3u] at hnvj; simp at hnvj
              · rw [h1u, h3u] at hnvj; simp at hnvj
              · rw [h1u, h2u] at hu12; cases hu12 rfl
              · rfl
              · rfl
          rw [← heq12, ← hnvj]
          exact ⟨id, id⟩
  refine ⟨hmain, ?_⟩
  funext j
  have hlt : (notIdxs C)[j] < C.gates.length := ((mem_notIdxs_iff C _).mp (List.getElem_mem j.isLt)).1
  have hm := hmain (M + (notIdxs C)[j]) (by unfold Circuit.size; omega)
  have heq13 := congrFun hnv13 j
  simp only [notVec] at heq13 ⊢
  cases h1v : (C.wires inp1).getD (M + (notIdxs C)[j]) false <;>
  cases h2v : (C.wires inp2).getD (M + (notIdxs C)[j]) false <;>
  cases h3v : (C.wires inp3).getD (M + (notIdxs C)[j]) false <;>
  simp_all

-- ============================================================================
-- Lower bound: from any valid circuit (C, a), extract cuts H and bad set Z
-- ============================================================================

private lemma lower_bound_cuts {n m b : Nat} (want : Fin (n + 1) → Fin m → Option Bool)
    (C : Circuit) (a : Fin m → Fin (n + 2 + C.size))
    (hF2 : FanInTwo C) (hRB : ReadsBack (n + 2) C) (hb : notCount C ≤ b) :
    ∃ H : Finset (Fin n), H.card ≤ 2 ^ b - 1 ∧
      ∀ (x y : Fin (n + 1)) (j : Fin m), x < y →
        want x j = some true → want y j = some false →
        (∃ (j' : Fin m) (v : Bool), want x j' = some v ∧ (C.wires (mkInput n x)).getD (a j').val false ≠ v) ∨
        (∃ (j' : Fin m) (v : Bool), want y j' = some v ∧ (C.wires (mkInput n y)).getD (a j').val false ≠ v) ∨
        ∃ i ∈ H, x.val ≤ i.val ∧ i.val < y.val := by
  let M := n + 2
  let nv : Fin (n + 1) → Fin (notIdxs C).length → Bool := fun k => notVec C M (mkInput n k)
  let H : Finset (Fin n) := Finset.univ.filter (fun i : Fin n =>
    nv ⟨i.val, by omega⟩ ≠ nv ⟨i.val + 1, by omega⟩)
  refine ⟨H, ?_, ?_⟩
  · -- H.card <= 2^b - 1
    have hinj : Set.InjOn (fun i : Fin n => nv ⟨i.val, by omega⟩) (H : Set (Fin n)) := by
      intro i1 hi1 i2 hi2 heq
      have h1' : nv ⟨i1.val, by omega⟩ ≠ nv ⟨i1.val + 1, by omega⟩ := (Finset.mem_filter.mp hi1).2
      have h2' : nv ⟨i2.val, by omega⟩ ≠ nv ⟨i2.val + 1, by omega⟩ := (Finset.mem_filter.mp hi2).2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
          (mkInput n ⟨i1.val, by omega⟩) (mkInput n ⟨i1.val + 1, by omega⟩) (mkInput n ⟨i2.val, by omega⟩)
          (mkInput_length n _) (mkInput_length n _) (mkInput_length n _)
          (mkInput_listLe (by show i1.val ≤ i1.val + 1; omega))
          (mkInput_listLe (by show i1.val + 1 ≤ i2.val; exact hlt))
          heq).2
        exact h1' hsw.symm
      · have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
          (mkInput n ⟨i2.val, by omega⟩) (mkInput n ⟨i2.val + 1, by omega⟩) (mkInput n ⟨i1.val, by omega⟩)
          (mkInput_length n _) (mkInput_length n _) (mkInput_length n _)
          (mkInput_listLe (by show i2.val ≤ i2.val + 1; omega))
          (mkInput_listLe (by show i2.val + 1 ≤ i1.val; exact hgt))
          heq.symm).2
        exact h2' hsw.symm
    let cLast := nv ⟨n, Nat.lt_succ_self n⟩
    have hne_last : ∀ i ∈ H, nv ⟨i.val, by omega⟩ ≠ cLast := by
      intro i hi heq
      have hi' : nv ⟨i.val, by omega⟩ ≠ nv ⟨i.val + 1, by omega⟩ := (Finset.mem_filter.mp hi).2
      have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
        (mkInput n ⟨i.val, by omega⟩) (mkInput n ⟨i.val + 1, by omega⟩) (mkInput n ⟨n, Nat.lt_succ_self n⟩)
        (mkInput_length n _) (mkInput_length n _) (mkInput_length n _)
        (mkInput_listLe (by show i.val ≤ i.val + 1; omega))
        (mkInput_listLe (by show i.val + 1 ≤ n; exact i.isLt))
        heq).2
      exact hi' hsw.symm
    have hsub : H.image (fun i : Fin n => nv ⟨i.val, by omega⟩) ⊆ Finset.univ.erase cLast := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
      exact Finset.mem_erase.mpr ⟨hne_last i hi, Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ] at hcard
    have hpow : 2 ^ (notIdxs C).length ≤ 2 ^ b := by
      rw [notIdxs_length]
      exact Nat.pow_le_pow_right (by omega) hb
    have hcard' : H.card ≤ 2 ^ (notIdxs C).length - 1 := by simpa using hcard
    omega
  · -- Cover condition
    intro x y j hxy hwx hwy
    by_cases hbadx : ∃ (j' : Fin m) (v : Bool), want x j' = some v ∧ (C.wires (mkInput n x)).getD (a j').val false ≠ v
    · exact Or.inl hbadx
    by_cases hbady : ∃ (j' : Fin m) (v : Bool), want y j' = some v ∧ (C.wires (mkInput n y)).getD (a j').val false ≠ v
    · exact Or.inr (Or.inl hbady)
    right; right
    by_contra hnocut
    -- Every step t in [x.val, y.val) satisfies nv(t) = nv(t+1), hence nv x = nv y!
    have hnv_eq : ∀ d : Nat, ∀ hd : x.val + d ≤ y.val, nv ⟨x.val + d, by omega⟩ = nv x := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        have hstep_not : ⟨x.val + d, by omega⟩ ∉ H := by
          intro hmem
          exact hnocut ⟨⟨x.val + d, by omega⟩, hmem, by simp, by simp; omega⟩
        have heq_step : nv ⟨x.val + d, by omega⟩ = nv ⟨x.val + d + 1, by omega⟩ := by
          by_contra hne
          exact hstep_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        exact heq_step.symm.trans (ih (by omega))
    have hxy_nv : nv x = nv y := by
      have h1 := hnv_eq (y.val - x.val) (by omega)
      have h2 : (⟨x.val + (y.val - x.val), by omega⟩ : Fin (n + 1)) = y := Fin.ext (by simp; omega)
      rw [h2] at h1
      exact h1.symm
    have hx_val : (C.wires (mkInput n x)).getD (a j).val false = true := by
      by_contra hne
      exact hbadx ⟨j, true, hwx, hne⟩
    have hy_val : (C.wires (mkInput n y)).getD (a j).val false = false := by
      by_contra hne
      exact hbady ⟨j, false, hwy, hne⟩
    have hmono := wires_mono_of_notVec_eq C hF2 hRB (mkInput n x) (mkInput n y)
      (mkInput_length n x) (mkInput_length n y)
      (mkInput_listLe (le_of_lt hxy)) hxy_nv (a j).val (a j).isLt hx_val
    rw [hy_val] at hmono; cases hmono

-- ============================================================================
-- Upper bound: Clean circuit builder + flexible Fischer inverter + indicators + outputs
-- ============================================================================

private structure Bld (M : Nat) where
  gates : List Gate
  hF2 : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  hRB : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs, i < M + j

private def Bld.toCircuit {M : Nat} (B : Bld M) : Circuit := ⟨B.gates, 0⟩
private def Bld.size {M : Nat} (B : Bld M) : Nat := B.gates.length
private def Bld.nots {M : Nat} (B : Bld M) : Nat := notCount B.toCircuit

private def Bld.empty (M : Nat) : Bld M :=
  ⟨[], (fun _ h => by cases h), (fun _ h => by cases h)⟩

private def Bld.Ext {M : Nat} (B1 B2 : Bld M) : Prop :=
  ∃ suf, B2.gates = B1.gates ++ suf

private lemma Bld.Ext.refl {M : Nat} (B : Bld M) : B.Ext B := ⟨[], by simp⟩

private lemma Bld.Ext.trans {M : Nat} {B1 B2 B3 : Bld M} (h12 : B1.Ext B2) (h23 : B2.Ext B3) :
    B1.Ext B3 := by
  rcases h12 with ⟨s1, hs1⟩; rcases h23 with ⟨s2, hs2⟩
  exact ⟨s1 ++ s2, by rw [hs2, hs1, List.append_assoc]⟩

private lemma Bld.Ext.size_le {M : Nat} {B1 B2 : Bld M} (h : B1.Ext B2) : B1.size ≤ B2.size := by
  rcases h with ⟨s, hs⟩; unfold Bld.size; rw [hs, List.length_append]; omega

private lemma Bld.Ext.wires_eq {M : Nat} {B1 B2 : Bld M} (h : B1.Ext B2) (inp : List Bool)
    (hinp : inp.length = M) (w : Nat) (hw : w < M + B1.size) :
    (B2.toCircuit.wires inp).getD w false = (B1.toCircuit.wires inp).getD w false := by
  rcases h with ⟨suf, hsuf⟩
  change (B2.gates.foldl _ inp).getD w false = (B1.gates.foldl _ inp).getD w false
  rw [hsuf, List.foldl_append]
  apply wires_getD_lt_aux
  rw [wires_length_aux, hinp]; exact hw

private def Bld.pushGate {M : Nat} (B : Bld M) (op : GateOp) (inps : List Nat)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inps.length ≤ 2) (hinp : ∀ u ∈ inps, u < M + B.size) : Bld M × Nat :=
  let g : Gate := ⟨op, inps⟩
  let B' : Bld M := {
    gates := B.gates ++ [g]
    hF2 := by
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact B.hF2 x hx
      · exact ⟨hop, hlen⟩
    hRB := by
      intro j hj i hi
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < B.gates.length
      · have hg : (B.gates ++ [g]).getD j ⟨GateOp.or, []⟩ = B.gates.getD j ⟨GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [hg] at hi
        exact B.hRB j hlt i hi
      · have hjeq : j = B.gates.length := by omega
        subst hjeq
        have hg : (B.gates ++ [g]).getD B.gates.length ⟨GateOp.or, []⟩ = g := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
        rw [hg] at hi
        exact hinp i hi
  }
  (B', M + B.size)

private lemma Bld.pushGate_ext {M : Nat} (B : Bld M) (op : GateOp) (inps : List Nat)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inps.length ≤ 2) (hinp : ∀ u ∈ inps, u < M + B.size) :
    B.Ext (B.pushGate op inps hop hlen hinp).1 := ⟨[⟨op, inps⟩], rfl⟩

private lemma Bld.pushGate_wire_lt {M : Nat} (B : Bld M) (op : GateOp) (inps : List Nat)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inps.length ≤ 2) (hinp : ∀ u ∈ inps, u < M + B.size) :
    (B.pushGate op inps hop hlen hinp).2 < M + (B.pushGate op inps hop hlen hinp).1.size := by
  simp [Bld.pushGate, Bld.size]

private lemma Bld.pushGate_size {M : Nat} (B : Bld M) (op : GateOp) (inps : List Nat)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inps.length ≤ 2) (hinp : ∀ u ∈ inps, u < M + B.size) :
    (B.pushGate op inps hop hlen hinp).1.size = B.size + 1 := by
  simp [Bld.pushGate, Bld.size]

private lemma Bld.pushGate_eval {M : Nat} (B : Bld M) (op : GateOp) (inps : List Nat)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inps.length ≤ 2) (hinp : ∀ u ∈ inps, u < M + B.size)
    (inp : List Bool) (hln : inp.length = M) :
    ((B.pushGate op inps hop hlen hinp).1.toCircuit.wires inp).getD
      (B.pushGate op inps hop hlen hinp).2 false =
      op.eval (inps.map fun u => (B.toCircuit.wires inp).getD u false) := by
  simp only [Bld.pushGate, Bld.toCircuit, Circuit.wires, Bld.size]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlenw : (B.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp).length =
      M + B.gates.length := by rw [wires_length_aux, hln]
  rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private def Bld.mkAnd {M : Nat} (B : Bld M) (u v : Nat) (hu : u < M + B.size) (hv : v < M + B.size) :
    Bld M × Nat :=
  B.pushGate GateOp.and [u, v] (by simp) (by simp) (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)

private def Bld.mkOr {M : Nat} (B : Bld M) (u v : Nat) (hu : u < M + B.size) (hv : v < M + B.size) :
    Bld M × Nat :=
  B.pushGate GateOp.or [u, v] (by simp) (by simp) (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)

private def Bld.mkNot {M : Nat} (B : Bld M) (u : Nat) (hu : u < M + B.size) :
    Bld M × Nat :=
  B.pushGate GateOp.not [u] (by simp) (by simp) (by intro w hw; simp at hw; rwa [hw])

private lemma Bld.mkAnd_nots {M : Nat} (B : Bld M) (u v : Nat) (hu : u < M + B.size) (hv : v < M + B.size) :
    (B.mkAnd u v hu hv).1.nots = B.nots := by
  simp [Bld.mkAnd, Bld.pushGate, Bld.nots, Bld.toCircuit, notCount]

private lemma Bld.mkOr_nots {M : Nat} (B : Bld M) (u v : Nat) (hu : u < M + B.size) (hv : v < M + B.size) :
    (B.mkOr u v hu hv).1.nots = B.nots := by
  simp [Bld.mkOr, Bld.pushGate, Bld.nots, Bld.toCircuit, notCount]

private lemma Bld.mkNot_nots {M : Nat} (B : Bld M) (u : Nat) (hu : u < M + B.size) :
    (B.mkNot u hu).1.nots = B.nots + 1 := by
  simp [Bld.mkNot, Bld.pushGate, Bld.nots, Bld.toCircuit, notCount]

private lemma Bld.mkAnd_eval {M : Nat} (B : Bld M) (u v : Nat) (hu : u < M + B.size) (hv : v < M + B.size)
    (inp : List Bool) (hln : inp.length = M) :
    ((B.mkAnd u v hu hv).1.toCircuit.wires inp).getD (B.mkAnd u v hu hv).2 false =
      ((B.toCircuit.wires inp).getD u false && (B.toCircuit.wires inp).getD v false) := by
  simpa [Bld.mkAnd, GateOp.eval] using B.pushGate_eval GateOp.and [u, v] _ _ _ inp hln

private lemma Bld.mkOr_eval {M : Nat} (B : Bld M) (u v : Nat) (hu : u < M + B.size) (hv : v < M + B.size)
    (inp : List Bool) (hln : inp.length = M) :
    ((B.mkOr u v hu hv).1.toCircuit.wires inp).getD (B.mkOr u v hu hv).2 false =
      ((B.toCircuit.wires inp).getD u false || (B.toCircuit.wires inp).getD v false) := by
  simpa [Bld.mkOr, GateOp.eval] using B.pushGate_eval GateOp.or [u, v] _ _ _ inp hln

private lemma Bld.mkNot_eval {M : Nat} (B : Bld M) (u : Nat) (hu : u < M + B.size)
    (inp : List Bool) (hln : inp.length = M) :
    ((B.mkNot u hu).1.toCircuit.wires inp).getD (B.mkNot u hu).2 false =
      !((B.toCircuit.wires inp).getD u false) := by
  simpa [Bld.mkNot, GateOp.eval] using B.pushGate_eval GateOp.not [u] _ _ _ inp hln

private lemma build_fischer_fold {M : Nat} (B0 : Bld M) (n : Nat)
    (Tlo Thi : Fin n → Nat) (notM : Nat)
    (hTlo : ∀ i, Tlo i < M + B0.size) (hThi : ∀ i, Thi i < M + B0.size) (hnotM : notM < M + B0.size) :
    ∃ (B1 : Bld M) (L : Fin n → Nat),
      B0.Ext B1 ∧
      B1.size = B0.size + 2 * n ∧
      B1.nots = B0.nots ∧
      (∀ i, L i < M + B1.size) ∧
      (∀ inp, inp.length = M → ∀ i,
        (B1.toCircuit.wires inp).getD (L i) false =
          (((B0.toCircuit.wires inp).getD (Tlo i) false && (B0.toCircuit.wires inp).getD notM false) ||
            (B0.toCircuit.wires inp).getD (Thi i) false)) := by
  induction n with
  | zero =>
    exact ⟨B0, Fin.elim0, Bld.Ext.refl B0, by simp, rfl, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩
  | succ n ih =>
    rcases ih (fun i => Tlo i.castSucc) (fun i => Thi i.castSucc)
      (fun i => hTlo i.castSucc) (fun i => hThi i.castSucc) with
      ⟨B1, L1, h01, hsz1, hnt1, hL1_lt, hL1_ev⟩
    have hsz01 : B0.size ≤ B1.size := h01.size_le
    let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let pA := B1.mkAnd (Tlo last) notM (by have := hTlo last; omega) (by omega)
    let B2 := pA.1; let wA := pA.2
    have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz2 : B2.size = B1.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt2 : B2.nots = B1.nots := Bld.mkAnd_nots _ _ _ _ _
    have hwA_lt : wA < M + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    let pO := B2.mkOr wA (Thi last) hwA_lt (by have := hThi last; omega)
    let B3 := pO.1; let wO := pO.2
    have h23 : B2.Ext B3 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz3 : B3.size = B2.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt3 : B3.nots = B2.nots := Bld.mkOr_nots _ _ _ _ _
    have hwO_lt : wO < M + B3.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    have h13 : B1.Ext B3 := h12.trans h23
    have h03 : B0.Ext B3 := h01.trans h13
    refine ⟨B3, fun i => if h : i.val < n then L1 ⟨i.val, h⟩ else wO, h03, by omega, by omega, ?_, ?_⟩
    · intro i; dsimp only; split_ifs with hi
      · have := hL1_lt ⟨i.val, hi⟩; omega
      · exact hwO_lt
    · intro inp hln i; dsimp only; split_ifs with hi
      · rw [h13.wires_eq inp hln _ (hL1_lt ⟨i.val, hi⟩)]
        exact hL1_ev inp hln ⟨i.val, hi⟩
      · have hieq : i = last := Fin.ext (by simp [last]; omega)
        subst hieq
        rw [Bld.mkOr_eval _ _ _ _ _ inp hln, Bld.mkAnd_eval _ _ _ _ _ inp hln]
        rw [h12.wires_eq inp hln (Thi last) (by have := hThi last; omega)]
        rw [h01.wires_eq inp hln (Tlo last) (hTlo last),
            h01.wires_eq inp hln notM hnotM,
            h01.wires_eq inp hln (Thi last) (hThi last)]

private lemma build_fischer_unfold {M : Nat} (B0 : Bld M) (n : Nat)
    (notL : Fin n → Nat) (notM : Nat)
    (hnotL : ∀ i, notL i < M + B0.size) (hnotM : notM < M + B0.size) :
    ∃ (B1 : Bld M) (lo hi : Fin n → Nat),
      B0.Ext B1 ∧
      B1.size = B0.size + 2 * n ∧
      B1.nots = B0.nots ∧
      (∀ i, lo i < M + B1.size) ∧ (∀ i, hi i < M + B1.size) ∧
      (∀ inp, inp.length = M → ∀ i,
        (B1.toCircuit.wires inp).getD (lo i) false =
          ((B0.toCircuit.wires inp).getD (notL i) false && (B0.toCircuit.wires inp).getD notM false) ∧
        (B1.toCircuit.wires inp).getD (hi i) false =
          ((B0.toCircuit.wires inp).getD (notL i) false || (B0.toCircuit.wires inp).getD notM false)) := by
  induction n with
  | zero =>
    exact ⟨B0, Fin.elim0, Fin.elim0, Bld.Ext.refl B0, by simp, rfl,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩
  | succ n ih =>
    rcases ih (fun i => notL i.castSucc) (fun i => hnotL i.castSucc) with
      ⟨B1, lo1, hi1, h01, hsz1, hnt1, hlo1_lt, hhi1_lt, hev1⟩
    have hsz01 : B0.size ≤ B1.size := h01.size_le
    let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let pA := B1.mkAnd (notL last) notM (by have := hnotL last; omega) (by omega)
    let B2 := pA.1; let wA := pA.2
    have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz2 : B2.size = B1.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt2 : B2.nots = B1.nots := Bld.mkAnd_nots _ _ _ _ _
    have hwA_lt : wA < M + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    let pO := B2.mkOr (notL last) notM (by have := hnotL last; omega) (by omega)
    let B3 := pO.1; let wO := pO.2
    have h23 : B2.Ext B3 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz3 : B3.size = B2.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt3 : B3.nots = B2.nots := Bld.mkOr_nots _ _ _ _ _
    have hwO_lt : wO < M + B3.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    have h13 : B1.Ext B3 := h12.trans h23
    have h03 : B0.Ext B3 := h01.trans h13
    refine ⟨B3,
      fun i => if h : i.val < n then lo1 ⟨i.val, h⟩ else wA,
      fun i => if h : i.val < n then hi1 ⟨i.val, h⟩ else wO,
      h03, by omega, by omega, ?_, ?_, ?_⟩
    · intro i; dsimp only; split_ifs with hi
      · have := hlo1_lt ⟨i.val, hi⟩; omega
      · omega
    · intro i; dsimp only; split_ifs with hi
      · have := hhi1_lt ⟨i.val, hi⟩; omega
      · exact hwO_lt
    · intro inp hln i; dsimp only; split_ifs with hi
      · rw [h13.wires_eq inp hln _ (hlo1_lt ⟨i.val, hi⟩),
            h13.wires_eq inp hln _ (hhi1_lt ⟨i.val, hi⟩)]
        exact hev1 inp hln ⟨i.val, hi⟩
      · have hieq : i = last := Fin.ext (by simp [last]; omega)
        subst hieq
        constructor
        · rw [h23.wires_eq inp hln wA hwA_lt, Bld.mkAnd_eval _ _ _ _ _ inp hln,
              h01.wires_eq inp hln (notL last) (hnotL last),
              h01.wires_eq inp hln notM hnotM]
        · rw [Bld.mkOr_eval _ _ _ _ _ inp hln,
              (h01.trans h12).wires_eq inp hln (notL last) (hnotL last),
              (h01.trans h12).wires_eq inp hln notM hnotM]

-- Flexible Fischer inverter on ANY h <= 2^b - 1 threshold bits, using <= b NOTs and <= 5*h gates!
private lemma build_fischer_flex {M : Nat} (wFalse : Nat) (hwF : wFalse < M) (b : Nat) :
    ∀ (h : Nat), h ≤ 2 ^ b - 1 → ∀ (B0 : Bld M) (T : Fin h → Nat),
      (∀ i, T i < M + B0.size) →
      ∃ (B1 : Bld M) (notT : Fin h → Nat),
        B0.Ext B1 ∧
        B1.size ≤ B0.size + 5 * h ∧
        B1.nots ≤ B0.nots + b ∧
        (∀ i, notT i < M + B1.size) ∧
        (∀ inp, inp.length = M → inp.getD wFalse false = false →
          ∀ t : Nat, t ≤ h →
            (∀ i : Fin h, (B0.toCircuit.wires inp).getD (T i) false = decide (i.val + 1 ≤ t)) →
            ∀ i : Fin h, (B1.toCircuit.wires inp).getD (notT i) false = !(decide (i.val + 1 ≤ t))) := by
  induction b with
  | zero =>
    intro h hh B0 T _
    have hh0 : h = 0 := by simp at hh; exact hh
    subst hh0
    exact ⟨B0, Fin.elim0, Bld.Ext.refl B0, by simp, by simp, fun i => Fin.elim0 i,
      fun _ _ _ _ _ _ i => Fin.elim0 i⟩
  | succ m ih =>
    intro h hh B0 T hT
    by_cases hh0 : h = 0
    · subst hh0
      exact ⟨B0, Fin.elim0, Bld.Ext.refl B0, by simp, by omega, fun i => Fin.elim0 i,
        fun _ _ _ _ _ _ i => Fin.elim0 i⟩
    have hh_pos : 1 ≤ h := by omega
    let mid : Nat := h / 2
    have hmid_lt : mid < h := by omega
    have hmid_le : mid ≤ 2 ^ m - 1 := by
      have h2m : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      omega
    let pN := B0.mkNot (T ⟨mid, hmid_lt⟩) (hT ⟨mid, hmid_lt⟩)
    let B1 := pN.1; let notM := pN.2
    have h01 : B0.Ext B1 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz1 : B1.size = B0.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt1 : B1.nots = B0.nots + 1 := Bld.mkNot_nots _ _ _
    have hnotM_lt : notM < M + B1.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    let Tlo : Fin mid → Nat := fun u => T ⟨u.val, by omega⟩
    let Thi : Fin mid → Nat := fun u => if hu : mid + 1 + u.val < h then T ⟨mid + 1 + u.val, hu⟩ else wFalse
    rcases build_fischer_fold B1 mid Tlo Thi notM
      (fun u => by have := hT ⟨u.val, by omega⟩; dsimp only [Tlo]; omega)
      (fun u => by
        dsimp only [Thi]; split_ifs with hu
        · have := hT ⟨mid + 1 + u.val, hu⟩; omega
        · omega)
      hnotM_lt with ⟨B2, L, h12, hsz2, hnt2, hL_lt, hL_ev⟩
    rcases ih mid hmid_le B2 L hL_lt with ⟨B3, notL, h23, hsz3, hnt3, hnotL_lt, hnotL_ev⟩
    have hnotM_lt3 : notM < M + B3.size := by have := (h12.trans h23).size_le; omega
    rcases build_fischer_unfold B3 mid notL notM hnotL_lt hnotM_lt3 with
      ⟨B4, lo, hi, h34, hsz4, hnt4, hlo_lt, hhi_lt, hunf_ev⟩
    have h04 : B0.Ext B4 := ((h01.trans h12).trans h23).trans h34
    let notT : Fin h → Nat := fun i =>
      if h1 : i.val < mid then lo ⟨i.val, h1⟩
      else if h2 : i.val = mid then notM
      else hi ⟨i.val - (mid + 1), by omega⟩
    refine ⟨B4, notT, h04, ?_, by omega, ?_, ?_⟩
    · -- B4.size <= B0.size + 5 * h
      -- B4.size <= B0.size + 1 + 9 * mid; for h = 1, mid = 0 -> 1 <= 5; for h >= 2, mid >= 1 -> 1 + 9*mid <= 5*h!
      omega
    · intro i; simp only [notT]; split_ifs with h1 h2
      · exact hlo_lt ⟨i.val, h1⟩
      · have := h34.size_le; omega
      · exact hhi_lt ⟨i.val - (mid + 1), by omega⟩
    · intro inp hln hwF_ev t ht hTev i
      have hnotM_B1 : (B1.toCircuit.wires inp).getD notM false = decide (t ≤ mid) := by
        rw [Bld.mkNot_eval _ _ _ inp hln, hTev ⟨mid, hmid_lt⟩]
        by_cases hle : t ≤ mid
        · have hgt : ¬ mid + 1 ≤ t := by omega
          simp [hle, hgt]
        · have hgt : mid + 1 ≤ t := by omega
          simp [hle, hgt]
      let t' : Nat := if t ≤ mid then t else t - (mid + 1)
      have ht'_le : t' ≤ mid := by simp only [t']; split_ifs <;> omega
      have hLev : ∀ u : Fin mid, (B2.toCircuit.wires inp).getD (L u) false = decide (u.val + 1 ≤ t') := by
        intro u
        rw [hL_ev inp hln u, hnotM_B1,
            h01.wires_eq inp hln (Tlo u) (hT _)]
        have hThi_ev : (B1.toCircuit.wires inp).getD (Thi u) false =
            if mid + 1 + u.val < h then decide (mid + 1 + u.val + 1 ≤ t) else false := by
          dsimp only [Thi]
          split_ifs with hu
          · rw [h01.wires_eq inp hln (T ⟨mid + 1 + u.val, hu⟩) (hT _), hTev ⟨mid + 1 + u.val, hu⟩]
          · rw [wires_getD_input _ _ wFalse (by omega), hwF_ev]
        rw [hThi_ev]
        dsimp only [Tlo]
        rw [hTev ⟨u.val, by omega⟩]
        by_cases hle : t ≤ mid
        · have ht'eq : t' = t := by simp [t', hle]
          rw [ht'eq]
          split_ifs with hu
          · have hbig : ¬ mid + 1 + u.val + 1 ≤ t := by omega
            simp [hle, hbig]
          · simp [hle]
        · have ht'eq : t' = t - (mid + 1) := by simp [t', hle]
          rw [ht'eq]
          split_ifs with hu
          · have hiff : mid + 1 + u.val + 1 ≤ t ↔ u.val + 1 ≤ t - (mid + 1) := by omega
            simp [hle, hiff]
          · have hbig : ¬ u.val + 1 ≤ t - (mid + 1) := by omega
            simp [hle, hbig]
      have hnotL_ev3 : ∀ u : Fin mid,
          (B3.toCircuit.wires inp).getD (notL u) false = !(decide (u.val + 1 ≤ t')) :=
        hnotL_ev inp hln hwF_ev t' ht'_le hLev
      have hnotM_B3 : (B3.toCircuit.wires inp).getD notM false = decide (t ≤ mid) := by
        rw [(h12.trans h23).wires_eq inp hln notM hnotM_lt, hnotM_B1]
      simp only [notT]
      split_ifs with h1 h2
      · rw [(hunf_ev inp hln ⟨i.val, h1⟩).1, hnotL_ev3 ⟨i.val, h1⟩, hnotM_B3]
        by_cases hle : t ≤ mid
        · have ht'eq : t' = t := by simp [t', hle]
          simp [hle, ht'eq]
        · have hge : i.val + 1 ≤ t := by omega
          simp [hle, hge]
      · rw [((h12.trans h23).trans h34).wires_eq inp hln notM hnotM_lt, hnotM_B1]
        rw [h2]
        by_cases hle : t ≤ mid
        · have hge : ¬ mid + 1 ≤ t := by omega
          simp [hle, hge]
        · have hge : mid + 1 ≤ t := by omega
          simp [hle, hge]
      · rw [(hunf_ev inp hln ⟨i.val - (mid + 1), by omega⟩).2,
            hnotL_ev3 ⟨i.val - (mid + 1), by omega⟩, hnotM_B3]
        by_cases hle : t ≤ mid
        · have hge : ¬ i.val + 1 ≤ t := by omega
          simp [hle, hge]
        · have ht'eq : t' = t - (mid + 1) := by simp [t', hle]
          have hiff : i.val - (mid + 1) + 1 ≤ t - (mid + 1) ↔ i.val + 1 ≤ t := by omega
          simp [hle, ht'eq, hiff]

-- Build phase indicators ind r = decide (t = r) for r in Fin (h + 1) using <= h gates (0 NOTs)!
private lemma build_indicators {M : Nat} (B0 : Bld M) (wTrue : Nat) (hwT : wTrue < M) (h : Nat)
    (T notT : Fin h → Nat) (hT : ∀ i, T i < M + B0.size) (hnotT : ∀ i, notT i < M + B0.size) :
    ∃ (B1 : Bld M) (ind : Fin (h + 1) → Nat),
      B0.Ext B1 ∧
      B1.size ≤ B0.size + h ∧
      B1.nots = B0.nots ∧
      (∀ r, ind r < M + B1.size) ∧
      (∀ inp, inp.length = M → inp.getD wTrue false = true →
        ∀ t : Nat, t ≤ h →
          (∀ i : Fin h, (B0.toCircuit.wires inp).getD (T i) false = decide (i.val + 1 ≤ t)) →
          (∀ i : Fin h, (B0.toCircuit.wires inp).getD (notT i) false = !(decide (i.val + 1 ≤ t))) →
          ∀ r : Fin (h + 1), (B1.toCircuit.wires inp).getD (ind r) false = decide (t = r.val)) := by
  -- For r = 0: if h = 0 then wTrue else notT 0 (0 gates)
  -- For 0 < r < h: T (r-1) && notT r (1 gate each, total h - 1 gates)
  -- For r = h (h >= 1): T (h-1) (0 gates)
  -- Build middle indicators m_u = T u && notT (u+1) for u : Fin (h - 1) by induction on k <= h - 1!
  have buildMid : ∀ (k : Nat) (hk : k + 1 ≤ h),
      ∃ (B1 : Bld M) (midW : Fin k → Nat),
        B0.Ext B1 ∧ B1.size = B0.size + k ∧ B1.nots = B0.nots ∧
        (∀ u, midW u < M + B1.size) ∧
        (∀ inp, inp.length = M → ∀ u : Fin k,
          (B1.toCircuit.wires inp).getD (midW u) false =
            ((B0.toCircuit.wires inp).getD (T ⟨u.val, by omega⟩) false &&
              (B0.toCircuit.wires inp).getD (notT ⟨u.val + 1, by omega⟩) false)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨B0, Fin.elim0, Bld.Ext.refl B0, by simp, rfl, fun u => Fin.elim0 u, fun _ _ u => Fin.elim0 u⟩
    | succ k ihk =>
      intro hk
      rcases ihk (by omega) with ⟨B1, mid1, h01, hsz1, hnt1, hm1_lt, hm1_ev⟩
      let pA := B1.mkAnd (T ⟨k, by omega⟩) (notT ⟨k + 1, by omega⟩)
        (by have := hT ⟨k, by omega⟩; have := h01.size_le; omega)
        (by have := hnotT ⟨k + 1, by omega⟩; have := h01.size_le; omega)
      let B2 := pA.1; let wA := pA.2
      have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
      have hsz2 : B2.size = B1.size + 1 := Bld.pushGate_size _ _ _ _ _ _
      have hnt2 : B2.nots = B1.nots := Bld.mkAnd_nots _ _ _ _ _
      have hwA_lt : wA < M + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
      refine ⟨B2, fun u => if hu : u.val < k then mid1 ⟨u.val, hu⟩ else wA,
        h01.trans h12, by omega, by omega, ?_, ?_⟩
      · intro u; dsimp only; split_ifs with hu
        · have := hm1_lt ⟨u.val, hu⟩; omega
        · exact hwA_lt
      · intro inp hln u; dsimp only; split_ifs with hu
        · rw [h12.wires_eq inp hln _ (hm1_lt ⟨u.val, hu⟩)]
          exact hm1_ev inp hln ⟨u.val, hu⟩
        · have huk : u.val = k := by omega
          rw [Bld.mkAnd_eval _ _ _ _ _ inp hln,
              h01.wires_eq inp hln _ (hT _), h01.wires_eq inp hln _ (hnotT _)]
          simp [huk]
  by_cases hh0 : h = 0
  · subst hh0
    refine ⟨B0, fun _ => wTrue, Bld.Ext.refl B0, by omega, rfl, fun _ => by dsimp only; omega, ?_⟩
    intro inp hln hwT_ev t ht _ _ r
    rw [wires_getD_input _ _ wTrue (by omega), hwT_ev]
    have ht0 : t = 0 := by omega
    have hr0 : r.val = 0 := by omega
    simp [ht0, hr0]
  · rcases buildMid (h - 1) (by omega) with ⟨B1, midW, h01, hsz1, hnt1, hmid_lt, hmid_ev⟩
    let ind : Fin (h + 1) → Nat := fun r =>
      if h0 : r.val = 0 then notT ⟨0, by omega⟩
      else if hlast : r.val = h then T ⟨h - 1, by omega⟩
      else midW ⟨r.val - 1, by omega⟩
    refine ⟨B1, ind, h01, by omega, hnt1, ?_, ?_⟩
    · intro r; simp only [ind]; split_ifs with h0 hlast
      · have := hnotT ⟨0, by omega⟩; omega
      · have := hT ⟨h - 1, by omega⟩; omega
      · exact hmid_lt ⟨r.val - 1, by omega⟩
    · intro inp hln _ t ht hTev hnotTev r
      simp only [ind]; split_ifs with h0 hlast
      · rw [h01.wires_eq inp hln _ (hnotT _), hnotTev ⟨0, by omega⟩, h0]
        by_cases ht0 : t = 0 <;> simp [ht0] <;> omega
      · rw [h01.wires_eq inp hln _ (hT _), hTev ⟨h - 1, by omega⟩, hlast]
        have hsub : h - 1 + 1 = h := by omega
        rw [hsub]
        by_cases hth : t = h
        · simp [hth]
        · have hnot : ¬ h ≤ t := by omega
          simp [hth, hnot]
      · rw [hmid_ev inp hln ⟨r.val - 1, by omega⟩,
            hTev ⟨r.val - 1, by omega⟩, hnotTev ⟨r.val - 1 + 1, by omega⟩]
        have hd1 : decide ((⟨r.val - 1, by omega⟩ : Fin h).val + 1 ≤ t) = decide (r.val ≤ t) :=
          decide_eq_decide.mpr (by dsimp only; omega)
        have hd2 : decide ((⟨r.val - 1 + 1, by omega⟩ : Fin h).val + 1 ≤ t) = decide (r.val + 1 ≤ t) :=
          decide_eq_decide.mpr (by dsimp only; omega)
        rw [hd1, hd2]
        by_cases htr : t = r.val
        · subst htr; simp
        · by_cases hle : r.val ≤ t
          · have hge : r.val + 1 ≤ t := by omega
            simp [htr, hle, hge]
          · simp [htr, hle]

private lemma list_any_congr {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.any_cons, h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

-- Build OR of a list of (ind_wire, thresh_wire) pairs using <= 2 * pairs.length gates (0 NOTs)!
private lemma build_or_and_list {M : Nat} (B0 : Bld M) (wFalse : Nat) (hwF : wFalse < M)
    (pairs : List (Nat × Nat))
    (hp : ∀ p ∈ pairs, p.1 < M + B0.size ∧ p.2 < M + B0.size) :
    ∃ (B1 : Bld M) (wOut : Nat),
      B0.Ext B1 ∧
      B1.size ≤ B0.size + 2 * pairs.length ∧
      B1.nots = B0.nots ∧
      wOut < M + B1.size ∧
      (∀ inp, inp.length = M → inp.getD wFalse false = false →
        (B1.toCircuit.wires inp).getD wOut false =
          pairs.any (fun p => (B0.toCircuit.wires inp).getD p.1 false &&
                              (B0.toCircuit.wires inp).getD p.2 false)) := by
  induction pairs generalizing B0 with
  | nil =>
    refine ⟨B0, wFalse, Bld.Ext.refl B0, by simp, rfl, by omega, ?_⟩
    intro inp hln hwF_ev
    rw [wires_getD_input _ _ wFalse (by omega), hwF_ev]; rfl
  | cons hd tl ih =>
    have hhd : hd.1 < M + B0.size ∧ hd.2 < M + B0.size := hp hd (by simp)
    let pA := B0.mkAnd hd.1 hd.2 hhd.1 hhd.2
    let B1 := pA.1; let wA := pA.2
    have h01 : B0.Ext B1 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz1 : B1.size = B0.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt1 : B1.nots = B0.nots := Bld.mkAnd_nots _ _ _ _ _
    have hwA_lt : wA < M + B1.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    rcases ih B1 (fun p hpt => by
      have := hp p (List.mem_cons_of_mem hd hpt); exact ⟨by omega, by omega⟩) with
      ⟨B2, wTl, h12, hsz2, hnt2, hwT_lt, hwT_ev⟩
    have h02 : B0.Ext B2 := h01.trans h12
    have hwA_lt2 : wA < M + B2.size := by have := h12.size_le; omega
    let pO := B2.mkOr wA wTl hwA_lt2 hwT_lt
    let B3 := pO.1; let wO := pO.2
    have h23 : B2.Ext B3 := Bld.pushGate_ext _ _ _ _ _ _
    have hsz3 : B3.size = B2.size + 1 := Bld.pushGate_size _ _ _ _ _ _
    have hnt3 : B3.nots = B2.nots := Bld.mkOr_nots _ _ _ _ _
    have hwO_lt : wO < M + B3.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    refine ⟨B3, wO, h02.trans h23, by simp [List.length_cons]; omega, by omega, hwO_lt, ?_⟩
    intro inp hln hwF_ev
    rw [Bld.mkOr_eval _ _ _ _ _ inp hln, h12.wires_eq inp hln wA hwA_lt,
        Bld.mkAnd_eval _ _ _ _ _ inp hln, hwT_ev inp hln hwF_ev]
    simp only [List.any_cons]
    congr 1
    apply list_any_congr
    intro p hpt
    have hpp := hp p (List.mem_cons_of_mem hd hpt)
    rw [h01.wires_eq inp hln p.1 hpp.1, h01.wires_eq inp hln p.2 hpp.2]

private lemma build_all_outputs {M : Nat} (B0 : Bld M) (wFalse : Nat) (hwF : wFalse < M) (m : Nat)
    (lists : Fin m → List (Nat × Nat))
    (hl : ∀ j, ∀ p ∈ lists j, p.1 < M + B0.size ∧ p.2 < M + B0.size) :
    ∃ (B1 : Bld M) (outs : Fin m → Nat),
      B0.Ext B1 ∧
      B1.size ≤ B0.size + 2 * (∑ j : Fin m, (lists j).length) ∧
      B1.nots = B0.nots ∧
      (∀ j, outs j < M + B1.size) ∧
      (∀ inp, inp.length = M → inp.getD wFalse false = false → ∀ j,
        (B1.toCircuit.wires inp).getD (outs j) false =
          (lists j).any (fun p => (B0.toCircuit.wires inp).getD p.1 false &&
                                  (B0.toCircuit.wires inp).getD p.2 false)) := by
  induction m generalizing B0 with
  | zero =>
    exact ⟨B0, Fin.elim0, Bld.Ext.refl B0, by simp, rfl, fun j => Fin.elim0 j,
      fun _ _ _ j => Fin.elim0 j⟩
  | succ m ih =>
    rcases ih B0 (fun j => lists j.castSucc) (fun j => hl j.castSucc) with
      ⟨B1, outs1, h01, hsz1, hnt1, ho1_lt, ho1_ev⟩
    let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    rcases build_or_and_list B1 wFalse hwF (lists last) (fun p hp => by
      have := hl last p hp; have := h01.size_le; exact ⟨by omega, by omega⟩) with
      ⟨B2, wLast, h12, hsz2, hnt2, hwL_lt, hwL_ev⟩
    refine ⟨B2, fun j => if hj : j.val < m then outs1 ⟨j.val, hj⟩ else wLast,
      h01.trans h12, ?_, by omega, ?_, ?_⟩
    · have hsum : (∑ j : Fin (m + 1), (lists j).length) =
          (∑ j : Fin m, (lists j.castSucc).length) + (lists last).length :=
        Fin.sum_univ_castSucc (fun j => (lists j).length)
      rw [hsum]; omega
    · intro j; dsimp only; split_ifs with hj
      · have := ho1_lt ⟨j.val, hj⟩; have := h12.size_le; omega
      · exact hwL_lt
    · intro inp hln hwF_ev j; dsimp only; split_ifs with hj
      · rw [h12.wires_eq inp hln _ (ho1_lt ⟨j.val, hj⟩)]
        exact ho1_ev inp hln hwF_ev ⟨j.val, hj⟩
      · have hjeq : j = last := Fin.ext (by simp [last]; omega)
        subst hjeq
        rw [hwL_ev inp hln hwF_ev]
        apply list_any_congr
        intro p hp
        have hpp := hl last p hp
        rw [h01.wires_eq inp hln p.1 hpp.1, h01.wires_eq inp hln p.2 hpp.2]

-- ============================================================================
-- Upper bound construction from any (H, Z) covering all true->false drops
-- ============================================================================

private lemma upper_bound_from_cover {n m b : Nat} (want : Fin (n + 1) → Fin m → Option Bool)
    (H : Finset (Fin n)) (Z : Finset (Fin (n + 1)))
    (hHcard : H.card ≤ 2 ^ b - 1)
    (hcov : ∀ (x y : Fin (n + 1)) (j : Fin m), x < y →
      want x j = some true → want y j = some false →
      x ∈ Z ∨ y ∈ Z ∨ ∃ i ∈ H, x.val ≤ i.val ∧ i.val < y.val) :
    let highs := (Finset.univ : Finset (Fin (n + 1))).sum (fun k =>
      ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card)
    ∃ (C : Circuit) (a : Fin m → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
      (∀ k : Fin (n + 1),
        (∃ (j : Fin m) (v : Bool), want k j = some v ∧ (C.wires (mkInput n k)).getD (a j).val false ≠ v) →
        k ∈ Z) ∧
      C.size ≤ 2 * (min highs (m * (H.card + 1))) + 7 * H.card + 2 := by
  intro highs
  let M := n + 2
  let wFalse := n
  let wTrue := n + 1
  let h := H.card
  let pEmb : Fin h ↪o Fin n := H.orderEmbOfFin rfl
  have hp_mem : ∀ r : Fin h, pEmb r ∈ H := fun r => H.orderEmbOfFin_mem rfl r
  have hp_strict : ∀ r1 r2 : Fin h, r1 < r2 → (pEmb r1).val < (pEmb r2).val := fun r1 r2 hr =>
    pEmb.strictMono hr
  -- Phase of k : Fin (n + 1) is the number of cuts p_r < k.val!
  let phase : Fin (n + 1) → Nat := fun k =>
    ((Finset.univ : Finset (Fin h)).filter (fun r => (pEmb r).val < k.val)).card
  have hphase_le : ∀ k, phase k ≤ h := fun k => by
    calc phase k ≤ (Finset.univ : Finset (Fin h)).card := Finset.card_filter_le _ _
      _ = h := Finset.card_fin h
  have hphase_iff : ∀ (k : Fin (n + 1)) (r : Fin h), (pEmb r).val < k.val ↔ r.val + 1 ≤ phase k := by
    intro k r
    let S := (Finset.univ : Finset (Fin h)).filter (fun u => (pEmb u).val < k.val)
    change (pEmb r).val < k.val ↔ r.val + 1 ≤ S.card
    constructor
    · intro hr
      have hsub : (Finset.univ.filter (fun u : Fin h => u.val ≤ r.val)) ⊆ S := by
        intro u hu
        have hule : u.val ≤ r.val := (Finset.mem_filter.mp hu).2
        have hple : (pEmb u).val ≤ (pEmb r).val := by
          rcases lt_or_eq_of_le hule with hlt | heq
          · exact le_of_lt (hp_strict u r hlt)
          · have : u = r := Fin.ext heq; rw [this]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt hple hr⟩
      have hcard_le : (Finset.univ.filter (fun u : Fin h => u.val ≤ r.val)).card = r.val + 1 := by
        have hbij : (Finset.univ.filter (fun u : Fin h => u.val ≤ r.val)).card =
            (Finset.range (r.val + 1)).card := by
          apply Finset.card_bij (fun u _ => u.val)
          · intro u hu; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hu).2; omega)
          · intro u1 _ u2 _ heq; exact Fin.ext heq
          · intro x hx
            have hxlt : x < r.val + 1 := Finset.mem_range.mp hx
            exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, rfl⟩
        rw [hbij, Finset.card_range]
      rw [← hcard_le]
      exact Finset.card_le_card hsub
    · intro hle
      by_contra hnotlt
      have hsub : S ⊆ Finset.univ.filter (fun u : Fin h => u.val < r.val) := by
        intro u hu
        have hult : (pEmb u).val < k.val := (Finset.mem_filter.mp hu).2
        have hur : u.val < r.val := by
          by_contra hge
          have hple : (pEmb r).val ≤ (pEmb u).val := by
            rcases lt_or_eq_of_le (show r.val ≤ u.val by omega) with hlt | heq
            · exact le_of_lt (hp_strict r u hlt)
            · have : r = u := Fin.ext heq; rw [this]
          omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hur⟩
      have hcard_lt : (Finset.univ.filter (fun u : Fin h => u.val < r.val)).card = r.val := by
        have hbij : (Finset.univ.filter (fun u : Fin h => u.val < r.val)).card =
            (Finset.range r.val).card := by
          apply Finset.card_bij (fun u _ => u.val)
          · intro u hu; exact Finset.mem_range.mpr (Finset.mem_filter.mp hu).2
          · intro u1 _ u2 _ heq; exact Fin.ext heq
          · intro x hx
            have hxlt : x < r.val := Finset.mem_range.mp hx
            exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxlt⟩, rfl⟩
        rw [hbij, Finset.card_range]
      have := Finset.card_le_card hsub
      omega
  -- Same phase implies no element of H lies in [x, y)!
  have hsame_phase_nocut : ∀ x y : Fin (n + 1), phase x = phase y →
      ∀ i ∈ H, ¬ (x.val ≤ i.val ∧ i.val < y.val) := by
    intro x y hph i hi ⟨hxi, hiy⟩
    -- i = pEmb r for some r : Fin h
    have hexr : ∃ r : Fin h, pEmb r = i := by
      have hrange := H.range_orderEmbOfFin rfl
      have : i ∈ Set.range pEmb := by rw [hrange]; exact hi
      exact this
    rcases hexr with ⟨r, rfl⟩
    have hr_y : r.val + 1 ≤ phase y := (hphase_iff y r).mp hiy
    have hr_x : ¬ (pEmb r).val < x.val := by omega
    have hr_x' : ¬ r.val + 1 ≤ phase x := mt (hphase_iff x r).mpr hr_x
    omega
  -- Build B0 -> B1 (Fischer inverter) -> B2 (indicators)
  let B0 := Bld.empty M
  let T : Fin h → Nat := fun r => (pEmb r).val
  rcases build_fischer_flex wFalse (by omega) b h hHcard B0 T
    (fun r => by simp [B0, Bld.empty, Bld.size, T, M]; have := (pEmb r).isLt; omega) with
    ⟨B1, notT, h01, hsz1, hnt1, hnotT_lt, hnotT_ev⟩
  rcases build_indicators B1 wTrue (by omega) h T notT
    (fun r => by simp [T, M]; have := (pEmb r).isLt; omega) hnotT_lt with
    ⟨B2, ind, h12, hsz2, hnt2, hind_lt, hind_ev⟩
  have h02 : B0.Ext B2 := h01.trans h12
  -- For each (r : Fin (h + 1), j : Fin m), define S_{r, j} = {k | phase k = r ∧ k ∉ Z ∧ want k j = some true}
  let grp : Fin (h + 1) → Fin m → Finset (Fin (n + 1)) := fun r j =>
    Finset.univ.filter (fun k => phase k = r.val ∧ k ∉ Z ∧ want k j = some true)
  -- Threshold wire for a nonempty grp r j: min' element x_{r,j}, wire = if x=0 then wTrue else x-1
  let threshWire : (r : Fin (h + 1)) → (j : Fin m) → Nat := fun r j =>
    if hne : (grp r j).Nonempty then
      let x := (grp r j).min' hne
      if x.val = 0 then wTrue else x.val - 1
    else wFalse
  have hthresh_lt : ∀ r j, threshWire r j < M := by
    intro r j; dsimp only [threshWire]; split_ifs with hne hx0
    · omega
    · have := ((grp r j).min' hne).isLt; omega
    · omega
  let activePairs : Fin m → List (Nat × Nat) := fun j =>
    ((List.finRange (h + 1)).filter (fun r => decide (grp r j).Nonempty)).map
      (fun r => (ind r, threshWire r j))
  rcases build_all_outputs B2 wFalse (by omega) m activePairs (fun j p hp => by
    rcases List.mem_map.mp hp with ⟨r, _, rfl⟩
    exact ⟨hind_lt r, by have := hthresh_lt r j; omega⟩) with
    ⟨B3, outs, h23, hsz3, hnt3, houts_lt, houts_ev⟩
  -- Bound ∑ j, (activePairs j).length <= min highs (m * (h + 1))!
  have hlen_le_m : (∑ j : Fin m, (activePairs j).length) ≤ m * (h + 1) := by
    calc ∑ j : Fin m, (activePairs j).length
        ≤ ∑ _j : Fin m, (h + 1) := by
          apply Finset.sum_le_sum; intro j _
          dsimp only [activePairs]
          rw [List.length_map]
          calc ((List.finRange (h + 1)).filter _).length ≤ (List.finRange (h + 1)).length :=
                List.length_filter_le _ _
            _ = h + 1 := List.length_finRange
      _ = m * (h + 1) := by simp
  have hlen_le_highs : (∑ j : Fin m, (activePairs j).length) ≤ highs := by
    -- Each (j, r) with (grp r j).Nonempty picks a witness k = (grp r j).min' _ with phase k = r and want k j = some true!
    -- Map (j, r) ↦ ((grp r j).min' _, j) is injective into {(k, j) | want k j = some true}!
    let activeSet : Finset (Fin m × Fin (h + 1)) :=
      Finset.univ.filter (fun jr => (grp jr.2 jr.1).Nonempty)
    have hsum_eq2 : (∑ j : Fin m, (activePairs j).length) = activeSet.card := by
      have hcard_j : ∀ j : Fin m, (activePairs j).length =
          (activeSet.filter (fun p => p.1 = j)).card := by
        intro j
        dsimp only [activePairs]
        rw [List.length_map]
        have hnd : ((List.finRange (h + 1)).filter (fun r => decide (grp r j).Nonempty)).Nodup :=
          List.Nodup.filter _ (List.nodup_finRange (h + 1))
        rw [← List.toFinset_card_of_nodup hnd]
        apply Finset.card_bij (fun r _ => (j, r))
        · intro r hr
          simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
            decide_eq_true_eq] at hr
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩
        · intro r1 _ r2 _ heq; exact congrArg Prod.snd heq
        · intro ⟨j', r⟩ hmem
          have hj' : j' = j := (Finset.mem_filter.mp hmem).2
          subst hj'
          have hne : (grp r j').Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
          exact ⟨r, by simp [List.mem_finRange, hne], rfl⟩
      simp_rw [hcard_j]
      rw [← Finset.card_biUnion]
      · congr 1; ext ⟨j, r⟩; simp
      · intro j1 _ j2 _ hne
        exact Finset.disjoint_left.mpr (fun p h1 h2 =>
          hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
    let highSet : Finset (Fin (n + 1) × Fin m) :=
      Finset.univ.filter (fun kj => want kj.1 kj.2 = some true)
    have hhigh_eq : highs = highSet.card := by
      dsimp only [highs]
      have hcard_k : ∀ k : Fin (n + 1),
          ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card =
          (highSet.filter (fun p => p.1 = k)).card := by
        intro k
        apply Finset.card_bij (fun j _ => (k, j))
        · intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩, rfl⟩
        · intro j1 _ j2 _ heq; exact congrArg Prod.snd heq
        · intro ⟨k', j⟩ hmem
          have hk' : k' = k := (Finset.mem_filter.mp hmem).2
          subst hk'
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2⟩, rfl⟩
      simp_rw [hcard_k]
      rw [← Finset.card_biUnion]
      · congr 1; ext ⟨k, j⟩; simp
      · intro k1 _ k2 _ hne
        exact Finset.disjoint_left.mpr (fun p h1 h2 =>
          hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
    rw [hsum_eq2, hhigh_eq]
    apply Finset.card_le_card_of_injOn (fun jr =>
      if hne : (grp jr.2 jr.1).Nonempty then ((grp jr.2 jr.1).min' hne, jr.1) else (⟨0, Nat.zero_lt_succ n⟩, jr.1))
    · intro ⟨j, r⟩ hmem
      have hne : (grp r j).Nonempty := (Finset.mem_filter.mp hmem).2
      dsimp only; rw [dif_pos hne]
      have hx := Finset.min'_mem (grp r j) hne
      have hwant : want ((grp r j).min' hne) j = some true := (Finset.mem_filter.mp hx).2.2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwant⟩
    · intro ⟨j1, r1⟩ h1 ⟨j2, r2⟩ h2 heq
      have hne1 : (grp r1 j1).Nonempty := (Finset.mem_filter.mp h1).2
      have hne2 : (grp r2 j2).Nonempty := (Finset.mem_filter.mp h2).2
      dsimp only at heq; rw [dif_pos hne1, dif_pos hne2] at heq
      have hj : j1 = j2 := congrArg Prod.snd heq
      subst hj
      have hx : (grp r1 j1).min' hne1 = (grp r2 j1).min' hne2 := congrArg Prod.fst heq
      have hph1 : phase ((grp r1 j1).min' hne1) = r1.val :=
        (Finset.mem_filter.mp (Finset.min'_mem (grp r1 j1) hne1)).2.1
      have hph2 : phase ((grp r2 j1).min' hne2) = r2.val :=
        (Finset.mem_filter.mp (Finset.min'_mem (grp r2 j1) hne2)).2.1
      rw [hx] at hph1
      exact Prod.ext rfl (Fin.ext (hph1.symm.trans hph2))
  -- Assemble circuit C and taps a
  let C := B3.toCircuit
  let a : Fin m → Fin (n + 2 + C.size) := fun j => ⟨outs j, houts_lt j⟩
  refine ⟨C, a, B3.hF2, B3.hRB, by simp [C, Bld.toCircuit], ?_, ?_, ?_⟩
  · -- notCount C <= b
    change B3.nots ≤ b
    have hb0 : B0.nots = 0 := by simp [B0, Bld.empty, Bld.nots, Bld.toCircuit, notCount]
    omega
  · -- bad C a ⊆ Z
    intro k ⟨j, v, hwkv, hneq⟩
    by_contra hkZ
    apply hneq
    let inp := mkInput n k
    have hln : inp.length = M := mkInput_length n k
    have hwF_ev : inp.getD wFalse false = false := mkInput_getD_false n k
    have hwT_ev : inp.getD wTrue false = true := mkInput_getD_true n k
    have hTev : ∀ r : Fin h, (B0.toCircuit.wires inp).getD (T r) false = decide (r.val + 1 ≤ phase k) := by
      intro r
      rw [wires_getD_input _ _ (T r) (by rw [hln]; simp [T, M]; have := (pEmb r).isLt; omega)]
      simp only [T]
      rw [mkInput_getD_lt n k (pEmb r).val (pEmb r).isLt]
      exact decide_eq_decide.mpr (hphase_iff k r)
    have hnotTev : ∀ r : Fin h, (B1.toCircuit.wires inp).getD (notT r) false = !(decide (r.val + 1 ≤ phase k)) :=
      hnotT_ev inp hln hwF_ev (phase k) (hphase_le k) hTev
    have hind_k : ∀ r : Fin (h + 1), (B2.toCircuit.wires inp).getD (ind r) false = decide (phase k = r.val) :=
      hind_ev inp hln hwT_ev (phase k) (hphase_le k)
        (fun r => by rw [h01.wires_eq inp hln (T r) (by simp [B0, Bld.empty, Bld.size, T, M]; have := (pEmb r).isLt; omega)]; exact hTev r)
        hnotTev
    have hout_k : (C.wires inp).getD (a j).val false =
        (activePairs j).any (fun p => (B2.toCircuit.wires inp).getD p.1 false &&
                                      (B2.toCircuit.wires inp).getD p.2 false) :=
      houts_ev inp hln hwF_ev j
    rw [hout_k]
    let rk : Fin (h + 1) := ⟨phase k, by have := hphase_le k; omega⟩
    have hthresh_ev : ∀ r : Fin (h + 1), (hne : (grp r j).Nonempty) →
        (B2.toCircuit.wires inp).getD (threshWire r j) false = decide (((grp r j).min' hne).val ≤ k.val) := by
      intro r hne
      rw [wires_getD_input _ _ (threshWire r j) (by rw [hln]; exact hthresh_lt r j)]
      dsimp only [threshWire]
      rw [dif_pos hne]
      split_ifs with hx0
      · rw [hwT_ev, hx0]; simp
      · have hlt_n : ((grp r j).min' hne).val - 1 < n := by
          have := ((grp r j).min' hne).isLt; omega
        rw [mkInput_getD_lt n k _ hlt_n]
        exact decide_eq_decide.mpr (by omega)
    cases v with
    | true =>
      -- k ∈ grp rk j, so (grp rk j).Nonempty, min' <= k, ind rk = true, thresh = true -> any = true!
      have hk_mem : k ∈ grp rk j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hkZ, hwkv⟩
      have hne : (grp rk j).Nonempty := ⟨k, hk_mem⟩
      rw [List.any_eq_true]
      refine ⟨(ind rk, threshWire rk j), ?_, ?_⟩
      · exact List.mem_map.mpr ⟨rk, List.mem_filter.mpr ⟨List.mem_finRange rk, decide_eq_true hne⟩, rfl⟩
      · rw [hind_k rk, hthresh_ev rk hne]
        have hmin_le : ((grp rk j).min' hne).val ≤ k.val := Finset.min'_le (grp rk j) k hk_mem
        simp [rk, hmin_le]
    | false =>
      -- Need any = false, i.e., for every r in activePairs j, ind r && thresh r = false!
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      rcases hany with ⟨p, hp, hpt⟩
      rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
      have hne : (grp r j).Nonempty := of_decide_eq_true (List.mem_filter.mp hr).2
      rw [hind_k r, hthresh_ev r hne, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hpt
      rcases hpt with ⟨hph_eq, hmin_le⟩
      let x := (grp r j).min' hne
      have hx_mem : x ∈ grp r j := Finset.min'_mem (grp r j) hne
      have hx_ph : phase x = r.val := (Finset.mem_filter.mp hx_mem).2.1
      have hx_nZ : x ∉ Z := (Finset.mem_filter.mp hx_mem).2.2.1
      have hx_w : want x j = some true := (Finset.mem_filter.mp hx_mem).2.2.2
      have hx_lt_k : x < k := by
        rcases lt_or_eq_of_le hmin_le with hlt | heq
        · exact hlt
        · have hxek : x = k := Fin.ext heq
          rw [hxek, hwkv] at hx_w; cases hx_w
      rcases hcov x k j hx_lt_k hx_w hwkv with hxZ | hkZ' | ⟨i, hiH, hxi, hik⟩
      · exact hx_nZ hxZ
      · exact hkZ hkZ'
      · exact hsame_phase_nocut x k (hx_ph.trans hph_eq.symm) i hiH ⟨hxi, hik⟩
  · -- C.size <= 2 * min highs (m * (h + 1)) + 7 * h + 2
    change B3.size ≤ 2 * min highs (m * (h + 1)) + 7 * h + 2
    have hb0 : B0.size = 0 := rfl
    have hmin : (∑ j : Fin m, (activePairs j).length) ≤ min highs (m * (h + 1)) :=
      le_min hlen_le_highs hlen_le_m
    omega

-- ============================================================================
-- Main proof matching the exact theorem statement
-- ============================================================================

private lemma finset_sum_mono_subset {α : Type*} {s t : Finset α} (h : s ⊆ t) (w : α → Nat) :
    s.sum w ≤ t.sum w :=
  Finset.sum_le_sum_of_subset h

private theorem main_proof :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (n m b : Nat) (want : Fin (n+1) → Fin m → Option Bool),
      let A := Fin (n+1)
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let input := fun (k : A) => List.ofFn (fun i : Fin n => decide (i.val < k.val)) ++ [false,true]
      let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
      let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
        PEqualNP.NotBracket.notCount C ≤ b
      let bad := fun (C : Circ) (a : taps C) => (Finset.univ : Finset A).filter (fun k =>
        ∃ (j : Fin m) (v : Bool), want k j = some v ∧
          (C.wires (input k)).getD (a j).val false ≠ v)
      let highs := (Finset.univ : Finset A).sum (fun k =>
        ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card)
      let cover := fun (H : Finset (Fin n)) (Z : Finset A) =>
        ∀ (x y : A) (j : Fin m), x < y → want x j = some true → want y j = some false →
          x ∈ Z ∨ y ∈ Z ∨ ∃ i ∈ H, x.val ≤ i.val ∧ i.val < y.val
      ((∀ (w : A → Nat) (K : Nat),
        (∃ (C : Circ) (a : taps C), valid C ∧ (bad C a).sum w ≤ K) ↔
        ∃ (H : Finset (Fin n)) (Z : Finset A), H.card ≤ 2^b-1 ∧ Z.sum w ≤ K ∧ cover H Z)) ∧
      ∀ (H : Finset (Fin n)) (Z : Finset A), H.card ≤ 2^b-1 → cover H Z →
        ∃ (C : Circ) (a : taps C), valid C ∧ bad C a ⊆ Z ∧
          C.size ≤ 2*(min highs (m*(H.card+1)))+7*H.card+2 := by
  intro n m b want
  -- First prove the constructive part (which gives both parts!)
  have hbuild : ∀ (H : Finset (Fin n)) (Z : Finset (Fin (n + 1))),
      H.card ≤ 2 ^ b - 1 →
      (∀ (x y : Fin (n + 1)) (j : Fin m), x < y → want x j = some true → want y j = some false →
        x ∈ Z ∨ y ∈ Z ∨ ∃ i ∈ H, x.val ≤ i.val ∧ i.val < y.val) →
      ∃ (C : Circuit) (a : Fin m → Fin (n + 2 + C.size)),
        (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b) ∧
        (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
         (Finset.univ : Finset (Fin (n + 1))).filter (fun k =>
           ∃ (j : Fin m) (v : Bool), want k j = some v ∧ (C.wires (mkInput n k)).getD (a j).val false ≠ v) ⊆ Z) ∧
        C.size ≤ 2 * min ((Finset.univ : Finset (Fin (n + 1))).sum (fun k =>
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card))
          (m * (H.card + 1)) + 7 * H.card + 2 := by
    intro H Z hHc hcov
    rcases upper_bound_from_cover want H Z hHc hcov with ⟨C, a, hF2, hRB, hout, hnb, hsub, hsz⟩
    refine ⟨C, a, ⟨hF2, hRB, hout, hnb⟩, ?_, ?_⟩
    · intro k hk
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      exact hsub k (Finset.mem_filter.mp hk).2
    · have hhigh_eq : (Finset.univ : Finset (Fin (n + 1))).sum (fun k =>
          ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card) =
          (Finset.univ : Finset (Fin (n + 1))).sum (fun k =>
            letI : ∀ p : Prop, Decidable p := Classical.propDecidable
            ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1; ext j; simp
      rwa [← hhigh_eq]
  refine ⟨?_, hbuild⟩
  intro w K
  constructor
  · rintro ⟨C, a, ⟨hF2, hRB, _hout, hnb⟩, hsum⟩
    rcases lower_bound_cuts want C a hF2 hRB hnb with ⟨H, hHc, hcov⟩
    refine ⟨H, (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      (Finset.univ : Finset (Fin (n + 1))).filter (fun k =>
        ∃ (j : Fin m) (v : Bool), want k j = some v ∧ (C.wires (mkInput n k)).getD (a j).val false ≠ v)),
      hHc, hsum, ?_⟩
    intro x y j hxy hwx hwy
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    rcases hcov x y j hxy hwx hwy with hx | hy | hcut
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩))
    · exact Or.inr (Or.inr hcut)
  · rintro ⟨H, Z, hHc, hZsum, hcov⟩
    rcases hbuild H Z hHc hcov with ⟨C, a, hval, hsub, _hsz⟩
    exact ⟨C, a, hval, le_trans (finset_sum_mono_subset hsub w) hZsum⟩

end PEqualNP.Outside.L_meta_53160

theorem PEqualNP.Outside.L_meta_53160 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m b : Nat) (want : Fin (n+1) → Fin m → Option Bool),
  let A := Fin (n+1)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let input := fun (k : A) => List.ofFn (fun i : Fin n => decide (i.val < k.val)) ++ [false,true]
  let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let bad := fun (C : Circ) (a : taps C) => (Finset.univ : Finset A).filter (fun k =>
    ∃ (j : Fin m) (v : Bool), want k j = some v ∧
      (C.wires (input k)).getD (a j).val false ≠ v)
  let highs := (Finset.univ : Finset A).sum (fun k =>
    ((Finset.univ : Finset (Fin m)).filter (fun j => want k j = some true)).card)
  let cover := fun (H : Finset (Fin n)) (Z : Finset A) =>
    ∀ (x y : A) (j : Fin m), x < y → want x j = some true → want y j = some false →
      x ∈ Z ∨ y ∈ Z ∨ ∃ i ∈ H, x.val ≤ i.val ∧ i.val < y.val
  ((∀ (w : A → Nat) (K : Nat),
    (∃ (C : Circ) (a : taps C), valid C ∧ (bad C a).sum w ≤ K) ↔
    ∃ (H : Finset (Fin n)) (Z : Finset A), H.card ≤ 2^b-1 ∧ Z.sum w ≤ K ∧ cover H Z)) ∧
  ∀ (H : Finset (Fin n)) (Z : Finset A), H.card ≤ 2^b-1 → cover H Z →
    ∃ (C : Circ) (a : taps C), valid C ∧ bad C a ⊆ Z ∧
      C.size ≤ 2*(min highs (m*(H.card+1)))+7*H.card+2 :=
  PEqualNP.Outside.L_meta_53160.main_proof
