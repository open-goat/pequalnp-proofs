import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1364

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

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

-- ============================================================================
-- Subset input encoding and monotonicity
-- ============================================================================

private noncomputable def mkInput {n : Nat} (x : Finset (Fin n)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

private lemma mkInput_length {n : Nat} (x : Finset (Fin n)) :
    (mkInput x).length = n + 2 := by
  unfold mkInput; simp

private lemma mkInput_getD_lt {n : Nat} (x : Finset (Fin n)) (i : Fin n) :
    (mkInput x).getD i.val false = decide (i ∈ x) := by
  unfold mkInput
  have hlen : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j ∈ x))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact i.isLt),
      List.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, Fin.eta]
  by_cases h : i ∈ x <;> simp [h]

private lemma mkInput_getD_false {n : Nat} (x : Finset (Fin n)) :
    (mkInput x).getD n false = false := by
  unfold mkInput
  have hlen : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j ∈ x))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

private lemma mkInput_getD_true {n : Nat} (x : Finset (Fin n)) :
    (mkInput x).getD (n + 1) false = true := by
  unfold mkInput
  have hlen : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j ∈ x))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen,
      show n + 1 - n = 1 by omega]
  rfl

private def listLe (l1 l2 : List Bool) : Prop :=
  l1.length = l2.length ∧ ∀ i, i < l1.length → l1.getD i false = true → l2.getD i false = true

private lemma mkInput_listLe {n : Nat} {x y : Finset (Fin n)} (h : x ⊆ y) :
    listLe (mkInput x) (mkInput y) := by
  refine ⟨by rw [mkInput_length, mkInput_length], ?_⟩
  intro i hi ht
  rw [mkInput_length] at hi
  by_cases hin : i < n
  · rw [mkInput_getD_lt x ⟨i, hin⟩] at ht
    rw [mkInput_getD_lt y ⟨i, hin⟩]
    have hmem : (⟨i, hin⟩ : Fin n) ∈ x := of_decide_eq_true ht
    exact decide_eq_true (h hmem)
  · have : i = n ∨ i = n + 1 := by omega
    rcases this with rfl | rfl
    · rw [mkInput_getD_false] at ht; cases ht
    · rw [mkInput_getD_true]

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

-- ============================================================================
-- Helper circuit builders: monomials, OR of list, AND of two wires
-- ============================================================================

private lemma build_monomial {n : Nat} (B0 : Bld (n + 2)) (S : Finset (Fin n)) :
    ∃ (B1 : Bld (n + 2)) (wOut : Nat),
      B0.Ext B1 ∧
      B1.nots = B0.nots ∧
      wOut < (n + 2) + B1.size ∧
      (∀ x : Finset (Fin n),
        (B1.toCircuit.wires (mkInput x)).getD wOut false = decide (S ⊆ x)) := by
  induction S using Finset.induction_on generalizing B0 with
  | empty =>
    refine ⟨B0, n + 1, Bld.Ext.refl B0, rfl, by omega, ?_⟩
    intro x
    rw [wires_getD_input _ _ (n + 1) (by rw [mkInput_length]; omega), mkInput_getD_true]
    simp
  | @insert j t hj ih =>
    rcases ih B0 with ⟨B1, wT, h01, hnt1, hwT_lt, hwT_ev⟩
    let pA := B1.mkAnd j.val wT (by have := j.isLt; omega) hwT_lt
    let B2 := pA.1; let wA := pA.2
    have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
    have hnt2 : B2.nots = B1.nots := Bld.mkAnd_nots _ _ _ _ _
    have hwA_lt : wA < (n + 2) + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    refine ⟨B2, wA, h01.trans h12, by omega, hwA_lt, ?_⟩
    intro x
    rw [Bld.mkAnd_eval _ _ _ _ _ (mkInput x) (mkInput_length x),
        wires_getD_input _ _ j.val (by rw [mkInput_length]; omega),
        mkInput_getD_lt x j, hwT_ev x]
    by_cases hjx : j ∈ x <;> by_cases htx : t ⊆ x <;> simp [hjx, htx, Finset.insert_subset_iff]

private lemma build_or_list {M : Nat} (B0 : Bld M) (wFalse : Nat) (hwF : wFalse < M)
    (ws : List Nat) (hws : ∀ w ∈ ws, w < M + B0.size) :
    ∃ (B1 : Bld M) (wOut : Nat),
      B0.Ext B1 ∧ B1.nots = B0.nots ∧ wOut < M + B1.size ∧
      (∀ inp, inp.length = M → inp.getD wFalse false = false →
        (B1.toCircuit.wires inp).getD wOut false =
          ws.any (fun w => (B0.toCircuit.wires inp).getD w false)) := by
  induction ws generalizing B0 with
  | nil =>
    refine ⟨B0, wFalse, Bld.Ext.refl B0, rfl, by omega, ?_⟩
    intro inp hln hwf
    rw [wires_getD_input _ _ wFalse (by omega), hwf]; rfl
  | cons hd tl ih =>
    have hhd : hd < M + B0.size := hws hd (by simp)
    rcases ih B0 (fun w hw => hws w (List.mem_cons_of_mem hd hw)) with
      ⟨B1, wTl, h01, hnt1, hwT_lt, hwT_ev⟩
    let pO := B1.mkOr hd wTl (by have := h01.size_le; omega) hwT_lt
    let B2 := pO.1; let wO := pO.2
    have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
    have hnt2 : B2.nots = B1.nots := Bld.mkOr_nots _ _ _ _ _
    have hwO_lt : wO < M + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
    refine ⟨B2, wO, h01.trans h12, by omega, hwO_lt, ?_⟩
    intro inp hln hwf
    rw [Bld.mkOr_eval _ _ _ _ _ inp hln, h01.wires_eq inp hln hd hhd, hwT_ev inp hln hwf]
    simp

private lemma build_upward_set {n : Nat} (B0 : Bld (n + 2)) (U : Finset (Finset (Fin n))) :
    ∃ (B1 : Bld (n + 2)) (wOut : Nat),
      B0.Ext B1 ∧ B1.nots = B0.nots ∧ wOut < (n + 2) + B1.size ∧
      (∀ x : Finset (Fin n),
        (B1.toCircuit.wires (mkInput x)).getD wOut false = decide (∃ y ∈ U, y ⊆ x)) := by
  have hbuild_list : ∀ (l : List (Finset (Fin n))) (B : Bld (n + 2)),
      ∃ (B' : Bld (n + 2)) (ws : List Nat),
        B.Ext B' ∧ B'.nots = B.nots ∧ (∀ w ∈ ws, w < (n + 2) + B'.size) ∧
        (∀ x : Finset (Fin n),
          ws.any (fun w => (B'.toCircuit.wires (mkInput x)).getD w false) =
          l.any (fun y => decide (y ⊆ x))) := by
    intro l
    induction l with
    | nil =>
      intro B
      exact ⟨B, [], Bld.Ext.refl B, rfl, (fun _ h => by cases h), fun _ => rfl⟩
    | cons hd tl ih =>
      intro B
      rcases build_monomial B hd with ⟨B1, wHd, h01, hnt1, hwH_lt, hwH_ev⟩
      rcases ih B1 with ⟨B2, wsTl, h12, hnt2, hws_lt, hws_ev⟩
      refine ⟨B2, wHd :: wsTl, h01.trans h12, by omega, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | htl
        · have := h12.size_le; omega
        · exact hws_lt w htl
      · intro x
        simp only [List.any_cons]
        rw [h12.wires_eq (mkInput x) (mkInput_length x) wHd hwH_lt, hwH_ev x, hws_ev x]
  rcases hbuild_list U.toList B0 with ⟨B1, ws, h01, hnt1, hws_lt, hws_ev⟩
  rcases build_or_list B1 n (by omega) ws hws_lt with ⟨B2, wOut, h12, hnt2, hwO_lt, hwO_ev⟩
  refine ⟨B2, wOut, h01.trans h12, by omega, hwO_lt, ?_⟩
  intro x
  rw [hwO_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x), hws_ev x]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Finset.mem_toList, decide_eq_true_eq]

-- ============================================================================
-- Poset Q = Fin (2^b) × (Fin a → Bool) and characterization of circuit fit
-- ============================================================================

private abbrev QState (a q : Nat) := Fin q × (Fin a → Bool)

private def qLe {a q : Nat} (p1 p2 : QState a q) : Prop :=
  p1.1.val < p2.1.val ∨ (p1.1 = p2.1 ∧ ∀ i : Fin a, p1.2 i = true → p2.2 i = true)

private def qLt {a q : Nat} (p1 p2 : QState a q) : Prop :=
  qLe p1 p2 ∧ p1 ≠ p2

private def qNext {a q : Nat} (p1 p2 : QState a q) : Prop :=
  qLt p1 p2 ∧ ¬ ∃ z : QState a q, qLt p1 z ∧ qLt z p2

private instance instDecidableQLe {a q : Nat} (p1 p2 : QState a q) : Decidable (qLe p1 p2) := by
  unfold qLe; infer_instance

private instance instDecidableQLt {a q : Nat} (p1 p2 : QState a q) : Decidable (qLt p1 p2) := by
  unfold qLt; infer_instance

private instance instDecidableQNext {a q : Nat} (p1 p2 : QState a q) : Decidable (qNext p1 p2) := by
  unfold qNext; infer_instance

private lemma qLe_refl {a q : Nat} (p : QState a q) : qLe p p :=
  Or.inr ⟨rfl, fun _ h => h⟩

private lemma qLe_trans {a q : Nat} {p1 p2 p3 : QState a q}
    (h12 : qLe p1 p2) (h23 : qLe p2 p3) : qLe p1 p3 := by
  rcases h12 with hlt1 | ⟨heq1, hm1⟩
  · rcases h23 with hlt2 | ⟨heq2, _⟩
    · exact Or.inl (Nat.lt_trans hlt1 hlt2)
    · exact Or.inl (by rw [← heq2]; exact hlt1)
  · rcases h23 with hlt2 | ⟨heq2, hm2⟩
    · exact Or.inl (by rw [heq1]; exact hlt2)
    · exact Or.inr ⟨heq1.trans heq2, fun i hi => hm2 i (hm1 i hi)⟩

private lemma qLe_antisymm {a q : Nat} {p1 p2 : QState a q}
    (h12 : qLe p1 p2) (h21 : qLe p2 p1) : p1 = p2 := by
  rcases h12 with hlt1 | ⟨heq1, hm1⟩
  · rcases h21 with hlt2 | ⟨heq2, _⟩
    · omega
    · rw [heq2] at hlt1; omega
  · rcases h21 with hlt2 | ⟨_, hm2⟩
    · rw [heq1] at hlt2; omega
    · apply Prod.ext heq1
      funext i
      cases h1 : p1.2 i <;> cases h2 : p2.2 i
      · rfl
      · have := hm2 i h2; rw [h1] at this; cases this
      · have := hm1 i h1; rw [h2] at this; cases this
      · rfl

private lemma qLt_trans {a q : Nat} {p1 p2 p3 : QState a q}
    (h12 : qLt p1 p2) (h23 : qLt p2 p3) : qLt p1 p3 :=
  ⟨qLe_trans h12.1 h23.1, fun heq => h12.2 (qLe_antisymm h12.1 (heq ▸ h23.1))⟩

private def popCnt {a : Nat} (w : Fin a → Bool) : Nat :=
  ((Finset.univ : Finset (Fin a)).filter (fun i => w i = true)).card

private lemma popCnt_le {a : Nat} (w : Fin a → Bool) : popCnt w ≤ a := by
  unfold popCnt
  calc ((Finset.univ : Finset (Fin a)).filter (fun i => w i = true)).card
      ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_filter_le _ _
    _ = a := Finset.card_fin a

private lemma popCnt_lt_of_mono_ne {a : Nat} {w1 w2 : Fin a → Bool}
    (hm : ∀ i, w1 i = true → w2 i = true) (hne : w1 ≠ w2) : popCnt w1 < popCnt w2 := by
  unfold popCnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm i (Finset.mem_filter.mp hi).2⟩
  · intro heq
    apply hne; funext i
    have hiff : w1 i = true ↔ w2 i = true := by
      have := Finset.ext_iff.mp heq i
      simpa using this
    cases h1 : w1 i <;> cases h2 : w2 i <;> simp_all

private def qMeas {a q : Nat} (p : QState a q) : Nat :=
  (q - 1 - p.1.val) * (a + 1) + (a - popCnt p.2)

private lemma qMeas_lt_of_qLt {a q : Nat} {p1 p2 : QState a q} (h : qLt p1 p2) :
    qMeas p2 < qMeas p1 := by
  unfold qMeas
  have hp1 := p1.1.isLt
  have hp2 := p2.1.isLt
  have hc1 := popCnt_le p1.2
  have hc2 := popCnt_le p2.2
  rcases h.1 with hlt | ⟨heq, hm⟩
  · have hmul : (q - 1 - p2.1.val + 1) * (a + 1) ≤ (q - 1 - p1.1.val) * (a + 1) :=
      Nat.mul_le_mul_right (a + 1) (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  · have hne : p1.2 ≠ p2.2 := fun hw => h.2 (Prod.ext heq hw)
    have hclt := popCnt_lt_of_mono_ne hm hne
    rw [heq]; omega

private lemma exists_qNext_between {a q : Nat} {p1 p2 : QState a q} (h : qLt p1 p2) :
    ∃ r : QState a q, qNext p1 r ∧ qLe r p2 := by
  induction hm : qMeas p1 - qMeas p2 using Nat.strong_induction_on generalizing p2 with
  | ind d ih =>
    by_cases hex : ∃ z : QState a q, qLt p1 z ∧ qLt z p2
    · rcases hex with ⟨z, h1z, hzp2⟩
      have hm1 := qMeas_lt_of_qLt h1z
      have hm2 := qMeas_lt_of_qLt hzp2
      rcases ih (qMeas p1 - qMeas z) (by omega) h1z rfl with ⟨r, hrn, hrz⟩
      exact ⟨r, hrn, qLe_trans hrz hzp2.1⟩
    · exact ⟨p2, ⟨h, hex⟩, qLe_refl p2⟩

-- Outward forest definition and FitCircuit / FitPoset equivalence!
private def IsForest {n : Nat} (V : Finset (Finset (Fin n))) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y

private def FitCirc (n a b : Nat) (S : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → (Fin a → Bool) → Prop) : Prop :=
  ∃ (C : Circuit) (tap : Fin a → Nat),
    FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
    (∀ i, tap i < n + 2 + C.size) ∧
    ∀ x ∈ S, ok x (fun i => (C.wires (mkInput x)).getD (tap i) false)

private def FitPoset {n a q : Nat} (S : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → (Fin a → Bool) → Prop) (p : QState a q) : Prop :=
  ∃ g : Finset (Fin n) → QState a q,
    (∀ x ∈ S, qLe p (g x) ∧ ok x (g x).2) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → qLe (g x) (g y)

private lemma fitCirc_to_fitPoset {n a b : Nat} {S : Finset (Finset (Fin n))}
    {ok : Finset (Fin n) → (Fin a → Bool) → Prop}
    (hfor : IsForest S) (hfit : FitCirc n a b S ok) :
    FitPoset (q := 2 ^ b) S ok (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, fun _ => false) := by
  rcases hfit with ⟨C, tap, hF2, hRB, _hout, hnb, htap_lt, hok⟩
  let M := n + 2
  let nv : Finset (Fin n) → Fin (notIdxs C).length → Bool := fun x => notVec C M (mkInput x)
  let anc : Finset (Fin n) → Finset (Finset (Fin n)) := fun x => S.filter (fun y => y ⊆ x)
  have hanc_card_pos : ∀ x ∈ S, 1 ≤ ((anc x).image nv).card := by
    intro x hx
    exact Finset.card_pos.mpr ⟨nv x, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, Finset.Subset.refl x⟩, rfl⟩⟩
  have hanc_card_le : ∀ x ∈ S, ((anc x).image nv).card ≤ 2 ^ b := by
    intro x _
    calc ((anc x).image nv).card
        ≤ (Finset.univ : Finset (Fin (notIdxs C).length → Bool)).card := Finset.card_le_univ _
      _ = 2 ^ (notIdxs C).length := by simp
      _ ≤ 2 ^ b := by rw [notIdxs_length]; exact Nat.pow_le_pow_right (by omega) hnb
  let lvl : Finset (Fin n) → Fin (2 ^ b) := fun x =>
    if hx : x ∈ S then ⟨((anc x).image nv).card - 1, by have := hanc_card_pos x hx; have := hanc_card_le x hx; omega⟩
    else ⟨0, Nat.pos_of_ne_zero (by positivity)⟩
  let val : Finset (Fin n) → Fin a → Bool := fun x i => (C.wires (mkInput x)).getD (tap i) false
  refine ⟨fun x => (lvl x, val x), ?_, ?_⟩
  · intro x hx
    refine ⟨?_, hok x hx⟩
    by_cases hl0 : (lvl x).val = 0
    · right
      refine ⟨Fin.ext (by dsimp only; omega), fun i hi => by cases hi⟩
    · left; dsimp only; omega
  · intro x hx y hy hxy
    have hanc_sub : anc x ⊆ anc y := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz'.1, Finset.Subset.trans hz'.2 hxy⟩
    have himg_sub : (anc x).image nv ⊆ (anc y).image nv := Finset.image_subset_image hanc_sub
    have hcard_le := Finset.card_le_card himg_sub
    have hpos_x := hanc_card_pos x hx
    have hpos_y := hanc_card_pos y hy
    have hlx : (lvl x).val = ((anc x).image nv).card - 1 := by dsimp only [lvl]; rw [dif_pos hx]
    have hly : (lvl y).val = ((anc y).image nv).card - 1 := by dsimp only [lvl]; rw [dif_pos hy]
    by_cases hlt : (lvl x).val < (lvl y).val
    · exact Or.inl hlt
    · have hcard_eq : ((anc x).image nv).card = ((anc y).image nv).card := by omega
      have himg_eq : (anc x).image nv = (anc y).image nv := Finset.eq_of_subset_of_card_le himg_sub (by omega)
      have hnvy_mem : nv y ∈ (anc x).image nv := by
        rw [himg_eq]
        exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, Finset.Subset.refl y⟩, rfl⟩
      rcases Finset.mem_image.mp hnvy_mem with ⟨z, hz_anc, hnv_zy⟩
      have hzx : z ⊆ x := (Finset.mem_filter.mp hz_anc).2
      have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
        (mkInput z) (mkInput x) (mkInput y)
        (mkInput_length z) (mkInput_length x) (mkInput_length y)
        (mkInput_listLe hzx) (mkInput_listLe hxy) hnv_zy).2
      have hnv_xy : nv x = nv y := hsw.trans hnv_zy
      right
      refine ⟨Fin.ext (by dsimp only; omega), ?_⟩
      intro i hi
      exact wires_mono_of_notVec_eq C hF2 hRB (mkInput x) (mkInput y)
        (mkInput_length x) (mkInput_length y) (mkInput_listLe hxy) hnv_xy (tap i) (htap_lt i) hi

private lemma fitPoset_to_fitCirc {n a b : Nat} {S : Finset (Finset (Fin n))}
    {ok : Finset (Fin n) → (Fin a → Bool) → Prop}
    (hpos : FitPoset (q := 2 ^ b) S ok (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, fun _ => false)) :
    FitCirc n a b S ok := by
  rcases hpos with ⟨g, hok, hmono⟩
  let M := n + 2
  let q := 2 ^ b
  let h := q - 1
  have hq_pos : 1 ≤ q := Nat.one_le_pow b 2 (by omega)
  -- Step 1: Build threshold wires T : Fin h → Nat with T u(x) = decide (u.val + 1 ≤ (g x).1.val) for x ∈ S!
  have build_T : ∀ (k : Nat), k ≤ h →
      ∃ (B1 : Bld M) (T : Fin k → Nat),
        B1.nots = 0 ∧ (∀ u : Fin k, T u < M + B1.size) ∧
        (∀ x ∈ S, ∀ u : Fin k, (B1.toCircuit.wires (mkInput x)).getD (T u) false = decide (u.val + 1 ≤ (g x).1.val)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Bld.empty M, Fin.elim0, rfl, fun u => Fin.elim0 u, fun _ _ u => Fin.elim0 u⟩
    | succ k ihk =>
      intro hkh
      rcases ihk (by omega) with ⟨B1, T1, hnt1, hT1_lt, hT1_ev⟩
      let U : Finset (Finset (Fin n)) := S.filter (fun y => k + 1 ≤ (g y).1.val)
      rcases build_upward_set B1 U with ⟨B2, wK, h12, hnt2, hwK_lt, hwK_ev⟩
      refine ⟨B2, fun u => if hu : u.val < k then T1 ⟨u.val, hu⟩ else wK, by omega, ?_, ?_⟩
      · intro u; dsimp only; split_ifs with hu
        · have := hT1_lt ⟨u.val, hu⟩; have := h12.size_le; omega
        · exact hwK_lt
      · intro x hx u; dsimp only; split_ifs with hu
        · rw [h12.wires_eq (mkInput x) (mkInput_length x) _ (hT1_lt ⟨u.val, hu⟩)]
          exact hT1_ev x hx ⟨u.val, hu⟩
        · have huk : u.val = k := by omega
          rw [hwK_ev x, huk]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, U, Finset.mem_filter]
          constructor
          · rintro ⟨y, ⟨hyS, hyk⟩, hyx⟩
            have hm := hmono y hyS x hx hyx
            rcases hm with hlt | ⟨heq, _⟩
            · omega
            · rw [← heq]; exact hyk
          · intro hxk
            exact ⟨x, ⟨hx, hxk⟩, Finset.Subset.refl x⟩
  rcases build_T h (le_refl h) with ⟨B1, T, hnt1, hT_lt, hT_ev⟩
  -- Step 2: Fischer inverter notT : Fin h → Nat with ≤ b NOT gates!
  rcases build_fischer_flex n (by omega) b h (le_refl h) B1 T hT_lt with
    ⟨B2, notT, h12, _hsz2, hnt2, hnotT_lt, hnotT_ev⟩
  -- Step 3: Build level indicators ind : Fin q → Nat!
  have build_ind : ∀ (k : Nat), k ≤ q →
      ∃ (B3 : Bld M) (ind : Fin k → Nat),
        B2.Ext B3 ∧ B3.nots = B2.nots ∧ (∀ t : Fin k, ind t < M + B3.size) ∧
        (∀ x ∈ S, ∀ t : Fin k, (B3.toCircuit.wires (mkInput x)).getD (ind t) false = decide ((g x).1.val = t.val)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨B2, Fin.elim0, Bld.Ext.refl B2, rfl, fun t => Fin.elim0 t, fun _ _ t => Fin.elim0 t⟩
    | succ k ihk =>
      intro hkq
      rcases ihk (by omega) with ⟨B3, ind1, h23, hnt3, hi1_lt, hi1_ev⟩
      let wLo : Nat := if hk0 : k = 0 then n + 1 else T ⟨k - 1, by omega⟩
      have hwLo_lt : wLo < M + B3.size := by
        dsimp only [wLo]; split_ifs with hk0
        · omega
        · have := hT_lt ⟨k - 1, by omega⟩; have := h12.size_le; have := h23.size_le; omega
      let wHi : Nat := if hkh : k < h then notT ⟨k, hkh⟩ else n + 1
      have hwHi_lt : wHi < M + B3.size := by
        dsimp only [wHi]; split_ifs with hkh
        · have := hnotT_lt ⟨k, hkh⟩; have := h23.size_le; omega
        · omega
      let pA := B3.mkAnd wLo wHi hwLo_lt hwHi_lt
      let B4 := pA.1; let wK := pA.2
      have h34 : B3.Ext B4 := Bld.pushGate_ext _ _ _ _ _ _
      have hnt4 : B4.nots = B3.nots := Bld.mkAnd_nots _ _ _ _ _
      have hwK_lt : wK < M + B4.size := Bld.pushGate_wire_lt _ _ _ _ _ _
      refine ⟨B4, fun t => if ht : t.val < k then ind1 ⟨t.val, ht⟩ else wK,
        h23.trans h34, by omega, ?_, ?_⟩
      · intro t; dsimp only; split_ifs with ht
        · have := hi1_lt ⟨t.val, ht⟩; have := h34.size_le; omega
        · exact hwK_lt
      · intro x hx t; dsimp only; split_ifs with ht
        · rw [h34.wires_eq (mkInput x) (mkInput_length x) _ (hi1_lt ⟨t.val, ht⟩)]
          exact hi1_ev x hx ⟨t.val, ht⟩
        · have htk : t.val = k := by omega
          rw [htk, Bld.mkAnd_eval _ _ _ _ _ (mkInput x) (mkInput_length x)]
          have hlo_ev : (B3.toCircuit.wires (mkInput x)).getD wLo false = decide (k ≤ (g x).1.val) := by
            dsimp only [wLo]; split_ifs with hk0
            · rw [wires_getD_input _ _ (n + 1) (by rw [mkInput_length]; omega), mkInput_getD_true, hk0]; simp
            · rw [(h12.trans h23).wires_eq (mkInput x) (mkInput_length x) _ (hT_lt ⟨k - 1, by omega⟩),
                  hT_ev x hx ⟨k - 1, by omega⟩]
              exact decide_eq_decide.mpr (by dsimp only; omega)
          have hhi_ev : (B3.toCircuit.wires (mkInput x)).getD wHi false = decide ((g x).1.val ≤ k) := by
            dsimp only [wHi]; split_ifs with hkh
            · rw [h23.wires_eq (mkInput x) (mkInput_length x) _ (hnotT_lt ⟨k, hkh⟩),
                  hnotT_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x) (g x).1.val (by have := (g x).1.isLt; omega) (hT_ev x hx) ⟨k, hkh⟩]
              by_cases hle : (g x).1.val ≤ k
              · have hnot : ¬ (k + 1 ≤ (g x).1.val) := by omega
                simp [hle, hnot]
              · have hge : k + 1 ≤ (g x).1.val := by omega
                simp [hle, hge]
            · rw [wires_getD_input _ _ (n + 1) (by rw [mkInput_length]; omega), mkInput_getD_true]
              have := (g x).1.isLt
              have : (g x).1.val ≤ k := by omega
              simp [this]
          rw [hlo_ev, hhi_ev]
          by_cases heq : (g x).1.val = k
          · simp [heq]
          · by_cases hlt : (g x).1.val < k
            · have h1 : ¬ (k ≤ (g x).1.val) := by omega
              simp [heq, h1]
            · have h2 : ¬ ((g x).1.val ≤ k) := by omega
              simp [heq, h2]
  rcases build_ind q (le_refl q) with ⟨B3, ind, h23, hnt3, hind_lt, hind_ev⟩
  -- Step 4: Build outputs tap : Fin a → Nat!
  have build_one_tap : ∀ (B : Bld M) (hB : B3.Ext B) (i : Fin a),
      ∃ (B' : Bld M) (wTap : Nat),
        B.Ext B' ∧ B'.nots = B.nots ∧ wTap < M + B'.size ∧
        (∀ x ∈ S, (B'.toCircuit.wires (mkInput x)).getD wTap false = (g x).2 i) := by
    intro B hB i
    -- For each t : Fin q, build (ind t ∧ upward_set {y ∈ S | (g y).1 = t ∧ (g y).2 i = true})
    have build_terms : ∀ (k : Nat), k ≤ q →
        ∃ (B' : Bld M) (ws : List Nat),
          B.Ext B' ∧ B'.nots = B.nots ∧ (∀ w ∈ ws, w < M + B'.size) ∧
          (∀ x ∈ S, ws.any (fun w => (B'.toCircuit.wires (mkInput x)).getD w false) =
            decide ((g x).1.val < k ∧ (g x).2 i = true)) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨B, [], Bld.Ext.refl B, rfl, (fun _ h => by cases h), fun _ _ => by simp⟩
      | succ k ihk =>
        intro hkq
        rcases ihk (by omega) with ⟨B4, ws1, h04, hnt4, hws1_lt, hws1_ev⟩
        let tK : Fin q := ⟨k, hkq⟩
        let U : Finset (Finset (Fin n)) := S.filter (fun y => (g y).1 = tK ∧ (g y).2 i = true)
        rcases build_upward_set B4 U with ⟨B5, wU, h45, hnt5, hwU_lt, hwU_ev⟩
        have hind_k_lt : ind tK < M + B5.size := by
          have := hind_lt tK; have := hB.size_le; have := h04.size_le; have := h45.size_le; omega
        let pA := B5.mkAnd (ind tK) wU hind_k_lt hwU_lt
        let B6 := pA.1; let wTerm := pA.2
        have h56 : B5.Ext B6 := Bld.pushGate_ext _ _ _ _ _ _
        have hnt6 : B6.nots = B5.nots := Bld.mkAnd_nots _ _ _ _ _
        have hwTerm_lt : wTerm < M + B6.size := Bld.pushGate_wire_lt _ _ _ _ _ _
        refine ⟨B6, wTerm :: ws1, (h04.trans h45).trans h56, by omega, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | htl
          · exact hwTerm_lt
          · have := hws1_lt w htl; have := h45.size_le; have := h56.size_le; omega
        · intro x hx
          simp only [List.any_cons]
          have htl_eq : ws1.any (fun w => (B6.toCircuit.wires (mkInput x)).getD w false) =
              ws1.any (fun w => (B4.toCircuit.wires (mkInput x)).getD w false) := by
            have hcongr : ∀ (l : List Nat), (∀ w ∈ l, w < M + B4.size) →
                l.any (fun w => (B6.toCircuit.wires (mkInput x)).getD w false) =
                l.any (fun w => (B4.toCircuit.wires (mkInput x)).getD w false) := by
              intro l hl
              induction l with
              | nil => rfl
              | cons u us ihu =>
                simp only [List.any_cons]
                rw [(h45.trans h56).wires_eq (mkInput x) (mkInput_length x) u (hl u (by simp)),
                    ihu (fun w hw => hl w (List.mem_cons_of_mem u hw))]
            exact hcongr ws1 hws1_lt
          rw [htl_eq, hws1_ev x hx, Bld.mkAnd_eval _ _ _ _ _ (mkInput x) (mkInput_length x),
              ((hB.trans h04).trans h45).wires_eq (mkInput x) (mkInput_length x) _ (hind_lt tK),
              hind_ev x hx tK, hwU_ev x]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, tK, U, Finset.mem_filter]
          constructor
          · rintro (⟨hgk, ⟨y, ⟨hyS, hy1, hy2⟩, hyx⟩⟩ | ⟨hlt, hgt⟩)
            · have hm := hmono y hyS x hx hyx
              have hyx_eq : (g y).1 = (g x).1 := Fin.ext (by rw [hy1]; dsimp only; omega)
              rcases hm with hlt' | ⟨_, hbm⟩
              · rw [hyx_eq] at hlt'; omega
              · exact ⟨by omega, hbm i hy2⟩
            · exact ⟨by omega, hgt⟩
          · rintro ⟨hlt, hgt⟩
            by_cases hgk : (g x).1.val = k
            · left
              exact ⟨hgk, x, ⟨hx, Fin.ext hgk, hgt⟩, Finset.Subset.refl x⟩
            · right; exact ⟨by omega, hgt⟩
    rcases build_terms q (le_refl q) with ⟨B4, ws, h04, hnt4, hws_lt, hws_ev⟩
    rcases build_or_list B4 n (by omega) ws hws_lt with ⟨B5, wTap, h45, hnt5, hwTap_lt, hwTap_ev⟩
    refine ⟨B5, wTap, h04.trans h45, by omega, hwTap_lt, ?_⟩
    intro x hx
    rw [hwTap_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x), hws_ev x hx]
    have hltq : (g x).1.val < q := (g x).1.isLt
    cases hv : (g x).2 i <;> simp [hltq, hv]
  have build_all_taps : ∀ (k : Nat) (hk_le : k ≤ a),
      ∃ (B4 : Bld M) (tap : Fin k → Nat),
        B3.Ext B4 ∧ B4.nots = B3.nots ∧ (∀ i : Fin k, tap i < M + B4.size) ∧
        (∀ x ∈ S, ∀ i : Fin k, (B4.toCircuit.wires (mkInput x)).getD (tap i) false = (g x).2 ⟨i.val, by have := i.isLt; omega⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨B3, Fin.elim0, Bld.Ext.refl B3, rfl, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩
    | succ k ihk =>
      intro hka
      rcases ihk (by omega) with ⟨B4, tap1, h34, hnt4, ht1_lt, ht1_ev⟩
      rcases build_one_tap B4 h34 ⟨k, hka⟩ with ⟨B5, wK, h45, hnt5, hwK_lt, hwK_ev⟩
      refine ⟨B5, fun i => if hi : i.val < k then tap1 ⟨i.val, hi⟩ else wK,
        h34.trans h45, by omega, ?_, ?_⟩
      · intro i; dsimp only; split_ifs with hi
        · have := ht1_lt ⟨i.val, hi⟩; have := h45.size_le; omega
        · exact hwK_lt
      · intro x hx i; dsimp only; split_ifs with hi
        · rw [h45.wires_eq (mkInput x) (mkInput_length x) _ (ht1_lt ⟨i.val, hi⟩)]
          exact ht1_ev x hx ⟨i.val, hi⟩
        · have hik : i.val = k := by omega
          rw [hwK_ev x hx]
          exact congrArg ((g x).2) (Fin.ext hik.symm)
  rcases build_all_taps a (le_refl a) with ⟨B4, tap, _h34, hnt4, htap_lt, htap_ev⟩
  refine ⟨B4.toCircuit, tap, B4.hF2, B4.hRB, by simp [Bld.toCircuit], ?_, htap_lt, ?_⟩
  · change B4.nots ≤ b; omega
  · intro x hx
    have hfun : (fun i : Fin a => (B4.toCircuit.wires (mkInput x)).getD (tap i) false) = (g x).2 := by
      funext i; exact htap_ev x hx i
    rw [hfun]; exact (hok x hx).2

-- ============================================================================
-- Saturated path count pathsCount on Q and exact formula = bound a b
-- ============================================================================

private def qCovers {a q : Nat} (p : QState a q) : Finset (QState a q) :=
  Finset.univ.filter (qNext p)

private def pathsCount {a q : Nat} (p : QState a q) : Nat :=
  1 + (qCovers p).attach.sum (fun r =>
    have _ : qMeas r.val < qMeas p := qMeas_lt_of_qLt (Finset.mem_filter.mp r.property).2.1
    pathsCount r.val)
termination_by qMeas p

private lemma pathsCount_eq {a q : Nat} (p : QState a q) :
    pathsCount p = 1 + (qCovers p).sum pathsCount := by
  conv_lhs => unfold pathsCount
  congr 1
  exact Finset.sum_attach (qCovers p) pathsCount

-- Explicit characterization of covers in Q (for a >= 1)!
private lemma qNext_iff_of_not_all_true {a q : Nat} {t : Fin q} {w : Fin a → Bool}
    (hnot : ∃ i : Fin a, w i = false) (r : QState a q) :
    qNext (t, w) r ↔ r.1 = t ∧ ∃ i : Fin a, w i = false ∧ r.2 = Function.update w i true := by
  rcases hnot with ⟨i0, hi0⟩
  constructor
  · rintro ⟨⟨hle, hne⟩, hno⟩
    dsimp only [qLe] at hle
    rcases hle with hlt | ⟨heq, hm⟩
    · exfalso
      let z : QState a q := (t, Function.update w i0 true)
      apply hno; refine ⟨z, ⟨Or.inr ⟨rfl, ?_⟩, ?_⟩, ⟨Or.inl hlt, ?_⟩⟩
      · intro j hj; dsimp only [z] at hj ⊢
        by_cases hji : j = i0
        · subst hji; simp
        · simp [hji, hj]
      · intro heqz
        have := congrFun (congrArg Prod.snd heqz) i0
        simp [z, hi0] at this
      · intro heqz; have := congrArg Prod.fst heqz; dsimp only [z] at this; rw [← this] at hlt; omega
    · refine ⟨heq.symm, ?_⟩
      have hex_diff : ∃ i : Fin a, w i = false ∧ r.2 i = true := by
        by_contra hall
        push Not at hall
        apply hne; apply Prod.ext heq; funext j; dsimp only
        cases hwj : w j
        · cases hrj : r.2 j
          · rfl
          · exact False.elim (hall j hwj hrj)
        · exact (hm j hwj).symm
      rcases hex_diff with ⟨i1, hi1w, hi1r⟩
      refine ⟨i1, hi1w, ?_⟩
      by_contra hne_u
      let z : QState a q := (t, Function.update w i1 true)
      apply hno
      refine ⟨z, ⟨Or.inr ⟨rfl, ?_⟩, ?_⟩, ⟨Or.inr ⟨heq, ?_⟩, ?_⟩⟩
      · intro j hj; dsimp only [z] at hj ⊢
        by_cases hji : j = i1
        · subst hji; simp
        · simp [hji, hj]
      · intro heqz
        have := congrFun (congrArg Prod.snd heqz) i1
        simp [z, hi1w] at this
      · intro j hj; dsimp only [z] at hj ⊢
        by_cases hji : j = i1
        · subst hji; exact hi1r
        · simp [hji] at hj; exact hm j hj
      · intro heqz; exact hne_u (congrArg Prod.snd heqz).symm
  · rintro ⟨ht, i1, hi1w, hr2⟩
    have hr_eq : r = (t, Function.update w i1 true) := Prod.ext ht hr2
    subst hr_eq
    refine ⟨⟨Or.inr ⟨rfl, ?_⟩, ?_⟩, ?_⟩
    · intro j hj; dsimp only at hj ⊢
      by_cases hji : j = i1
      · subst hji; simp
      · simp [hji, hj]
    · intro heq
      have := congrFun (congrArg Prod.snd heq) i1
      simp [hi1w] at this
    · rintro ⟨z, ⟨h1z_le, h1z_ne⟩, ⟨hz2_le, hz2_ne⟩⟩
      dsimp only [qLe] at h1z_le hz2_le
      have hzt : z.1 = t := by
        rcases h1z_le with h1 | ⟨h1, _⟩ <;> rcases hz2_le with h2 | ⟨h2, _⟩
        · omega
        · rw [h2] at h1; omega
        · rw [← h1] at h2; omega
        · exact h1.symm
      have hm1 : ∀ j, w j = true → z.2 j = true := by
        rcases h1z_le with h1 | ⟨_, hm⟩
        · rw [hzt] at h1; omega
        · exact hm
      have hm2 : ∀ j, z.2 j = true → Function.update w i1 true j = true := by
        rcases hz2_le with h2 | ⟨_, hm⟩
        · rw [hzt] at h2; omega
        · exact hm
      cases hzi1 : z.2 i1
      · apply h1z_ne; apply Prod.ext hzt.symm; funext j; dsimp only
        by_cases hji : j = i1
        · subst hji; rw [hi1w, hzi1]
        · cases hwj : w j
          · cases hzj : z.2 j
            · rfl
            · have := hm2 j hzj; simp [hji, hwj] at this
          · exact (hm1 j hwj).symm
      · apply hz2_ne; apply Prod.ext hzt; funext j; dsimp only
        by_cases hji : j = i1
        · subst hji; simp [hzi1]
        · simp only [Function.update_of_ne hji]
          cases hwj : w j
          · cases hzj : z.2 j
            · rfl
            · have := hm2 j hzj; simp [hji, hwj] at this
          · exact hm1 j hwj

private lemma qNext_iff_of_all_true {a q : Nat} (ha : 1 ≤ a) {t : Fin q} {w : Fin a → Bool}
    (hall : ∀ i : Fin a, w i = true) (r : QState a q) :
    qNext (t, w) r ↔ r.1.val = t.val + 1 ∧ ∀ i : Fin a, r.2 i = false := by
  constructor
  · rintro ⟨⟨hle, hne⟩, hno⟩
    dsimp only [qLe] at hle
    have hlt : t.val < r.1.val := by
      rcases hle with h | ⟨heq, hm⟩
      · exact h
      · exfalso; apply hne; apply Prod.ext heq; funext i; dsimp only
        rw [hall i, hm i (hall i)]
    have hstep : r.1.val = t.val + 1 := by
      by_contra hne_s
      let z : QState a q := (⟨t.val + 1, by have := r.1.isLt; omega⟩, fun _ => false)
      apply hno
      refine ⟨z, ⟨Or.inl (by dsimp only [z]; omega), ?_⟩, ⟨Or.inl (by dsimp only [z]; omega), ?_⟩⟩
      · intro h; have := congrArg (fun p : QState a q => p.1.val) h; dsimp only [z] at this; omega
      · intro h; have := congrArg (fun p : QState a q => p.1.val) h; dsimp only [z] at this; omega
    refine ⟨hstep, ?_⟩
    intro i
    cases hri : r.2 i
    · rfl
    · exfalso
      let z : QState a q := (r.1, fun _ => false)
      apply hno
      refine ⟨z, ⟨Or.inl hlt, ?_⟩, ⟨Or.inr ⟨rfl, fun _ h => by cases h⟩, ?_⟩⟩
      · intro h; have := congrArg (fun p : QState a q => p.1.val) h; dsimp only [z] at this; omega
      · intro h; have := congrFun (congrArg Prod.snd h) i; simp [z, hri] at this
  · rintro ⟨hstep, hrf⟩
    refine ⟨⟨Or.inl (by dsimp only; omega), ?_⟩, ?_⟩
    · intro h; have := congrArg (fun p : QState a q => p.1.val) h; dsimp only at this; omega
    · rintro ⟨z, ⟨h1z_le, h1z_ne⟩, ⟨hz2_le, hz2_ne⟩⟩
      dsimp only [qLe] at h1z_le hz2_le
      have hzt_ge : t.val ≤ z.1.val := by
        rcases h1z_le with h | ⟨h, _⟩
        · omega
        · rw [h]
      have hzr_le : z.1.val ≤ r.1.val := by
        rcases hz2_le with h | ⟨h, _⟩
        · omega
        · rw [h]
      have hcases : z.1.val = t.val ∨ z.1.val = r.1.val := by omega
      rcases hcases with hzt | hzr
      · rcases h1z_le with hlt | ⟨heq, hm⟩
        · omega
        · apply h1z_ne; apply Prod.ext heq; funext i; dsimp only; rw [hall i, hm i (hall i)]
      · rcases hz2_le with hlt | ⟨heq, hm⟩
        · omega
        · apply hz2_ne; apply Prod.ext heq; funext i
          cases hzi : z.2 i
          · rw [hrf i]
          · have := hm i hzi; rw [hrf i] at this; cases this

private def tailPermSum (rem : Nat) : Nat :=
  (Finset.range rem).sum (fun j => Nat.factorial rem / Nat.factorial (rem - j))

private lemma tailPermSum_succ (m : Nat) :
    tailPermSum (m + 1) = 1 + (m + 1) * tailPermSum m := by
  unfold tailPermSum
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.div_self (Nat.factorial_pos _)]
  rw [Nat.add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j < m := Finset.mem_range.mp hj
  have hsub : m + 1 - (j + 1) = m - j := by omega
  rw [hsub, Nat.factorial_succ]
  have hdvd : Nat.factorial (m - j) ∣ Nat.factorial m := Nat.factorial_dvd_factorial (by omega)
  exact Nat.mul_div_assoc (m + 1) hdvd

private lemma pathsCount_formula {a q : Nat} (ha : 1 ≤ a) (hq : 1 ≤ q) :
    let F := Nat.factorial a
    let H := (Finset.range (a + 1)).sum (fun j => F / Nat.factorial (a - j))
    ∀ (t : Fin q) (w : Fin a → Bool),
      let rem := a - popCnt w
      pathsCount (t, w) =
        tailPermSum rem + Nat.factorial rem * (1 + (Finset.range (q - 1 - t.val)).sum (fun s => H * F ^ s)) := by
  intro F H
  have hH_eq : H = tailPermSum a + F := by
    dsimp only [H, tailPermSum]
    rw [Finset.sum_range_succ]
    simp [F]
  have hmain : ∀ (d : Nat) (t : Fin q) (w : Fin a → Bool),
      qMeas (t, w) = d →
      pathsCount (t, w) =
        tailPermSum (a - popCnt w) +
          Nat.factorial (a - popCnt w) * (1 + (Finset.range (q - 1 - t.val)).sum (fun s => H * F ^ s)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro t w hmd
      by_cases hall : ∀ i : Fin a, w i = true
      · have hpop : popCnt w = a := by
          unfold popCnt
          have : (Finset.univ : Finset (Fin a)).filter (fun i => w i = true) = Finset.univ := by
            ext i; simp [hall i]
          rw [this, Finset.card_fin]
        have hrem : a - popCnt w = 0 := by omega
        rw [hrem]
        simp only [tailPermSum, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero, Nat.one_mul, Nat.zero_add]
        rw [pathsCount_eq]
        by_cases hlast : t.val + 1 = q
        · have hcov_empty : qCovers (t, w) = ∅ := by
            ext r; simp only [qCovers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            rw [qNext_iff_of_all_true ha hall]
            rintro ⟨hr1, _⟩; have := r.1.isLt; omega
          rw [hcov_empty, Finset.sum_empty]
          have : q - 1 - t.val = 0 := by omega
          simp [this]
        · have ht1 : t.val + 1 < q := by have := t.isLt; omega
          let r0 : QState a q := (⟨t.val + 1, ht1⟩, fun _ => false)
          have hcov_sing : qCovers (t, w) = {r0} := by
            ext r
            simp only [qCovers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            rw [qNext_iff_of_all_true ha hall]
            constructor
            · rintro ⟨hr1, hrf⟩
              exact Prod.ext (Fin.ext hr1) (funext hrf)
            · rintro rfl; exact ⟨rfl, fun _ => rfl⟩
          rw [hcov_sing, Finset.sum_singleton]
          have hlt_m : qMeas r0 < d := by
            rw [← hmd]
            apply qMeas_lt_of_qLt
            have hmem : r0 ∈ qCovers (t, w) := by rw [hcov_sing]; exact Finset.mem_singleton_self r0
            exact (Finset.mem_filter.mp hmem).2.1
          have hih := ih (qMeas r0) hlt_m r0.1 r0.2 rfl
          have hpop0 : popCnt r0.2 = 0 := by
            unfold popCnt; simp [r0]
          rw [hpop0, Nat.sub_zero] at hih
          rw [hih]
          have hsub_t : q - 1 - t.val = (q - 1 - (t.val + 1)) + 1 := by omega
          rw [hsub_t, Finset.sum_range_succ']
          simp only [Nat.pow_zero, Nat.mul_one]
          have hmul_sum : F * (Finset.range (q - 1 - (t.val + 1))).sum (fun s => H * F ^ s) =
              (Finset.range (q - 1 - (t.val + 1))).sum (fun s => H * F ^ (s + 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro s _; ring
          dsimp only [r0]
          change 1 + (tailPermSum a + F * (1 + (Finset.range (q - 1 - (t.val + 1))).sum (fun s => H * F ^ s))) = _
          rw [Nat.mul_add, Nat.mul_one, hmul_sum, hH_eq]
          ring
      · have hnot : ∃ i : Fin a, w i = false := by
          by_contra hno; push Not at hno
          apply hall; intro i; cases hwi : w i
          · exact False.elim (hno i hwi)
          · rfl
        let zeros : Finset (Fin a) := Finset.univ.filter (fun i => w i = false)
        have hzeros_card : zeros.card = a - popCnt w := by
          have hdisj : Disjoint (Finset.univ.filter (fun i => w i = true)) zeros := by
            rw [Finset.disjoint_left]; intro i hi1 hi2
            have h1 := (Finset.mem_filter.mp hi1).2
            have h2 := (Finset.mem_filter.mp hi2).2
            rw [h1] at h2; cases h2
          have hunion : (Finset.univ.filter (fun i => w i = true)) ∪ zeros = Finset.univ := by
            ext i; simp only [zeros, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            cases w i <;> simp
          have hsum := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_fin] at hsum
          unfold popCnt; omega
        have hrem_pos : 1 ≤ a - popCnt w := by
          rcases hnot with ⟨i0, hi0⟩
          have : 0 < zeros.card := Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩⟩
          omega
        let rem := a - popCnt w
        have hcov_img : qCovers (t, w) = zeros.image (fun i => (t, Function.update w i true)) := by
          ext r
          simp only [qCovers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, zeros]
          rw [qNext_iff_of_not_all_true hnot]
          constructor
          · rintro ⟨ht, i, hiw, hr2⟩
            exact ⟨i, hiw, Prod.ext ht.symm hr2.symm⟩
          · rintro ⟨i, hiw, rfl⟩
            exact ⟨rfl, i, hiw, rfl⟩
        have hinj : Set.InjOn (fun i : Fin a => (t, Function.update w i true)) (zeros : Set (Fin a)) := by
          intro i1 hi1 i2 hi2 heq
          have h1 : w i1 = false := (Finset.mem_filter.mp hi1).2
          have hfn := congrFun (congrArg Prod.snd heq) i1
          by_contra hne
          simp [hne, h1] at hfn
        rw [pathsCount_eq, hcov_img, Finset.sum_image hinj]
        have heach : ∀ i ∈ zeros,
            pathsCount (t, Function.update w i true) =
              tailPermSum (rem - 1) +
                Nat.factorial (rem - 1) * (1 + (Finset.range (q - 1 - t.val)).sum (fun s => H * F ^ s)) := by
          intro i hi
          have hiw : w i = false := (Finset.mem_filter.mp hi).2
          have hmem_cov : (t, Function.update w i true) ∈ qCovers (t, w) := by
            rw [hcov_img]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
          have hlt_m : qMeas (t, Function.update w i true) < d := by
            rw [← hmd]
            exact qMeas_lt_of_qLt (Finset.mem_filter.mp hmem_cov).2.1
          have hpop_up : popCnt (Function.update w i true) = popCnt w + 1 := by
            unfold popCnt
            have hins : (Finset.univ : Finset (Fin a)).filter (fun j => Function.update w i true j = true) =
                insert i ((Finset.univ : Finset (Fin a)).filter (fun j => w j = true)) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              by_cases hji : j = i
              · subst hji; simp
              · simp [hji]
            have hni : i ∉ (Finset.univ : Finset (Fin a)).filter (fun j => w j = true) := by
              simp [hiw]
            rw [hins, Finset.card_insert_of_notMem hni]
          have hih := ih (qMeas (t, Function.update w i true)) hlt_m t (Function.update w i true) rfl
          have hrem_eq : a - popCnt (Function.update w i true) = rem - 1 := by dsimp only [rem]; omega
          rw [hrem_eq] at hih
          exact hih
        rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hzeros_card]
        have hrem_succ : a - popCnt w = (rem - 1) + 1 := by dsimp only [rem]; omega
        conv_lhs => rw [hrem_succ]
        conv_rhs => rw [hrem_succ, tailPermSum_succ, Nat.factorial_succ]
        dsimp only [rem]
        ring
  intro t w; exact hmain (qMeas (t, w)) t w rfl

private lemma pathsCount_bot_eq_bound (a b : Nat) (ha : 1 ≤ a) :
    pathsCount (q := 2 ^ b) (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, (fun _ : Fin a => false)) =
      ((Finset.range (a + 1)).sum (fun j => Nat.factorial a / Nat.factorial (a - j))) *
        (Finset.range (2 ^ b)).sum (fun j => (Nat.factorial a) ^ j) := by
  let q := 2 ^ b
  let F := Nat.factorial a
  let H := (Finset.range (a + 1)).sum (fun j => F / Nat.factorial (a - j))
  have hq : 1 ≤ q := Nat.one_le_pow b 2 (by omega)
  have hf := pathsCount_formula (q := q) ha hq ⟨0, by omega⟩ (fun _ => false)
  have hpop0 : popCnt (fun _ : Fin a => false) = 0 := by unfold popCnt; simp
  have hH_eq : H = tailPermSum a + F := by
    dsimp only [H, tailPermSum]; rw [Finset.sum_range_succ]; simp [F]
  rw [hpop0, Nat.sub_zero, Nat.sub_zero] at hf
  change pathsCount (q := q) (⟨0, by omega⟩, fun _ : Fin a => false) = H * (Finset.range q).sum (fun j => F ^ j)
  rw [hf]
  have hq_succ : q = (q - 1) + 1 := by omega
  conv_rhs => rw [hq_succ, Finset.sum_range_succ']
  simp only [Nat.pow_zero]
  have hrhs : H * ((Finset.range (q - 1)).sum (fun s => F ^ (s + 1)) + 1) =
      H + F * (Finset.range (q - 1)).sum (fun s => H * F ^ s) := by
    rw [Nat.mul_add, Nat.mul_one, Finset.mul_sum, Finset.mul_sum, Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl; intro s _; ring
  rw [hrhs]
  change tailPermSum a + F * (1 + (Finset.range (q - 1)).sum (fun s => H * F ^ s)) = _
  rw [Nat.mul_add, Nat.mul_one, hH_eq]
  ring

-- ============================================================================
-- Part 1: Outward-forest Helly theorem on Q
-- ============================================================================

private lemma forest_poset_helly {n a q : Nat}
    (V : Finset (Finset (Fin n))) (ok : Finset (Fin n) → (Fin a → Bool) → Prop)
    (hfor : IsForest V) :
    ∀ (p : QState a q),
      (∀ S ⊆ V, S.card ≤ pathsCount p → FitPoset S ok p) → FitPoset V ok p := by
  intro p
  induction hm : qMeas p using Nat.strong_induction_on generalizing p V with
  | ind d ih_p =>
    induction hcard : V.card using Nat.strong_induction_on generalizing V with
    | ind m ih_V =>
      intro hloc
      by_cases hV0 : V = ∅
      · subst hV0
        exact ⟨fun _ => p, (fun _ h => by cases h), (fun _ h => by cases h)⟩
      · -- Pick a minimal element r of V (minimum card among x ∈ V)!
        have hne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hV0
        rcases Finset.exists_min_image V Finset.card hne with ⟨r, hrV, hr_min⟩
        let Tr : Finset (Finset (Fin n)) := V.filter (fun x => r ⊆ x)
        let Rest : Finset (Finset (Fin n)) := V \ Tr
        have hTr_sub : Tr ⊆ V := Finset.filter_subset _ V
        have hRest_sub : Rest ⊆ V := Finset.sdiff_subset
        have hr_in_Tr : r ∈ Tr := Finset.mem_filter.mpr ⟨hrV, Finset.Subset.refl r⟩
        by_cases hRest_ne : Rest.Nonempty
        · -- Disjoint incomparable decomposition V = Tr ∪ Rest, both strictly smaller than V!
          have hTr_lt : Tr.card < m := by
            rw [← hcard]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hTr_sub, fun heq => ?_⟩
            rcases hRest_ne with ⟨z, hz⟩
            have hz' := Finset.mem_sdiff.mp hz
            rw [heq] at hz'; exact hz'.2 hz'.1
          have hRest_lt : Rest.card < m := by
            rw [← hcard]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hRest_sub, fun heq => ?_⟩
            have : r ∈ Rest := by rw [heq]; exact hrV
            exact (Finset.mem_sdiff.mp this).2 hr_in_Tr
          have hfor_Tr : IsForest Tr := fun x hx y hy z hz => hfor x (hTr_sub hx) y (hTr_sub hy) z (hTr_sub hz)
          have hfor_Rest : IsForest Rest := fun x hx y hy z hz => hfor x (hRest_sub hx) y (hRest_sub hy) z (hRest_sub hz)
          rcases ih_V Tr.card hTr_lt Tr hfor_Tr rfl (fun S hS => hloc S (Finset.Subset.trans hS hTr_sub)) with ⟨g1, hok1, hm1⟩
          rcases ih_V Rest.card hRest_lt Rest hfor_Rest rfl (fun S hS => hloc S (Finset.Subset.trans hS hRest_sub)) with ⟨g2, hok2, hm2⟩
          refine ⟨fun x => if x ∈ Tr then g1 x else g2 x, ?_, ?_⟩
          · intro x hx
            by_cases hxT : x ∈ Tr
            · simp only [hxT, ↓reduceIte]; exact hok1 x hxT
            · simp only [hxT, ↓reduceIte]; exact hok2 x (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)
          · intro x hx y hy hxy
            by_cases hxT : x ∈ Tr <;> by_cases hyT : y ∈ Tr
            · simp only [hxT, hyT, ↓reduceIte]; exact hm1 x hxT y hyT hxy
            · exfalso
              have hrx : r ⊆ x := (Finset.mem_filter.mp hxT).2
              exact hyT (Finset.mem_filter.mpr ⟨hy, Finset.Subset.trans hrx hxy⟩)
            · exfalso
              have hry : r ⊆ y := (Finset.mem_filter.mp hyT).2
              rcases hfor y hy r hrV x hx hry hxy with hrx | hxr
              · exact hxT (Finset.mem_filter.mpr ⟨hx, hrx⟩)
              · have hle_c := hr_min x hx
                have hcard_xr := Finset.card_le_card hxr
                have hxeq : x = r := Finset.eq_of_subset_of_card_le hxr hle_c
                exact hxT (hxeq ▸ hr_in_Tr)
            · simp only [hxT, hyT, ↓reduceIte]
              exact hm2 x (Finset.mem_sdiff.mpr ⟨hx, hxT⟩) y (Finset.mem_sdiff.mpr ⟨hy, hyT⟩) hxy
        · -- Rest = ∅, so r is the unique minimum of V (∀ x ∈ V, r ⊆ x)!
          have hr_all : ∀ x ∈ V, r ⊆ x := by
            intro x hx
            by_contra hnr
            have : x ∈ Rest := Finset.mem_sdiff.mpr ⟨hx, fun h => hnr (Finset.mem_filter.mp h).2⟩
            exact hRest_ne ⟨x, this⟩
          by_cases hokr : ok r p.2
          · -- Root allows p: solve V.erase r and set g(r) = p!
            let V' := V.erase r
            have hV'_sub : V' ⊆ V := Finset.erase_subset r V
            have hV'_lt : V'.card < m := by rw [← hcard]; exact Finset.card_erase_lt_of_mem hrV
            have hfor' : IsForest V' := fun x hx y hy z hz => hfor x (hV'_sub hx) y (hV'_sub hy) z (hV'_sub hz)
            rcases ih_V V'.card hV'_lt V' hfor' rfl (fun S hS => hloc S (Finset.Subset.trans hS hV'_sub)) with ⟨g', hok', hm'⟩
            refine ⟨fun x => if x = r then p else g' x, ?_, ?_⟩
            · intro x hx
              by_cases hxr : x = r
              · subst hxr; simp only [↓reduceIte]; exact ⟨qLe_refl p, hokr⟩
              · simp only [hxr, ↓reduceIte]; exact hok' x (Finset.mem_erase.mpr ⟨hxr, hx⟩)
            · intro x hx y hy hxy
              by_cases hxr : x = r <;> by_cases hyr : y = r
              · simp only [hxr, hyr, ↓reduceIte]; exact qLe_refl p
              · simp only [hxr, hyr, ↓reduceIte]; exact (hok' y (Finset.mem_erase.mpr ⟨hyr, hy⟩)).1
              · exfalso
                subst hyr
                have hrx := hr_all x hx
                exact hxr (Finset.Subset.antisymm hxy hrx)
              · simp only [hxr, hyr, ↓reduceIte]
                exact hm' x (Finset.mem_erase.mpr ⟨hxr, hx⟩) y (Finset.mem_erase.mpr ⟨hyr, hy⟩) hxy
          · -- Root forbids p: must find a cover c ∈ qCovers p such that FitPoset V ok c!
            by_contra hno_fit
            have hbad_cov : ∀ c ∈ qCovers p, ∃ Sc ⊆ V, Sc.card ≤ pathsCount c ∧ ¬ FitPoset Sc ok c := by
              intro c hc
              have hnot_c : ¬ FitPoset V ok c := by
                intro ⟨g, hok_g, hm_g⟩
                apply hno_fit
                have hpc : qLe p c := (Finset.mem_filter.mp hc).2.1.1
                exact ⟨g, fun x hx => ⟨qLe_trans hpc (hok_g x hx).1, (hok_g x hx).2⟩, hm_g⟩
              by_contra hall_c
              push Not at hall_c
              have hlt_c : qMeas c < d := by
                rw [← hm]; exact qMeas_lt_of_qLt (Finset.mem_filter.mp hc).2.1
              exact hnot_c (ih_p (qMeas c) hlt_c V hfor c rfl hall_c)
            let pick : (c : QState a q) → c ∈ qCovers p → Finset (Finset (Fin n)) :=
              fun c hc => Classical.choose (hbad_cov c hc)
            have hpick_spec : ∀ c hc, pick c hc ⊆ V ∧ (pick c hc).card ≤ pathsCount c ∧ ¬ FitPoset (pick c hc) ok c :=
              fun c hc => Classical.choose_spec (hbad_cov c hc)
            let S : Finset (Finset (Fin n)) := insert r ((qCovers p).attach.biUnion (fun c => pick c.val c.property))
            have hS_sub : S ⊆ V := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hbu
              · exact hrV
              · rcases Finset.mem_biUnion.mp hbu with ⟨c, _, hxc⟩
                exact (hpick_spec c.val c.property).1 hxc
            have hS_card : S.card ≤ pathsCount p := by
              rw [pathsCount_eq]
              calc S.card ≤ 1 + ((qCovers p).attach.biUnion (fun c => pick c.val c.property)).card := by
                    have := Finset.card_insert_le r ((qCovers p).attach.biUnion (fun c => pick c.val c.property))
                    dsimp only [S]; omega
                _ ≤ 1 + (qCovers p).attach.sum (fun c => (pick c.val c.property).card) := by
                    exact Nat.add_le_add_left Finset.card_biUnion_le 1
                _ ≤ 1 + (qCovers p).attach.sum (fun c => pathsCount c.val) := by
                    apply Nat.add_le_add_left
                    apply Finset.sum_le_sum; intro c _; exact (hpick_spec c.val c.property).2.1
                _ = 1 + (qCovers p).sum pathsCount := by
                    congr 1; exact Finset.sum_attach (qCovers p) pathsCount
            rcases hloc S hS_sub hS_card with ⟨g, hok_g, hm_g⟩
            have hrS : r ∈ S := Finset.mem_insert_self r _
            have hgr := hok_g r hrS
            have hne_gr : p ≠ g r := by
              intro heq; rw [← heq] at hgr; exact hokr hgr.2
            rcases exists_qNext_between ⟨hgr.1, hne_gr⟩ with ⟨c, hpc_next, hc_gr⟩
            have hc_mem : c ∈ qCovers p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc_next⟩
            have hSc_sub_S : pick c hc_mem ⊆ S := by
              intro x hx
              exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨c, hc_mem⟩, Finset.mem_attach _ _, hx⟩)
            apply (hpick_spec c hc_mem).2.2
            refine ⟨g, ?_, fun x hx y hy hxy => hm_g x (hSc_sub_S hx) y (hSc_sub_S hy) hxy⟩
            intro x hx
            have hxS := hSc_sub_S hx
            have hxV := (hpick_spec c hc_mem).1 hx
            exact ⟨qLe_trans hc_gr (hm_g r hrS x hxS (hr_all x hxV)), (hok_g x hxS).2⟩

-- ============================================================================
-- Part 2: Sharpness construction in Fin (q * a * (2 * (Nat.log2 a + 1)) + (q - 1))
-- ============================================================================

private def dualRail {n : Nat} (baseOff L : Nat) (hlen : baseOff + 2 * L ≤ n) (idx : Nat) : Finset (Fin n) :=
  (Finset.range L).attach.image (fun r =>
    ⟨baseOff + 2 * r.val + (if idx.testBit r.val then 1 else 0), by
      have := Finset.mem_range.mp r.property; split_ifs <;> omega⟩)

private lemma dualRail_mem_range {n : Nat} {baseOff L : Nat} {hlen : baseOff + 2 * L ≤ n} {idx : Nat}
    {x : Fin n} (hx : x ∈ dualRail baseOff L hlen idx) :
    baseOff ≤ x.val ∧ x.val < baseOff + 2 * L := by
  rcases Finset.mem_image.mp hx with ⟨r, _, rfl⟩
  have hr := Finset.mem_range.mp r.property
  dsimp only; split_ifs <;> omega

private lemma dualRail_nonempty {n : Nat} {baseOff L : Nat} (hL : 1 ≤ L) (hlen : baseOff + 2 * L ≤ n) (idx : Nat) :
    (dualRail baseOff L hlen idx).Nonempty := by
  refine ⟨⟨baseOff + 2 * 0 + (if idx.testBit 0 then 1 else 0), by split_ifs <;> omega⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨0, Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _, rfl⟩

private lemma dualRail_eq_of_subset {n : Nat} {baseOff L : Nat} {hlen : baseOff + 2 * L ≤ n}
    {i1 i2 : Nat} (hi1 : i1 < 2 ^ L) (hi2 : i2 < 2 ^ L)
    (hsub : dualRail baseOff L hlen i1 ⊆ dualRail baseOff L hlen i2) : i1 = i2 := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hrL : r < L
  · let pt : Fin n := ⟨baseOff + 2 * r + (if i1.testBit r then 1 else 0), by split_ifs <;> omega⟩
    have hpt1 : pt ∈ dualRail baseOff L hlen i1 :=
      Finset.mem_image.mpr ⟨⟨r, Finset.mem_range.mpr hrL⟩, Finset.mem_attach _ _, rfl⟩
    have hpt2 := hsub hpt1
    rcases Finset.mem_image.mp hpt2 with ⟨r', _, heq⟩
    have hval := congrArg Fin.val heq
    dsimp only [pt] at hval
    have hreq : r'.val = r := by split_ifs at hval <;> omega
    rw [hreq] at hval
    cases hb1 : i1.testBit r <;> cases hb2 : i2.testBit r <;> simp_all
  · have h1 : i1.testBit r = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hi1 (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : i2.testBit r = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hi2 (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

-- Coordinate threshold for state p = (t, w): all bits strictly below levelOffset p are frozen in base!
private def blockOff (a L : Nat) (t k : Nat) : Nat :=
  (t * a + k) * (2 * L)

private def transOff (a q L : Nat) (t : Nat) : Nat :=
  q * a * (2 * L) + t

private def usedMask {a q : Nat} (p : QState a q) (L : Nat) (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun c : Fin n =>
    c.val < blockOff a L p.1.val (popCnt p.2) ∨
    (q * a * (2 * L) ≤ c.val ∧ c.val < transOff a q L p.1.val))

private lemma build_sharp_tree (a b : Nat) (ha : 1 ≤ a) :
    let q := 2 ^ b
    let L := Nat.log2 a + 1
    let n := q * a * (2 * L) + (q - 1)
    ∀ (p : QState a q) (base : Finset (Fin n)),
      base ⊆ usedMask p L n →
      ∃ (V : Finset (Finset (Fin n))) (ban : Finset (Fin n) → (Fin a → Bool)),
        IsForest V ∧
        V.card = pathsCount p ∧
        (∀ x ∈ V, base ⊆ x ∧ x ∩ usedMask p L n = base) ∧
        (∀ u : QState a q, FitPoset V (fun x w => w ≠ ban x) u ↔ ¬ qLe p u) ∧
        (∀ x ∈ V, FitPoset (V.erase x) (fun y w => w ≠ ban y) p) := by
  intro q L n
  have hq_pos : 1 ≤ q := Nat.one_le_pow b 2 (by omega)
  have hL_pos : 1 ≤ L := by omega
  have ha_lt_pow : a < 2 ^ L := (Nat.log2_lt (by omega : a ≠ 0)).mp (Nat.lt_succ_self a.log2)
  have hmain : ∀ (d : Nat) (p : QState a q) (base : Finset (Fin n)),
      qMeas p = d → base ⊆ usedMask p L n →
      ∃ (V : Finset (Finset (Fin n))) (ban : Finset (Fin n) → (Fin a → Bool)),
        IsForest V ∧
        V.card = pathsCount p ∧
        (∀ x ∈ V, base ⊆ x ∧ x ∩ usedMask p L n = base) ∧
        (∀ u : QState a q, FitPoset V (fun x w => w ≠ ban x) u ↔ ¬ qLe p u) ∧
        (∀ x ∈ V, FitPoset (V.erase x) (fun y w => w ≠ ban y) p) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro p base hmd hbase_sub
      by_cases hall : ∀ i : Fin a, p.2 i = true
      · -- All a bits of p.2 are true!
        have hpop : popCnt p.2 = a := by
          unfold popCnt
          have : (Finset.univ : Finset (Fin a)).filter (fun i => p.2 i = true) = Finset.univ := by
            ext i; simp [hall i]
          rw [this, Finset.card_fin]
        by_cases hlast : p.1.val + 1 = q
        · -- Top element of QState a q: singleton tree {base}!
          have hcov_empty : qCovers p = ∅ := by
            ext r; simp only [qCovers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            have hiff := qNext_iff_of_all_true (t := p.1) ha hall r
            have hp_eq : (p.1, p.2) = p := rfl
            rw [hp_eq] at hiff
            rw [hiff]; rintro ⟨hr1, _⟩; have := r.1.isLt; omega
          refine ⟨{base}, fun _ => p.2, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx y hy z hz _ _
            rw [Finset.mem_singleton.mp hy, Finset.mem_singleton.mp hz]; exact Or.inl (Finset.Subset.refl _)
          · rw [Finset.card_singleton, pathsCount_eq, hcov_empty, Finset.sum_empty, Nat.add_zero]
          · intro x hx
            rw [Finset.mem_singleton.mp hx]
            exact ⟨Finset.Subset.refl _, Finset.inter_eq_left.mpr hbase_sub⟩
          · intro u
            constructor
            · rintro ⟨g, hok, _⟩ hpu
              have hgb := hok base (Finset.mem_singleton_self base)
              have hp_le := qLe_trans hpu hgb.1
              have hgb_eq : g base = p := by
                rcases hp_le with hlt | ⟨heq, hm⟩
                · have := (g base).1.isLt; omega
                · apply Prod.ext heq.symm; funext i
                  rw [hall i, hm i (hall i)]
              exact hgb.2 (congrArg Prod.snd hgb_eq)
            · intro hnot
              by_cases hu2 : u.2 ≠ p.2
              · exact ⟨fun _ => u, fun x hx => by rw [Finset.mem_singleton.mp hx]; exact ⟨qLe_refl u, hu2⟩,
                  fun _ _ _ _ _ => qLe_refl u⟩
              · push Not at hu2
                have hult : u.1.val < p.1.val := by
                  by_contra hge
                  apply hnot
                  have hlt_u := u.1.isLt
                  have heq1 : p.1 = u.1 := Fin.ext (by omega)
                  exact Or.inr ⟨heq1, fun i hi => by rw [hu2]; exact hi⟩
                let u' : QState a q := (⟨u.1.val + 1, by have := p.1.isLt; omega⟩, fun _ => false)
                have huu' : qLe u u' := Or.inl (by dsimp only [u']; omega)
                have hu'ne : u'.2 ≠ p.2 := by
                  intro h
                  have := congrFun h ⟨0, ha⟩
                  rw [hall ⟨0, ha⟩] at this; cases this
                exact ⟨fun _ => u', fun x hx => by rw [Finset.mem_singleton.mp hx]; exact ⟨huu', hu'ne⟩,
                  fun _ _ _ _ _ => qLe_refl u'⟩
          · intro x hx
            rw [Finset.mem_singleton.mp hx, Finset.erase_singleton]
            exact ⟨fun _ => p, (fun _ h => by cases h), (fun _ h => by cases h)⟩
        · -- Level transition to r0 = (p.1 + 1, all-false) using single transition bit tBit!
          have ht1 : p.1.val + 1 < q := by have := p.1.isLt; omega
          let r0 : QState a q := (⟨p.1.val + 1, ht1⟩, fun _ => false)
          have hcov_sing : qCovers p = {r0} := by
            ext r; simp only [qCovers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            have hiff := qNext_iff_of_all_true (t := p.1) ha hall r
            have hp_eq : (p.1, p.2) = p := rfl
            rw [hp_eq] at hiff
            rw [hiff]
            constructor
            · rintro ⟨hr1, hrf⟩; exact Prod.ext (Fin.ext hr1) (funext hrf)
            · rintro rfl; exact ⟨rfl, fun _ => rfl⟩
          have hr0_next : qNext p r0 := by
            have := Finset.mem_singleton_self r0
            rw [← hcov_sing] at this
            exact (Finset.mem_filter.mp this).2
          have hlt_m : qMeas r0 < d := by rw [← hmd]; exact qMeas_lt_of_qLt hr0_next.1
          have htBit_lt : transOff a q L p.1.val < n := by
            dsimp only [n, transOff]; omega
          let tBit : Fin n := ⟨transOff a q L p.1.val, htBit_lt⟩
          have htBit_not_used : tBit ∉ usedMask p L n := by
            simp only [usedMask, Finset.mem_filter, Finset.mem_univ, true_and, tBit, blockOff, transOff, hpop]
            have hmul : (p.1.val * a + a) * (2 * L) ≤ q * a * (2 * L) := by
              have h1 : p.1.val * a + a = (p.1.val + 1) * a := by ring
              rw [h1]
              exact Nat.mul_le_mul_right (2 * L) (Nat.mul_le_mul_right a (by omega))
            omega
          have hused_sub : usedMask p L n ⊆ usedMask r0 L n := by
            intro c hc
            have hc' := (Finset.mem_filter.mp hc).2
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ c, ?_⟩
            have hpop0 : popCnt r0.2 = 0 := by unfold popCnt; simp [r0]
            rw [hpop] at hc'
            rw [hpop0]
            dsimp only [blockOff, transOff, r0] at hc' ⊢
            rcases hc' with hlt | ⟨hlo, hhi⟩
            · left
              have h1 : (p.1.val * a + a) * (2 * L) = ((p.1.val + 1) * a + 0) * (2 * L) := by ring
              omega
            · right; omega
          have htBit_in_r0 : tBit ∈ usedMask r0 L n := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, Or.inr ?_⟩
            dsimp only [tBit, transOff, r0]; omega
          have hbase'_sub : insert tBit base ⊆ usedMask r0 L n := by
            intro c hc
            rcases Finset.mem_insert.mp hc with rfl | hcb
            · exact htBit_in_r0
            · exact hused_sub (hbase_sub hcb)
          rcases ih (qMeas r0) hlt_m r0 (insert tBit base) rfl hbase'_sub with
            ⟨V0, ban0, hfor0, hcard0, hdom0, hfit0, herase0⟩
          have hbase_not_V0 : base ∉ V0 := by
            intro hmem
            have hsub := (hdom0 base hmem).1
            exact htBit_not_used (hbase_sub (hsub (Finset.mem_insert_self tBit base)))
          let V := insert base V0
          let ban : Finset (Fin n) → (Fin a → Bool) := fun y => if y = base then p.2 else ban0 y
          have hok_V0 : ∀ y ∈ V0, ban y = ban0 y := by
            intro y hy
            have hne : y ≠ base := fun h => hbase_not_V0 (h ▸ hy)
            simp [ban, hne]
          refine ⟨V, ban, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx y hy z hz hyx hzx
            rcases Finset.mem_insert.mp hy with hyeq | hy0
            · left
              rw [hyeq]
              rcases Finset.mem_insert.mp hz with hzeq | hz0
              · rw [hzeq]
              · exact Finset.Subset.trans (Finset.subset_insert tBit base) (hdom0 z hz0).1
            · rcases Finset.mem_insert.mp hz with hzeq | hz0
              · right; rw [hzeq]; exact Finset.Subset.trans (Finset.subset_insert tBit base) (hdom0 y hy0).1
              · rcases Finset.mem_insert.mp hx with hxeq | hx0
                · rw [hxeq] at hyx
                  exfalso; exact htBit_not_used (hbase_sub (hyx ((hdom0 y hy0).1 (Finset.mem_insert_self tBit base))))
                · exact hfor0 x hx0 y hy0 z hz0 hyx hzx
          · dsimp only [V]
            rw [Finset.card_insert_of_notMem hbase_not_V0, hcard0]
            conv_rhs => rw [pathsCount_eq, hcov_sing, Finset.sum_singleton]
            omega
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx0
            · exact ⟨Finset.Subset.refl _, Finset.inter_eq_left.mpr hbase_sub⟩
            · rcases hdom0 x hx0 with ⟨hsub, hinter⟩
              refine ⟨Finset.Subset.trans (Finset.subset_insert tBit base) hsub, ?_⟩
              ext c
              simp only [Finset.mem_inter]
              constructor
              · rintro ⟨hcx, hcu⟩
                have hcr0 : c ∈ x ∩ usedMask r0 L n := Finset.mem_inter.mpr ⟨hcx, hused_sub hcu⟩
                rw [hinter] at hcr0
                rcases Finset.mem_insert.mp hcr0 with rfl | hcb
                · exact False.elim (htBit_not_used hcu)
                · exact hcb
              · intro hcb
                exact ⟨hsub (Finset.mem_insert_of_mem hcb), hbase_sub hcb⟩
          · intro u
            constructor
            · rintro ⟨g, hok, hm⟩ hpu
              have hgb := hok base (Finset.mem_insert_self base V0)
              have hp_le := qLe_trans hpu hgb.1
              have hp_ne : p ≠ g base := by
                intro heq; have h2 : (g base).2 = p.2 := congrArg Prod.snd heq.symm
                have := hgb.2; simp only [ban, ↓reduceIte] at this; exact this h2
              rcases exists_qNext_between ⟨hp_le, hp_ne⟩ with ⟨c, hpc, hcg⟩
              have hc_eq : c = r0 := by
                have : c ∈ qCovers p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩
                rw [hcov_sing] at this; exact Finset.mem_singleton.mp this
              subst hc_eq
              have hfit_r0 : FitPoset V0 (fun y w => w ≠ ban0 y) r0 := by
                refine ⟨g, ?_, fun x hx y hy hxy => hm x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy⟩
                intro y hy
                have hgy := hok y (Finset.mem_insert_of_mem hy)
                have hby : base ⊆ y := Finset.Subset.trans (Finset.subset_insert tBit base) (hdom0 y hy).1
                refine ⟨qLe_trans hcg (hm base (Finset.mem_insert_self _ _) y (Finset.mem_insert_of_mem hy) hby), ?_⟩
                dsimp only; rw [← hok_V0 y hy]; exact hgy.2
              exact ((hfit0 r0).mp hfit_r0) (qLe_refl r0)
            · intro hnot
              -- Choose u' >= u with u'.2 != p.2 and ¬ qLe p u'!
              have hex_u' : ∃ u' : QState a q, qLe u u' ∧ u'.2 ≠ p.2 ∧ ¬ qLe p u' := by
                by_cases hu2 : u.2 ≠ p.2
                · exact ⟨u, qLe_refl u, hu2, hnot⟩
                · push Not at hu2
                  have hult : u.1.val < p.1.val := by
                    by_contra hge
                    apply hnot
                    by_cases heq1 : p.1.val = u.1.val
                    · exact Or.inr ⟨Fin.ext heq1, fun i hi => by rw [hu2]; exact hi⟩
                    · exact Or.inl (by omega)
                  let u' : QState a q := (⟨u.1.val + 1, by have := p.1.isLt; omega⟩, fun _ => false)
                  refine ⟨u', Or.inl (by dsimp only [u']; omega), ?_, ?_⟩
                  · intro h; have := congrFun h ⟨0, ha⟩; rw [hall ⟨0, ha⟩] at this; cases this
                  · intro hpu'
                    rcases hpu' with hlt | ⟨heq, hm⟩
                    · dsimp only [u'] at hlt; omega
                    · have := hm ⟨0, ha⟩ (hall ⟨0, ha⟩); cases this
              rcases hex_u' with ⟨u', huu', hu'ne, hnot_pu'⟩
              have hnot_r0 : ¬ qLe r0 u' := fun h => hnot_pu' (qLe_trans hr0_next.1.1 h)
              rcases (hfit0 u').mpr hnot_r0 with ⟨g0, hok0, hm0⟩
              refine ⟨fun y => if y = base then u' else g0 y, ?_, ?_⟩
              · intro y hy
                rcases Finset.mem_insert.mp hy with rfl | hy0
                · simp only [ban, ↓reduceIte]; exact ⟨huu', hu'ne⟩
                · have hne : y ≠ base := fun h => hbase_not_V0 (h ▸ hy0)
                  simp only [hne, ↓reduceIte, ban]
                  have hg0 := hok0 y hy0
                  exact ⟨qLe_trans huu' hg0.1, hg0.2⟩
              · intro x hx y hy hxy
                rcases Finset.mem_insert.mp hx with hxb | hx0 <;> rcases Finset.mem_insert.mp hy with hyb | hy0
                · rw [hxb, hyb]; dsimp only; simp only [↓reduceIte]; exact qLe_refl u'
                · rw [hxb]; have hne : y ≠ base := fun h => hbase_not_V0 (h ▸ hy0)
                  dsimp only; rw [if_pos rfl, if_neg hne]; exact (hok0 y hy0).1
                · rw [hyb] at hxy; exfalso
                  exact htBit_not_used (hbase_sub (hxy ((hdom0 x hx0).1 (Finset.mem_insert_self tBit base))))
                · have hnex : x ≠ base := fun h => hbase_not_V0 (h ▸ hx0)
                  have hney : y ≠ base := fun h => hbase_not_V0 (h ▸ hy0)
                  simp only [hnex, hney, ↓reduceIte]; exact hm0 x hx0 y hy0 hxy
          · intro x hx
            rcases Finset.mem_insert.mp hx with hxb | hx0
            · rw [hxb]
              have her : V.erase base = V0 := Finset.erase_insert hbase_not_V0
              rw [her]
              have hnot_r0p : ¬ qLe r0 p := fun h => hr0_next.1.2 (qLe_antisymm hr0_next.1.1 h)
              rcases (hfit0 p).mpr hnot_r0p with ⟨g0, hok0, hm0⟩
              refine ⟨g0, fun y hy => ?_, hm0⟩
              dsimp only; rw [hok_V0 y hy]; exact hok0 y hy
            · rcases herase0 x hx0 with ⟨g0, hok0, hm0⟩
              have hne_xb : x ≠ base := fun h => hbase_not_V0 (h ▸ hx0)
              have hr0_ne_p : r0.2 ≠ p.2 := by
                intro h; have := congrFun h ⟨0, ha⟩; rw [hall ⟨0, ha⟩] at this; cases this
              refine ⟨fun y => if y = base then r0 else g0 y, ?_, ?_⟩
              · intro y hy
                have hy' := Finset.mem_erase.mp hy
                rcases Finset.mem_insert.mp hy'.2 with rfl | hy0
                · simp only [ban, ↓reduceIte]; exact ⟨hr0_next.1.1, hr0_ne_p⟩
                · have hne : y ≠ base := fun h => hbase_not_V0 (h ▸ hy0)
                  simp only [hne, ↓reduceIte, ban]
                  have hg0 := hok0 y (Finset.mem_erase.mpr ⟨hy'.1, hy0⟩)
                  exact ⟨qLe_trans hr0_next.1.1 hg0.1, hg0.2⟩
              · intro y1 hy1 y2 hy2 h12
                have hy1' := Finset.mem_erase.mp hy1
                have hy2' := Finset.mem_erase.mp hy2
                rcases Finset.mem_insert.mp hy1'.2 with h1b | h10 <;> rcases Finset.mem_insert.mp hy2'.2 with h2b | h20
                · rw [h1b, h2b]; dsimp only; simp only [↓reduceIte]; exact qLe_refl r0
                · rw [h1b]; have hne2 : y2 ≠ base := fun h => hbase_not_V0 (h ▸ h20)
                  dsimp only; rw [if_pos rfl, if_neg hne2]; exact (hok0 y2 (Finset.mem_erase.mpr ⟨hy2'.1, h20⟩)).1
                · rw [h2b] at h12; exfalso
                  exact htBit_not_used (hbase_sub (h12 ((hdom0 y1 h10).1 (Finset.mem_insert_self tBit base))))
                · have hne1 : y1 ≠ base := fun h => hbase_not_V0 (h ▸ h10)
                  have hne2 : y2 ≠ base := fun h => hbase_not_V0 (h ▸ h20)
                  simp only [hne1, hne2, ↓reduceIte]
                  exact hm0 y1 (Finset.mem_erase.mpr ⟨hy1'.1, h10⟩) y2 (Finset.mem_erase.mpr ⟨hy2'.1, h20⟩) h12
      · -- Case 2: some bit of p.2 is false! Branch on all zeros using dualRail in block (p.1.val, popCnt p.2)!
        have hnot : ∃ i : Fin a, p.2 i = false := by
          by_contra hno; push Not at hno
          apply hall; intro i; cases hi : p.2 i
          · exact False.elim (hno i hi)
          · rfl
        rcases hnot with ⟨i0, hi0⟩
        let k := popCnt p.2
        have hk_lt : k < a := by
          have hsub : (Finset.univ : Finset (Fin a)).filter (fun i => p.2 i = true) ⊂ Finset.univ := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.subset_univ _, fun heq => ?_⟩
            have : i0 ∈ (Finset.univ : Finset (Fin a)).filter (fun i => p.2 i = true) := by rw [heq]; exact Finset.mem_univ _
            have := (Finset.mem_filter.mp this).2
            rw [hi0] at this; cases this
          have := Finset.card_lt_card hsub
          rw [Finset.card_fin] at this
          exact this
        let zeros : Finset (Fin a) := Finset.univ.filter (fun i => p.2 i = false)
        have hblk_len : blockOff a L p.1.val k + 2 * L ≤ n := by
          dsimp only [n, blockOff]
          have h1 : (p.1.val * a + k) * (2 * L) + 2 * L = (p.1.val * a + (k + 1)) * (2 * L) := by ring
          rw [h1]
          have h2 : p.1.val * a + (k + 1) ≤ q * a := by
            have hp1 := p.1.isLt
            have h3 : (p.1.val + 1) * a ≤ q * a := Nat.mul_le_mul_right a (by omega)
            linarith [show (p.1.val + 1) * a = p.1.val * a + a by ring]
          have h4 : (p.1.val * a + (k + 1)) * (2 * L) ≤ q * a * (2 * L) :=
            Nat.mul_le_mul_right (2 * L) h2
          omega
        let blk : Fin a → Finset (Fin n) := fun i => dualRail (blockOff a L p.1.val k) L hblk_len i.val
        let rOf : Fin a → QState a q := fun i => (p.1, Function.update p.2 i true)
        have hpop_rOf : ∀ i ∈ zeros, popCnt (rOf i).2 = k + 1 := by
          intro i hi
          have hiw : p.2 i = false := (Finset.mem_filter.mp hi).2
          dsimp only [rOf, k]
          unfold popCnt
          have hins : (Finset.univ : Finset (Fin a)).filter (fun j => Function.update p.2 i true j = true) =
              insert i ((Finset.univ : Finset (Fin a)).filter (fun j => p.2 j = true)) := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            by_cases hji : j = i
            · subst hji; simp
            · simp [hji]
          have hni : i ∉ (Finset.univ : Finset (Fin a)).filter (fun j => p.2 j = true) := by simp [hiw]
          rw [hins, Finset.card_insert_of_notMem hni]
        have hcov_img : qCovers p = zeros.image rOf := by
          ext r
          simp only [qCovers, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, zeros, rOf]
          have hiff := qNext_iff_of_not_all_true (t := p.1) ⟨i0, hi0⟩ r
          have hp_eq : (p.1, p.2) = p := rfl
          rw [hp_eq] at hiff
          rw [hiff]
          constructor
          · rintro ⟨ht, i, hiw, hr2⟩; exact ⟨i, hiw, Prod.ext ht.symm hr2.symm⟩
          · rintro ⟨i, hiw, rfl⟩; exact ⟨rfl, i, hiw, rfl⟩
        have hrOf_inj : Set.InjOn rOf (zeros : Set (Fin a)) := by
          intro i1 hi1 i2 hi2 heq
          have h1 : p.2 i1 = false := (Finset.mem_filter.mp hi1).2
          have hfn := congrFun (congrArg Prod.snd heq) i1
          by_contra hne
          simp [rOf, hne, h1] at hfn
        have hblk_disj_used : ∀ i : Fin a, Disjoint (blk i) (usedMask p L n) := by
          intro i
          rw [Finset.disjoint_left]
          intro c hc1 hc2
          have hcr := dualRail_mem_range hc1
          have hc2' := (Finset.mem_filter.mp hc2).2
          have hle_qa : blockOff a L p.1.val k + 2 * L ≤ q * a * (2 * L) := by
            dsimp only [blockOff]
            have h1 : (p.1.val * a + k) * (2 * L) + 2 * L = (p.1.val * a + (k + 1)) * (2 * L) := by ring
            rw [h1]
            have hp1 := p.1.isLt
            have h2 : p.1.val * a + (k + 1) ≤ q * a := by
              have h3 : (p.1.val + 1) * a ≤ q * a := Nat.mul_le_mul_right a (by omega)
              linarith [show (p.1.val + 1) * a = p.1.val * a + a by ring]
            exact Nat.mul_le_mul_right (2 * L) h2
          rcases hc2' with hlt | ⟨hlo, _⟩
          · dsimp only [k] at hcr; omega
          · omega
        have hused_sub : ∀ i ∈ zeros, usedMask p L n ⊆ usedMask (rOf i) L n := by
          intro i hi c hc
          have hc' := (Finset.mem_filter.mp hc).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ c, ?_⟩
          rw [hpop_rOf i hi]
          dsimp only [rOf, blockOff, transOff] at hc' ⊢
          rcases hc' with h1 | h2
          · left
            dsimp only [k]
            have : (p.1.val * a + popCnt p.2) * (2 * L) ≤ (p.1.val * a + (popCnt p.2 + 1)) * (2 * L) :=
              Nat.mul_le_mul_right (2 * L) (by omega)
            omega
          · right; exact h2
        have hblk_in_used : ∀ i ∈ zeros, blk i ⊆ usedMask (rOf i) L n := by
          intro i hi c hc
          have hcr := dualRail_mem_range hc
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ c, Or.inl ?_⟩
          rw [hpop_rOf i hi]
          dsimp only [rOf, blockOff] at hcr ⊢
          have h1 : (p.1.val * a + k) * (2 * L) + 2 * L = (p.1.val * a + (k + 1)) * (2 * L) := by ring
          omega
        have hchild_ex : ∀ i ∈ zeros,
            ∃ (Vi : Finset (Finset (Fin n))) (bani : Finset (Fin n) → (Fin a → Bool)),
              IsForest Vi ∧ Vi.card = pathsCount (rOf i) ∧
              (∀ x ∈ Vi, base ∪ blk i ⊆ x ∧ x ∩ usedMask (rOf i) L n = base ∪ blk i) ∧
              (∀ u : QState a q, FitPoset Vi (fun x w => w ≠ bani x) u ↔ ¬ qLe (rOf i) u) ∧
              (∀ x ∈ Vi, FitPoset (Vi.erase x) (fun y w => w ≠ bani y) (rOf i)) := by
          intro i hi
          have hcov_i : rOf i ∈ qCovers p := by rw [hcov_img]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
          have hlt_m : qMeas (rOf i) < d := by
            rw [← hmd]; exact qMeas_lt_of_qLt (Finset.mem_filter.mp hcov_i).2.1
          have hbi_sub : base ∪ blk i ⊆ usedMask (rOf i) L n := by
            intro c hc
            rcases Finset.mem_union.mp hc with hcb | hck
            · exact hused_sub i hi (hbase_sub hcb)
            · exact hblk_in_used i hi hck
          exact ih (qMeas (rOf i)) hlt_m (rOf i) (base ∪ blk i) rfl hbi_sub
        let Vch : (i : Fin a) → i ∈ zeros → Finset (Finset (Fin n)) :=
          fun i hi => Classical.choose (hchild_ex i hi)
        let banch : (i : Fin a) → i ∈ zeros → Finset (Fin n) → (Fin a → Bool) :=
          fun i hi => Classical.choose (Classical.choose_spec (hchild_ex i hi))
        have hch_spec : ∀ i hi,
            IsForest (Vch i hi) ∧ (Vch i hi).card = pathsCount (rOf i) ∧
            (∀ x ∈ Vch i hi, base ∪ blk i ⊆ x ∧ x ∩ usedMask (rOf i) L n = base ∪ blk i) ∧
            (∀ u : QState a q, FitPoset (Vch i hi) (fun x w => w ≠ banch i hi x) u ↔ ¬ qLe (rOf i) u) ∧
            (∀ x ∈ Vch i hi, FitPoset ((Vch i hi).erase x) (fun y w => w ≠ banch i hi y) (rOf i)) :=
          fun i hi => Classical.choose_spec (Classical.choose_spec (hchild_ex i hi))
        -- Key incomparability lemma across distinct child trees!
        have hincomp : ∀ (i1 : Fin a) (h1 : i1 ∈ zeros) (i2 : Fin a) (h2 : i2 ∈ zeros)
            (y1 : Finset (Fin n)) (y2 : Finset (Fin n)),
            y1 ∈ Vch i1 h1 → y2 ∈ Vch i2 h2 → y1 ⊆ y2 → i1 = i2 := by
          intro i1 h1 i2 h2 y1 y2 hy1 hy2 hsub
          have hblk1_sub_y2 : blk i1 ⊆ y2 :=
            Finset.Subset.trans (Finset.subset_union_right) (Finset.Subset.trans ((hch_spec i1 h1).2.2.1 y1 hy1).1 hsub)
          have hused_eq : usedMask (rOf i1) L n = usedMask (rOf i2) L n := by
            ext c; simp only [usedMask, Finset.mem_filter, Finset.mem_univ, true_and, rOf, hpop_rOf i1 h1, hpop_rOf i2 h2]
          have hblk1_sub_b2 : blk i1 ⊆ base ∪ blk i2 := by
            rw [← ((hch_spec i2 h2).2.2.1 y2 hy2).2]
            intro c hc
            exact Finset.mem_inter.mpr ⟨hblk1_sub_y2 hc, hused_eq ▸ hblk_in_used i1 h1 hc⟩
          have hblk1_sub_blk2 : blk i1 ⊆ blk i2 := by
            intro c hc
            rcases Finset.mem_union.mp (hblk1_sub_b2 hc) with hcb | hck
            · exact False.elim (Finset.disjoint_left.mp (hblk_disj_used i1) hc (hbase_sub hcb))
            · exact hck
          exact Fin.ext (dualRail_eq_of_subset (lt_trans i1.isLt ha_lt_pow) (lt_trans i2.isLt ha_lt_pow) hblk1_sub_blk2)
        have hbase_not_ch : ∀ i hi, base ∉ Vch i hi := by
          intro i hi hmem
          rcases dualRail_nonempty hL_pos hblk_len i.val with ⟨c, hc⟩
          have hc_base : c ∈ base := ((hch_spec i hi).2.2.1 base hmem).1 (Finset.mem_union_right base hc)
          exact Finset.disjoint_left.mp (hblk_disj_used i) hc (hbase_sub hc_base)
        let Uall : Finset (Finset (Fin n)) := zeros.attach.biUnion (fun i => Vch i.val i.property)
        have hbase_not_U : base ∉ Uall := by
          intro hmem
          rcases Finset.mem_biUnion.mp hmem with ⟨i, _, hi⟩
          exact hbase_not_ch i.val i.property hi
        let V := insert base Uall
        let ban : Finset (Fin n) → (Fin a → Bool) := fun y =>
          if y = base then p.2
          else if h : ∃ i : {i : Fin a // i ∈ zeros}, y ∈ Vch i.val i.property then
            let idx := Classical.choose h
            banch idx.val idx.property y
          else p.2
        have hsub_app : ∀ {β : Type} (f : (i : Fin a) → i ∈ zeros → β)
            {s1 s2 : {i : Fin a // i ∈ zeros}}, s1 = s2 → f s1.val s1.property = f s2.val s2.property := by
          intro β f s1 s2 h; subst h; rfl
        have hban_ch : ∀ (i : Fin a) (hi : i ∈ zeros) (y : Finset (Fin n)),
            y ∈ Vch i hi → ban y = banch i hi y := by
          intro i hi y hy
          have hne : y ≠ base := fun h => hbase_not_ch i hi (h ▸ hy)
          have hex : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property := ⟨⟨i, hi⟩, hy⟩
          dsimp only [ban]
          rw [if_neg hne, dif_pos hex]
          have hspec := Classical.choose_spec hex
          have heq_val : (Classical.choose hex).val = i := hincomp _ (Classical.choose hex).property i hi y y hspec hy (Finset.Subset.refl y)
          have heq_sub : Classical.choose hex = ⟨i, hi⟩ := Subtype.ext heq_val
          exact hsub_app (fun i hi => banch i hi y) heq_sub
        refine ⟨V, ban, ?_, ?_, ?_, ?_, ?_⟩
        · -- IsForest V
          intro x hx y hy z hz hyx hzx
          rcases Finset.mem_insert.mp hy with hyeq | hyU
          · left; rw [hyeq]
            rcases Finset.mem_insert.mp hz with hzeq | hzU
            · rw [hzeq]
            · rcases Finset.mem_biUnion.mp hzU with ⟨i, _, hzi⟩
              exact Finset.Subset.trans Finset.subset_union_left ((hch_spec i.val i.property).2.2.1 z hzi).1
          · rcases Finset.mem_insert.mp hz with hzeq | hzU
            · right; rw [hzeq]
              rcases Finset.mem_biUnion.mp hyU with ⟨i, _, hyi⟩
              exact Finset.Subset.trans Finset.subset_union_left ((hch_spec i.val i.property).2.2.1 y hyi).1
            · rcases Finset.mem_biUnion.mp hyU with ⟨iy, _, hyi⟩
              rcases Finset.mem_biUnion.mp hzU with ⟨iz, _, hzi⟩
              rcases Finset.mem_insert.mp hx with hxb | hxU
              · rw [hxb] at hyx; exfalso
                rcases dualRail_nonempty hL_pos hblk_len iy.val.val with ⟨c, hc⟩
                have hc_y : c ∈ y := ((hch_spec iy.val iy.property).2.2.1 y hyi).1 (Finset.mem_union_right base hc)
                exact Finset.disjoint_left.mp (hblk_disj_used iy.val) hc (hbase_sub (hyx hc_y))
              · rcases Finset.mem_biUnion.mp hxU with ⟨ix, _, hxi⟩
                have heq_yx : iy = ix := Subtype.ext (hincomp iy.val iy.property ix.val ix.property y x hyi hxi hyx)
                have heq_zx : iz = ix := Subtype.ext (hincomp iz.val iz.property ix.val ix.property z x hzi hxi hzx)
                rw [heq_yx] at hyi
                rw [heq_zx] at hzi
                exact (hch_spec ix.val ix.property).1 x hxi y hyi z hzi hyx hzx
        · -- V.card = pathsCount p
          dsimp only [V]
          rw [Finset.card_insert_of_notMem hbase_not_U, pathsCount_eq, hcov_img, Finset.sum_image hrOf_inj]
          have hdisj_U : (zeros.attach : Set {i : Fin a // i ∈ zeros}).PairwiseDisjoint (fun i => Vch i.val i.property) := by
            intro i1 _ i2 _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro y hy1 hy2
            exact hne (Subtype.ext (hincomp i1.val i1.property i2.val i2.property y y hy1 hy2 (Finset.Subset.refl y)))
          rw [Finset.card_biUnion hdisj_U]
          have hsum_eq : zeros.attach.sum (fun i => (Vch i.val i.property).card) = zeros.sum (fun i => pathsCount (rOf i)) := by
            calc zeros.attach.sum (fun i => (Vch i.val i.property).card)
                = zeros.attach.sum (fun i => pathsCount (rOf i.val)) :=
                  Finset.sum_congr rfl (fun i _ => (hch_spec i.val i.property).2.1)
              _ = zeros.sum (fun i => pathsCount (rOf i)) := Finset.sum_attach zeros (fun i => pathsCount (rOf i))
          omega
        · -- base ⊆ x ∧ x ∩ usedMask p = base
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxU
          · exact ⟨Finset.Subset.refl _, Finset.inter_eq_left.mpr hbase_sub⟩
          · rcases Finset.mem_biUnion.mp hxU with ⟨i, _, hxi⟩
            rcases (hch_spec i.val i.property).2.2.1 x hxi with ⟨hsub, hinter⟩
            refine ⟨Finset.Subset.trans Finset.subset_union_left hsub, ?_⟩
            ext c; simp only [Finset.mem_inter]
            constructor
            · rintro ⟨hcx, hcu⟩
              have hci : c ∈ x ∩ usedMask (rOf i.val) L n := Finset.mem_inter.mpr ⟨hcx, hused_sub i.val i.property hcu⟩
              rw [hinter] at hci
              rcases Finset.mem_union.mp hci with hcb | hck
              · exact hcb
              · exact False.elim (Finset.disjoint_left.mp (hblk_disj_used i.val) hck hcu)
            · intro hcb
              exact ⟨hsub (Finset.mem_union_left _ hcb), hbase_sub hcb⟩
        · -- FitPoset V ok u ↔ ¬ qLe p u
          intro u
          constructor
          · rintro ⟨g, hok, hm⟩ hpu
            have hgb := hok base (Finset.mem_insert_self base Uall)
            have hp_le := qLe_trans hpu hgb.1
            have hp_ne : p ≠ g base := by
              intro heq; have h2 : (g base).2 = p.2 := congrArg Prod.snd heq.symm
              have := hgb.2; simp only [ban, ↓reduceIte] at this; exact this h2
            rcases exists_qNext_between ⟨hp_le, hp_ne⟩ with ⟨c, hpc, hcg⟩
            have hc_mem : c ∈ zeros.image rOf := by rw [← hcov_img]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩
            rcases Finset.mem_image.mp hc_mem with ⟨i, hi, rfl⟩
            have hfit_i : FitPoset (Vch i hi) (fun y w => w ≠ banch i hi y) (rOf i) := by
              refine ⟨g, ?_, fun x hx y hy hxy => hm x (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, hx⟩))
                  y (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, hy⟩)) hxy⟩
              intro y hy
              have hyV : y ∈ V := Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, hy⟩)
              have hby : base ⊆ y := Finset.Subset.trans Finset.subset_union_left ((hch_spec i hi).2.2.1 y hy).1
              refine ⟨qLe_trans hcg (hm base (Finset.mem_insert_self _ _) y hyV hby), ?_⟩
              dsimp only; rw [← hban_ch i hi y hy]; exact (hok y hyV).2
            exact (((hch_spec i hi).2.2.2.1 (rOf i)).mp hfit_i) (qLe_refl _)
          · intro hnot
            have hex_u' : ∃ u' : QState a q, qLe u u' ∧ u'.2 ≠ p.2 ∧ ¬ qLe p u' := by
              by_cases hu2 : u.2 ≠ p.2
              · exact ⟨u, qLe_refl u, hu2, hnot⟩
              · push Not at hu2
                have hult : u.1.val < p.1.val := by
                  by_contra hge
                  apply hnot
                  by_cases heq1 : p.1.val = u.1.val
                  · exact Or.inr ⟨Fin.ext heq1, fun i hi => by rw [hu2]; exact hi⟩
                  · exact Or.inl (by omega)
                let u' : QState a q := (u.1, Function.update p.2 i0 true)
                refine ⟨u', Or.inr ⟨rfl, fun j hj => ?_⟩, ?_, ?_⟩
                · by_cases hji : j = i0
                  · subst hji; simp [u']
                  · rw [hu2] at hj; simp [u', hji, hj]
                · intro h; have := congrFun h i0; simp [u', hi0] at this
                · intro hpu'
                  rcases hpu' with hlt | ⟨heq, _⟩
                  · dsimp only [u'] at hlt; omega
                  · dsimp only [u'] at heq; rw [heq] at hult; omega
            rcases hex_u' with ⟨u', huu', hu'ne, hnot_pu'⟩
            have hgi : ∀ i (hi : i ∈ zeros), FitPoset (Vch i hi) (fun y w => w ≠ banch i hi y) u' := by
              intro i hi
              apply ((hch_spec i hi).2.2.2.1 u').mpr
              intro hle
              have hcov_i : rOf i ∈ qCovers p := by rw [hcov_img]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
              exact hnot_pu' (qLe_trans (Finset.mem_filter.mp hcov_i).2.1.1 hle)
            let gch : (i : Fin a) → i ∈ zeros → Finset (Fin n) → QState a q :=
              fun i hi => Classical.choose (hgi i hi)
            have hgch_spec : ∀ i hi, (∀ y ∈ Vch i hi, qLe u' (gch i hi y) ∧ (gch i hi y).2 ≠ banch i hi y) ∧
                ∀ y1 ∈ Vch i hi, ∀ y2 ∈ Vch i hi, y1 ⊆ y2 → qLe (gch i hi y1) (gch i hi y2) :=
              fun i hi => Classical.choose_spec (hgi i hi)
            let g : Finset (Fin n) → QState a q := fun y =>
              if y = base then u'
              else if h : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property then
                let idx := Classical.choose h
                gch idx.val idx.property y
              else u'
            have hg_base : g base = u' := by simp [g]
            have hg_ch : ∀ i hi y, y ∈ Vch i hi → g y = gch i hi y := by
              intro i hi y hy
              have hne : y ≠ base := fun h => hbase_not_ch i hi (h ▸ hy)
              have hex : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property := ⟨⟨i, hi⟩, hy⟩
              dsimp only [g]; rw [if_neg hne, dif_pos hex]
              have hsub : Classical.choose hex = ⟨i, hi⟩ :=
                Subtype.ext (hincomp _ (Classical.choose hex).property i hi y y (Classical.choose_spec hex) hy (Finset.Subset.refl y))
              exact hsub_app (fun i hi => gch i hi y) hsub
            refine ⟨g, ?_, ?_⟩
            · intro y hy
              rcases Finset.mem_insert.mp hy with rfl | hyU
              · simp only [g, ban, ↓reduceIte]; exact ⟨huu', hu'ne⟩
              · rcases Finset.mem_biUnion.mp hyU with ⟨i, _, hyi⟩
                dsimp only
                rw [hg_ch i.val i.property y hyi, hban_ch i.val i.property y hyi]
                have hsp := (hgch_spec i.val i.property).1 y hyi
                exact ⟨qLe_trans huu' hsp.1, hsp.2⟩
            · intro x hx y hy hxy
              rcases Finset.mem_insert.mp hx with hxb | hxU <;> rcases Finset.mem_insert.mp hy with hyb | hyU
              · rw [hxb, hyb, hg_base]; exact qLe_refl u'
              · rw [hxb]; rcases Finset.mem_biUnion.mp hyU with ⟨i, _, hyi⟩
                rw [hg_base, hg_ch i.val i.property y hyi]
                exact ((hgch_spec i.val i.property).1 y hyi).1
              · rw [hyb] at hxy; exfalso
                rcases Finset.mem_biUnion.mp hxU with ⟨i, _, hxi⟩
                rcases dualRail_nonempty hL_pos hblk_len i.val.val with ⟨c, hc⟩
                exact Finset.disjoint_left.mp (hblk_disj_used i.val) hc
                  (hbase_sub (hxy (((hch_spec i.val i.property).2.2.1 x hxi).1 (Finset.mem_union_right base hc))))
              · rcases Finset.mem_biUnion.mp hxU with ⟨ix, _, hxi⟩
                rcases Finset.mem_biUnion.mp hyU with ⟨iy, _, hyi⟩
                have heq : ix = iy := Subtype.ext (hincomp ix.val ix.property iy.val iy.property x y hxi hyi hxy)
                subst heq
                rw [hg_ch ix.val ix.property x hxi, hg_ch ix.val ix.property y hyi]
                exact (hgch_spec ix.val ix.property).2 x hxi y hyi hxy
        · -- ∀ x ∈ V, FitPoset (V.erase x) ok p
          intro x hx
          rcases Finset.mem_insert.mp hx with hxb | hxU
          · -- Erase root base: V.erase base = Uall; solve each Vch i hi at p!
            rw [hxb]
            have her : V.erase base = Uall := Finset.erase_insert hbase_not_U
            rw [her]
            have hgi : ∀ i (hi : i ∈ zeros), FitPoset (Vch i hi) (fun y w => w ≠ banch i hi y) p := by
              intro i hi
              apply ((hch_spec i hi).2.2.2.1 p).mpr
              intro hle
              have hcov_i : rOf i ∈ qCovers p := by rw [hcov_img]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
              have hlt_i := (Finset.mem_filter.mp hcov_i).2.1
              exact hlt_i.2 (qLe_antisymm hlt_i.1 hle)
            let gch : (i : Fin a) → i ∈ zeros → Finset (Fin n) → QState a q :=
              fun i hi => Classical.choose (hgi i hi)
            have hgch_spec : ∀ i hi, (∀ y ∈ Vch i hi, qLe p (gch i hi y) ∧ (gch i hi y).2 ≠ banch i hi y) ∧
                ∀ y1 ∈ Vch i hi, ∀ y2 ∈ Vch i hi, y1 ⊆ y2 → qLe (gch i hi y1) (gch i hi y2) :=
              fun i hi => Classical.choose_spec (hgi i hi)
            let g : Finset (Fin n) → QState a q := fun y =>
              if h : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property then
                let idx := Classical.choose h
                gch idx.val idx.property y
              else p
            have hg_ch : ∀ i hi y, y ∈ Vch i hi → g y = gch i hi y := by
              intro i hi y hy
              have hex : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property := ⟨⟨i, hi⟩, hy⟩
              dsimp only [g]; rw [dif_pos hex]
              have hsub : Classical.choose hex = ⟨i, hi⟩ :=
                Subtype.ext (hincomp _ (Classical.choose hex).property i hi y y (Classical.choose_spec hex) hy (Finset.Subset.refl y))
              exact hsub_app (fun i hi => gch i hi y) hsub
            refine ⟨g, ?_, ?_⟩
            · intro y hyU
              rcases Finset.mem_biUnion.mp hyU with ⟨i, _, hyi⟩
              dsimp only
              rw [hg_ch i.val i.property y hyi, hban_ch i.val i.property y hyi]
              exact (hgch_spec i.val i.property).1 y hyi
            · intro y1 hy1 y2 hy2 h12
              rcases Finset.mem_biUnion.mp hy1 with ⟨i1, _, h1i⟩
              rcases Finset.mem_biUnion.mp hy2 with ⟨i2, _, h2i⟩
              have heq : i1 = i2 := Subtype.ext (hincomp i1.val i1.property i2.val i2.property y1 y2 h1i h2i h12)
              subst heq
              rw [hg_ch i1.val i1.property y1 h1i, hg_ch i1.val i1.property y2 h2i]
              exact (hgch_spec i1.val i1.property).2 y1 h1i y2 h2i h12
          · -- Erase x ∈ Vch iStar hiStar: assign base ↦ rOf iStar, solve (Vch iStar).erase x at rOf iStar, and all other Vch i at rOf iStar!
            rcases Finset.mem_biUnion.mp hxU with ⟨iStar, _, hx_iStar⟩
            rcases (hch_spec iStar.val iStar.property).2.2.2.2 x hx_iStar with ⟨gStar, hokStar, hmStar⟩
            have hcov_star : rOf iStar.val ∈ qCovers p := by
              rw [hcov_img]; exact Finset.mem_image.mpr ⟨iStar.val, iStar.property, rfl⟩
            have hp_le_star : qLe p (rOf iStar.val) := (Finset.mem_filter.mp hcov_star).2.1.1
            have hstar_ne_p : (rOf iStar.val).2 ≠ p.2 := by
              intro h; have := congrFun h iStar.val
              have hw := (Finset.mem_filter.mp iStar.property).2
              simp [rOf, hw] at this
            have hother : ∀ i (hi : i ∈ zeros), i ≠ iStar.val →
                FitPoset (Vch i hi) (fun y w => w ≠ banch i hi y) (rOf iStar.val) := by
              intro i hi hne
              apply ((hch_spec i hi).2.2.2.1 (rOf iStar.val)).mpr
              intro hle
              rcases hle with hlt | ⟨_, hm⟩
              · dsimp only [rOf] at hlt; omega
              · have h1 := hm i (by simp [rOf])
                have hw := (Finset.mem_filter.mp hi).2
                simp [rOf, hne, hw] at h1
            let gOth : (i : Fin a) → (hi : i ∈ zeros) → i ≠ iStar.val → Finset (Fin n) → QState a q :=
              fun i hi hne => Classical.choose (hother i hi hne)
            have hgOth_spec : ∀ i hi hne,
                (∀ y ∈ Vch i hi, qLe (rOf iStar.val) (gOth i hi hne y) ∧ (gOth i hi hne y).2 ≠ banch i hi y) ∧
                ∀ y1 ∈ Vch i hi, ∀ y2 ∈ Vch i hi, y1 ⊆ y2 → qLe (gOth i hi hne y1) (gOth i hi hne y2) :=
              fun i hi hne => Classical.choose_spec (hother i hi hne)
            let g : Finset (Fin n) → QState a q := fun y =>
              if y = base then rOf iStar.val
              else if h : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property then
                let idx := Classical.choose h
                if heq : idx.val = iStar.val then gStar y
                else gOth idx.val idx.property heq y
              else rOf iStar.val
            have hg_star : ∀ y, y ∈ Vch iStar.val iStar.property → g y = gStar y := by
              intro y hy
              have hne : y ≠ base := fun h => hbase_not_ch iStar.val iStar.property (h ▸ hy)
              have hex : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property := ⟨iStar, hy⟩
              dsimp only [g]; rw [if_neg hne, dif_pos hex]
              have hval : (Classical.choose hex).val = iStar.val :=
                hincomp _ (Classical.choose hex).property iStar.val iStar.property y y (Classical.choose_spec hex) hy (Finset.Subset.refl y)
              rw [dif_pos hval]
            have hg_base : g base = rOf iStar.val := by simp [g]
            have hg_oth : ∀ i hi (hne : i ≠ iStar.val) y, y ∈ Vch i hi → g y = gOth i hi hne y := by
              intro i hi hne y hy
              have hneb : y ≠ base := fun h => hbase_not_ch i hi (h ▸ hy)
              have hex : ∃ idx : {i : Fin a // i ∈ zeros}, y ∈ Vch idx.val idx.property := ⟨⟨i, hi⟩, hy⟩
              dsimp only [g]; rw [if_neg hneb, dif_pos hex]
              have hsub : Classical.choose hex = ⟨i, hi⟩ :=
                Subtype.ext (hincomp _ (Classical.choose hex).property i hi y y (Classical.choose_spec hex) hy (Finset.Subset.refl y))
              have hne_c : (Classical.choose hex).val ≠ iStar.val := by
                rw [congrArg Subtype.val hsub]; exact hne
              rw [dif_neg hne_c]
              have hfn : ∀ (s1 s2 : {i : Fin a // i ∈ zeros}) (h1 : s1.val ≠ iStar.val) (h2 : s2.val ≠ iStar.val),
                  s1 = s2 → gOth s1.val s1.property h1 y = gOth s2.val s2.property h2 y := by
                intro s1 s2 h1 h2 hs; subst hs; rfl
              exact hfn (Classical.choose hex) ⟨i, hi⟩ hne_c hne hsub
            refine ⟨g, ?_, ?_⟩
            · intro y hy
              have hy' := Finset.mem_erase.mp hy
              rcases Finset.mem_insert.mp hy'.2 with rfl | hyU
              · simp only [g, ban, ↓reduceIte]; exact ⟨hp_le_star, hstar_ne_p⟩
              · rcases Finset.mem_biUnion.mp hyU with ⟨i, _, hyi⟩
                dsimp only
                rw [hban_ch i.val i.property y hyi]
                by_cases his : i.val = iStar.val
                · have his' : i = iStar := Subtype.ext his
                  subst his'
                  rw [hg_star y hyi]
                  have hs := hokStar y (Finset.mem_erase.mpr ⟨hy'.1, hyi⟩)
                  exact ⟨qLe_trans hp_le_star hs.1, hs.2⟩
                · rw [hg_oth i.val i.property his y hyi]
                  have hs := (hgOth_spec i.val i.property his).1 y hyi
                  exact ⟨qLe_trans hp_le_star hs.1, hs.2⟩
            · intro y1 hy1 y2 hy2 h12
              have hy1' := Finset.mem_erase.mp hy1
              have hy2' := Finset.mem_erase.mp hy2
              rcases Finset.mem_insert.mp hy1'.2 with h1b | h1U <;> rcases Finset.mem_insert.mp hy2'.2 with h2b | h2U
              · rw [h1b, h2b, hg_base]; exact qLe_refl _
              · rw [h1b, hg_base]
                rcases Finset.mem_biUnion.mp h2U with ⟨i2, _, h2i⟩
                by_cases his : i2.val = iStar.val
                · have his' : i2 = iStar := Subtype.ext his
                  subst his'
                  rw [hg_star y2 h2i]
                  exact (hokStar y2 (Finset.mem_erase.mpr ⟨hy2'.1, h2i⟩)).1
                · rw [hg_oth i2.val i2.property his y2 h2i]
                  exact ((hgOth_spec i2.val i2.property his).1 y2 h2i).1
              · rw [h2b] at h12; exfalso
                rcases Finset.mem_biUnion.mp h1U with ⟨i1, _, h1i⟩
                rcases dualRail_nonempty hL_pos hblk_len i1.val.val with ⟨c, hc⟩
                exact Finset.disjoint_left.mp (hblk_disj_used i1.val) hc
                  (hbase_sub (h12 (((hch_spec i1.val i1.property).2.2.1 y1 h1i).1 (Finset.mem_union_right base hc))))
              · rcases Finset.mem_biUnion.mp h1U with ⟨i1, _, h1i⟩
                rcases Finset.mem_biUnion.mp h2U with ⟨i2, _, h2i⟩
                have heq : i1 = i2 := Subtype.ext (hincomp i1.val i1.property i2.val i2.property y1 y2 h1i h2i h12)
                subst heq
                by_cases his : i1.val = iStar.val
                · have his' : i1 = iStar := Subtype.ext his
                  subst his'
                  rw [hg_star y1 h1i, hg_star y2 h2i]
                  exact hmStar y1 (Finset.mem_erase.mpr ⟨hy1'.1, h1i⟩) y2 (Finset.mem_erase.mpr ⟨hy2'.1, h2i⟩) h12
                · rw [hg_oth i1.val i1.property his y1 h1i, hg_oth i1.val i1.property his y2 h2i]
                  exact (hgOth_spec i1.val i1.property his).2 y1 h1i y2 h2i h12
  intro p base hsub; exact hmain (qMeas p) p base rfl hsub

-- ============================================================================
-- Assembly of both parts and main_proof bridge
-- ============================================================================

private def boundOf (a b : Nat) : Nat :=
  let F := Nat.factorial a
  let H := (Finset.range (a + 1)).sum (fun j => F / Nat.factorial (a - j))
  if a = 0 then 1 else H * (Finset.range (2 ^ b)).sum (fun j => F ^ j)

private lemma main_1364_part1 (n a b : Nat) (V : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → (Fin a → Bool) → Prop) (hfor : IsForest V) :
    FitCirc n a b V ok ↔ ∀ S ⊆ V, S.card ≤ boundOf a b → FitCirc n a b S ok := by
  constructor
  · rintro ⟨C, tap, hF2, hRB, hout, hnb, htap, hok⟩ S hSV _
    exact ⟨C, tap, hF2, hRB, hout, hnb, htap, fun x hx => hok x (hSV hx)⟩
  · intro hloc
    by_cases ha0 : a = 0
    · subst ha0
      have hall : ∀ x ∈ V, ok x Fin.elim0 := by
        intro x hx
        have hsing : ({x} : Finset (Finset (Fin n))) ⊆ V := Finset.singleton_subset_iff.mpr hx
        have hcard : ({x} : Finset (Finset (Fin n))).card ≤ boundOf 0 b := by simp [boundOf]
        rcases hloc {x} hsing hcard with ⟨C, tap, _, _, _, _, _, hokx⟩
        have hfun : (fun i : Fin 0 => (C.wires (mkInput x)).getD (tap i) false) = Fin.elim0 := by
          funext i; exact Fin.elim0 i
        have := hokx x (Finset.mem_singleton_self x)
        rwa [hfun] at this
      let B0 := Bld.empty (n + 2)
      refine ⟨B0.toCircuit, Fin.elim0, B0.hF2, B0.hRB, by simp [B0, Bld.toCircuit],
        by simp [B0, Bld.toCircuit, Bld.empty, notCount], fun i => Fin.elim0 i, fun x hx => ?_⟩
      have hfun : (fun i : Fin 0 => (B0.toCircuit.wires (mkInput x)).getD (Fin.elim0 i) false) = Fin.elim0 := by
        funext i; exact Fin.elim0 i
      rw [hfun]; exact hall x hx
    · have ha1 : 1 ≤ a := by omega
      let bot : QState a (2 ^ b) := (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, fun _ => false)
      have hbd : pathsCount bot = boundOf a b := by
        dsimp only [boundOf, bot]; rw [if_neg ha0]
        exact pathsCount_bot_eq_bound a b ha1
      apply fitPoset_to_fitCirc
      apply forest_poset_helly V ok hfor bot
      intro S hSV hScard
      rw [hbd] at hScard
      have hforS : IsForest S := fun x hx y hy z hz => hfor x (hSV hx) y (hSV hy) z (hSV hz)
      exact fitCirc_to_fitPoset hforS (hloc S hSV hScard)

private lemma main_1364_part2 (a b : Nat) :
    ∃ (V : Finset (Finset (Fin (2 ^ b * a * (2 * (Nat.log2 a + 1)) + (2 ^ b - 1)))))
      (ban : Finset (Fin (2 ^ b * a * (2 * (Nat.log2 a + 1)) + (2 ^ b - 1))) → (Fin a → Bool)),
      IsForest V ∧ V.card = boundOf a b ∧
      (¬ FitCirc (2 ^ b * a * (2 * (Nat.log2 a + 1)) + (2 ^ b - 1)) a b V (fun x w => w ≠ ban x)) ∧
      ∀ x ∈ V, FitCirc (2 ^ b * a * (2 * (Nat.log2 a + 1)) + (2 ^ b - 1)) a b (V.erase x) (fun x w => w ≠ ban x) := by
  let q := 2 ^ b
  let n := q * a * (2 * (Nat.log2 a + 1)) + (q - 1)
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨{(∅ : Finset (Fin n))}, fun _ => Fin.elim0, ?_, (Finset.card_singleton (∅ : Finset (Fin n))).trans (by simp [boundOf]), ?_, ?_⟩
    · intro x hx y hy z hz _ _
      rw [Finset.mem_singleton.mp hy, Finset.mem_singleton.mp hz]; exact Or.inl (Finset.Subset.refl _)
    · rintro ⟨C, tap, _, _, _, _, _, hok⟩
      have h0 := hok ∅ (Finset.mem_singleton_self ∅)
      apply h0; funext i; exact Fin.elim0 i
    · intro x hx
      rw [Finset.mem_singleton.mp hx, Finset.erase_singleton]
      let B0 := Bld.empty (n + 2)
      exact ⟨B0.toCircuit, Fin.elim0, B0.hF2, B0.hRB, by simp [B0, Bld.toCircuit],
        by simp [B0, Bld.toCircuit, Bld.empty, notCount], fun i => Fin.elim0 i, fun _ h => by cases h⟩
  · have ha1 : 1 ≤ a := by omega
    let bot : QState a q := (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, fun _ => false)
    have hbd : pathsCount bot = boundOf a b := by
      dsimp only [boundOf, bot, q]; rw [if_neg ha0]
      exact pathsCount_bot_eq_bound a b ha1
    rcases build_sharp_tree a b ha1 bot ∅ (Finset.empty_subset _) with
      ⟨V, ban, hfor, hcard, _hdom, hfit_iff, herase⟩
    refine ⟨V, ban, hfor, by rw [hcard, hbd], ?_, ?_⟩
    · intro hfit
      have hpos := fitCirc_to_fitPoset hfor hfit
      exact ((hfit_iff bot).mp hpos) (qLe_refl bot)
    · intro x hx
      exact fitPoset_to_fitCirc (herase x hx)

private lemma mem_erase_of_decEq {α : Type} (d1 d2 : DecidableEq α) {V : Finset α} {x y : α}
    (hy : y ∈ @Finset.erase α d1 V x) : y ∈ @Finset.erase α d2 V x := by
  have h1 : y ≠ x ∧ y ∈ V := by
    letI : DecidableEq α := d1
    exact Finset.mem_erase.mp hy
  letI : DecidableEq α := d2
  exact Finset.mem_erase.mpr h1

private theorem main_proof :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let bound := fun (a b : Nat) =>
  let F := Nat.factorial a
  let H := (Finset.range (a+1)).sum (fun j => F / Nat.factorial (a-j))
  if a = 0 then 1 else H * (Finset.range (2^b)).sum (fun j => F^j)
let forest := fun (n : Nat) (V : Finset (Finset (Fin n))) =>
  ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y
let raw := fun (n : Nat) (x : Finset (Fin n)) =>
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
let fit := fun (n a b : Nat) (S : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → (Fin a → Bool) → Prop) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    (∀ i, tap i < n+2+C.size) ∧
    ∀ x ∈ S, ok x (fun i => (C.wires (raw n x)).getD (tap i) false)
(∀ (n a b : Nat) (V : Finset (Finset (Fin n))) (ok : Finset (Fin n) → (Fin a → Bool) → Prop),
  forest n V → (fit n a b V ok ↔ ∀ S ⊆ V, S.card ≤ bound a b → fit n a b S ok)) ∧
∀ a b : Nat,
  let q := 2^b
  let n := q*a*(2*(Nat.log2 a+1)) + (q-1)
  ∃ (V : Finset (Finset (Fin n))) (ban : Finset (Fin n) → (Fin a → Bool)),
    let ok := fun x w => w ≠ ban x
    forest n V ∧ V.card = bound a b ∧
    (¬ fit n a b V ok) ∧ ∀ x ∈ V, fit n a b (V.erase x) ok := by
  have hfit_eq : ∀ (n a b : Nat) (S : Finset (Finset (Fin n))) (ok : Finset (Fin n) → (Fin a → Bool) → Prop),
      (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
       ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
         PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
         C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
         (∀ i, tap i < n+2+C.size) ∧
         ∀ x ∈ S, ok x (fun i => (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false,true])).getD (tap i) false)) =
      FitCirc n a b S ok := fun _ _ _ _ _ => rfl
  have hbd_eq : ∀ a b : Nat,
      (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
       let F := Nat.factorial a
       let H := (Finset.range (a+1)).sum (fun j => F / Nat.factorial (a-j))
       if a = 0 then 1 else H * (Finset.range (2^b)).sum (fun j => F^j)) =
      boundOf a b := by
    intro a b; dsimp only [boundOf]; split_ifs <;> rfl
  constructor
  · intro n a b V ok hfor
    have h1 := main_1364_part1 n a b V ok hfor
    dsimp only
    rw [hfit_eq, hbd_eq]
    simpa only [hfit_eq] using h1
  · intro a b
    dsimp only
    rcases main_1364_part2 a b with ⟨V, ban, hfor, hcard, hnf, her⟩
    refine ⟨V, ban, hfor, ?_, ?_, ?_⟩
    · rw [hbd_eq]; exact hcard
    · change ¬ FitCirc _ a b V (fun x w => w ≠ ban x); exact hnf
    · intro x hx
      rcases her x hx with ⟨C, tap, h1, h2, h3, h4, h5, h6⟩
      refine ⟨C, tap, h1, h2, h3, h4, h5, fun y hy => h6 y (mem_erase_of_decEq _ _ hy)⟩

end PEqualNP.Outside.L_lib_1364

theorem PEqualNP.Outside.L_lib_1364 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let bound := fun (a b : Nat) =>
  let F := Nat.factorial a
  let H := (Finset.range (a+1)).sum (fun j => F / Nat.factorial (a-j))
  if a = 0 then 1 else H * (Finset.range (2^b)).sum (fun j => F^j)
let forest := fun (n : Nat) (V : Finset (Finset (Fin n))) =>
  ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y
let raw := fun (n : Nat) (x : Finset (Fin n)) =>
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
let fit := fun (n a b : Nat) (S : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → (Fin a → Bool) → Prop) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    (∀ i, tap i < n+2+C.size) ∧
    ∀ x ∈ S, ok x (fun i => (C.wires (raw n x)).getD (tap i) false)
(∀ (n a b : Nat) (V : Finset (Finset (Fin n))) (ok : Finset (Fin n) → (Fin a → Bool) → Prop),
  forest n V → (fit n a b V ok ↔ ∀ S ⊆ V, S.card ≤ bound a b → fit n a b S ok)) ∧
∀ a b : Nat,
  let q := 2^b
  let n := q*a*(2*(Nat.log2 a+1)) + (q-1)
  ∃ (V : Finset (Finset (Fin n))) (ban : Finset (Fin n) → (Fin a → Bool)),
    let ok := fun x w => w ≠ ban x
    forest n V ∧ V.card = bound a b ∧
    (¬ fit n a b V ok) ∧ ∀ x ∈ V, fit n a b (V.erase x) ok :=
  PEqualNP.Outside.L_lib_1364.main_proof
