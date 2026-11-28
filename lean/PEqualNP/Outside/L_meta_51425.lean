import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51425

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
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

private lemma mkInput_length {n : Nat} (x : Finset (Fin n)) :
    (mkInput x).length = n + 2 := by
  unfold mkInput; simp

private lemma mkInput_getD_lt {n : Nat} (x : Finset (Fin n)) (i : Fin n) :
    (mkInput x).getD i.val false = decide (i ∈ x) := by
  unfold mkInput
  have hlen : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j ∈ x))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact i.isLt),
      List.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some, Fin.eta]
  by_cases h : i ∈ x <;> simp [h]

private lemma mkInput_getD_false {n : Nat} (x : Finset (Fin n)) :
    (mkInput x).getD n false = false := by
  unfold mkInput
  have hlen : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j ∈ x))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

private lemma mkInput_getD_true {n : Nat} (x : Finset (Fin n)) :
    (mkInput x).getD (n + 1) false = true := by
  unfold mkInput
  have hlen : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      List.ofFn (fun j : Fin n => decide (j ∈ x))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen]
  have hsub : n + 1 - n = 1 := by omega
  rw [hsub]; rfl

private def listLe (l1 l2 : List Bool) : Prop :=
  l1.length = l2.length ∧ ∀ i, i < l1.length → l1.getD i false = true → l2.getD i false = true

private lemma mkInput_listLe {n : Nat} {x y : Finset (Fin n)} (h : x ⊆ y) :
    listLe (mkInput x) (mkInput y) := by
  refine ⟨by rw [mkInput_length, mkInput_length], ?_⟩
  intro i hi ht
  rw [mkInput_length] at hi
  by_cases hin : i < n
  · let fi : Fin n := ⟨i, hin⟩
    have ht' := mkInput_getD_lt x fi
    have hy' := mkInput_getD_lt y fi
    change (mkInput x).getD i false = decide (fi ∈ x) at ht'
    change (mkInput y).getD i false = decide (fi ∈ y) at hy'
    rw [ht'] at ht; rw [hy']
    have hx : fi ∈ x := of_decide_eq_true ht
    exact decide_eq_true (h hx)
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

-- ============================================================================
-- Helper definitions for L-meta-51425 (permutations, visits, pay, loss)
-- ============================================================================

private def absentOf {n : Nat} (x : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x)

private def preOf {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).image (fun i => π i)

private def visitsOf {n : Nat} (L : List (Equiv.Perm (Fin n))) (x : Finset (Fin n)) (j : Fin n) : Nat :=
  (L.filter (fun π => decide (preOf π (π.symm j) = x))).length

private def payOf {n : Nat} (w : Finset (Fin n) → Fin n → Nat) (L : List (Equiv.Perm (Fin n))) : Nat :=
  (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
    (absentOf x).sum (fun j => min (w x j) (visitsOf L x j)))

private lemma mem_preOf_iff {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) (a : Fin n) :
    a ∈ preOf π k ↔ (π.symm a).val < k.val := by
  unfold preOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact (Finset.mem_filter.mp hi).2
  · intro hlt
    exact ⟨π.symm a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, Equiv.apply_symm_apply π a⟩

private lemma not_mem_preOf_self {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    π k ∉ preOf π k := by
  rw [mem_preOf_iff, Equiv.symm_apply_apply]; exact lt_irrefl _

-- ============================================================================
-- Part 1: Lower bound pay L <= loss C a + (2^b - 1) * L.length
-- ============================================================================

private lemma single_perm_true_count_le {n b : Nat} (C : Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (hF2 : FanInTwo C) (hRB : ReadsBack (n + 2) C) (hb : notCount C ≤ b)
    (hone : ∀ (x : Finset (Fin n)) (j : Fin n), j ∈ x → (C.wires (mkInput x)).getD (a j).val false = false)
    (π : Equiv.Perm (Fin n)) :
    ((Finset.univ : Finset (Fin n)).filter (fun k =>
      (C.wires (mkInput (preOf π k))).getD (a (π k)).val false = true)).card ≤ 2 ^ b - 1 := by
  let M := n + 2
  let S : Fin (n + 1) → Finset (Fin n) := fun t =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < t.val)).image π
  have hS_sub : ∀ {t1 t2 : Fin (n + 1)}, t1 ≤ t2 → S t1 ⊆ S t2 := by
    intro t1 t2 hle x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi' : i.val < t1.val := (Finset.mem_filter.mp hi).2
    have hle' : t1.val ≤ t2.val := hle
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, rfl⟩
  have hS_pre : ∀ k : Fin n, S ⟨k.val, by omega⟩ = preOf π k := fun _ => rfl
  have hS_mem : ∀ k : Fin n, π k ∈ S ⟨k.val + 1, by omega⟩ := fun k =>
    Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, rfl⟩
  let nv : Fin (n + 1) → Fin (notIdxs C).length → Bool := fun t => notVec C M (mkInput (S t))
  let active : Finset (Fin n) := Finset.univ.filter (fun k =>
    (C.wires (mkInput (preOf π k))).getD (a (π k)).val false = true)
  let jumps : Finset (Fin n) := Finset.univ.filter (fun k =>
    nv ⟨k.val, by omega⟩ ≠ nv ⟨k.val + 1, by omega⟩)
  have hsub_jumps : active ⊆ jumps := by
    intro k hk
    have htrue : (C.wires (mkInput (preOf π k))).getD (a (π k)).val false = true :=
      (Finset.mem_filter.mp hk).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro heq
    have hfalse : (C.wires (mkInput (S ⟨k.val + 1, by omega⟩))).getD (a (π k)).val false = false :=
      hone (S ⟨k.val + 1, by omega⟩) (π k) (hS_mem k)
    have hmono := wires_mono_of_notVec_eq C hF2 hRB
      (mkInput (S ⟨k.val, by omega⟩)) (mkInput (S ⟨k.val + 1, by omega⟩))
      (mkInput_length _) (mkInput_length _)
      (mkInput_listLe (hS_sub (by show k.val ≤ k.val + 1; omega)))
      heq (a (π k)).val (a (π k)).isLt (by rwa [hS_pre])
    rw [hfalse] at hmono; cases hmono
  have hinj : Set.InjOn (fun k : Fin n => nv ⟨k.val, by omega⟩) (jumps : Set (Fin n)) := by
    intro k1 hk1 k2 hk2 heq
    have h1' := (Finset.mem_filter.mp hk1).2
    have h2' := (Finset.mem_filter.mp hk2).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
        (mkInput (S ⟨k1.val, by omega⟩)) (mkInput (S ⟨k1.val + 1, by omega⟩)) (mkInput (S ⟨k2.val, by omega⟩))
        (mkInput_length _) (mkInput_length _) (mkInput_length _)
        (mkInput_listLe (hS_sub (by show k1.val ≤ k1.val + 1; omega)))
        (mkInput_listLe (hS_sub (by show k1.val + 1 ≤ k2.val; exact hlt)))
        heq).2
      exact h1' hsw.symm
    · have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
        (mkInput (S ⟨k2.val, by omega⟩)) (mkInput (S ⟨k2.val + 1, by omega⟩)) (mkInput (S ⟨k1.val, by omega⟩))
        (mkInput_length _) (mkInput_length _) (mkInput_length _)
        (mkInput_listLe (hS_sub (by show k2.val ≤ k2.val + 1; omega)))
        (mkInput_listLe (hS_sub (by show k2.val + 1 ≤ k1.val; exact hgt)))
        heq.symm).2
      exact h2' hsw.symm
  let cLast := nv ⟨n, Nat.lt_succ_self n⟩
  have hne_last : ∀ k ∈ jumps, nv ⟨k.val, by omega⟩ ≠ cLast := by
    intro k hk heq
    have hk' := (Finset.mem_filter.mp hk).2
    have hsw := (wires_sandwich_and_notVec_eq C hF2 hRB
      (mkInput (S ⟨k.val, by omega⟩)) (mkInput (S ⟨k.val + 1, by omega⟩)) (mkInput (S ⟨n, Nat.lt_succ_self n⟩))
      (mkInput_length _) (mkInput_length _) (mkInput_length _)
      (mkInput_listLe (hS_sub (by show k.val ≤ k.val + 1; omega)))
      (mkInput_listLe (hS_sub (by show k.val + 1 ≤ n; exact k.isLt)))
      heq).2
    exact hk' hsw.symm
  have hsub_img : jumps.image (fun k : Fin n => nv ⟨k.val, by omega⟩) ⊆ Finset.univ.erase cLast := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨k, hk, rfl⟩
    exact Finset.mem_erase.mpr ⟨hne_last k hk, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub_img
  rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ] at hcard
  have hpow : 2 ^ (notIdxs C).length ≤ 2 ^ b := by
    rw [notIdxs_length]; exact Nat.pow_le_pow_right (by omega) hb
  have hle1 : jumps.card ≤ 2 ^ (notIdxs C).length - 1 := by simpa using hcard
  have hle2 : active.card ≤ jumps.card := Finset.card_le_card hsub_jumps
  change active.card ≤ 2 ^ b - 1
  omega

private lemma visitsOf_nil {n : Nat} (x : Finset (Fin n)) (j : Fin n) :
    visitsOf [] x j = 0 := rfl

private lemma visitsOf_cons {n : Nat} (π : Equiv.Perm (Fin n)) (L : List (Equiv.Perm (Fin n)))
    (x : Finset (Fin n)) (j : Fin n) :
    visitsOf (π :: L) x j = (if preOf π (π.symm j) = x then 1 else 0) + visitsOf L x j := by
  unfold visitsOf
  simp only [List.filter_cons]
  by_cases h : preOf π (π.symm j) = x <;> simp [h, Nat.add_comm]

private lemma sum_visits_eq_perm_sum {n : Nat} (P : Finset (Fin n) → Fin n → Bool)
    (L : List (Equiv.Perm (Fin n))) :
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      (absentOf x).sum (fun j => if P x j = true then visitsOf L x j else 0)) =
    (L.map (fun π => ((Finset.univ : Finset (Fin n)).filter (fun k => P (preOf π k) (π k) = true)).card)).sum := by
  induction L with
  | nil => simp [visitsOf_nil]
  | cons π tl ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    have hsplit : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = true then visitsOf (π :: tl) x j else 0)) =
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = true then (if preOf π (π.symm j) = x then 1 else 0) else 0)) +
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = true then visitsOf tl x j else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [visitsOf_cons]
      split_ifs <;> omega
    rw [hsplit]
    congr 1
    -- For single π: sum_{x, j ∉ x} [P x j = true ∧ preOf π (π.symm j) = x] = #{k | P (preOf π k) (π k) = true}!
    have hsingle : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = true then (if preOf π (π.symm j) = x then 1 else 0) else 0)) =
        (Finset.univ : Finset (Fin n)).sum (fun j =>
          (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            if j ∉ x ∧ P x j = true ∧ preOf π (π.symm j) = x then 1 else 0)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      unfold absentOf
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro j _
      by_cases h1 : j ∉ x <;> by_cases h2 : P x j = true <;> by_cases h3 : preOf π (π.symm j) = x <;>
        simp [h1, h2, h3]
    rw [hsingle]
    have hinner : ∀ j : Fin n,
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          if j ∉ x ∧ P x j = true ∧ preOf π (π.symm j) = x then 1 else 0) =
        if P (preOf π (π.symm j)) j = true then 1 else 0 := by
      intro j
      have hnotmem : j ∉ preOf π (π.symm j) := by
        have := not_mem_preOf_self π (π.symm j)
        simpa [Equiv.apply_symm_apply] using this
      rw [Finset.sum_eq_single (preOf π (π.symm j))]
      · by_cases hp : P (preOf π (π.symm j)) j = true <;> simp [hnotmem, hp]
      · intro x _ hne
        have hne' : preOf π (π.symm j) ≠ x := hne.symm
        simp [hne']
      · intro h; exact (h (Finset.mem_univ _)).elim
    simp_rw [hinner]
    rw [← Equiv.sum_comp π (fun j => if P (preOf π (π.symm j)) j = true then 1 else 0)]
    simp only [Equiv.symm_apply_apply, Finset.sum_boole, Nat.cast_id]

private lemma lower_bound_pay {n b : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (C : Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (hF2 : FanInTwo C) (hRB : ReadsBack (n + 2) C) (hb : notCount C ≤ b)
    (hone : ∀ (x : Finset (Fin n)) (j : Fin n), j ∈ x → (C.wires (mkInput x)).getD (a j).val false = false)
    (L : List (Equiv.Perm (Fin n))) :
    payOf w L ≤
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if (C.wires (mkInput x)).getD (a j).val false = false then w x j else 0)) +
      (2 ^ b - 1) * L.length := by
  let P : Finset (Fin n) → Fin n → Bool := fun x j => (C.wires (mkInput x)).getD (a j).val false
  have hpt : payOf w L ≤
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = false then w x j else 0)) +
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = true then visitsOf L x j else 0)) := by
    rw [← Finset.sum_add_distrib]
    unfold payOf
    apply Finset.sum_le_sum; intro x _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro j _
    cases h : P x j
    · simp
    · simp
  have htail : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if P x j = true then visitsOf L x j else 0)) ≤
      (2 ^ b - 1) * L.length := by
    rw [sum_visits_eq_perm_sum P L]
    clear hpt
    induction L with
    | nil => simp
    | cons π tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := single_perm_true_count_le C a hF2 hRB hb hone π
      have hmul : (2 ^ b - 1) * (tl.length + 1) = (2 ^ b - 1) + (2 ^ b - 1) * tl.length := by ring
      dsimp only [P] at ih ⊢
      omega
  exact le_trans hpt (Nat.add_le_add_left htail _)

-- ============================================================================
-- Helper: Construct a permutation visiting a specific (x, j) with j ∉ x (for b = 0)
-- ============================================================================

private lemma exists_perm_visiting {n : Nat} (x : Finset (Fin n)) (j : Fin n) (hj : j ∉ x) :
    ∃ π : Equiv.Perm (Fin n), preOf π (π.symm j) = x := by
  let c := x.card
  let y := (Finset.univ : Finset (Fin n)) \ insert j x
  have hc_lt : c < n := by
    have hsub : insert j x ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hj, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hy_card : y.card = n - (c + 1) := by
    have h1 : (insert j x).card = c + 1 := Finset.card_insert_of_notMem hj
    have h2 : y.card = (Finset.univ : Finset (Fin n)).card - (insert j x).card := by
      dsimp only [y]; rw [Finset.card_sdiff, Finset.inter_univ]
    rw [h2, Finset.card_univ, Fintype.card_fin, h1]
  let eX : Fin c ≃ {a : Fin n // a ∈ x} :=
    ((Fintype.equivFin {a : Fin n // a ∈ x}).trans (finCongr (Fintype.card_coe x))).symm
  let eY : Fin (n - (c + 1)) ≃ {a : Fin n // a ∈ y} :=
    ((Fintype.equivFin {a : Fin n // a ∈ y}).trans (finCongr (by rw [Fintype.card_coe, hy_card]))).symm
  let fn : Fin n → Fin n := fun i =>
    if h1 : i.val < c then (eX ⟨i.val, h1⟩).val
    else if h2 : i.val = c then j
    else (eY ⟨i.val - (c + 1), by omega⟩).val
  have hfn_inj : Function.Injective fn := by
    intro i1 i2 heq
    dsimp only [fn] at heq
    by_cases h1 : i1.val < c
    · simp only [h1, ↓reduceDIte] at heq
      by_cases h3 : i2.val < c
      · simp only [h3, ↓reduceDIte] at heq
        have hsub : eX ⟨i1.val, h1⟩ = eX ⟨i2.val, h3⟩ := Subtype.ext heq
        have hfin := eX.injective hsub
        exact Fin.ext (congrArg (fun t : Fin c => t.val) hfin)
      · simp only [h3, ↓reduceDIte] at heq
        by_cases h4 : i2.val = c
        · simp only [h4, ↓reduceDIte] at heq
          exfalso; exact hj (heq ▸ (eX ⟨i1.val, h1⟩).property)
        · simp only [h4, ↓reduceDIte] at heq
          exfalso
          have hmemX : (eX ⟨i1.val, h1⟩).val ∈ x := (eX ⟨i1.val, h1⟩).property
          have hmemY : (eY ⟨i2.val - (c + 1), by omega⟩).val ∈ y := (eY ⟨i2.val - (c + 1), by omega⟩).property
          rw [← heq] at hmemY
          exact (Finset.mem_sdiff.mp hmemY).2 (Finset.mem_insert_of_mem hmemX)
    · simp only [h1, ↓reduceDIte] at heq
      by_cases h2 : i1.val = c
      · simp only [h2, ↓reduceDIte] at heq
        by_cases h3 : i2.val < c
        · simp only [h3, ↓reduceDIte] at heq
          exfalso; exact hj (heq.symm ▸ (eX ⟨i2.val, h3⟩).property)
        · simp only [h3, ↓reduceDIte] at heq
          by_cases h4 : i2.val = c
          · exact Fin.ext (h2.trans h4.symm)
          · simp only [h4, ↓reduceDIte] at heq
            exfalso
            have hmemY : (eY ⟨i2.val - (c + 1), by omega⟩).val ∈ y := (eY ⟨i2.val - (c + 1), by omega⟩).property
            rw [← heq] at hmemY
            exact (Finset.mem_sdiff.mp hmemY).2 (Finset.mem_insert_self j x)
      · simp only [h2, ↓reduceDIte] at heq
        by_cases h3 : i2.val < c
        · simp only [h3, ↓reduceDIte] at heq
          exfalso
          have hmemX : (eX ⟨i2.val, h3⟩).val ∈ x := (eX ⟨i2.val, h3⟩).property
          have hmemY : (eY ⟨i1.val - (c + 1), by omega⟩).val ∈ y := (eY ⟨i1.val - (c + 1), by omega⟩).property
          rw [heq] at hmemY
          exact (Finset.mem_sdiff.mp hmemY).2 (Finset.mem_insert_of_mem hmemX)
        · simp only [h3, ↓reduceDIte] at heq
          by_cases h4 : i2.val = c
          · simp only [h4, ↓reduceDIte] at heq
            exfalso
            have hmemY : (eY ⟨i1.val - (c + 1), by omega⟩).val ∈ y := (eY ⟨i1.val - (c + 1), by omega⟩).property
            rw [heq] at hmemY
            exact (Finset.mem_sdiff.mp hmemY).2 (Finset.mem_insert_self j x)
          · simp only [h4, ↓reduceDIte] at heq
            have hsub : eY ⟨i1.val - (c + 1), by omega⟩ = eY ⟨i2.val - (c + 1), by omega⟩ := Subtype.ext heq
            have hfin := eY.injective hsub
            have hv := congrArg (fun t : Fin (n - (c + 1)) => t.val) hfin
            dsimp only at hv
            exact Fin.ext (by omega)
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective fn (Finite.injective_iff_bijective.mp hfn_inj)
  refine ⟨π, ?_⟩
  have hπc : π ⟨c, hc_lt⟩ = j := by
    change fn ⟨c, hc_lt⟩ = j
    simp [fn]
  have hsymm : π.symm j = ⟨c, hc_lt⟩ := by
    apply π.injective; rw [Equiv.apply_symm_apply, hπc]
  rw [hsymm]
  ext a
  unfold preOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hilt : i.val < c := (Finset.mem_filter.mp hi).2
    change fn i ∈ x
    simp only [fn, hilt, ↓reduceDIte]
    exact (eX ⟨i.val, hilt⟩).property
  · intro hax
    let idx := eX.symm ⟨a, hax⟩
    refine ⟨⟨idx.val, by have := idx.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, idx.isLt⟩, ?_⟩
    change fn ⟨idx.val, _⟩ = a
    simp only [fn, idx.isLt, ↓reduceDIte, Fin.eta]
    exact congrArg Subtype.val (Equiv.apply_symm_apply eX ⟨a, hax⟩)

-- ============================================================================
-- Part 2A: Integer flows on the hypercube DAG, decomposition, and Bellman-Ford duality
-- ============================================================================

private def IsFlow {n : Nat} (v : Nat) (f : Finset (Fin n) → Fin n → Nat) : Prop :=
  (∀ x j, j ∈ x → f x j = 0) ∧
  (∀ x : Finset (Fin n),
    (absentOf x).sum (fun j => f x j) + (if x = Finset.univ then v else 0) =
    x.sum (fun j => f (x.erase j) j) + (if x = ∅ then v else 0))

private lemma flow_zero_implies_f_zero {n : Nat} {f : Finset (Fin n) → Fin n → Nat}
    (hf : IsFlow 0 f) : ∀ x j, f x j = 0 := by
  have hbycard : ∀ c (x : Finset (Fin n)), x.card = c → ∀ j, f x j = 0 := by
    intro c
    induction c with
    | zero =>
      intro x hx j
      have hx0 : x = ∅ := Finset.card_eq_zero.mp hx
      subst hx0
      have hcons := hf.2 ∅
      simp only [Finset.sum_empty, ite_self, Nat.zero_add, Nat.add_zero] at hcons
      have h0 : ∀ j ∈ absentOf (∅ : Finset (Fin n)), f ∅ j = 0 :=
        Finset.sum_eq_zero_iff.mp hcons
      exact h0 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.notMem_empty j⟩)
    | succ c ih =>
      intro x hx j
      by_cases hjx : j ∈ x
      · exact hf.1 x j hjx
      · have hcons := hf.2 x
        simp only [ite_self, Nat.add_zero] at hcons
        have hin0 : x.sum (fun i => f (x.erase i) i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hcard : (x.erase i).card = c := by rw [Finset.card_erase_of_mem hi, hx]; omega
          exact ih (x.erase i) hcard i
        rw [hin0] at hcons
        exact (Finset.sum_eq_zero_iff.mp hcons) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjx⟩)
  intro x j
  exact hbycard x.card x rfl j

private lemma flow_decompose {n : Nat} (hn : 1 ≤ n) :
    ∀ (v : Nat) (f : Finset (Fin n) → Fin n → Nat), IsFlow v f →
      ∃ L : List (Equiv.Perm (Fin n)), L.length = v ∧
        ∀ x j, j ∉ x → visitsOf L x j = f x j := by
  intro v
  induction v with
  | zero =>
    intro f hf
    refine ⟨[], rfl, fun x j _ => ?_⟩
    rw [visitsOf_nil, flow_zero_implies_f_zero hf x j]
  | succ v ih =>
    intro f hf
    have hne_eu : (∅ : Finset (Fin n)) ≠ Finset.univ := by
      intro h
      have := congrArg Finset.card h
      rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at this
      omega
    -- Construct a chain seq : Fin k → Fin n of length k <= n with positive flow along every step!
    have hchain : ∀ (k : Nat), k ≤ n →
        ∃ (seq : Fin k → Fin n), Function.Injective seq ∧
          (∀ t : Fin k, 1 ≤ f (((Finset.univ : Finset (Fin k)).filter (fun i => i.val < t.val)).image seq) (seq t)) ∧
          (k < n → 1 ≤ (absentOf ((Finset.univ : Finset (Fin k)).image seq)).sum
            (fun j => f ((Finset.univ : Finset (Fin k)).image seq) j)) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun t => Fin.elim0 t, fun _ => ?_⟩
        have himg : (Finset.univ : Finset (Fin 0)).image (Fin.elim0 : Fin 0 → Fin n) = ∅ := by simp
        rw [himg]
        have hcons := hf.2 ∅
        simp only [hne_eu, ↓reduceIte, Finset.sum_empty, Nat.add_zero, Nat.zero_add] at hcons
        omega
      | succ k ihk =>
        intro hkn
        rcases ihk (by omega) with ⟨seq, hinj, hpos, hout⟩
        let S := (Finset.univ : Finset (Fin k)).image seq
        have hS_pos : 1 ≤ (absentOf S).sum (fun j => f S j) := hout (by omega)
        have hex_j : ∃ j ∈ absentOf S, 1 ≤ f S j := by
          by_contra hall
          push_neg at hall
          have h0 : (absentOf S).sum (fun j => f S j) = 0 :=
            Finset.sum_eq_zero (fun j hj => by have := hall j hj; omega)
          omega
        rcases hex_j with ⟨j_new, hj_abs, hj_pos⟩
        have hj_nS : j_new ∉ S := (Finset.mem_filter.mp hj_abs).2
        let seq' : Fin (k + 1) → Fin n := fun i => if h : i.val < k then seq ⟨i.val, h⟩ else j_new
        have hpre_eq : ∀ t : Fin k,
            ((Finset.univ : Finset (Fin (k + 1))).filter (fun i => i.val < t.val)).image seq' =
            ((Finset.univ : Finset (Fin k)).filter (fun i => i.val < t.val)).image seq := by
          intro t; ext a; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hik : i.val < k := by omega
            exact ⟨⟨i.val, hik⟩, hi, by simp [seq', hik]⟩
          · rintro ⟨i, hi, rfl⟩
            exact ⟨⟨i.val, by omega⟩, hi, by simp [seq', i.isLt]⟩
        have hpre_last :
            ((Finset.univ : Finset (Fin (k + 1))).filter (fun i => i.val < k)).image seq' = S := by
          ext a; simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact ⟨⟨i.val, hi⟩, by simp [seq', hi]⟩
          · rintro ⟨i, rfl⟩
            exact ⟨⟨i.val, by omega⟩, i.isLt, by simp [seq', i.isLt]⟩
        have himg_new : (Finset.univ : Finset (Fin (k + 1))).image seq' = insert j_new S := by
          ext a; simp only [S, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨i, rfl⟩
            by_cases hik : i.val < k
            · right; exact ⟨⟨i.val, hik⟩, by simp [seq', hik]⟩
            · left; simp [seq', hik]
          · rintro (rfl | ⟨i, rfl⟩)
            · exact ⟨⟨k, Nat.lt_succ_self k⟩, by simp [seq']⟩
            · exact ⟨⟨i.val, by omega⟩, by simp [seq', i.isLt]⟩
        refine ⟨seq', ?_, ?_, ?_⟩
        · intro i1 i2 heq
          dsimp only [seq'] at heq
          by_cases h1 : i1.val < k <;> by_cases h2 : i2.val < k <;> simp only [h1, h2, ↓reduceDIte] at heq
          · exact Fin.ext (congrArg (fun t : Fin k => t.val) (hinj heq))
          · exfalso; exact hj_nS (heq ▸ Finset.mem_image.mpr ⟨⟨i1.val, h1⟩, Finset.mem_univ _, rfl⟩)
          · exfalso; exact hj_nS (heq.symm ▸ Finset.mem_image.mpr ⟨⟨i2.val, h2⟩, Finset.mem_univ _, rfl⟩)
          · exact Fin.ext (by omega)
        · intro t
          by_cases htk : t.val < k
          · rw [hpre_eq ⟨t.val, htk⟩]
            simp only [seq', htk, ↓reduceDIte]
            exact hpos ⟨t.val, htk⟩
          · have hteq : t.val = k := by omega
            simp only [hteq, hpre_last, seq', lt_irrefl, ↓reduceDIte]
            exact hj_pos
        · intro hklt
          rw [himg_new]
          have hcard_ins : (insert j_new S).card = k + 1 := by
            rw [Finset.card_insert_of_notMem hj_nS, Finset.card_image_of_injective _ hinj, Finset.card_fin]
          have hne_u : insert j_new S ≠ Finset.univ := by
            intro h; have := congrArg Finset.card h; rw [hcard_ins, Finset.card_univ, Fintype.card_fin] at this; omega
          have hcons := hf.2 (insert j_new S)
          simp only [hne_u, ↓reduceIte, Nat.add_zero] at hcons
          have hle_in : f S j_new ≤ (insert j_new S).sum (fun i => f ((insert j_new S).erase i) i) := by
            have hmem : j_new ∈ insert j_new S := Finset.mem_insert_self j_new S
            have her : (insert j_new S).erase j_new = S := Finset.erase_insert hj_nS
            calc f S j_new = f ((insert j_new S).erase j_new) j_new := by rw [her]
              _ ≤ (insert j_new S).sum (fun i => f ((insert j_new S).erase i) i) :=
                Finset.single_le_sum (f := fun i => f ((insert j_new S).erase i) i) (fun _ _ => Nat.zero_le _) hmem
          omega
    rcases hchain n (le_refl n) with ⟨seq, hinj, hpos, _⟩
    let π : Equiv.Perm (Fin n) := Equiv.ofBijective seq (Finite.injective_iff_bijective.mp hinj)
    have hpos_π : ∀ k : Fin n, 1 ≤ f (preOf π k) (π k) := hpos
    -- Subtract 1 along π to get f'
    let f' : Finset (Fin n) → Fin n → Nat := fun x j =>
      if preOf π (π.symm j) = x then f x j - 1 else f x j
    have hf'_flow : IsFlow v f' := by
      constructor
      · intro x j hjx
        dsimp only [f']
        split_ifs with hpre
        · rw [hf.1 x j hjx]
        · exact hf.1 x j hjx
      · intro x
        have hcons := hf.2 x
        -- Check how many out-edges of x and in-edges of x lie on π!
        have hout_eq : (absentOf x).sum (fun j => f x j) =
            (absentOf x).sum (fun j => f' x j) +
            (if ∃ k : Fin n, preOf π k = x then 1 else 0) := by
          by_cases hex : ∃ k : Fin n, preOf π k = x
          · rcases hex with ⟨k, hk⟩
            have hex' : ∃ k' : Fin n, preOf π k' = x := ⟨k, hk⟩
            have huniq : ∀ j : Fin n, preOf π (π.symm j) = x ↔ j = π k := by
              intro j
              constructor
              · intro hjx
                have hcard1 : (preOf π (π.symm j)).card = (π.symm j).val := by
                  unfold preOf
                  rw [Finset.card_image_of_injective _ π.injective]
                  have hbij : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < (π.symm j).val)).card =
                      (Finset.range (π.symm j).val).card := by
                    apply Finset.card_bij (fun i _ => i.val)
                    · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
                    · intro i1 _ i2 _ heq; exact Fin.ext heq
                    · intro m hm; have := Finset.mem_range.mp hm; exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩, rfl⟩
                  rw [hbij, Finset.card_range]
                have hcard2 : (preOf π k).card = k.val := by
                  unfold preOf
                  rw [Finset.card_image_of_injective _ π.injective]
                  have hbij : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).card =
                      (Finset.range k.val).card := by
                    apply Finset.card_bij (fun i _ => i.val)
                    · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
                    · intro i1 _ i2 _ heq; exact Fin.ext heq
                    · intro m hm; have := Finset.mem_range.mp hm; exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩, rfl⟩
                  rw [hbij, Finset.card_range]
                have hval : (π.symm j).val = k.val := by rw [← hcard1, hjx, ← hk, hcard2]
                have : π.symm j = k := Fin.ext hval
                rw [← this, Equiv.apply_symm_apply]
              · rintro rfl; rw [Equiv.symm_apply_apply]; exact hk
            have hpk_abs : π k ∈ absentOf x := by
              rw [← hk]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_mem_preOf_self π k⟩
            have h1 : (absentOf x).sum (fun j => f x j) =
                (absentOf x).sum (fun j => f' x j + if j = π k then 1 else 0) := by
              apply Finset.sum_congr rfl; intro j _
              dsimp only [f']
              by_cases hj : j = π k
              · subst hj
                have hpre : preOf π (π.symm (π k)) = x := (huniq (π k)).mpr rfl
                simp only [hpre, ↓reduceIte]
                have := hpos_π k; rw [hk] at this; omega
              · have hpre : preOf π (π.symm j) ≠ x := fun h => hj ((huniq j).mp h)
                simp only [hj, hpre, ↓reduceIte]; omega
            rw [h1, Finset.sum_add_distrib]
            simp only [Finset.sum_ite_eq', hpk_abs, ↓reduceIte, hex']
          · simp only [hex, ↓reduceIte, Nat.add_zero]
            apply Finset.sum_congr rfl; intro j _
            dsimp only [f']
            have hne : preOf π (π.symm j) ≠ x := fun h => hex ⟨π.symm j, h⟩
            simp [hne]
        have hin_eq : x.sum (fun j => f (x.erase j) j) =
            x.sum (fun j => f' (x.erase j) j) +
            (if ∃ k : Fin n, insert (π k) (preOf π k) = x then 1 else 0) := by
          by_cases hex : ∃ k : Fin n, insert (π k) (preOf π k) = x
          · rcases hex with ⟨k, hk⟩
            have hex' : ∃ k' : Fin n, insert (π k') (preOf π k') = x := ⟨k, hk⟩
            have huniq : ∀ j ∈ x, preOf π (π.symm j) = x.erase j ↔ j = π k := by
              intro j hjx
              constructor
              · intro hjx'
                have hcard1 : (preOf π (π.symm j)).card = (π.symm j).val := by
                  unfold preOf
                  rw [Finset.card_image_of_injective _ π.injective]
                  have hbij : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < (π.symm j).val)).card =
                      (Finset.range (π.symm j).val).card := by
                    apply Finset.card_bij (fun i _ => i.val)
                    · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
                    · intro i1 _ i2 _ heq; exact Fin.ext heq
                    · intro m hm; have := Finset.mem_range.mp hm; exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩, rfl⟩
                  rw [hbij, Finset.card_range]
                have hcard2 : (preOf π k).card = k.val := by
                  unfold preOf
                  rw [Finset.card_image_of_injective _ π.injective]
                  have hbij : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).card =
                      (Finset.range k.val).card := by
                    apply Finset.card_bij (fun i _ => i.val)
                    · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
                    · intro i1 _ i2 _ heq; exact Fin.ext heq
                    · intro m hm; have := Finset.mem_range.mp hm; exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩, rfl⟩
                  rw [hbij, Finset.card_range]
                have hcx : x.card = k.val + 1 := by
                  rw [← hk, Finset.card_insert_of_notMem (not_mem_preOf_self π k), hcard2]
                have hval : (π.symm j).val = k.val := by
                  have h1 := congrArg Finset.card hjx'
                  rw [hcard1, Finset.card_erase_of_mem hjx, hcx] at h1
                  omega
                have : π.symm j = k := Fin.ext hval
                rw [← this, Equiv.apply_symm_apply]
              · rintro rfl
                rw [Equiv.symm_apply_apply, ← hk, Finset.erase_insert (not_mem_preOf_self π k)]
            have hpk_x : π k ∈ x := hk ▸ Finset.mem_insert_self _ _
            have h1 : x.sum (fun j => f (x.erase j) j) =
                x.sum (fun j => f' (x.erase j) j + if j = π k then 1 else 0) := by
              apply Finset.sum_congr rfl; intro j hjx
              dsimp only [f']
              by_cases hj : j = π k
              · subst hj
                have hpre : preOf π (π.symm (π k)) = x.erase (π k) := (huniq (π k) hjx).mpr rfl
                simp only [hpre, ↓reduceIte]
                have her : x.erase (π k) = preOf π k := by
                  rw [← hk, Finset.erase_insert (not_mem_preOf_self π k)]
                rw [her]; have := hpos_π k; omega
              · have hpre : preOf π (π.symm j) ≠ x.erase j := fun h => hj ((huniq j hjx).mp h)
                simp only [hj, hpre, ↓reduceIte]; omega
            rw [h1, Finset.sum_add_distrib]
            simp only [Finset.sum_ite_eq', hpk_x, ↓reduceIte, hex']
          · simp only [hex, ↓reduceIte, Nat.add_zero]
            apply Finset.sum_congr rfl; intro j hjx
            dsimp only [f']
            have hne : preOf π (π.symm j) ≠ x.erase j := by
              intro h
              apply hex
              refine ⟨π.symm j, ?_⟩
              rw [Equiv.apply_symm_apply, h, Finset.insert_erase hjx]
            simp [hne]
        -- Check that (∃ k, preOf π k = x) ↔ (x = ∅ ∨ ∃ k, insert (π k) (preOf π k) = x) ∧ x ≠ univ!
        have hbal_π :
            (if ∃ k : Fin n, preOf π k = x then 1 else 0) + (if x = Finset.univ then 1 else 0) =
            (if ∃ k : Fin n, insert (π k) (preOf π k) = x then 1 else 0) + (if x = ∅ then 1 else 0) := by
          have hex_out : (∃ k : Fin n, preOf π k = x) ↔
              (x = ∅ ∨ ∃ k : Fin n, insert (π k) (preOf π k) = x) ∧ x ≠ Finset.univ := by
            constructor
            · rintro ⟨k, rfl⟩
              constructor
              · by_cases hk0 : k.val = 0
                · left; ext a; simp [preOf, hk0]
                · right
                  refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
                  ext a; simp only [Finset.mem_insert, mem_preOf_iff, Equiv.symm_apply_apply]
                  constructor
                  · rintro (rfl | h)
                    · simp; omega
                    · omega
                  · intro hlt
                    by_cases heq : (π.symm a).val = k.val - 1
                    · left; have : π.symm a = ⟨k.val - 1, by omega⟩ := Fin.ext heq; rw [← this, Equiv.apply_symm_apply]
                    · right; omega
              · intro hu
                have := not_mem_preOf_self π k
                rw [hu] at this; exact this (Finset.mem_univ _)
            · rintro ⟨h1 | ⟨k, rfl⟩, hne⟩
              · subst h1
                refine ⟨⟨0, by omega⟩, ?_⟩
                ext a; simp [preOf]
              · have hklt : k.val + 1 < n := by
                  by_contra hge
                  apply hne
                  ext a
                  simp only [Finset.mem_insert, mem_preOf_iff, Finset.mem_univ, iff_true]
                  by_cases heq : (π.symm a).val = k.val
                  · left; have : π.symm a = k := Fin.ext heq; rw [← this, Equiv.apply_symm_apply]
                  · right; have := (π.symm a).isLt; omega
                refine ⟨⟨k.val + 1, hklt⟩, ?_⟩
                ext a; simp only [Finset.mem_insert, mem_preOf_iff]
                constructor
                · intro hlt
                  by_cases heq : (π.symm a).val = k.val
                  · left; have : π.symm a = k := Fin.ext heq; rw [← this, Equiv.apply_symm_apply]
                  · right; omega
                · rintro (rfl | hlt)
                  · rw [Equiv.symm_apply_apply]; simp
                  · omega
          by_cases hx0 : x = ∅
          · subst hx0
            have hnot_in : ¬ ∃ k : Fin n, insert (π k) (preOf π k) = ∅ := by
              rintro ⟨k, hk⟩; exact Finset.insert_ne_empty _ _ hk
            have hex1 : ∃ k : Fin n, preOf π k = ∅ := hex_out.mpr ⟨Or.inl rfl, hne_eu⟩
            simp [hex1, hne_eu, hnot_in]
          · by_cases hxu : x = Finset.univ
            · subst hxu
              have hnot_out : ¬ ∃ k : Fin n, preOf π k = Finset.univ := fun h => (hex_out.mp h).2 rfl
              have hex_in : ∃ k : Fin n, insert (π k) (preOf π k) = Finset.univ := by
                refine ⟨⟨n - 1, by omega⟩, ?_⟩
                ext a; simp only [Finset.mem_insert, mem_preOf_iff, Finset.mem_univ, iff_true]
                by_cases heq : (π.symm a).val = n - 1
                · left; have : π.symm a = ⟨n - 1, by omega⟩ := Fin.ext heq; rw [← this, Equiv.apply_symm_apply]
                · right; have := (π.symm a).isLt; omega
              simp [hnot_out, hex_in, hx0]
            · have hiff : (∃ k : Fin n, preOf π k = x) ↔ (∃ k : Fin n, insert (π k) (preOf π k) = x) := by
                rw [hex_out]; simp [hx0, hxu]
              by_cases hex1 : ∃ k : Fin n, preOf π k = x
              · have hex2 := hiff.mp hex1; simp [hex1, hex2, hx0, hxu]
              · have hex2 : ¬ ∃ k : Fin n, insert (π k) (preOf π k) = x := fun h => hex1 (hiff.mpr h)
                simp [hex1, hex2, hx0, hxu]
        rw [hout_eq, hin_eq] at hcons
        by_cases hxu : x = Finset.univ
        · rw [if_pos hxu] at hcons hbal_π ⊢
          have hx0 : x ≠ ∅ := by rw [hxu]; exact hne_eu.symm
          rw [if_neg hx0] at hcons hbal_π ⊢
          omega
        · rw [if_neg hxu] at hcons hbal_π ⊢
          by_cases hx0 : x = ∅
          · rw [if_pos hx0] at hcons hbal_π ⊢
            omega
          · rw [if_neg hx0] at hcons hbal_π ⊢
            omega
    rcases ih f' hf'_flow with ⟨L', hL'_len, hL'_vis⟩
    refine ⟨π :: L', by simp [hL'_len], ?_⟩
    intro x j hjx
    rw [visitsOf_cons, hL'_vis x j hjx]
    dsimp only [f']
    split_ifs with hpre
    · have hp := hpos_π (π.symm j)
      rw [hpre, Equiv.apply_symm_apply] at hp
      omega
    · omega

-- Residual graph steps, Bellman-Ford potential, and extremal flow optimality!
private inductive ResStep (n : Nat) where
  | fwd (x : Finset (Fin n)) (j : Fin n) (hj : j ∉ x)
  | bwd (x : Finset (Fin n)) (j : Fin n) (hj : j ∉ x)
  | fwdRet
  | bwdRet
  deriving DecidableEq

private def ResStep.src {n : Nat} : ResStep n → Finset (Fin n)
  | .fwd x _ _ => x
  | .bwd x j _ => insert j x
  | .fwdRet => Finset.univ
  | .bwdRet => ∅

private def ResStep.dst {n : Nat} : ResStep n → Finset (Fin n)
  | .fwd x j _ => insert j x
  | .bwd x _ _ => x
  | .fwdRet => ∅
  | .bwdRet => Finset.univ

private def ResStep.valid {n : Nat} (v : Nat) (f : Finset (Fin n) → Fin n → Nat) : ResStep n → Prop
  | .fwd _ _ _ => True
  | .bwd x j _ => 0 < f x j
  | .fwdRet => True
  | .bwdRet => 0 < v

private instance instDecResStepValid {n : Nat} (v : Nat) (f : Finset (Fin n) → Fin n → Nat)
    (s : ResStep n) : Decidable (s.valid v f) := by
  cases s with
  | fwd _ _ _ => exact inferInstanceAs (Decidable True)
  | bwd x j _ => exact inferInstanceAs (Decidable (0 < f x j))
  | fwdRet => exact inferInstanceAs (Decidable True)
  | bwdRet => exact inferInstanceAs (Decidable (0 < v))

private def ResStep.cost {n : Nat} (w : Finset (Fin n) → Fin n → Nat) (d : Nat)
    (f : Finset (Fin n) → Fin n → Nat) : ResStep n → Int
  | .fwd x j _ => if f x j < w x j then -1 else 0
  | .bwd x j _ => if f x j ≤ w x j then 1 else 0
  | .fwdRet => (d : Int)
  | .bwdRet => -(d : Int)

private def IsWalk {n : Nat} (v : Nat) (f : Finset (Fin n) → Fin n → Nat) :
    Finset (Fin n) → Finset (Fin n) → List (ResStep n) → Prop
  | a, b, [] => a = b
  | a, b, s :: rest => s.valid v f ∧ s.src = a ∧ IsWalk v f s.dst b rest

private lemma IsWalk.append {n : Nat} {v : Nat} {f : Finset (Fin n) → Fin n → Nat}
    {a b c : Finset (Fin n)} {W1 W2 : List (ResStep n)}
    (h1 : IsWalk v f a b W1) (h2 : IsWalk v f b c W2) :
    IsWalk v f a c (W1 ++ W2) := by
  induction W1 generalizing a with
  | nil => cases h1; exact h2
  | cons s rest ih =>
    rcases h1 with ⟨hv, hs, hr⟩
    exact ⟨hv, hs, ih hr⟩

private def walkCost {n : Nat} (w : Finset (Fin n) → Fin n → Nat) (d : Nat)
    (f : Finset (Fin n) → Fin n → Nat) (W : List (ResStep n)) : Int :=
  (W.map (ResStep.cost w d f)).sum

private lemma walkCost_append {n : Nat} (w : Finset (Fin n) → Fin n → Nat) (d : Nat)
    (f : Finset (Fin n) → Fin n → Nat) (W1 W2 : List (ResStep n)) :
    walkCost w d f (W1 ++ W2) = walkCost w d f W1 + walkCost w d f W2 := by
  simp [walkCost, List.map_append, List.sum_append]

private lemma walk_from_empty_zero {n : Nat} (v : Nat) (f : Finset (Fin n) → Fin n → Nat)
    (w : Finset (Fin n) → Fin n → Nat) (d : Nat) (x : Finset (Fin n)) :
    ∃ W : List (ResStep n), IsWalk v f ∅ x W ∧ walkCost w d f W ≤ 0 := by
  induction x using Finset.induction_on with
  | empty => exact ⟨[], rfl, by simp [walkCost]⟩
  | @insert j s hj ih =>
    rcases ih with ⟨W, hW, hc⟩
    refine ⟨W ++ [ResStep.fwd s j hj], hW.append ⟨trivial, rfl, rfl⟩, ?_⟩
    rw [walkCost_append]
    have hstep : walkCost w d f [ResStep.fwd s j hj] ≤ 0 := by
      simp only [walkCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ResStep.cost]
      split_ifs <;> omega
    omega

private def flowObj {n : Nat} (w : Finset (Fin n) → Fin n → Nat) (d : Nat)
    (v : Nat) (f : Finset (Fin n) → Fin n → Nat) : Int :=
  (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
    (absentOf x).sum (fun j => (min (w x j) (f x j) : Int))) - (d : Int) * (v : Int)

private lemma walk_split_at {n : Nat} {v : Nat} {f : Finset (Fin n) → Fin n → Nat}
    {a b : Finset (Fin n)} {W : List (ResStep n)} (hW : IsWalk v f a b W)
    (i : Nat) (hi : i < W.length) :
    IsWalk v f a (W[i].src) (W.take i) ∧ IsWalk v f (W[i].src) b (W.drop i) := by
  induction W generalizing a i with
  | nil => simp at hi
  | cons s rest ih =>
    rcases hW with ⟨hv, rfl, hrest⟩
    cases i with
    | zero => exact ⟨rfl, ⟨hv, rfl, hrest⟩⟩
    | succ i =>
      have hi' : i < rest.length := by simp at hi; omega
      rcases ih hrest i hi' with ⟨h1, h2⟩
      exact ⟨⟨hv, rfl, h1⟩, h2⟩

private lemma optimal_no_neg_cycle {n : Nat} (hn : 1 ≤ n) (w : Finset (Fin n) → Fin n → Nat)
    (d : Nat) (v : Nat) (f : Finset (Fin n) → Fin n → Nat)
    (hflow : IsFlow v f)
    (hopt : ∀ v' f', IsFlow v' f' → flowObj w d v' f' ≤ flowObj w d v f) :
    ∀ (a : Finset (Fin n)) (W : List (ResStep n)), IsWalk v f a a W → 0 ≤ walkCost w d f W := by
  by_contra hneg
  push_neg at hneg
  have hex_len : ∃ len : Nat, ∃ a W, W.length = len ∧ IsWalk v f a a W ∧ walkCost w d f W < 0 := by
    rcases hneg with ⟨a, W, hW, hc⟩; exact ⟨W.length, a, W, rfl, hW, hc⟩
  classical
  let minLen := Nat.find hex_len
  rcases Nat.find_spec hex_len with ⟨a, W, hWlen, hW, hWc⟩
  have hmin : ∀ a' W', IsWalk v f a' a' W' → W'.length < W.length → 0 ≤ walkCost w d f W' := by
    intro a' W' hW' hlt
    by_contra hlt0
    push_neg at hlt0
    exact Nat.find_min hex_len (hWlen ▸ hlt) ⟨a', W', rfl, hW', hlt0⟩
  have hW_ne : W ≠ [] := by
    intro hnil; subst hnil; simp [walkCost] at hWc
  -- All sources along W are pairwise distinct!
  have hsrc_nodup : (W.map ResStep.src).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    by_contra hne
    have hlt_or : i.val < j.val ∨ j.val < i.val := lt_or_gt_of_ne (fun h => hne (Fin.ext h))
    suffices haux : ∀ (p q : Nat) (hp : p < W.length) (hq : q < W.length),
        p < q → W[p].src = W[q].src → False by
      rcases hlt_or with h | h
      · exact haux i.val j.val (by simpa using i.isLt) (by simpa using j.isLt) h (by simpa using hij)
      · exact haux j.val i.val (by simpa using j.isLt) (by simpa using i.isLt) h (by simpa using hij.symm)
    intro p q hp hq hpq hsrceq
    rcases walk_split_at hW p hp with ⟨hWp1, hWp2⟩
    have hq_sub : q - p < (W.drop p).length := by simp; omega
    rcases walk_split_at hWp2 (q - p) hq_sub with ⟨hWmid, hWtail⟩
    have hmid_src : (W.drop p)[q - p].src = W[q].src := by
      simp [List.getElem_drop, show p + (q - p) = q by omega]
    rw [hmid_src, ← hsrceq] at hWmid hWtail
    let W_mid := (W.drop p).take (q - p)
    let W_out := W.take p ++ (W.drop p).drop (q - p)
    have hmid_len : W_mid.length = q - p := by simp [W_mid]; omega
    have hout_len : W_out.length = W.length - (q - p) := by simp [W_out]; omega
    have hmid_lt : W_mid.length < W.length := by omega
    have hout_lt : W_out.length < W.length := by omega
    have hW_out_walk : IsWalk v f a a W_out := hWp1.append hWtail
    have hcost_split : walkCost w d f W = walkCost w d f W_mid + walkCost w d f W_out := by
      have h1 : W = W.take p ++ (W_mid ++ (W.drop p).drop (q - p)) := by
        rw [List.take_append_drop, List.take_append_drop]
      conv_lhs => rw [h1]
      rw [walkCost_append, walkCost_append]
      simp only [W_out, walkCost_append]; ring
    have hc1 := hmin _ W_mid hWmid hmid_lt
    have hc2 := hmin _ W_out hW_out_walk hout_lt
    omega
  -- Helper: if W contains two opposite steps (s1 : u -> u', s2 : u' -> u) with cost s1 + cost s2 >= 0, contradiction!
  have hno_opp : ∀ s1 s2 : ResStep n, s1 ∈ W → s2 ∈ W →
      s1.src = s2.dst → s1.dst = s2.src → 0 ≤ s1.cost w d f + s2.cost w d f → False := by
    intro s1 s2 hm1 hm2 h12 h21 hcsum
    -- Rotate W so s1 is at index 0; wait: even simpler, locate indices p, q of s1, s2!
    rcases List.mem_iff_getElem.mp hm1 with ⟨p, hp, hpeq⟩
    rcases List.mem_iff_getElem.mp hm2 with ⟨q, hq, hqeq⟩
    have hne_pq : p ≠ q := by
      intro heq; subst heq; rw [hqeq] at hpeq
      subst hpeq
      -- s2 = s1 implies s2.src = s2.dst, impossible for all ResStep constructors (since n >= 1)!
      cases s2 with
      | fwd x j hj =>
        dsimp only [ResStep.src, ResStep.dst] at h12
        exact hj (by rw [h12]; exact Finset.mem_insert_self j x)
      | bwd x j hj =>
        dsimp only [ResStep.src, ResStep.dst] at h12
        exact hj (by rw [← h12]; exact Finset.mem_insert_self j x)
      | fwdRet =>
        dsimp only [ResStep.src, ResStep.dst] at h12
        have := congrArg Finset.card h12
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_empty] at this; omega
      | bwdRet =>
        dsimp only [ResStep.src, ResStep.dst] at h12
        have := congrArg Finset.card h12
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_empty] at this; omega
    -- WLOG p < q (otherwise swap s1 and s2!)
    suffices haux : ∀ (s1 s2 : ResStep n) (p q : Nat) (hp : p < W.length) (hq : q < W.length),
        W[p] = s1 → W[q] = s2 → p < q → s1.src = s2.dst → s1.dst = s2.src →
        0 ≤ s1.cost w d f + s2.cost w d f → False by
      rcases lt_or_gt_of_ne hne_pq with h | h
      · exact haux s1 s2 p q hp hq hpeq hqeq h h12 h21 hcsum
      · exact haux s2 s1 q p hq hp hqeq hpeq h h21.symm h12.symm (by omega)
    intro s1 s2 p q hp hq hpeq hqeq hpq h12 h21 hcsum
    -- Split W at p, p+1, q, q+1: W = P ++ [s1] ++ M ++ [s2] ++ T
    -- Since s1.src = s2.dst and s1.dst = s2.src:
    -- M is a closed walk s1.dst -> s2.src = s1.dst, and P ++ T is a closed walk a -> a!
    -- Both have length < W.length (since [s1] and [s2] were dropped!), and walkCost W = cost(s1)+cost(s2) + cost(M) + cost(P++T)!
    rcases walk_split_at hW p hp with ⟨hP, hfrom_p⟩
    have hdrop_p : W.drop p = s1 :: W.drop (p + 1) := by
      rw [← hpeq]; exact List.drop_eq_getElem_cons hp
    rw [hdrop_p] at hfrom_p
    rcases hfrom_p with ⟨_, _, hfrom_p1⟩
    have hq_sub : q - (p + 1) < (W.drop (p + 1)).length := by simp; omega
    rcases walk_split_at hfrom_p1 (q - (p + 1)) hq_sub with ⟨hM, hfrom_q⟩
    have hq_elem : (W.drop (p + 1))[q - (p + 1)] = s2 := by
      simp [List.getElem_drop, show p + 1 + (q - (p + 1)) = q by omega, hqeq]
    have hdrop_q : (W.drop (p + 1)).drop (q - (p + 1)) = s2 :: W.drop (q + 1) := by
      rw [List.drop_drop, show p + 1 + (q - (p + 1)) = q by omega, ← hqeq]
      exact List.drop_eq_getElem_cons hq
    rw [hq_elem, ← h21] at hM
    rw [hdrop_q] at hfrom_q
    rcases hfrom_q with ⟨_, _, hT⟩
    rw [hpeq, h12] at hP
    let W_M := (W.drop (p + 1)).take (q - (p + 1))
    let W_PT := W.take p ++ W.drop (q + 1)
    have hM_len : W_M.length < W.length := by simp [W_M]; omega
    have hPT_len : W_PT.length < W.length := by simp [W_PT]; omega
    have hPT_walk : IsWalk v f a a W_PT := hP.append hT
    have hW_eq : W = W.take p ++ (s1 :: (W_M ++ (s2 :: W.drop (q + 1)))) := by
      calc W = W.take p ++ W.drop p := (List.take_append_drop p W).symm
        _ = W.take p ++ (s1 :: W.drop (p + 1)) := by rw [hdrop_p]
        _ = W.take p ++ (s1 :: (W_M ++ (W.drop (p + 1)).drop (q - (p + 1)))) := by
            rw [List.take_append_drop]
        _ = W.take p ++ (s1 :: (W_M ++ (s2 :: W.drop (q + 1)))) := by rw [hdrop_q]
    have hcost_eq : walkCost w d f W = s1.cost w d f + s2.cost w d f + walkCost w d f W_M + walkCost w d f W_PT := by
      conv_lhs => rw [hW_eq]
      simp only [walkCost, W_PT, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      ring
    have hcM := hmin _ W_M hM hM_len
    have hcPT := hmin _ W_PT hPT_walk hPT_len
    omega
  -- Hence W has no duplicate steps, no (fwd, bwd) pair on the same edge, and no (fwdRet, bwdRet) pair!
  have hW_nodup : W.Nodup := List.Nodup.of_map ResStep.src hsrc_nodup
  have hno_fb : ∀ (x : Finset (Fin n)) (j : Fin n) (hj : j ∉ x),
      ¬ (ResStep.fwd x j hj ∈ W ∧ ResStep.bwd x j hj ∈ W) := by
    intro x j hj ⟨h1, h2⟩
    apply hno_opp (ResStep.fwd x j hj) (ResStep.bwd x j hj) h1 h2 rfl rfl
    simp only [ResStep.cost]; split_ifs <;> omega
  have hno_ret : ¬ (ResStep.fwdRet ∈ W ∧ ResStep.bwdRet ∈ W) := by
    intro ⟨h1, h2⟩
    apply hno_opp ResStep.fwdRet ResStep.bwdRet h1 h2 rfl rfl
    simp only [ResStep.cost]; omega
  have hW_valid : ∀ s ∈ W, s.valid v f := by
    have haux : ∀ {a' b'} {U : List (ResStep n)}, IsWalk v f a' b' U → ∀ s ∈ U, s.valid v f := by
      intro a' b' U hU
      induction U generalizing a' with
      | nil => intro _ h; cases h
      | cons s rest ih =>
        intro s' hs'
        rcases hU with ⟨hv, _, hr⟩
        rcases List.mem_cons.mp hs' with rfl | hmem
        · exact hv
        · exact ih hr s' hmem
    exact haux hW
  -- Update (v, f) along W to get (v', f')!
  let v' : Nat := if ResStep.fwdRet ∈ W then v + 1 else if ResStep.bwdRet ∈ W then v - 1 else v
  let f' : Finset (Fin n) → Fin n → Nat := fun x j =>
    if hj : j ∉ x then
      if ResStep.fwd x j hj ∈ W then f x j + 1
      else if ResStep.bwd x j hj ∈ W then f x j - 1
      else f x j
    else 0
  -- Helper: integer flow balance at every vertex u changes by 0 along any closed walk!
  have hwalk_bal : ∀ (u : Finset (Fin n)),
      (W.map (fun s : ResStep n => (if s.src = u then (1 : Int) else 0) - (if s.dst = u then 1 else 0))).sum = 0 := by
    have htele : ∀ {a' b' : Finset (Fin n)} (U : List (ResStep n)), IsWalk v f a' b' U →
        ∀ u : Finset (Fin n),
          (U.map (fun s : ResStep n => (if s.src = u then (1 : Int) else 0) - (if s.dst = u then 1 else 0))).sum =
          (if a' = u then 1 else 0) - (if b' = u then 1 else 0) := by
      intro a' b' U hU
      induction U generalizing a' with
      | nil =>
        cases hU; intro u; simp
      | cons s rest ih =>
        rcases hU with ⟨_, rfl, hr⟩
        intro u
        simp only [List.map_cons, List.sum_cons]
        rw [ih hr u]; ring
    intro u; rw [htele W hW u]; ring
  have hf'_flow : IsFlow v' f' := by
    constructor
    · intro x j hjx; simp [f', hjx]
    · intro x
      -- Convert Nat equality to Int equality and use hwalk_bal x!
      have hcons_int :
          ((absentOf x).sum (fun j => (f x j : Int))) + (if x = Finset.univ then (v : Int) else 0) -
          (x.sum (fun j => (f (x.erase j) j : Int)) + (if x = ∅ then (v : Int) else 0)) = 0 := by
        have h := congrArg (fun m : Nat => (m : Int)) (hflow.2 x)
        push_cast at h
        have : (if x = Finset.univ then (v : Int) else 0) = ((if x = Finset.univ then v else 0 : Nat) : Int) := by
          split_ifs <;> simp
        have : (if x = ∅ then (v : Int) else 0) = ((if x = ∅ then v else 0 : Nat) : Int) := by
          split_ifs <;> simp
        omega
      -- Compute delta of out-edges of x
      have hd_out : (absentOf x).sum (fun j => (f' x j : Int) - (f x j : Int)) =
          (W.map (fun s : ResStep n =>
            (match s with | .fwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0) -
            (match s with | .bwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0))).sum := by
        have hsum_step : ∀ (j : Fin n) (hj : j ∉ x),
            (f' x j : Int) - (f x j : Int) =
            (if ResStep.fwd x j hj ∈ W then (1 : Int) else 0) -
            (if ResStep.bwd x j hj ∈ W then (1 : Int) else 0) := by
          intro j hj
          dsimp only [f']
          rw [dif_pos hj]
          by_cases hf1 : ResStep.fwd x j hj ∈ W
          · have hnb : ResStep.bwd x j hj ∉ W := fun hb => hno_fb x j hj ⟨hf1, hb⟩
            simp [hf1, hnb]
          · by_cases hb1 : ResStep.bwd x j hj ∈ W
            · have hv1 : 0 < f x j := hW_valid _ hb1
              simp only [hf1, ↓reduceIte, hb1]
              omega
            · simp [hf1, hb1]
        have hlhs : (absentOf x).sum (fun j => (f' x j : Int) - (f x j : Int)) =
            (absentOf x).sum (fun j =>
              (if h : j ∉ x then if ResStep.fwd x j h ∈ W then (1 : Int) else 0 else 0) -
              (if h : j ∉ x then if ResStep.bwd x j h ∈ W then (1 : Int) else 0 else 0)) := by
          apply Finset.sum_congr rfl; intro j hj
          have hjx : j ∉ x := (Finset.mem_filter.mp hj).2
          rw [hsum_step j hjx, dif_pos hjx, dif_pos hjx]
        rw [hlhs, Finset.sum_sub_distrib]
        have hpart1 : ∀ (U : List (ResStep n)), U.Nodup →
            (absentOf x).sum (fun j => if h : j ∉ x then if ResStep.fwd x j h ∈ U then (1 : Int) else 0 else 0) =
            (U.map (fun s : ResStep n => match s with | .fwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0)).sum := by
          intro U hUnd
          induction U with
          | nil => simp
          | cons s rest ih =>
            have hnd_r : rest.Nodup := (List.nodup_cons.mp hUnd).2
            have hs_nr : s ∉ rest := (List.nodup_cons.mp hUnd).1
            simp only [List.map_cons, List.sum_cons]
            rw [← ih hnd_r]
            cases s with
            | fwd y j hj =>
              by_cases hyx : y = x
              · subst hyx
                have hmem_abs : j ∈ absentOf y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
                have hsplit : (absentOf y).sum (fun i => if h : i ∉ y then if ResStep.fwd y i h ∈ ResStep.fwd y j hj :: rest then (1 : Int) else 0 else 0) =
                    (absentOf y).sum (fun i => (if i = j then (1 : Int) else 0) +
                      (if h : i ∉ y then if ResStep.fwd y i h ∈ rest then (1 : Int) else 0 else 0)) := by
                  apply Finset.sum_congr rfl; intro i hi
                  have hiy : i ∉ y := (Finset.mem_filter.mp hi).2
                  rw [dif_pos hiy, dif_pos hiy]
                  by_cases hij : i = j
                  · subst hij; simp [hs_nr]
                  · have hne : ResStep.fwd y i hiy ≠ ResStep.fwd y j hj := fun h => hij (by cases h; rfl)
                    simp [hij, hne]
                rw [hsplit, Finset.sum_add_distrib]
                simp [hmem_abs]
              · simp only [hyx, ↓reduceIte, zero_add]
                apply Finset.sum_congr rfl; intro i hi
                have hix : i ∉ x := (Finset.mem_filter.mp hi).2
                have hne : ResStep.fwd x i hix ≠ ResStep.fwd y j hj := fun h => hyx (by cases h; rfl)
                simp [hix, hne]
            | bwd _ _ _ | fwdRet | bwdRet =>
              simp only [zero_add]
              apply Finset.sum_congr rfl; intro i hi
              have hix : i ∉ x := (Finset.mem_filter.mp hi).2
              simp [hix]
        have hpart2 : ∀ (U : List (ResStep n)), U.Nodup →
            (absentOf x).sum (fun j => if h : j ∉ x then if ResStep.bwd x j h ∈ U then (1 : Int) else 0 else 0) =
            (U.map (fun s : ResStep n => match s with | .bwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0)).sum := by
          intro U hUnd
          induction U with
          | nil => simp
          | cons s rest ih =>
            have hnd_r : rest.Nodup := (List.nodup_cons.mp hUnd).2
            have hs_nr : s ∉ rest := (List.nodup_cons.mp hUnd).1
            simp only [List.map_cons, List.sum_cons]
            rw [← ih hnd_r]
            cases s with
            | bwd y j hj =>
              by_cases hyx : y = x
              · subst hyx
                have hmem_abs : j ∈ absentOf y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
                have hsplit : (absentOf y).sum (fun i => if h : i ∉ y then if ResStep.bwd y i h ∈ ResStep.bwd y j hj :: rest then (1 : Int) else 0 else 0) =
                    (absentOf y).sum (fun i => (if i = j then (1 : Int) else 0) +
                      (if h : i ∉ y then if ResStep.bwd y i h ∈ rest then (1 : Int) else 0 else 0)) := by
                  apply Finset.sum_congr rfl; intro i hi
                  have hiy : i ∉ y := (Finset.mem_filter.mp hi).2
                  rw [dif_pos hiy, dif_pos hiy]
                  by_cases hij : i = j
                  · subst hij; simp [hs_nr]
                  · have hne : ResStep.bwd y i hiy ≠ ResStep.bwd y j hj := fun h => hij (by cases h; rfl)
                    simp [hij, hne]
                rw [hsplit, Finset.sum_add_distrib]
                simp [hmem_abs]
              · simp only [hyx, ↓reduceIte, zero_add]
                apply Finset.sum_congr rfl; intro i hi
                have hix : i ∉ x := (Finset.mem_filter.mp hi).2
                have hne : ResStep.bwd x i hix ≠ ResStep.bwd y j hj := fun h => hyx (by cases h; rfl)
                simp [hix, hne]
            | fwd _ _ _ | fwdRet | bwdRet =>
              simp only [zero_add]
              apply Finset.sum_congr rfl; intro i hi
              have hix : i ∉ x := (Finset.mem_filter.mp hi).2
              simp [hix]
        rw [hpart1 W hW_nodup, hpart2 W hW_nodup]
        have hsub_u : ∀ (U : List (ResStep n)),
            (U.map (fun s : ResStep n => match s with | .fwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0)).sum -
            (U.map (fun s : ResStep n => match s with | .bwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0)).sum =
            (U.map (fun s : ResStep n =>
              (match s with | .fwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0) -
              (match s with | .bwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0))).sum := by
          intro U; induction U with
          | nil => simp
          | cons s rest ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring
        exact hsub_u W
      -- Compute delta of in-edges of x
      have hd_in : x.sum (fun j => (f' (x.erase j) j : Int) - (f (x.erase j) j : Int)) =
          (W.map (fun s : ResStep n =>
            (match s with | .fwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0) -
            (match s with | .bwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0))).sum := by
        have hsum_step : ∀ (j : Fin n), j ∈ x →
            (f' (x.erase j) j : Int) - (f (x.erase j) j : Int) =
            (if ResStep.fwd (x.erase j) j (Finset.notMem_erase j x) ∈ W then (1 : Int) else 0) -
            (if ResStep.bwd (x.erase j) j (Finset.notMem_erase j x) ∈ W then (1 : Int) else 0) := by
          intro j hj
          have hne := Finset.notMem_erase j x
          dsimp only [f']
          rw [dif_pos hne]
          by_cases hf1 : ResStep.fwd (x.erase j) j hne ∈ W
          · have hnb : ResStep.bwd (x.erase j) j hne ∉ W := fun hb => hno_fb _ j hne ⟨hf1, hb⟩
            simp [hf1, hnb]
          · by_cases hb1 : ResStep.bwd (x.erase j) j hne ∈ W
            · have hv1 : 0 < f (x.erase j) j := hW_valid _ hb1
              simp only [hf1, ↓reduceIte, hb1]
              omega
            · simp [hf1, hb1]
        have hlhs : x.sum (fun j => (f' (x.erase j) j : Int) - (f (x.erase j) j : Int)) =
            x.sum (fun j =>
              (if ResStep.fwd (x.erase j) j (Finset.notMem_erase j x) ∈ W then (1 : Int) else 0) -
              (if ResStep.bwd (x.erase j) j (Finset.notMem_erase j x) ∈ W then (1 : Int) else 0)) := by
          apply Finset.sum_congr rfl; intro j hj; exact hsum_step j hj
        rw [hlhs, Finset.sum_sub_distrib]
        have hpart1 : ∀ (U : List (ResStep n)), U.Nodup →
            x.sum (fun j => if ResStep.fwd (x.erase j) j (Finset.notMem_erase j x) ∈ U then (1 : Int) else 0) =
            (U.map (fun s : ResStep n => match s with | .fwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0)).sum := by
          intro U hUnd
          induction U with
          | nil => simp
          | cons s rest ih =>
            have hnd_r : rest.Nodup := (List.nodup_cons.mp hUnd).2
            have hs_nr : s ∉ rest := (List.nodup_cons.mp hUnd).1
            simp only [List.map_cons, List.sum_cons]
            rw [← ih hnd_r]
            cases s with
            | fwd y j hj =>
              by_cases hins : insert j y = x
              · have hjx : j ∈ x := hins ▸ Finset.mem_insert_self j y
                have hy_eq : x.erase j = y := hins ▸ Finset.erase_insert hj
                have hsplit : x.sum (fun i => if ResStep.fwd (x.erase i) i (Finset.notMem_erase i x) ∈ ResStep.fwd y j hj :: rest then (1 : Int) else 0) =
                    x.sum (fun i => (if i = j then (1 : Int) else 0) +
                      (if ResStep.fwd (x.erase i) i (Finset.notMem_erase i x) ∈ rest then (1 : Int) else 0)) := by
                  apply Finset.sum_congr rfl; intro i _
                  by_cases hij : i = j
                  · subst hij
                    have hfeq : ResStep.fwd (x.erase i) i (Finset.notMem_erase i x) = ResStep.fwd y i hj := by
                      cases hy_eq; rfl
                    rw [hfeq]; simp [hs_nr]
                  · have hne : ResStep.fwd (x.erase i) i (Finset.notMem_erase i x) ≠ ResStep.fwd y j hj :=
                      fun h => hij (by cases h; rfl)
                    simp [hij, hne]
                rw [hsplit, Finset.sum_add_distrib]; simp [hins, hjx]
              · simp only [hins, ↓reduceIte, zero_add]
                apply Finset.sum_congr rfl; intro i hi
                have hne : ResStep.fwd (x.erase i) i (Finset.notMem_erase i x) ≠ ResStep.fwd y j hj := by
                  intro h; cases h; exact hins (Finset.insert_erase hi)
                simp [hne]
            | bwd _ _ _ | fwdRet | bwdRet =>
              simp only [zero_add]
              apply Finset.sum_congr rfl; intro i _; simp
        have hpart2 : ∀ (U : List (ResStep n)), U.Nodup →
            x.sum (fun j => if ResStep.bwd (x.erase j) j (Finset.notMem_erase j x) ∈ U then (1 : Int) else 0) =
            (U.map (fun s : ResStep n => match s with | .bwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0)).sum := by
          intro U hUnd
          induction U with
          | nil => simp
          | cons s rest ih =>
            have hnd_r : rest.Nodup := (List.nodup_cons.mp hUnd).2
            have hs_nr : s ∉ rest := (List.nodup_cons.mp hUnd).1
            simp only [List.map_cons, List.sum_cons]
            rw [← ih hnd_r]
            cases s with
            | bwd y j hj =>
              by_cases hins : insert j y = x
              · have hjx : j ∈ x := hins ▸ Finset.mem_insert_self j y
                have hy_eq : x.erase j = y := hins ▸ Finset.erase_insert hj
                have hsplit : x.sum (fun i => if ResStep.bwd (x.erase i) i (Finset.notMem_erase i x) ∈ ResStep.bwd y j hj :: rest then (1 : Int) else 0) =
                    x.sum (fun i => (if i = j then (1 : Int) else 0) +
                      (if ResStep.bwd (x.erase i) i (Finset.notMem_erase i x) ∈ rest then (1 : Int) else 0)) := by
                  apply Finset.sum_congr rfl; intro i _
                  by_cases hij : i = j
                  · subst hij
                    have hfeq : ResStep.bwd (x.erase i) i (Finset.notMem_erase i x) = ResStep.bwd y i hj := by
                      cases hy_eq; rfl
                    rw [hfeq]; simp [hs_nr]
                  · have hne : ResStep.bwd (x.erase i) i (Finset.notMem_erase i x) ≠ ResStep.bwd y j hj :=
                      fun h => hij (by cases h; rfl)
                    simp [hij, hne]
                rw [hsplit, Finset.sum_add_distrib]; simp [hins, hjx]
              · simp only [hins, ↓reduceIte, zero_add]
                apply Finset.sum_congr rfl; intro i hi
                have hne : ResStep.bwd (x.erase i) i (Finset.notMem_erase i x) ≠ ResStep.bwd y j hj := by
                  intro h; cases h; exact hins (Finset.insert_erase hi)
                simp [hne]
            | fwd _ _ _ | fwdRet | bwdRet =>
              simp only [zero_add]
              apply Finset.sum_congr rfl; intro i _; simp
        rw [hpart1 W hW_nodup, hpart2 W hW_nodup]
        have hsub_u : ∀ (U : List (ResStep n)),
            (U.map (fun s : ResStep n => match s with | .fwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0)).sum -
            (U.map (fun s : ResStep n => match s with | .bwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0)).sum =
            (U.map (fun s : ResStep n =>
              (match s with | .fwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0) -
              (match s with | .bwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0))).sum := by
          intro U; induction U with
          | nil => simp
          | cons s rest ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring
        exact hsub_u W
      -- Delta of return terms (v' - v)
      have hdv : (v' : Int) - (v : Int) =
          (W.map (fun s : ResStep n => match s with | .fwdRet => (1 : Int) | .bwdRet => -1 | _ => 0)).sum := by
        have hsum_ret : ∀ (U : List (ResStep n)), U.Nodup →
            (U.map (fun s : ResStep n => match s with | .fwdRet => (1 : Int) | .bwdRet => -1 | _ => 0)).sum =
            (if ResStep.fwdRet ∈ U then (1 : Int) else 0) - (if ResStep.bwdRet ∈ U then (1 : Int) else 0) := by
          intro U hUnd
          induction U with
          | nil => simp
          | cons s rest ih =>
            have hnd_r := (List.nodup_cons.mp hUnd).2
            have hs_nr := (List.nodup_cons.mp hUnd).1
            simp only [List.map_cons, List.sum_cons, ih hnd_r]
            cases s with
            | fwdRet => simp [hs_nr]; ring
            | bwdRet => simp [hs_nr]; ring
            | fwd _ _ _ => simp
            | bwd _ _ _ => simp
        rw [hsum_ret W hW_nodup]
        dsimp only [v']
        by_cases hfr : ResStep.fwdRet ∈ W
        · have hnbr : ResStep.bwdRet ∉ W := fun h => hno_ret ⟨hfr, h⟩
          simp [hfr, hnbr]
        · by_cases hbr : ResStep.bwdRet ∈ W
          · have hv0 : 0 < v := hW_valid _ hbr
            simp only [hfr, ↓reduceIte, hbr]; omega
          · simp [hfr, hbr]
      -- Combine hd_out, hd_in, hdv to see the total delta equals hwalk_bal x = 0!
      have htot_delta :
          ((absentOf x).sum (fun j => (f' x j : Int)) - (absentOf x).sum (fun j => (f x j : Int))) +
          (if x = Finset.univ then (v' : Int) - (v : Int) else 0) -
          ((x.sum (fun j => (f' (x.erase j) j : Int)) - x.sum (fun j => (f (x.erase j) j : Int))) +
           (if x = ∅ then (v' : Int) - (v : Int) else 0)) =
          (W.map (fun s : ResStep n => (if s.src = x then (1 : Int) else 0) - (if s.dst = x then 1 else 0))).sum := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, hd_out, hd_in]
        have hret_u : (if x = Finset.univ then (v' : Int) - (v : Int) else 0) -
            (if x = ∅ then (v' : Int) - (v : Int) else 0) =
            (W.map (fun s : ResStep n =>
              (match s with | .fwdRet => if Finset.univ = x then (1 : Int) else 0 | .bwdRet => if ∅ = x then 1 else 0 | _ => 0) -
              (match s with | .fwdRet => if ∅ = x then (1 : Int) else 0 | .bwdRet => if Finset.univ = x then 1 else 0 | _ => 0))).sum := by
          rw [hdv]
          have haux : ∀ (U : List (ResStep n)),
              (if x = Finset.univ then (U.map (fun s : ResStep n => match s with | .fwdRet => (1 : Int) | .bwdRet => -1 | _ => 0)).sum else 0) -
              (if x = ∅ then (U.map (fun s : ResStep n => match s with | .fwdRet => (1 : Int) | .bwdRet => -1 | _ => 0)).sum else 0) =
              (U.map (fun s : ResStep n =>
                (match s with | .fwdRet => if Finset.univ = x then (1 : Int) else 0 | .bwdRet => if ∅ = x then 1 else 0 | _ => 0) -
                (match s with | .fwdRet => if ∅ = x then (1 : Int) else 0 | .bwdRet => if Finset.univ = x then 1 else 0 | _ => 0))).sum := by
            intro U
            by_cases h1 : x = Finset.univ <;> by_cases h2 : x = ∅
            · induction U with
              | nil => simp
              | cons s rest ih =>
                simp only [List.map_cons, List.sum_cons, if_pos h1, if_pos h2, if_pos h1.symm, if_pos h2.symm] at ih ⊢
                cases s <;> linarith
            · induction U with
              | nil => simp
              | cons s rest ih =>
                simp only [List.map_cons, List.sum_cons, if_pos h1, if_neg h2, if_pos h1.symm, if_neg (Ne.symm h2)] at ih ⊢
                cases s <;> linarith
            · induction U with
              | nil => simp
              | cons s rest ih =>
                simp only [List.map_cons, List.sum_cons, if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm] at ih ⊢
                cases s <;> linarith
            · induction U with
              | nil => simp
              | cons s rest ih =>
                simp only [List.map_cons, List.sum_cons, if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)] at ih ⊢
                cases s <;> linarith
          exact haux W
        have hstep_comb : ∀ (U : List (ResStep n)),
            (U.map (fun s : ResStep n =>
              (match s with | .fwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0) -
              (match s with | .bwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0))).sum -
            (U.map (fun s : ResStep n =>
              (match s with | .fwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0) -
              (match s with | .bwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0))).sum +
            (U.map (fun s : ResStep n =>
              (match s with | .fwdRet => if Finset.univ = x then (1 : Int) else 0 | .bwdRet => if ∅ = x then 1 else 0 | _ => 0) -
              (match s with | .fwdRet => if ∅ = x then (1 : Int) else 0 | .bwdRet => if Finset.univ = x then 1 else 0 | _ => 0))).sum =
            (U.map (fun s : ResStep n => (if s.src = x then (1 : Int) else 0) - (if s.dst = x then 1 else 0))).sum := by
          intro U
          have hite_irrel : ∀ (P : Prop) (d1 d2 : Decidable P),
              (@ite Int P d1 1 0) = (@ite Int P d2 1 0) := by
            intro P d1 d2; cases d1 <;> cases d2 <;> simp_all
          have hpt : ∀ s : ResStep n,
              ((match s with | .fwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0) -
               (match s with | .bwd y _ _ => if y = x then (1 : Int) else 0 | _ => 0)) -
              ((match s with | .fwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0) -
               (match s with | .bwd y j _ => if insert j y = x then (1 : Int) else 0 | _ => 0)) +
              ((match s with | .fwdRet => if Finset.univ = x then (1 : Int) else 0 | .bwdRet => if ∅ = x then 1 else 0 | _ => 0) -
               (match s with | .fwdRet => if ∅ = x then (1 : Int) else 0 | .bwdRet => if Finset.univ = x then 1 else 0 | _ => 0)) =
              (if s.src = x then (1 : Int) else 0) - (if s.dst = x then 1 else 0) := by
            intro s
            cases s with
            | fwd _ _ _ =>
              simp [ResStep.src, ResStep.dst]
              exact congrArg₂ (· - ·) (hite_irrel _ _ _) (hite_irrel _ _ _)
            | bwd _ _ _ =>
              simp only [ResStep.src, ResStep.dst, zero_sub, sub_zero, add_zero, sub_neg_eq_add, neg_add_eq_sub]
              exact congrArg₂ (· - ·) (hite_irrel _ _ _) (hite_irrel _ _ _)
            | fwdRet =>
              simp [ResStep.src, ResStep.dst]
              try exact congrArg₂ (· - ·) (hite_irrel _ _ _) (hite_irrel _ _ _)
            | bwdRet =>
              simp [ResStep.src, ResStep.dst]
              try exact congrArg₂ (· - ·) (hite_irrel _ _ _) (hite_irrel _ _ _)
          induction U with
          | nil => simp
          | cons s rest ih =>
            simp only [List.map_cons, List.sum_cons]
            have hs := hpt s
            omega
        linarith [hret_u, hstep_comb W]
      rw [hwalk_bal x] at htot_delta
      have hint_eq :
          ((absentOf x).sum (fun j => f' x j) + (if x = Finset.univ then v' else 0) : Int) =
          ((x.sum (fun j => f' (x.erase j) j) + (if x = ∅ then v' else 0) : Nat) : Int) := by
        push_cast
        have h1 : (if x = Finset.univ then (v' : Int) else 0) - (if x = Finset.univ then (v : Int) else 0) =
            if x = Finset.univ then (v' : Int) - (v : Int) else 0 := by split_ifs <;> simp
        have h2 : (if x = ∅ then (v' : Int) else 0) - (if x = ∅ then (v : Int) else 0) =
            if x = ∅ then (v' : Int) - (v : Int) else 0 := by split_ifs <;> simp
        have h3 : ((if x = ∅ then v' else 0 : Nat) : Int) = if x = ∅ then (v' : Int) else 0 := by split_ifs <;> simp
        have h4 : ((if x = Finset.univ then v' else 0 : Nat) : Int) = if x = Finset.univ then (v' : Int) else 0 := by split_ifs <;> simp
        linarith
      exact Int.ofNat.inj (by simpa using hint_eq)
  -- Compute exact objective gain flowObj w d v' f' - flowObj w d v f = - walkCost w d f W > 0!
  have hobj_gain : flowObj w d v' f' - flowObj w d v f = - walkCost w d f W := by
    unfold flowObj
    have hdv_cost : -((d : Int) * (v' : Int) - (d : Int) * (v : Int)) =
        -(W.map (fun s : ResStep n => match s with | .fwdRet => (d : Int) | .bwdRet => -(d : Int) | _ => 0)).sum := by
      have hsum_ret : ∀ (U : List (ResStep n)), U.Nodup →
          (U.map (fun s : ResStep n => match s with | .fwdRet => (d : Int) | .bwdRet => -(d : Int) | _ => 0)).sum =
          (if ResStep.fwdRet ∈ U then (d : Int) else 0) - (if ResStep.bwdRet ∈ U then (d : Int) else 0) := by
        intro U hUnd
        induction U with
        | nil => simp
        | cons s rest ih =>
          have hnd_r := (List.nodup_cons.mp hUnd).2
          have hs_nr := (List.nodup_cons.mp hUnd).1
          simp only [List.map_cons, List.sum_cons, ih hnd_r]
          cases s with
          | fwdRet => simp [hs_nr]; ring
          | bwdRet => simp [hs_nr]; ring
          | fwd _ _ _ => simp
          | bwd _ _ _ => simp
      rw [hsum_ret W hW_nodup]
      dsimp only [v']
      by_cases hfr : ResStep.fwdRet ∈ W
      · have hnbr : ResStep.bwdRet ∉ W := fun h => hno_ret ⟨hfr, h⟩
        simp [hfr, hnbr]; ring
      · by_cases hbr : ResStep.bwdRet ∈ W
        · have hv0 : 0 < v := hW_valid _ hbr
          simp only [hfr, ↓reduceIte, hbr]
          have hsub : ((v - 1 : Nat) : Int) = (v : Int) - 1 := by omega
          rw [hsub]; ring
        · simp [hfr, hbr]
    have hpay_diff :
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => (min (w x j) (f' x j) : Int) - (min (w x j) (f x j) : Int))) =
        -(W.map (fun s : ResStep n => match s with
          | .fwd x j _ => if f x j < w x j then (-1 : Int) else 0
          | .bwd x j _ => if f x j ≤ w x j then (1 : Int) else 0
          | _ => 0)).sum := by
      have hterm : ∀ (x : Finset (Fin n)) (j : Fin n) (hj : j ∉ x),
          (min (w x j) (f' x j) : Int) - (min (w x j) (f x j) : Int) =
          (if ResStep.fwd x j hj ∈ W then (if f x j < w x j then (1 : Int) else 0) else 0) -
          (if ResStep.bwd x j hj ∈ W then (if f x j ≤ w x j then (1 : Int) else 0) else 0) := by
        intro x j hj
        dsimp only [f']; rw [dif_pos hj]
        by_cases hf1 : ResStep.fwd x j hj ∈ W
        · have hnb : ResStep.bwd x j hj ∉ W := fun hb => hno_fb x j hj ⟨hf1, hb⟩
          simp only [hf1, ↓reduceIte, hnb, sub_zero]
          split_ifs with hlt <;> omega
        · by_cases hb1 : ResStep.bwd x j hj ∈ W
          · have hv1 : 0 < f x j := hW_valid _ hb1
            simp only [hf1, ↓reduceIte, hb1, zero_sub]
            split_ifs with hle <;> omega
          · simp [hf1, hb1]
      have hlhs : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            (absentOf x).sum (fun j => (min (w x j) (f' x j) : Int) - (min (w x j) (f x j) : Int))) =
          (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            (absentOf x).sum (fun j =>
              (if h : j ∉ x then if ResStep.fwd x j h ∈ W then (if f x j < w x j then (1 : Int) else 0) else 0 else 0) -
              (if h : j ∉ x then if ResStep.bwd x j h ∈ W then (if f x j ≤ w x j then (1 : Int) else 0) else 0 else 0))) := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro j hj
        have hjx : j ∉ x := (Finset.mem_filter.mp hj).2
        rw [hterm x j hjx, dif_pos hjx, dif_pos hjx]
      rw [hlhs]
      have haux_pay : ∀ (U : List (ResStep n)), U.Nodup →
          (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            (absentOf x).sum (fun j =>
              (if h : j ∉ x then if ResStep.fwd x j h ∈ U then (if f x j < w x j then (1 : Int) else 0) else 0 else 0) -
              (if h : j ∉ x then if ResStep.bwd x j h ∈ U then (if f x j ≤ w x j then (1 : Int) else 0) else 0 else 0))) =
          -(U.map (fun s : ResStep n => match s with
            | .fwd x j _ => if f x j < w x j then (-1 : Int) else 0
            | .bwd x j _ => if f x j ≤ w x j then (1 : Int) else 0
            | _ => 0)).sum := by
        intro U hUnd
        induction U with
        | nil => simp
        | cons s rest ih =>
          have hnd_r := (List.nodup_cons.mp hUnd).2
          have hs_nr := (List.nodup_cons.mp hUnd).1
          simp only [List.map_cons, List.sum_cons, neg_add]
          rw [← ih hnd_r]
          cases s with
          | fwd y j hj =>
            have hmem_y : y ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ y
            have hmem_j : j ∈ absentOf y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
            have hsplit : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
                (absentOf x).sum (fun i =>
                  (if h : i ∉ x then if ResStep.fwd x i h ∈ ResStep.fwd y j hj :: rest then (if f x i < w x i then (1 : Int) else 0) else 0 else 0) -
                  (if h : i ∉ x then if ResStep.bwd x i h ∈ ResStep.fwd y j hj :: rest then (if f x i ≤ w x i then (1 : Int) else 0) else 0 else 0))) =
                (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
                  (absentOf x).sum (fun i =>
                    (if x = y ∧ i = j then (if f y j < w y j then (1 : Int) else 0) else 0) +
                    ((if h : i ∉ x then if ResStep.fwd x i h ∈ rest then (if f x i < w x i then (1 : Int) else 0) else 0 else 0) -
                     (if h : i ∉ x then if ResStep.bwd x i h ∈ rest then (if f x i ≤ w x i then (1 : Int) else 0) else 0 else 0)))) := by
              apply Finset.sum_congr rfl; intro x _
              apply Finset.sum_congr rfl; intro i hi
              have hix : i ∉ x := (Finset.mem_filter.mp hi).2
              rw [dif_pos hix, dif_pos hix, dif_pos hix, dif_pos hix]
              by_cases hxy : x = y ∧ i = j
              · rcases hxy with ⟨rfl, rfl⟩
                simp [hs_nr]; ring
              · have hne : ResStep.fwd x i hix ≠ ResStep.fwd y j hj := by
                  intro h; cases h; exact hxy ⟨rfl, rfl⟩
                simp [hxy, hne]
            rw [hsplit]
            simp_rw [Finset.sum_add_distrib]
            have hdelta : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
                (absentOf x).sum (fun i => if x = y ∧ i = j then (if f y j < w y j then (1 : Int) else 0) else 0)) =
                -(if f y j < w y j then (-1 : Int) else 0) := by
              rw [Finset.sum_eq_single y]
              · rw [Finset.sum_eq_single j]
                · by_cases hlt : f y j < w y j <;> simp [hlt]
                · intro i _ hne; simp [hne]
                · intro h; exact (h hmem_j).elim
              · intro x _ hne; apply Finset.sum_eq_zero; intro i _; simp [hne]
              · intro h; exact (h hmem_y).elim
            rw [hdelta]
          | bwd y j hj =>
            have hmem_y : y ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ y
            have hmem_j : j ∈ absentOf y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
            have hsplit : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
                (absentOf x).sum (fun i =>
                  (if h : i ∉ x then if ResStep.fwd x i h ∈ ResStep.bwd y j hj :: rest then (if f x i < w x i then (1 : Int) else 0) else 0 else 0) -
                  (if h : i ∉ x then if ResStep.bwd x i h ∈ ResStep.bwd y j hj :: rest then (if f x i ≤ w x i then (1 : Int) else 0) else 0 else 0))) =
                (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
                  (absentOf x).sum (fun i =>
                    (if x = y ∧ i = j then -(if f y j ≤ w y j then (1 : Int) else 0) else 0) +
                    ((if h : i ∉ x then if ResStep.fwd x i h ∈ rest then (if f x i < w x i then (1 : Int) else 0) else 0 else 0) -
                     (if h : i ∉ x then if ResStep.bwd x i h ∈ rest then (if f x i ≤ w x i then (1 : Int) else 0) else 0 else 0)))) := by
              apply Finset.sum_congr rfl; intro x _
              apply Finset.sum_congr rfl; intro i hi
              have hix : i ∉ x := (Finset.mem_filter.mp hi).2
              rw [dif_pos hix, dif_pos hix, dif_pos hix, dif_pos hix]
              by_cases hxy : x = y ∧ i = j
              · rcases hxy with ⟨rfl, rfl⟩
                simp [hs_nr]; ring
              · have hne : ResStep.bwd x i hix ≠ ResStep.bwd y j hj := by
                  intro h; cases h; exact hxy ⟨rfl, rfl⟩
                simp [hxy, hne]
            rw [hsplit]
            simp_rw [Finset.sum_add_distrib]
            have hdelta : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
                (absentOf x).sum (fun i => if x = y ∧ i = j then -(if f y j ≤ w y j then (1 : Int) else 0) else 0)) =
                -(if f y j ≤ w y j then (1 : Int) else 0) := by
              rw [Finset.sum_eq_single y]
              · rw [Finset.sum_eq_single j]
                · simp
                · intro i _ hne; simp [hne]
                · intro h; exact (h hmem_j).elim
              · intro x _ hne; apply Finset.sum_eq_zero; intro i _; simp [hne]
              · intro h; exact (h hmem_y).elim
            rw [hdelta]
          | fwdRet | bwdRet =>
            simp only [neg_zero, zero_add]
            apply Finset.sum_congr rfl; intro x _
            apply Finset.sum_congr rfl; intro i hi
            have hix : i ∉ x := (Finset.mem_filter.mp hi).2
            simp [hix]
      exact haux_pay W hW_nodup
    have hwc_split : walkCost w d f W =
        (W.map (fun s : ResStep n => match s with
          | .fwd x j _ => if f x j < w x j then (-1 : Int) else 0
          | .bwd x j _ => if f x j ≤ w x j then (1 : Int) else 0
          | _ => 0)).sum +
        (W.map (fun s : ResStep n => match s with | .fwdRet => (d : Int) | .bwdRet => -(d : Int) | _ => 0)).sum := by
      have haux_wc : ∀ (U : List (ResStep n)), walkCost w d f U =
          (U.map (fun s : ResStep n => match s with
            | .fwd x j _ => if f x j < w x j then (-1 : Int) else 0
            | .bwd x j _ => if f x j ≤ w x j then (1 : Int) else 0
            | _ => 0)).sum +
          (U.map (fun s : ResStep n => match s with | .fwdRet => (d : Int) | .bwdRet => -(d : Int) | _ => 0)).sum := by
        intro U; unfold walkCost
        induction U with
        | nil => simp
        | cons s rest ih =>
          simp only [List.map_cons, List.sum_cons, ih]
          cases s <;> simp [ResStep.cost] <;> ring
      exact haux_wc W
    have hsub_sum :
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (absentOf x).sum (fun j => (min (w x j) (f' x j) : Int))) -
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (absentOf x).sum (fun j => (min (w x j) (f x j) : Int))) =
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => (min (w x j) (f' x j) : Int) - (min (w x j) (f x j) : Int))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_sub_distrib]
    linarith [hsub_sum, hpay_diff, hdv_cost, hwc_split]
  have hle := hopt v' f' hf'_flow
  omega

-- Bellman-Ford existence of potential π : Finset (Fin n) → Int from no_neg_cycle!
private noncomputable def allResSteps (n : Nat) : List (ResStep n) :=
  ResStep.fwdRet :: ResStep.bwdRet ::
  ((Finset.univ : Finset (Finset (Fin n))).toList.flatMap fun x =>
    (Finset.univ : Finset (Fin n)).toList.flatMap fun j =>
      if hj : j ∉ x then [ResStep.fwd x j hj, ResStep.bwd x j hj] else [])

private lemma mem_allResSteps {n : Nat} (s : ResStep n) : s ∈ allResSteps n := by
  unfold allResSteps
  cases s with
  | fwdRet => simp
  | bwdRet => simp
  | fwd x j hj =>
    simp only [List.mem_cons]
    right; right
    rw [List.mem_flatMap]
    refine ⟨x, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
    rw [List.mem_flatMap]
    exact ⟨j, Finset.mem_toList.mpr (Finset.mem_univ _), by rw [dif_pos hj]; simp⟩
  | bwd x j hj =>
    simp only [List.mem_cons]
    right; right
    rw [List.mem_flatMap]
    refine ⟨x, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
    rw [List.mem_flatMap]
    exact ⟨j, Finset.mem_toList.mpr (Finset.mem_univ _), by rw [dif_pos hj]; simp⟩

private noncomputable def bfDp {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (d : Nat) (f : Finset (Fin n) → Fin n → Nat) (validSteps : List (ResStep n)) :
    Nat → Finset (Fin n) → Int
  | 0, _ => 0
  | k + 1, y =>
    (validSteps.filter (fun s => decide (s.dst = y))).foldl
      (fun acc s => min acc (bfDp w d f validSteps k s.src + s.cost w d f))
      (bfDp w d f validSteps k y)

private lemma exists_potential_of_no_neg_cycle {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (d : Nat) (v : Nat) (f : Finset (Fin n) → Fin n → Nat)
    (hnocyc : ∀ (a : Finset (Fin n)) (W : List (ResStep n)), IsWalk v f a a W → 0 ≤ walkCost w d f W) :
    ∃ pi : Finset (Fin n) → Int,
      pi ∅ = 0 ∧ (∀ x, pi x ≤ 0) ∧
      ∀ s : ResStep n, s.valid v f → pi s.dst ≤ pi s.src + s.cost w d f := by
  let validSteps : List (ResStep n) := (allResSteps n).filter (fun s => decide (s.valid v f))
  let dp : Nat → Finset (Fin n) → Int := bfDp w d f validSteps
  have hfold_le_init : ∀ (l : List (ResStep n)) (g : ResStep n → Int) (init : Int),
      l.foldl (fun acc s => min acc (g s)) init ≤ init := by
    intro l g init
    induction l generalizing init with
    | nil => exact le_refl _
    | cons s rest ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min init (g s))) (min_le_left _ _)
  have hfold_le_mem : ∀ (l : List (ResStep n)) (g : ResStep n → Int) (init : Int) (s : ResStep n),
      s ∈ l → l.foldl (fun acc s => min acc (g s)) init ≤ g s := by
    intro l g init s hs
    induction l generalizing init with
    | nil => cases hs
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hs with rfl | htl
      · exact le_trans (hfold_le_init tl g _) (min_le_right _ _)
      · exact ih _ htl
  have hfold_mem_or_init : ∀ (l : List (ResStep n)) (g : ResStep n → Int) (init : Int),
      l.foldl (fun acc s => min acc (g s)) init = init ∨
      ∃ s ∈ l, l.foldl (fun acc s => min acc (g s)) init = g s := by
    intro l g init
    induction l generalizing init with
    | nil => left; rfl
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      rcases ih (min init (g hd)) with heq | ⟨s, hs, heq⟩
      · rw [heq]
        rcases min_cases init (g hd) with ⟨h, _⟩ | ⟨h, _⟩
        · left; exact h
        · right; exact ⟨hd, by simp, h⟩
      · right; exact ⟨s, List.mem_cons_of_mem hd hs, heq⟩
  have hdp_mono : ∀ k x, dp (k + 1) x ≤ dp k x := fun k x => by
    dsimp only [dp, bfDp]; exact hfold_le_init _ _ _
  have hdp_le0 : ∀ k x, dp k x ≤ 0 := by
    intro k; induction k with
    | zero => intro _; dsimp only [dp, bfDp]; exact le_refl 0
    | succ k ih => intro x; exact le_trans (hdp_mono k x) (ih x)
  have hdp_step : ∀ k (s : ResStep n), s.valid v f → dp (k + 1) s.dst ≤ dp k s.src + s.cost w d f := by
    intro k s hsv
    dsimp only [dp, bfDp]
    apply hfold_le_mem
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨mem_allResSteps s, decide_eq_true hsv⟩, decide_eq_true rfl⟩
  have hdp_realized : ∀ k x, ∃ W : List (ResStep n), IsWalk v f ∅ x W ∧ walkCost w d f W ≤ dp k x := by
    intro k
    induction k with
    | zero =>
      intro x; dsimp only [dp, bfDp]; exact walk_from_empty_zero v f w d x
    | succ k ih =>
      intro x
      rcases hfold_mem_or_init (validSteps.filter (fun s => decide (s.dst = x)))
          (fun s => dp k s.src + s.cost w d f) (dp k x) with heq | ⟨s, hs, heq⟩
      · rcases ih x with ⟨W, hW, hc⟩
        exact ⟨W, hW, by dsimp only [dp, bfDp]; rw [show List.foldl _ _ _ = dp k x from heq]; exact hc⟩
      · have hs1 := List.mem_filter.mp hs
        have hdst : s.dst = x := of_decide_eq_true hs1.2
        have hsv : s.valid v f := of_decide_eq_true (List.mem_filter.mp hs1.1).2
        rcases ih s.src with ⟨W, hW, hc⟩
        refine ⟨W ++ [s], hW.append ⟨hsv, rfl, hdst⟩, ?_⟩
        rw [walkCost_append]
        have hsc : walkCost w d f [s] = s.cost w d f := by simp [walkCost]
        have hdp_eq : dp (k + 1) x = dp k s.src + s.cost w d f := heq
        omega
  have hdp_le_walk : ∀ k y x W, IsWalk v f y x W → W.length ≤ k → dp k x ≤ walkCost w d f W := by
    intro k
    induction k with
    | zero =>
      intro y x W hW hlen
      cases W with
      | nil => simp [dp, bfDp, walkCost]
      | cons _ _ => simp at hlen
    | succ k ih =>
      intro y x W hW hlen
      cases W with
      | nil =>
        simp only [walkCost, List.map_nil, List.sum_nil]
        exact hdp_le0 (k + 1) x
      | cons hd tl =>
        -- Peel off the LAST step of W!
        have hne : hd :: tl ≠ [] := List.cons_ne_nil hd tl
        let initW := (hd :: tl).dropLast
        let lastS := (hd :: tl).getLast hne
        have hsplit : hd :: tl = initW ++ [lastS] := (List.dropLast_append_getLast hne).symm
        have hlen_i : initW.length < (hd :: tl).length := by simp [initW]
        rcases walk_split_at hW initW.length hlen_i with ⟨hW1, hW2⟩
        have htake : (hd :: tl).take initW.length = initW := by
          conv_lhs => rw [hsplit]
          exact List.take_left
        have hdrop : (hd :: tl).drop initW.length = [lastS] := by
          conv_lhs => rw [hsplit]
          exact List.drop_left
        have helem : (hd :: tl)[initW.length] = lastS := by
          have h1 : ((hd :: tl).drop initW.length)[0]? = some lastS := by rw [hdrop]; rfl
          have h2 : (hd :: tl)[initW.length]? = some lastS := by simpa [List.getElem?_drop] using h1
          rw [List.getElem?_eq_getElem hlen_i] at h2
          exact Option.some.inj h2
        rw [htake, helem] at hW1
        rw [hdrop, helem] at hW2
        rcases hW2 with ⟨hsv, _, hdst⟩
        have hih := ih y lastS.src initW hW1 (by omega)
        have hst := hdp_step k lastS hsv
        rw [hdst] at hst
        have hwc : walkCost w d f (hd :: tl) = walkCost w d f initW + lastS.cost w d f := by
          conv_lhs => rw [hsplit]
          rw [walkCost_append]; simp [walkCost]
        omega
  -- Shorten any walk to length <= Fintype.card (Finset (Fin n)) with <= cost!
  let K := Fintype.card (Finset (Fin n))
  have hshorten : ∀ (a b : Finset (Fin n)) (W : List (ResStep n)), IsWalk v f a b W →
      ∃ W' : List (ResStep n), IsWalk v f a b W' ∧ W'.length ≤ K ∧ walkCost w d f W' ≤ walkCost w d f W := by
    intro a b W
    induction hlenW : W.length using Nat.strong_induction_on generalizing W a b with
    | ind m ih =>
      intro hW
      by_cases hmK : m ≤ K
      · exact ⟨W, hW, by omega, le_refl _⟩
      · -- m > K, so W.map ResStep.src has length m > K = Fintype.card (Finset (Fin n)), hence a repeated src!
        have hnot_inj : ¬ Function.Injective (fun i : Fin W.length => W[i].src) := by
          intro hinj
          have hcard := Fintype.card_le_of_injective _ hinj
          rw [Fintype.card_fin] at hcard; omega
        unfold Function.Injective at hnot_inj
        push_neg at hnot_inj
        rcases hnot_inj with ⟨i, j, hsrceq, hne⟩
        suffices hcut : ∀ (p q : Nat) (hp : p < W.length) (hq : q < W.length),
            p < q → W[p].src = W[q].src →
            ∃ W' : List (ResStep n), IsWalk v f a b W' ∧ W'.length ≤ K ∧ walkCost w d f W' ≤ walkCost w d f W by
          rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
          · exact hcut i.val j.val i.isLt j.isLt h hsrceq
          · exact hcut j.val i.val j.isLt i.isLt h hsrceq.symm
        intro p q hp hq hpq hsrceq'
        rcases walk_split_at hW p hp with ⟨hWp1, hWp2⟩
        have hq_sub : q - p < (W.drop p).length := by simp; omega
        rcases walk_split_at hWp2 (q - p) hq_sub with ⟨hWmid, hWtail⟩
        have hmid_src : (W.drop p)[q - p].src = W[q].src := by
          simp [List.getElem_drop, show p + (q - p) = q by omega]
        rw [hmid_src, ← hsrceq'] at hWmid hWtail
        let W_mid := (W.drop p).take (q - p)
        let W_out := W.take p ++ (W.drop p).drop (q - p)
        have hW_out : IsWalk v f a b W_out := hWp1.append hWtail
        have hout_lt : W_out.length < m := by simp [W_out]; omega
        have hcost_eq : walkCost w d f W = walkCost w d f W_mid + walkCost w d f W_out := by
          have h1 : W = W.take p ++ (W_mid ++ (W.drop p).drop (q - p)) := by
            rw [List.take_append_drop, List.take_append_drop]
          conv_lhs => rw [h1]
          rw [walkCost_append, walkCost_append]
          simp only [W_out, walkCost_append]; ring
        have hc_mid : 0 ≤ walkCost w d f W_mid := hnocyc _ W_mid hWmid
        rcases ih W_out.length hout_lt a b W_out rfl hW_out with ⟨W', hW', hW'K, hW'c⟩
        exact ⟨W', hW', hW'K, by omega⟩
  refine ⟨dp K, ?_, hdp_le0 K, ?_⟩
  · -- dp K ∅ = 0
    have hle := hdp_le0 K ∅
    rcases hdp_realized K ∅ with ⟨W, hW, hc⟩
    have hge := hnocyc ∅ W hW
    omega
  · -- dp K s.dst <= dp K s.src + s.cost
    intro s hsv
    have h1 : dp (K + 1) s.dst ≤ dp K s.src + s.cost w d f := hdp_step K s hsv
    have h2 : dp K s.dst ≤ dp (K + 1) s.dst := by
      rcases hdp_realized (K + 1) s.dst with ⟨W, hW, hc⟩
      rcases hshorten ∅ s.dst W hW with ⟨W', hW', hW'K, hW'c⟩
      have h3 := hdp_le_walk K ∅ s.dst W' hW' hW'K
      omega
    omega

private instance instDecidableIsFlow {n : Nat} (v : Nat) (f : Finset (Fin n) → Fin n → Nat) :
    Decidable (IsFlow v f) := by
  unfold IsFlow; infer_instance

-- Existence of an optimal flow (v*, f*) with v* <= W and optimal_no_neg_cycle + rank r!
private lemma exists_optimal_flow_and_rank {n : Nat} (hn : 1 ≤ n)
    (w : Finset (Fin n) → Fin n → Nat) (d : Nat) (hd : 1 ≤ d) :
    let W := (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (absentOf x).sum (w x))
    ∃ (L : List (Equiv.Perm (Fin n))) (r : Finset (Fin n) → Nat),
      L.length ≤ W ∧
      (∀ x, r x ≤ d) ∧
      (∀ x y : Finset (Fin n), x ⊆ y → r x ≤ r y) ∧
      payOf w L =
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => if r x = r (insert j x) then w x j else 0)) +
        d * L.length := by
  intro W
  -- Finite domain of bounded flows: (v, f) in Fin (W + 1) × (Finset (Fin n) → Fin n → Fin (W + 1))
  let Dom := Fin (W + 1) × (Finset (Fin n) → Fin n → Fin (W + 1))
  let toV : Dom → Nat := fun p => p.1.val
  let toF : Dom → Finset (Fin n) → Fin n → Nat := fun p x j => (p.2 x j).val
  let validDom : Finset Dom := Finset.univ.filter (fun p => IsFlow (toV p) (toF p))
  have hzero_mem : (⟨0, Nat.zero_lt_succ W⟩, fun _ _ => ⟨0, Nat.zero_lt_succ W⟩) ∈ validDom := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro _ _ _; rfl
    · intro x; simp [toV, toF]
  rcases Finset.exists_max_image validDom (fun p => flowObj w d (toV p) (toF p)) ⟨_, hzero_mem⟩ with
    ⟨pStar, hpStar_mem, hpStar_max⟩
  let vStar := toV pStar
  let fStar := toF pStar
  have hvStar_le : vStar ≤ W := by have := pStar.1.isLt; dsimp only [vStar, toV]; omega
  have hfStar_flow : IsFlow vStar fStar := (Finset.mem_filter.mp hpStar_mem).2
  have hobj_nonneg : 0 ≤ flowObj w d vStar fStar := by
    have h0 := hpStar_max _ hzero_mem
    have hz : flowObj w d (toV (⟨0, Nat.zero_lt_succ W⟩, fun _ _ => ⟨0, Nat.zero_lt_succ W⟩))
        (toF (⟨0, Nat.zero_lt_succ W⟩, fun _ _ => ⟨0, Nat.zero_lt_succ W⟩)) = 0 := by
      simp [flowObj, toV, toF]
    dsimp only [vStar, fStar]; omega
  -- Global optimality over ALL flows (v', f'), even with v' > W!
  have hglobal_opt : ∀ v' f', IsFlow v' f' → flowObj w d v' f' ≤ flowObj w d vStar fStar := by
    intro v' f' hf'
    by_cases hvW : v' ≤ W
    · rcases flow_decompose hn v' f' hf' with ⟨L', hL'_len, hL'_vis⟩
      have hf'_le : ∀ x j, f' x j ≤ W := by
        intro x j
        by_cases hjx : j ∈ x
        · rw [hf'.1 x j hjx]; omega
        · rw [← hL'_vis x j hjx]
          calc visitsOf L' x j ≤ L'.length := List.length_filter_le _ _
            _ = v' := hL'_len
            _ ≤ W := hvW
      let p' : Dom := (⟨v', by omega⟩, fun x j => ⟨f' x j, by have := hf'_le x j; omega⟩)
      have hp'_mem : p' ∈ validDom := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'⟩
      exact hpStar_max p' hp'_mem
    · -- v' > W implies flowObj w d v' f' <= W - d * v' <= W - (W + 1) = -1 < 0 <= flowObj vStar fStar!
      have hpay_le : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => (min (w x j) (f' x j) : Int))) ≤ (W : Int) := by
        have hnat : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            (absentOf x).sum (fun j => min (w x j) (f' x j))) ≤ W := by
          apply Finset.sum_le_sum; intro x _
          apply Finset.sum_le_sum; intro j _
          exact min_le_left _ _
        have hcast := Int.ofNat_le.mpr hnat
        push_cast at hcast; exact hcast
      have hdv : (W : Int) + 1 ≤ (d : Int) * (v' : Int) := by
        have h1 : W + 1 ≤ d * v' := by
          calc W + 1 ≤ 1 * v' := by omega
            _ ≤ d * v' := Nat.mul_le_mul_right v' hd
        exact_mod_cast h1
      have hneg1 : flowObj w d v' f' ≤ -1 := by unfold flowObj; omega
      omega
  have hnocyc := optimal_no_neg_cycle hn w d vStar fStar hfStar_flow hglobal_opt
  rcases exists_potential_of_no_neg_cycle w d vStar fStar hnocyc with ⟨pi, hpi0, hpile0, hpi_tri⟩
  let r : Finset (Fin n) → Nat := fun x => (-pi x).toNat
  have hr_cast : ∀ x, (r x : Int) = -pi x := fun x => by
    dsimp only [r]; have := hpile0 x; omega
  have hr_empty : r ∅ = 0 := by dsimp only [r]; rw [hpi0]; rfl
  have hr_le_d : ∀ x, r x ≤ d := by
    -- First show r is monotone on subsets, then r univ <= d!
    have hstep : ∀ (x : Finset (Fin n)) (j : Fin n), j ∉ x → r x ≤ r (insert j x) := by
      intro x j hj
      have htri := hpi_tri (ResStep.fwd x j hj) trivial
      simp only [ResStep.src, ResStep.dst, ResStep.cost] at htri
      have h1 := hr_cast x; have h2 := hr_cast (insert j x)
      split_ifs at htri <;> omega
    have hsub_mono : ∀ x y : Finset (Fin n), x ⊆ y → r x ≤ r y := by
      intro x y hxy
      have hdiff : ∀ (s : Finset (Fin n)), Disjoint x s → r x ≤ r (x ∪ s) := by
        intro s
        induction s using Finset.induction_on with
        | empty => intro _; simp
        | @insert j t hj ih =>
          intro hdisj
          have hdisj_t : Disjoint x t := Disjoint.mono_right (Finset.subset_insert j t) hdisj
          have hjx : j ∉ x := Finset.disjoint_right.mp hdisj (Finset.mem_insert_self j t)
          have hjxt : j ∉ x ∪ t := by simp [hjx, hj]
          have h1 := ih hdisj_t
          have h2 := hstep (x ∪ t) j hjxt
          have hu : insert j (x ∪ t) = x ∪ insert j t := by ext a; simp
          rw [hu] at h2; omega
      have h1 := hdiff (y \ x) disjoint_sdiff_self_right
      rwa [Finset.union_sdiff_of_subset hxy] at h1
    have huniv : r Finset.univ ≤ d := by
      have htri := hpi_tri ResStep.fwdRet trivial
      simp only [ResStep.src, ResStep.dst, ResStep.cost, hpi0] at htri
      have hu := hr_cast Finset.univ
      omega
    intro x; exact le_trans (hsub_mono x Finset.univ (Finset.subset_univ x)) huniv
  have hr_mono : ∀ x y : Finset (Fin n), x ⊆ y → r x ≤ r y := by
    have hstep : ∀ (x : Finset (Fin n)) (j : Fin n), j ∉ x → r x ≤ r (insert j x) := by
      intro x j hj
      have htri := hpi_tri (ResStep.fwd x j hj) trivial
      simp only [ResStep.src, ResStep.dst, ResStep.cost] at htri
      have h1 := hr_cast x; have h2 := hr_cast (insert j x)
      split_ifs at htri <;> omega
    intro x y hxy
    have hdiff : ∀ (s : Finset (Fin n)), Disjoint x s → r x ≤ r (x ∪ s) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | @insert j t hj ih =>
        intro hdisj
        have hdisj_t : Disjoint x t := Disjoint.mono_right (Finset.subset_insert j t) hdisj
        have hjx : j ∉ x := Finset.disjoint_right.mp hdisj (Finset.mem_insert_self j t)
        have hjxt : j ∉ x ∪ t := by simp [hjx, hj]
        have h1 := ih hdisj_t
        have h2 := hstep (x ∪ t) j hjxt
        have hu : insert j (x ∪ t) = x ∪ insert j t := by ext a; simp
        rw [hu] at h2; omega
    have h1 := hdiff (y \ x) disjoint_sdiff_self_right
    rwa [Finset.union_sdiff_of_subset hxy] at h1
  -- Complementary slackness on every edge (x, j) with j ∉ x!
  have hcs_edge : ∀ (x : Finset (Fin n)) (j : Fin n), j ∉ x →
      min (w x j) (fStar x j) =
        (if r x = r (insert j x) then w x j else 0) + fStar x j * (r (insert j x) - r x) := by
    intro x j hj
    have hmono_e : r x ≤ r (insert j x) := hr_mono x (insert j x) (Finset.subset_insert j x)
    have hf_tri := hpi_tri (ResStep.fwd x j hj) trivial
    simp only [ResStep.src, ResStep.dst, ResStep.cost] at hf_tri
    have hrx := hr_cast x; have hry := hr_cast (insert j x)
    by_cases hf0 : fStar x j = 0
    · rw [hf0, Nat.min_zero, Nat.zero_mul, Nat.add_zero]
      by_cases hw0 : w x j = 0
      · simp [hw0]
      · have hlt : fStar x j < w x j := by omega
        simp only [hlt, ↓reduceIte] at hf_tri
        have hne : r x ≠ r (insert j x) := by omega
        simp [hne]
    · have hb_tri := hpi_tri (ResStep.bwd x j hj) (by change 0 < fStar x j; omega)
      simp only [ResStep.src, ResStep.dst, ResStep.cost] at hb_tri
      by_cases hlt : fStar x j < w x j
      · have hle : fStar x j ≤ w x j := le_of_lt hlt
        simp only [hlt, ↓reduceIte] at hf_tri
        simp only [hle, ↓reduceIte] at hb_tri
        have hdiff1 : r (insert j x) - r x = 1 := by omega
        have hne : r x ≠ r (insert j x) := by omega
        simp [hle, hne, hdiff1]
      · by_cases heq : fStar x j = w x j
        · have hle : fStar x j ≤ w x j := le_of_eq heq
          simp only [hle, ↓reduceIte] at hb_tri
          by_cases hreq : r x = r (insert j x)
          · simp [heq, hreq]
          · have hdiff1 : r (insert j x) - r x = 1 := by omega
            simp [heq, hreq, hdiff1]
        · have hgt : ¬ fStar x j ≤ w x j := by omega
          simp only [hgt, ↓reduceIte] at hb_tri
          have hreq : r x = r (insert j x) := by omega
          have hmin : min (w x j) (fStar x j) = w x j := min_eq_left (by omega)
          simp [hmin, hreq]
  -- Decompose (vStar, fStar) into L of length vStar <= W!
  rcases flow_decompose hn vStar fStar hfStar_flow with ⟨L, hL_len, hL_vis⟩
  -- Compute ∑_{x, j ∉ x} fStar x j * (r (insert j x) - r x) = d * L.length by telescoping along L!
  have htele_perm : ∀ π : Equiv.Perm (Fin n),
      (Finset.univ : Finset (Fin n)).sum (fun k => r (insert (π k) (preOf π k)) - r (preOf π k)) = r Finset.univ := by
    intro π
    let S : Nat → Finset (Fin n) := fun t =>
      ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < t)).image π
    have hS0 : S 0 = ∅ := by ext a; simp [S]
    have hSn : S n = Finset.univ := by
      ext a; simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨π.symm a, (π.symm a).isLt, Equiv.apply_symm_apply π a⟩
    have hS_step : ∀ k : Fin n, S (k.val + 1) = insert (π k) (S k.val) := by
      intro k; ext a; simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        by_cases heq : i.val = k.val
        · left; congr 1; exact Fin.ext heq
        · right; exact ⟨i, by omega, rfl⟩
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨k, by omega, rfl⟩
        · exact ⟨i, by omega, rfl⟩
    have hsum_t : ∀ t : Nat, t ≤ n →
        ((Finset.range t).sum (fun i => r (S (i + 1)) - r (S i))) = r (S t) := by
      intro t
      induction t with
      | zero => intro _; simp [hS0, hr_empty]
      | succ t iht =>
        intro htn
        rw [Finset.sum_range_succ, iht (by omega)]
        have hsub : S t ⊆ S (t + 1) := by
          intro a ha; rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hi).2; omega⟩, rfl⟩
        have hle := hr_mono _ _ hsub
        omega
    have hfin_eq : (Finset.univ : Finset (Fin n)).sum (fun k => r (insert (π k) (preOf π k)) - r (preOf π k)) =
        (Finset.range n).sum (fun i => r (S (i + 1)) - r (S i)) := by
      apply Finset.sum_bij (fun k _ => k.val)
      · intro k _; exact Finset.mem_range.mpr k.isLt
      · intro k1 _ k2 _ heq; exact Fin.ext heq
      · intro i hi; exact ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩
      · intro k _; rw [hS_step k]; rfl
    rw [hfin_eq, hsum_t n (le_refl n), hSn]
  have htele_L : ∀ (U : List (Equiv.Perm (Fin n))),
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => visitsOf U x j * (r (insert j x) - r x))) =
      r Finset.univ * U.length := by
    intro U
    induction U with
    | nil => simp [visitsOf_nil]
    | cons π tl ih =>
      simp only [List.length_cons]
      have hsplit : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => visitsOf (π :: tl) x j * (r (insert j x) - r x))) =
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => (if preOf π (π.symm j) = x then r (insert j x) - r x else 0))) +
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => visitsOf tl x j * (r (insert j x) - r x))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro x _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        rw [visitsOf_cons, Nat.add_mul]
        split_ifs <;> simp
      rw [hsplit, ih]
      have hsingle : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => if preOf π (π.symm j) = x then r (insert j x) - r x else 0)) =
          r Finset.univ := by
        have hswap : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
            (absentOf x).sum (fun j => if preOf π (π.symm j) = x then r (insert j x) - r x else 0)) =
          (Finset.univ : Finset (Fin n)).sum (fun j =>
            (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
              if j ∉ x ∧ preOf π (π.symm j) = x then r (insert j x) - r x else 0)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro x _
          unfold absentOf; rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro j _
          by_cases h1 : j ∉ x <;> by_cases h2 : preOf π (π.symm j) = x <;> simp [h1, h2]
        rw [hswap]
        have hinner : ∀ j : Fin n,
            (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
              if j ∉ x ∧ preOf π (π.symm j) = x then r (insert j x) - r x else 0) =
            r (insert j (preOf π (π.symm j))) - r (preOf π (π.symm j)) := by
          intro j
          have hnm : j ∉ preOf π (π.symm j) := by
            have := not_mem_preOf_self π (π.symm j); simpa [Equiv.apply_symm_apply] using this
          rw [Finset.sum_eq_single (preOf π (π.symm j))]
          · simp [hnm]
          · intro x _ hne; simp [hne.symm]
          · intro h; exact (h (Finset.mem_univ _)).elim
        simp_rw [hinner]
        rw [← Equiv.sum_comp π (fun j => r (insert j (preOf π (π.symm j))) - r (preOf π (π.symm j)))]
        simp only [Equiv.symm_apply_apply]
        exact htele_perm π
      rw [hsingle]; ring
  have hrv : r Finset.univ * L.length = d * L.length := by
    by_cases hL0 : L.length = 0
    · simp [hL0]
    · have hvpos : 0 < vStar := by omega
      have hbtri := hpi_tri ResStep.bwdRet hvpos
      simp only [ResStep.src, ResStep.dst, ResStep.cost, hpi0] at hbtri
      have hu := hr_cast Finset.univ
      have hru_le := hr_le_d Finset.univ
      have hru_eq : r Finset.univ = d := by omega
      rw [hru_eq]
  refine ⟨L, r, by omega, hr_le_d, hr_mono, ?_⟩
  unfold payOf
  have h1 : (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      (absentOf x).sum (fun j => min (w x j) (visitsOf L x j))) =
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      (absentOf x).sum (fun j =>
        (if r x = r (insert j x) then w x j else 0) + visitsOf L x j * (r (insert j x) - r x))) := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro j hj
    have hjx : j ∉ x := (Finset.mem_filter.mp hj).2
    rw [hL_vis x j hjx, hcs_edge x j hjx]
  rw [h1]
  simp_rw [Finset.sum_add_distrib]
  rw [htele_L L, hrv]

-- ============================================================================
-- Part 2B: Circuit construction from monotone rank r (size <= 64*(n+1)^2*(supp+1))
-- ============================================================================

private lemma build_monomial {n : Nat} (B0 : Bld (n + 2)) (S : Finset (Fin n)) :
    ∃ (B1 : Bld (n + 2)) (wOut : Nat),
      B0.Ext B1 ∧
      B1.size ≤ B0.size + S.card ∧
      B1.nots = B0.nots ∧
      wOut < (n + 2) + B1.size ∧
      (∀ x : Finset (Fin n),
        (B1.toCircuit.wires (mkInput x)).getD wOut false = decide (S ⊆ x)) := by
  have buildList : ∀ (B : Bld (n + 2)) (l : List (Fin n)),
      ∃ (B' : Bld (n + 2)) (wOut : Nat),
        B.Ext B' ∧ B'.size ≤ B.size + l.length ∧ B'.nots = B.nots ∧
        wOut < (n + 2) + B'.size ∧
        (∀ x : Finset (Fin n),
          (B'.toCircuit.wires (mkInput x)).getD wOut false = l.all (fun i => decide (i ∈ x))) := by
    intro B l
    induction l generalizing B with
    | nil =>
      refine ⟨B, n + 1, Bld.Ext.refl B, by simp, rfl, by omega, fun x => ?_⟩
      rw [wires_getD_input _ _ (n + 1) (by rw [mkInput_length]; omega), mkInput_getD_true]; rfl
    | cons a tl ih =>
      rcases ih B with ⟨B1, wTl, h01, hsz1, hnt1, hwT_lt, hwT_ev⟩
      let pA := B1.mkAnd a.val wTl (by have := a.isLt; omega) hwT_lt
      let B2 := pA.1; let wA := pA.2
      have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
      have hsz2 : B2.size = B1.size + 1 := Bld.pushGate_size _ _ _ _ _ _
      have hnt2 : B2.nots = B1.nots := Bld.mkAnd_nots _ _ _ _ _
      have hwA_lt : wA < (n + 2) + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
      refine ⟨B2, wA, h01.trans h12, by simp [List.length_cons]; omega, by omega, hwA_lt, fun x => ?_⟩
      rw [Bld.mkAnd_eval _ _ _ _ _ (mkInput x) (mkInput_length x), hwT_ev x,
          wires_getD_input _ _ a.val (by rw [mkInput_length]; have := a.isLt; omega),
          mkInput_getD_lt x a]
      rfl
  rcases buildList B0 S.toList with ⟨B1, wOut, h01, hsz1, hnt1, hw_lt, hw_ev⟩
  refine ⟨B1, wOut, h01, by rw [Finset.length_toList] at hsz1; exact hsz1, hnt1, hw_lt, fun x => ?_⟩
  rw [hw_ev x]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Finset.mem_toList, decide_eq_true_eq]
  exact Finset.subset_iff.symm

private lemma build_monomials_list {n h : Nat} (B0 : Bld (n + 2))
    (specs : List (Fin h × Finset (Fin n))) :
    ∃ (B1 : Bld (n + 2)) (items : List (Fin h × Nat)),
      B0.Ext B1 ∧
      B1.size ≤ B0.size + n * specs.length ∧
      B1.nots = B0.nots ∧
      items.length = specs.length ∧
      (∀ p ∈ items, p.2 < (n + 2) + B1.size) ∧
      (∀ x : Finset (Fin n), ∀ u : Fin h,
        items.any (fun p => decide (u.val ≤ p.1.val) && (B1.toCircuit.wires (mkInput x)).getD p.2 false) =
        specs.any (fun q => decide (u.val ≤ q.1.val) && decide (q.2 ⊆ x))) := by
  induction specs generalizing B0 with
  | nil =>
    exact ⟨B0, [], Bld.Ext.refl B0, by simp, rfl, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons hd tl ih =>
    rcases build_monomial B0 hd.2 with ⟨B1, wHd, h01, hsz1, hnt1, hwH_lt, hwH_ev⟩
    rcases ih B1 with ⟨B2, itemsTl, h12, hsz2, hnt2, hlen2, hlt2, hev2⟩
    have hcard_le : hd.2.card ≤ n := by
      calc hd.2.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := Finset.card_fin n
    refine ⟨B2, (hd.1, wHd) :: itemsTl, h01.trans h12, ?_, by omega, by simp [hlen2], ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · have := h12.size_le; omega
      · exact hlt2 p hmem
    · intro x u
      simp only [List.any_cons]
      rw [h12.wires_eq (mkInput x) (mkInput_length x) wHd hwH_lt, hwH_ev x, hev2 x u]

private lemma build_cum_or {M h : Nat} (B0 : Bld M) (wFalse : Nat) (hwF : wFalse < M)
    (items : List (Fin h × Nat)) (hit : ∀ p ∈ items, p.2 < M + B0.size) :
    ∃ (B1 : Bld M) (T : Fin h → Nat),
      B0.Ext B1 ∧
      B1.size ≤ B0.size + items.length + h ∧
      B1.nots = B0.nots ∧
      (∀ u, T u < M + B1.size) ∧
      (∀ inp, inp.length = M → inp.getD wFalse false = false → ∀ u : Fin h,
        (B1.toCircuit.wires inp).getD (T u) false =
          items.any (fun p => decide (u.val ≤ p.1.val) && (B0.toCircuit.wires inp).getD p.2 false)) := by
  -- Step 1: bucket OR per level u : Fin h (items.length gates!)
  have buildBuckets : ∀ (l : List (Fin h × Nat)), (∀ p ∈ l, p.2 < M + B0.size) →
      ∃ (B1 : Bld M) (bkt : Fin h → Nat),
        B0.Ext B1 ∧ B1.size ≤ B0.size + l.length ∧ B1.nots = B0.nots ∧
        (∀ u, bkt u < M + B1.size) ∧
        (∀ inp, inp.length = M → inp.getD wFalse false = false → ∀ u : Fin h,
          (B1.toCircuit.wires inp).getD (bkt u) false =
            l.any (fun p => decide (p.1 = u) && (B0.toCircuit.wires inp).getD p.2 false)) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨B0, fun _ => wFalse, Bld.Ext.refl B0, by simp, rfl, fun _ => by dsimp only; omega, ?_⟩
      intro inp hln hwF_ev _
      rw [wires_getD_input _ _ wFalse (by omega), hwF_ev]; rfl
    | cons hd tl ih =>
      intro hl
      rcases ih (fun p hp => hl p (List.mem_cons_of_mem hd hp)) with
        ⟨B1, bkt1, h01, hsz1, hnt1, hb1_lt, hb1_ev⟩
      have hhd : hd.2 < M + B0.size := hl hd (by simp)
      let pO := B1.mkOr (bkt1 hd.1) hd.2 (hb1_lt hd.1) (by have := h01.size_le; omega)
      let B2 := pO.1; let wO := pO.2
      have h12 : B1.Ext B2 := Bld.pushGate_ext _ _ _ _ _ _
      have hsz2 : B2.size = B1.size + 1 := Bld.pushGate_size _ _ _ _ _ _
      have hnt2 : B2.nots = B1.nots := Bld.mkOr_nots _ _ _ _ _
      have hwO_lt : wO < M + B2.size := Bld.pushGate_wire_lt _ _ _ _ _ _
      refine ⟨B2, fun u => if u = hd.1 then wO else bkt1 u,
        h01.trans h12, by simp [List.length_cons]; omega, by omega, ?_, ?_⟩
      · intro u; dsimp only; split_ifs with hu
        · exact hwO_lt
        · have := hb1_lt u; omega
      · intro inp hln hwF_ev u; dsimp only; split_ifs with hu
        · subst hu
          rw [Bld.mkOr_eval _ _ _ _ _ inp hln, hb1_ev inp hln hwF_ev hd.1,
              h01.wires_eq inp hln hd.2 hhd]
          simp [Bool.or_comm]
        · rw [h12.wires_eq inp hln _ (hb1_lt u), hb1_ev inp hln hwF_ev u]
          have hne : hd.1 ≠ u := fun h => hu h.symm
          simp [hne]
  rcases buildBuckets items hit with ⟨B1, bkt, h01, hsz1, hnt1, hb_lt, hb_ev⟩
  -- Step 2: suffix OR from top down: T[h - 1 - k] = bkt[h - 1 - k] || T[h - k] (at most h gates!)
  have buildSuffix : ∀ (k : Nat), k ≤ h →
      ∃ (B2 : Bld M) (T : Fin k → Nat),
        B1.Ext B2 ∧ B2.size ≤ B1.size + k ∧ B2.nots = B1.nots ∧
        (∀ i : Fin k, T i < M + B2.size) ∧
        (∀ inp, inp.length = M → ∀ i : Fin k,
          (B2.toCircuit.wires inp).getD (T i) false =
            decide (∃ v : Fin h, h - 1 - i.val ≤ v.val ∧ (B1.toCircuit.wires inp).getD (bkt v) false = true)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨B1, Fin.elim0, Bld.Ext.refl B1, by simp, rfl, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩
    | succ k ihk =>
      intro hkh
      rcases ihk (by omega) with ⟨B2, T2, h12, hsz2, hnt2, hT2_lt, hT2_ev⟩
      let cur : Fin h := ⟨h - 1 - k, by omega⟩
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨B2, fun _ => bkt cur, h12, by omega, hnt2,
          fun _ => by dsimp only; have := hb_lt cur; have := h12.size_le; omega, ?_⟩
        intro inp hln i
        rw [h12.wires_eq inp hln _ (hb_lt cur)]
        have hi0 : i.val = 0 := by omega
        rw [hi0]
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq]
        constructor
        · intro ht; exact ⟨cur, by simp [cur], ht⟩
        · rintro ⟨v, hv, hvt⟩
          have hveq : v = cur := Fin.ext (by dsimp only [cur]; have := v.isLt; omega)
          rwa [← hveq]
      · let prev : Fin k := ⟨k - 1, by omega⟩
        let pO := B2.mkOr (bkt cur) (T2 prev) (by have := hb_lt cur; have := h12.size_le; omega) (hT2_lt prev)
        let B3 := pO.1; let wO := pO.2
        have h23 : B2.Ext B3 := Bld.pushGate_ext _ _ _ _ _ _
        have hsz3 : B3.size = B2.size + 1 := Bld.pushGate_size _ _ _ _ _ _
        have hnt3 : B3.nots = B2.nots := Bld.mkOr_nots _ _ _ _ _
        have hwO_lt : wO < M + B3.size := Bld.pushGate_wire_lt _ _ _ _ _ _
        refine ⟨B3, fun i => if hi : i.val < k then T2 ⟨i.val, hi⟩ else wO,
          h12.trans h23, by omega, by omega, ?_, ?_⟩
        · intro i; dsimp only; split_ifs with hi
          · have := hT2_lt ⟨i.val, hi⟩; omega
          · exact hwO_lt
        · intro inp hln i; dsimp only; split_ifs with hi
          · rw [h23.wires_eq inp hln _ (hT2_lt ⟨i.val, hi⟩)]
            exact hT2_ev inp hln ⟨i.val, hi⟩
          · have hik : i.val = k := by omega
            rw [hik, Bld.mkOr_eval _ _ _ _ _ inp hln,
                h12.wires_eq inp hln _ (hb_lt cur), hT2_ev inp hln prev]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq, prev]
            constructor
            · rintro (ht | ⟨v, hv, hvt⟩)
              · exact ⟨cur, by simp [cur], ht⟩
              · exact ⟨v, by omega, hvt⟩
            · rintro ⟨v, hv, hvt⟩
              by_cases hveq : v.val = h - 1 - k
              · left; have : v = cur := Fin.ext hveq; rwa [← this]
              · right; exact ⟨v, by omega, hvt⟩
  rcases buildSuffix h (le_refl h) with ⟨B2, Tsuf, h12, hsz2, hnt2, hTs_lt, hTs_ev⟩
  let T : Fin h → Nat := fun u => Tsuf ⟨h - 1 - u.val, by omega⟩
  refine ⟨B2, T, h01.trans h12, by omega, by omega, fun u => hTs_lt _, ?_⟩
  intro inp hln hwF_ev u
  simp only [T]
  rw [hTs_ev inp hln ⟨h - 1 - u.val, by omega⟩]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have hsub : h - 1 - (h - 1 - u.val) = u.val := by have := u.isLt; omega
  rw [hsub]
  constructor
  · rintro ⟨v, hv, hvt⟩
    rw [hb_ev inp hln hwF_ev v, List.any_eq_true] at hvt
    rcases hvt with ⟨p, hp, hpt⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at hpt
    exact ⟨p, hp, by rw [hpt.1]; exact hv, hpt.2⟩
  · rintro ⟨p, hp, hup, hpt⟩
    refine ⟨p.1, hup, ?_⟩
    rw [hb_ev inp hln hwF_ev p.1, List.any_eq_true]
    exact ⟨p, hp, by rw [hpt]; simp⟩

private lemma circuit_from_rank {n b : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (r : Finset (Fin n) → Nat)
    (hr_le : ∀ x, r x ≤ 2 ^ b - 1)
    (hr_mono : ∀ x y : Finset (Fin n), x ⊆ y → r x ≤ r y) :
    let supp := (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card)
    ∃ (C : Circuit) (a : Fin n → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
      (∀ (x : Finset (Fin n)) (j : Fin n), j ∈ x → (C.wires (mkInput x)).getD (a j).val false = false) ∧
      C.size ≤ 64 * (n + 1) ^ 2 * (supp + 1) ∧
      ∀ (x : Finset (Fin n)) (j : Fin n), j ∉ x → 0 < w x j → r x < r (insert j x) →
        (C.wires (mkInput x)).getD (a j).val false = true := by
  intro supp
  let M := n + 2
  let wFalse := n
  let suppSet : Finset (Finset (Fin n) × Fin n) :=
    Finset.univ.filter (fun p => p.2 ∉ p.1 ∧ 0 < w p.1 p.2)
  have hsupp_eq : supp = suppSet.card := by
    dsimp only [supp]
    have hcard_x : ∀ x : Finset (Fin n),
        ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card =
        (suppSet.filter (fun p => p.1 = x)).card := by
      intro x
      apply Finset.card_bij (fun j _ => (x, j))
      · intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩, rfl⟩
      · intro j1 _ j2 _ heq; exact congrArg Prod.snd heq
      · intro ⟨x', j⟩ hm
        have hx' : x' = x := (Finset.mem_filter.mp hm).2
        subst hx'
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2⟩, rfl⟩
    simp_rw [hcard_x]
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨x, j⟩; simp
    · intro x1 _ x2 _ hne
      exact Finset.disjoint_left.mpr (fun p h1 h2 =>
        hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
  let A : Finset (Finset (Fin n) × Fin n) := suppSet.filter (fun p => r p.1 < r (insert p.2 p.1))
  have hA_le : A.card ≤ supp := by rw [hsupp_eq]; exact Finset.card_filter_le _ _
  let Vvals : Finset Nat := A.image (fun p => r (insert p.2 p.1))
  let h := Vvals.card
  have hh_le_A : h ≤ A.card := Finset.card_image_le
  have hh_le_d : h ≤ 2 ^ b - 1 := by
    have hsub : Vvals ⊆ Finset.Icc 1 (2 ^ b - 1) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
      have hlt : r p.1 < r (insert p.2 p.1) := (Finset.mem_filter.mp hp).2
      have hle := hr_le (insert p.2 p.1)
      exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
    calc h ≤ (Finset.Icc 1 (2 ^ b - 1)).card := Finset.card_le_card hsub
      _ = 2 ^ b - 1 := by rw [Nat.card_Icc]; omega
  let vEmb : Fin h ↪o Nat := Vvals.orderEmbOfFin rfl
  have hvEmb_mem : ∀ u : Fin h, vEmb u ∈ Vvals := fun u => Vvals.orderEmbOfFin_mem rfl u
  have hvEmb_ex : ∀ v ∈ Vvals, ∃ u : Fin h, vEmb u = v := by
    intro v hv
    have hrange := Vvals.range_orderEmbOfFin rfl
    have : v ∈ Set.range vEmb := by rw [hrange]; exact hv
    exact this
  let idxOf : (p : Finset (Fin n) × Fin n) → p ∈ A → Fin h := fun p hp =>
    Classical.choose (hvEmb_ex (r (insert p.2 p.1)) (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have hidxOf_spec : ∀ p hp, vEmb (idxOf p hp) = r (insert p.2 p.1) :=
    fun p hp => Classical.choose_spec (hvEmb_ex (r (insert p.2 p.1)) (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  -- List of active specs (u_e, insert j' y) of length A.card <= supp!
  let baseSpecs : List (Fin h × Finset (Fin n)) :=
    A.attach.toList.map (fun p => (idxOf p.val p.property, insert p.val.2 p.val.1))
  have hbase_len : baseSpecs.length = A.card := by
    simp [baseSpecs]
  -- Compressed rank rc x = #{u : Fin h | ∃ p ∈ A, vEmb u ≤ r (insert p.2 p.1) ∧ insert p.2 p.1 ⊆ x}!
  let rcPred (x : Finset (Fin n)) (u : Fin h) : Prop :=
    ∃ p ∈ A, vEmb u ≤ r (insert p.2 p.1) ∧ insert p.2 p.1 ⊆ x
  let rc (x : Finset (Fin n)) : Nat := ((Finset.univ : Finset (Fin h)).filter (rcPred x)).card
  have hrc_le : ∀ x, rc x ≤ h := fun x => by
    calc rc x ≤ (Finset.univ : Finset (Fin h)).card := Finset.card_filter_le _ _
      _ = h := Finset.card_fin h
  have hrc_iff : ∀ x (u : Fin h), rcPred x u ↔ u.val + 1 ≤ rc x := by
    intro x u
    have hdown : ∀ u1 u2 : Fin h, u1 ≤ u2 → rcPred x u2 → rcPred x u1 := by
      intro u1 u2 hle ⟨p, hp, hvu, hsub⟩
      exact ⟨p, hp, le_trans (vEmb.monotone hle) hvu, hsub⟩
    constructor
    · intro hu
      have hsub : (Finset.univ.filter (fun i : Fin h => i.val ≤ u.val)) ⊆ Finset.univ.filter (rcPred x) := by
        intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdown i u (Finset.mem_filter.mp hi).2 hu⟩
      have hcard : (Finset.univ.filter (fun i : Fin h => i.val ≤ u.val)).card = u.val + 1 := by
        have hbij : (Finset.univ.filter (fun i : Fin h => i.val ≤ u.val)).card = (Finset.range (u.val + 1)).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega)
          · intro i1 _ i2 _ heq; exact Fin.ext heq
          · intro m hm; have := Finset.mem_range.mp hm; exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, rfl⟩
        rw [hbij, Finset.card_range]
      rw [← hcard]; exact Finset.card_le_card hsub
    · intro hle
      by_contra hnot
      have hsub : Finset.univ.filter (rcPred x) ⊆ Finset.univ.filter (fun i : Fin h => i.val < u.val) := by
        intro i hi
        have hip := (Finset.mem_filter.mp hi).2
        have hilt : i.val < u.val := by
          by_contra hge
          exact hnot (hdown u i (by show u.val ≤ i.val; omega) hip)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hilt⟩
      have hcard : (Finset.univ.filter (fun i : Fin h => i.val < u.val)).card = u.val := by
        have hbij : (Finset.univ.filter (fun i : Fin h => i.val < u.val)).card = (Finset.range u.val).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro i1 _ i2 _ heq; exact Fin.ext heq
          · intro m hm; have := Finset.mem_range.mp hm; exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩, rfl⟩
        rw [hbij, Finset.card_range]
      have := Finset.card_le_card hsub
      dsimp only [rc] at hle
      omega
  -- Step 1: Build base monomials + T u = decide (u.val + 1 <= rc x) + Fischer inverter notT!
  let B0 := Bld.empty M
  rcases build_monomials_list B0 baseSpecs with ⟨B1, items0, h01, hsz1, hnt1, hlen1, hit1, hev1⟩
  rcases build_cum_or B1 wFalse (by omega) items0 hit1 with ⟨B2, T, h12, hsz2, hnt2, hT_lt, hT_ev⟩
  rcases build_fischer_flex wFalse (by omega) b h hh_le_d B2 T hT_lt with
    ⟨B3, notT, h23, hsz3, hnt3, hnotT_lt, hnotT_ev⟩
  have hT_rc : ∀ x (u : Fin h), (B2.toCircuit.wires (mkInput x)).getD (T u) false = decide (u.val + 1 ≤ rc x) := by
    intro x u
    rw [hT_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x) u, hev1 x u]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, baseSpecs, List.mem_map,
      Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists]
    rw [← hrc_iff x u]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hle, hsub⟩
      have hvm : vEmb u ≤ vEmb (idxOf p hp) := vEmb.monotone hle
      rw [hidxOf_spec p hp] at hvm
      exact ⟨p, hp, hvm, hsub⟩
    · rintro ⟨p, hp, hvu, hsub⟩
      refine ⟨(idxOf p hp, insert p.2 p.1), ⟨p, hp, rfl⟩, ?_, hsub⟩
      rw [← hidxOf_spec p hp] at hvu
      exact vEmb.le_iff_le.mp hvu
  have hnotT_rc : ∀ x (u : Fin h),
      (B3.toCircuit.wires (mkInput x)).getD (notT u) false = !(decide (u.val + 1 ≤ rc x)) :=
    fun x u => hnotT_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x) (rc x) (hrc_le x) (hT_rc x) u
  -- Step 2: Build one output wire out_j = decide (rc x < rc (insert j x)) for each j : Fin n!
  have buildOneOut : ∀ (B : Bld M) (j : Fin n), B3.Ext B →
      ∃ (B' : Bld M) (wOut : Nat),
        B.Ext B' ∧
        B'.size ≤ B.size + n * A.card + A.card + 3 * h ∧
        B'.nots = B.nots ∧
        wOut < M + B'.size ∧
        (∀ x : Finset (Fin n),
          (B'.toCircuit.wires (mkInput x)).getD wOut false = decide (rc x < rc (insert j x))) := by
    intro B j h3B
    let specsJ : List (Fin h × Finset (Fin n)) :=
      A.attach.toList.map (fun p => (idxOf p.val p.property, (insert p.val.2 p.val.1).erase j))
    have hspJ_len : specsJ.length = A.card := by simp [specsJ]
    rcases build_monomials_list B specsJ with ⟨Ba, itemsJ, hBa, hsza, hnta, hlena, hita, heva⟩
    rcases build_cum_or Ba wFalse (by omega) itemsJ hita with ⟨Bb, TJ, hBb, hszb, hntb, hTJ_lt, hTJ_ev⟩
    let pairsJ : List (Nat × Nat) := (List.finRange h).map (fun u => (notT u, TJ u))
    have hpJ_lt : ∀ p ∈ pairsJ, p.1 < M + Bb.size ∧ p.2 < M + Bb.size := by
      intro p hp
      rcases List.mem_map.mp hp with ⟨u, _, rfl⟩
      have hsz3b : B3.size ≤ Bb.size := ((h3B.trans hBa).trans hBb).size_le
      exact ⟨by have := hnotT_lt u; omega, hTJ_lt u⟩
    rcases build_or_and_list Bb wFalse (by omega) pairsJ hpJ_lt with
      ⟨Bc, wOut, hBc, hszc, hntc, hwO_lt, hwO_ev⟩
    have hTJ_rc : ∀ x (u : Fin h),
        (Bb.toCircuit.wires (mkInput x)).getD (TJ u) false = decide (u.val + 1 ≤ rc (insert j x)) := by
      intro x u
      rw [hTJ_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x) u, heva x u]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, specsJ, List.mem_map,
        Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists]
      rw [← hrc_iff (insert j x) u]
      have her_iff : ∀ S : Finset (Fin n), S.erase j ⊆ x ↔ S ⊆ insert j x := by
        intro S; constructor
        · intro h a ha
          by_cases haj : a = j
          · rw [haj]; exact Finset.mem_insert_self j x
          · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.mpr ⟨haj, ha⟩))
        · intro h a ha
          have ha' := Finset.mem_erase.mp ha
          rcases Finset.mem_insert.mp (h ha'.2) with rfl | hax
          · exact (ha'.1 rfl).elim
          · exact hax
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, hle, hsub⟩
        have hvm : vEmb u ≤ vEmb (idxOf p hp) := vEmb.monotone hle
        rw [hidxOf_spec p hp] at hvm
        exact ⟨p, hp, hvm, (her_iff _).mp hsub⟩
      · rintro ⟨p, hp, hvu, hsub⟩
        refine ⟨(idxOf p hp, (insert p.2 p.1).erase j), ⟨p, hp, rfl⟩, ?_, (her_iff _).mpr hsub⟩
        rw [← hidxOf_spec p hp] at hvu
        exact vEmb.le_iff_le.mp hvu
    refine ⟨Bc, wOut, (hBa.trans hBb).trans hBc, ?_, by omega, hwO_lt, fun x => ?_⟩
    · have hpJ_len : pairsJ.length = h := by simp [pairsJ]
      rw [hspJ_len] at hsza hlena
      rw [hlena] at hszb
      rw [hpJ_len] at hszc
      omega
    · rw [hwO_ev (mkInput x) (mkInput_length x) (mkInput_getD_false x)]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Bool.and_eq_true, pairsJ, List.mem_map, List.mem_finRange, true_and,
        decide_eq_true_eq]
      constructor
      · rintro ⟨_, ⟨u, rfl⟩, hnt, htj⟩
        rw [((h3B.trans hBa).trans hBb).wires_eq (mkInput x) (mkInput_length x) (notT u) (hnotT_lt u),
            hnotT_rc x u] at hnt
        rw [hTJ_rc x u] at htj
        have h1 : ¬ u.val + 1 ≤ rc x := by simpa using hnt
        have h2 : u.val + 1 ≤ rc (insert j x) := by simpa using htj
        omega
      · intro hlt
        have hrc_ins_le := hrc_le (insert j x)
        let u : Fin h := ⟨rc x, by omega⟩
        refine ⟨(notT u, TJ u), ⟨u, rfl⟩, ?_, ?_⟩
        · rw [((h3B.trans hBa).trans hBb).wires_eq (mkInput x) (mkInput_length x) (notT u) (hnotT_lt u),
              hnotT_rc x u]
          simp [u]
        · rw [hTJ_rc x u]; simp only [u, decide_eq_true_eq]; omega
  -- Build all n outputs by induction on m <= n!
  have buildAllOuts : ∀ (m : Nat) (hm : m ≤ n),
      ∃ (B' : Bld M) (outs : Fin m → Nat),
        B3.Ext B' ∧
        B'.size ≤ B3.size + m * (n * A.card + A.card + 3 * h) ∧
        B'.nots = B3.nots ∧
        (∀ j, outs j < M + B'.size) ∧
        (∀ x (j : Fin m),
          (B'.toCircuit.wires (mkInput x)).getD (outs j) false =
            decide (rc x < rc (insert ⟨j.val, by omega⟩ x))) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨B3, Fin.elim0, Bld.Ext.refl B3, by simp, rfl, fun j => Fin.elim0 j, fun _ j => Fin.elim0 j⟩
    | succ m ihm =>
      intro hmn
      rcases ihm (by omega) with ⟨B4, outs4, h34, hsz4, hnt4, ho4_lt, ho4_ev⟩
      rcases buildOneOut B4 ⟨m, by omega⟩ h34 with ⟨B5, wLast, h45, hsz5, hnt5, hwL_lt, hwL_ev⟩
      refine ⟨B5, fun j => if hj : j.val < m then outs4 ⟨j.val, hj⟩ else wLast,
        h34.trans h45, ?_, by omega, ?_, ?_⟩
      · have hmul : (m + 1) * (n * A.card + A.card + 3 * h) =
            m * (n * A.card + A.card + 3 * h) + (n * A.card + A.card + 3 * h) := by ring
        omega
      · intro j; dsimp only; split_ifs with hj
        · have := ho4_lt ⟨j.val, hj⟩; have := h45.size_le; omega
        · exact hwL_lt
      · intro x j; dsimp only; split_ifs with hj
        · rw [h45.wires_eq (mkInput x) (mkInput_length x) _ (ho4_lt ⟨j.val, hj⟩)]
          exact ho4_ev x ⟨j.val, hj⟩
        · have hjm : j.val = m := by omega
          have hjeq : (⟨j.val, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext hjm
          rw [hjeq, hwL_ev x]
  rcases buildAllOuts n (le_refl n) with ⟨Bfin, outs, h3f, hszf, hntf, hof_lt, hof_ev⟩
  let C := Bfin.toCircuit
  let a : Fin n → Fin (n + 2 + C.size) := fun j => ⟨outs j, hof_lt j⟩
  refine ⟨C, a, Bfin.hF2, Bfin.hRB, by simp [C, Bld.toCircuit], ?_, ?_, ?_, ?_⟩
  · -- notCount C <= b
    change Bfin.nots ≤ b
    have hb0 : B0.nots = 0 := by simp [B0, Bld.empty, Bld.nots, Bld.toCircuit, notCount]
    omega
  · -- oneSide C a
    intro x j hjx
    change (Bfin.toCircuit.wires (mkInput x)).getD (outs j) false = false
    rw [hof_ev x j]
    have hins : insert (⟨j.val, by omega⟩ : Fin n) x = x := Finset.insert_eq_of_mem hjx
    rw [hins]; simp
  · -- C.size <= 64 * (n + 1)^2 * (supp + 1)
    change Bfin.size ≤ 64 * (n + 1) ^ 2 * (supp + 1)
    have hb0 : B0.size = 0 := rfl
    rw [hbase_len] at hsz1 hlen1
    rw [hlen1] at hsz2
    have hA_le_s : A.card ≤ supp := hA_le
    have hh_le_s : h ≤ supp := le_trans hh_le_A hA_le_s
    have hstep1 : B3.size ≤ (n + 7) * supp := by
      have h1 : B3.size ≤ n * A.card + A.card + 6 * h := by omega
      have h2 : n * A.card ≤ n * supp := Nat.mul_le_mul_left n hA_le_s
      have h3 : n * supp + supp + 6 * supp = (n + 7) * supp := by ring
      omega
    have hstep2 : n * (n * A.card + A.card + 3 * h) ≤ n * ((n + 4) * supp) := by
      apply Nat.mul_le_mul_left n
      have h1 : n * A.card ≤ n * supp := Nat.mul_le_mul_left n hA_le_s
      have h2 : n * supp + supp + 3 * supp = (n + 4) * supp := by ring
      omega
    have hpoly : (n + 7) * supp + n * ((n + 4) * supp) ≤ 64 * (n + 1) ^ 2 * (supp + 1) := by
      have h1 : (n + 7) * supp + n * ((n + 4) * supp) = (n ^ 2 + 5 * n + 7) * supp := by ring
      have h2 : n ^ 2 + 5 * n + 7 ≤ 64 * (n + 1) ^ 2 := by nlinarith
      rw [h1]
      calc (n ^ 2 + 5 * n + 7) * supp ≤ 64 * (n + 1) ^ 2 * supp := Nat.mul_le_mul_right supp h2
        _ ≤ 64 * (n + 1) ^ 2 * (supp + 1) := Nat.mul_le_mul_left _ (Nat.le_succ supp)
    omega
  · -- Active edges evaluate to true!
    intro x j hjx hwpos hrlt
    change (Bfin.toCircuit.wires (mkInput x)).getD (outs j) false = true
    rw [hof_ev x j]
    have hjeq : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
    rw [hjeq, decide_eq_true_eq]
    have hpA : (x, j) ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjx, hwpos⟩, hrlt⟩
    let u := idxOf (x, j) hpA
    have hu_val : vEmb u = r (insert j x) := hidxOf_spec (x, j) hpA
    have h1 : u.val + 1 ≤ rc (insert j x) := by
      rw [← hrc_iff (insert j x) u]
      exact ⟨(x, j), hpA, by rw [hu_val], subset_refl _⟩
    have h2 : ¬ u.val + 1 ≤ rc x := by
      rw [← hrc_iff x u]
      rintro ⟨p, _, hvu, hsub⟩
      have hmono := hr_mono _ _ hsub
      rw [hu_val] at hvu
      omega
    omega

-- ============================================================================
-- Main proof matching the exact theorem statement
-- ============================================================================

private lemma main_51425_core (n b : Nat) (w : Finset (Fin n) → Fin n → Nat) :
    let supp := (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card)
    let W := (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (absentOf x).sum (w x))
    ∃ (C : Circuit) (a : Fin n → Fin (n + 2 + C.size)) (L : List (Equiv.Perm (Fin n))),
      (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b) ∧
      (∀ (x : Finset (Fin n)) (j : Fin n), j ∈ x → (C.wires (mkInput x)).getD (a j).val false = false) ∧
      C.size ≤ 64 * (n + 1) ^ 2 * (supp + 1) ∧
      L.length ≤ W ∧
      payOf w L =
        (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
          (absentOf x).sum (fun j => if (C.wires (mkInput x)).getD (a j).val false = false then w x j else 0)) +
        (2 ^ b - 1) * L.length := by
  intro supp W
  by_cases hn0 : n = 0
  · subst hn0
    let B0 := Bld.empty 2
    refine ⟨B0.toCircuit, Fin.elim0, [], ⟨B0.hF2, B0.hRB, by simp [B0, Bld.toCircuit], by simp [B0, Bld.empty, Bld.toCircuit, notCount]⟩,
      fun _ j => Fin.elim0 j, by simp [B0, Bld.empty, Bld.toCircuit, Circuit.size], by simp, ?_⟩
    simp [payOf, absentOf]
  have hn1 : 1 ≤ n := by omega
  by_cases hb0 : b = 0
  · subst hb0
    let B0 := Bld.empty (n + 2)
    let C := B0.toCircuit
    let a : Fin n → Fin (n + 2 + C.size) := fun _ => ⟨n, by simp [C, B0, Bld.toCircuit, Bld.empty, Circuit.size]⟩
    -- Build L by replicating a visiting perm w x j times for every (x, j) with j ∉ x!
    let pairs : List (Finset (Fin n) × Fin n) :=
      (Finset.univ : Finset (Finset (Fin n))).toList.flatMap (fun x =>
        (absentOf x).toList.map (fun j => (x, j)))
    let permFor : Finset (Fin n) × Fin n → Equiv.Perm (Fin n) := fun p =>
      if h : p.2 ∉ p.1 then Classical.choose (exists_perm_visiting p.1 p.2 h) else 1
    let L : List (Equiv.Perm (Fin n)) := pairs.flatMap (fun p => List.replicate (w p.1 p.2) (permFor p))
    have hL_len : L.length = W := by
      dsimp only [L, pairs, W]
      have hsum_flatMap : ∀ {α β : Type} (l : List α) (g : α → List β) (h : β → Nat),
          ((l.flatMap g).map h).sum = (l.map (fun x => ((g x).map h).sum)).sum := by
        intro α β l g h
        induction l with
        | nil => simp
        | cons hd tl ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]
      rw [List.length_flatMap, hsum_flatMap]
      have hmap_toList : ∀ {α : Type} (s : Finset α) (f : α → Nat), (s.toList.map f).sum = s.sum f := by
        intro α s f
        change ((s.toList.map f : List Nat) : Multiset Nat).sum = (s.val.map f).sum
        rw [← Multiset.map_coe, Finset.coe_toList]
      have h1 : ∀ x : Finset (Fin n),
          (((absentOf x).toList.map (fun j => (x, j))).map (fun p => (List.replicate (w p.1 p.2) (permFor p)).length)).sum =
          (absentOf x).sum (w x) := by
        intro x
        rw [List.map_map]
        have heq : (absentOf x).toList.map ((fun p : Finset (Fin n) × Fin n => (List.replicate (w p.1 p.2) (permFor p)).length) ∘ fun j => (x, j)) =
            (absentOf x).toList.map (w x) := by
          apply List.map_congr_left; intro j _; simp
        rw [heq, hmap_toList]
      have h2 : (((Finset.univ : Finset (Finset (Fin n))).toList).map (fun x =>
          (((absentOf x).toList.map (fun j => (x, j))).map (fun p => (List.replicate (w p.1 p.2) (permFor p)).length)).sum)).sum =
          ((Finset.univ : Finset (Finset (Fin n))).toList.map (fun x => (absentOf x).sum (w x))).sum := by
        congr 1; apply List.map_congr_left; intro x _; exact h1 x
      rw [h2, hmap_toList]
    have hL_vis_ge : ∀ x j, j ∉ x → w x j ≤ visitsOf L x j := by
      intro x j hjx
      have hmem_p : (x, j) ∈ pairs := by
        dsimp only [pairs]
        rw [List.mem_flatMap]
        refine ⟨x, Finset.mem_toList.mpr (Finset.mem_univ _), List.mem_map.mpr ⟨j, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjx⟩), rfl⟩⟩
      have hspec : preOf (permFor (x, j)) ((permFor (x, j)).symm j) = x := by
        dsimp only [permFor]; rw [dif_pos hjx]; exact Classical.choose_spec (exists_perm_visiting x j hjx)
      unfold visitsOf
      have hgen : ∀ (ps : List (Finset (Fin n) × Fin n)), (x, j) ∈ ps →
          w x j ≤ ((ps.flatMap (fun p => List.replicate (w p.1 p.2) (permFor p))).filter
            (fun π => decide (preOf π (π.symm j) = x))).length := by
        intro ps hps
        induction ps with
        | nil => cases hps
        | cons hd tl ih =>
          rw [List.flatMap_cons, List.filter_append, List.length_append]
          rcases List.mem_cons.mp hps with rfl | htl
          · have hrep : ((List.replicate (w x j) (permFor (x, j))).filter
                (fun π => decide (preOf π (π.symm j) = x))).length = w x j := by
              have hall : ∀ π ∈ List.replicate (w x j) (permFor (x, j)),
                  decide (preOf π (π.symm j) = x) = true := by
                intro π hπ
                rw [List.mem_replicate.mp hπ |>.2]
                exact decide_eq_true hspec
              rw [List.filter_eq_self.mpr hall, List.length_replicate]
            dsimp only; rw [hrep]; omega
          · have := ih htl; omega
      exact hgen pairs hmem_p
    have hw_all_false : ∀ (x : Finset (Fin n)) (j : Fin n),
        (C.wires (mkInput x)).getD (a j).val false = false := by
      intro x j
      dsimp only [C, B0, a]
      rw [wires_getD_input _ _ n (by rw [mkInput_length]; omega), mkInput_getD_false]
    refine ⟨C, a, L,
      ⟨B0.hF2, B0.hRB, by simp [C, B0, Bld.toCircuit], by simp [C, B0, Bld.toCircuit, Bld.empty, notCount]⟩,
      fun x j _ => hw_all_false x j,
      by simp [C, B0, Bld.toCircuit, Bld.empty, Circuit.size], by omega, ?_⟩
    simp only [Nat.pow_zero, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    unfold payOf
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro j hj
    have hjx : j ∉ x := (Finset.mem_filter.mp hj).2
    rw [hw_all_false x j, if_pos rfl, min_eq_left (hL_vis_ge x j hjx)]
  -- Main case: n >= 1 and b >= 1, so d = 2^b - 1 >= 1!
  have hd_pos : 1 ≤ 2 ^ b - 1 := by
    have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rcases exists_optimal_flow_and_rank hn1 w (2 ^ b - 1) hd_pos with
    ⟨L, r, hL_le_W, hr_le, hr_mono, hpay_eq⟩
  rcases circuit_from_rank w r hr_le hr_mono with
    ⟨C, a, hF2, hRB, hout, hnb, hone, hsz, hactive⟩
  have hloss_le :
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if (C.wires (mkInput x)).getD (a j).val false = false then w x j else 0)) ≤
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if r x = r (insert j x) then w x j else 0)) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro j hj
    have hjx : j ∉ x := (Finset.mem_filter.mp hj).2
    by_cases hreq : r x = r (insert j x)
    · rw [if_pos hreq]; split_ifs <;> omega
    · rw [if_neg hreq]
      by_cases hw0 : w x j = 0
      · simp [hw0]
      · have hmono_e : r x ≤ r (insert j x) := hr_mono x (insert j x) (Finset.subset_insert j x)
        have hlt : r x < r (insert j x) := by omega
        have ht := hactive x j hjx (by omega) hlt
        rw [ht]; simp
  have hlb := lower_bound_pay w C a hF2 hRB hnb hone L
  refine ⟨C, a, L, ⟨hF2, hRB, hout, hnb⟩, hone, hsz, hL_le_W, by omega⟩

private theorem main_proof :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n b : Nat) (w : Finset (Fin n) → Fin n → Nat),
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin n → Fin (n+2+C.size)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin n) =>
    (C.wires (input x)).getD (a j).val false
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let oneSide := fun (C : Circ) (a : taps C) => ∀ (x : X) (j : Fin n), j ∈ x → val C a x j = false
  let pre := fun (π : Equiv.Perm (Fin n)) (k : Fin n) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).image (fun i => π i)
  let supp := (Finset.univ : Finset X).sum (fun x =>
    ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card)
  let absent := fun (x : X) => (Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x)
  let W := (Finset.univ : Finset X).sum (fun x => (absent x).sum (w x))
  let loss := fun (C : Circ) (a : taps C) => (Finset.univ : Finset X).sum (fun x =>
    (absent x).sum (fun j => if val C a x j = false then w x j else 0))
  let orders := List (Equiv.Perm (Fin n))
  let visits := fun (L : orders) (x : X) (j : Fin n) =>
    (L.filter (fun π => decide (pre π (π.symm j) = x))).length
  let pay := fun (L : orders) => (Finset.univ : Finset X).sum (fun x =>
    (absent x).sum (fun j => min (w x j) (visits L x j)))
  (∀ (C : Circ) (a : taps C), valid C → oneSide C a → ∀ L : orders,
    pay L ≤ loss C a + (2^b-1)*L.length) ∧
  ∃ (C : Circ) (a : taps C) (L : orders), valid C ∧ oneSide C a ∧
    C.size ≤ 64*(n+1)^2*(supp+1) ∧ L.length ≤ W ∧ pay L = loss C a + (2^b-1)*L.length := by
  intro n b w
  let absC : Finset (Fin n) → Finset (Fin n) := fun x =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    (Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x)
  let preC : Equiv.Perm (Fin n) → Fin n → Finset (Fin n) := fun π k =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).image (fun i => π i)
  let visC : List (Equiv.Perm (Fin n)) → Finset (Fin n) → Fin n → Nat := fun L x j =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    (L.filter (fun π => decide (preC π (π.symm j) = x))).length
  let payC : List (Equiv.Perm (Fin n)) → Nat := fun L =>
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      (absC x).sum (fun j => min (w x j) (visC L x j)))
  let lossC : (C : Circuit) → (Fin n → Fin (n + 2 + C.size)) → Nat := fun C a =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      (absC x).sum (fun j => if (C.wires (mkInput x)).getD (a j).val false = false then w x j else 0))
  let WC : Nat :=
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (absC x).sum (w x))
  let suppC : Nat :=
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card)
  have habs_eq : ∀ x, absC x = absentOf x := by
    intro x; ext j; simp [absC, absentOf]
  have hpre_eq : ∀ π k, preC π k = preOf π k := by
    intro π k; ext a
    dsimp only [preC, preOf]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  have hvis_eq : ∀ L x j, visC L x j = visitsOf L x j := by
    intro L x j
    dsimp only [visC, visitsOf]
    congr 1; apply List.filter_congr; intro π _
    rw [hpre_eq π (π.symm j)]
    exact decide_eq_decide.mpr Iff.rfl
  have hpay_eq : ∀ L, payC L = payOf w L := by
    intro L; dsimp only [payC]; unfold payOf
    apply Finset.sum_congr rfl; intro x _
    rw [habs_eq x]
    apply Finset.sum_congr rfl; intro j _
    rw [hvis_eq L x j]
  have hloss_eq : ∀ C a, lossC C a =
      (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
        (absentOf x).sum (fun j => if (C.wires (mkInput x)).getD (a j).val false = false then w x j else 0)) := by
    intro C a; dsimp only [lossC]
    apply Finset.sum_congr rfl; intro x _
    rw [habs_eq x]
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> rfl
  have hW_eq : WC = (Finset.univ : Finset (Finset (Fin n))).sum (fun x => (absentOf x).sum (w x)) := by
    dsimp only [WC]
    apply Finset.sum_congr rfl; intro x _; rw [habs_eq x]
  have hsupp_eq : suppC = (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
      ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card) := by
    dsimp only [suppC]
    apply Finset.sum_congr rfl; intro x _; congr 1; ext j; simp
  constructor
  · intro C a ⟨hF2, hRB, _hout, hnb⟩ hone L
    change payC L ≤ lossC C a + (2 ^ b - 1) * L.length
    rw [hpay_eq L, hloss_eq C a]
    exact lower_bound_pay w C a hF2 hRB hnb hone L
  · rcases main_51425_core n b w with ⟨C, a, L, hval, hone, hsz, hLlen, heq⟩
    refine ⟨C, a, L, hval, hone, ?_, ?_, ?_⟩
    · change C.size ≤ 64 * (n + 1) ^ 2 * (suppC + 1)
      rw [hsupp_eq]; exact hsz
    · change L.length ≤ WC
      rw [hW_eq]; exact hLlen
    · change payC L = lossC C a + (2 ^ b - 1) * L.length
      rw [hpay_eq L, hloss_eq C a]; exact heq

end PEqualNP.Outside.L_meta_51425

theorem PEqualNP.Outside.L_meta_51425 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n b : Nat) (w : Finset (Fin n) → Fin n → Nat),
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin n → Fin (n+2+C.size)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin n) =>
    (C.wires (input x)).getD (a j).val false
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let oneSide := fun (C : Circ) (a : taps C) => ∀ (x : X) (j : Fin n), j ∈ x → val C a x j = false
  let pre := fun (π : Equiv.Perm (Fin n)) (k : Fin n) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).image (fun i => π i)
  let supp := (Finset.univ : Finset X).sum (fun x =>
    ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < w x j)).card)
  let absent := fun (x : X) => (Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x)
  let W := (Finset.univ : Finset X).sum (fun x => (absent x).sum (w x))
  let loss := fun (C : Circ) (a : taps C) => (Finset.univ : Finset X).sum (fun x =>
    (absent x).sum (fun j => if val C a x j = false then w x j else 0))
  let orders := List (Equiv.Perm (Fin n))
  let visits := fun (L : orders) (x : X) (j : Fin n) =>
    (L.filter (fun π => decide (pre π (π.symm j) = x))).length
  let pay := fun (L : orders) => (Finset.univ : Finset X).sum (fun x =>
    (absent x).sum (fun j => min (w x j) (visits L x j)))
  (∀ (C : Circ) (a : taps C), valid C → oneSide C a → ∀ L : orders,
    pay L ≤ loss C a + (2^b-1)*L.length) ∧
  ∃ (C : Circ) (a : taps C) (L : orders), valid C ∧ oneSide C a ∧
    C.size ≤ 64*(n+1)^2*(supp+1) ∧ L.length ≤ W ∧ pay L = loss C a + (2^b-1)*L.length :=
  PEqualNP.Outside.L_meta_51425.main_proof
