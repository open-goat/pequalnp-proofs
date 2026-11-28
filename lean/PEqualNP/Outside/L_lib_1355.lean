import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1355

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

/-! ### Part 1: Basic List and Circuit Helpers -/

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  induction C.gates generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]; simp only [List.length_append, List.length_singleton]; omega

lemma wires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    (Circuit.mk (gs₁ ++ gs₂) 0).wires x =
      (Circuit.mk gs₂ 0).wires ((Circuit.mk gs₁ 0).wires x) := by
  unfold Circuit.wires; simp [List.foldl_append]

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  rw [wires_append]; simp [Circuit.wires]

lemma getD_append_left_lt {α : Type*} (l₁ l₂ : List α) (i : Nat) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right_ge {α : Type*} (l₁ l₂ : List α) (i : Nat) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma getD_append_right_eq {α : Type*} (l₁ : List α) (a : α) (d : α) :
    (l₁ ++ [a]).getD l₁.length d = a := by
  simp [List.getD]

lemma wires_getD_input (C : Circuit) (x : List Bool) (w : Nat) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false := by
  have h : ∀ (gs : List Gate) (v : List Bool), w < v.length →
      ((Circuit.mk gs 0).wires v).getD w false = v.getD w false := by
    intro gs
    induction gs with
    | nil => intro v _; rfl
    | cons g gs ih =>
      intro v hvw
      have h1 : (Circuit.mk (g :: gs) 0).wires v =
          (Circuit.mk gs 0).wires (v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)]) := rfl
      rw [h1, ih _ (by simp; omega), getD_append_left_lt _ _ _ _ hvw]
  exact h C.gates x hw

lemma wires_take_getD (gs : List Gate) (v : List Bool) (q w : Nat) (hw : w < v.length + q) :
    ((Circuit.mk gs 0).wires v).getD w false =
      ((Circuit.mk (gs.take q) 0).wires v).getD w false := by
  have hsplit : gs = gs.take q ++ gs.drop q := (List.take_append_drop q gs).symm
  conv_lhs => rw [hsplit]
  rw [wires_append]
  have hlen : ((Circuit.mk (gs.take q) 0).wires v).length = v.length + (gs.take q).length :=
    wires_length _ _
  by_cases hq : q ≤ gs.length
  · have ht : (gs.take q).length = q := List.length_take_of_le hq
    exact wires_getD_input ⟨gs.drop q, 0⟩ _ w (by omega)
  · have hdrop : gs.drop q = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]; rfl

lemma wires_gate_eval {K : Nat} (C : Circuit) (hBack : ReadsBack K C)
    (v : List Bool) (hv : v.length = K) (p : Nat) (hp : p < C.gates.length) :
    (C.wires v).getD (K + p) false =
      (gateAt C p).op.eval ((gateAt C p).inputs.map fun a => (C.wires v).getD a false) := by
  have hC : C.wires v = (Circuit.mk C.gates 0).wires v := rfl
  rw [hC, wires_take_getD C.gates v (p + 1) (K + p) (by omega)]
  have htake : C.gates.take (p + 1) = C.gates.take p ++ [gateAt C p] := by
    have hg : C.gates[p]'hp = gateAt C p := by dsimp only [gateAt]; simp [List.getD, hp]
    rw [List.take_succ_eq_append_getElem hp, hg]
  rw [htake, wires_snoc]
  have hlen : ((Circuit.mk (C.gates.take p) 0).wires v).length = K + p := by
    rw [wires_length, hv, List.length_take]; omega
  rw [← hlen, getD_append_right_eq]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  have halt : a < K + p := hBack p hp a ha
  exact (wires_take_getD C.gates v p a (by omega)).symm

lemma notCount_le_size (C : Circuit) : notCount C ≤ C.size := by
  unfold notCount Circuit.size
  exact List.length_filter_le _ _

open Classical in
lemma notCount_snoc (C : Circuit) (g : Gate) :
    notCount ⟨C.gates ++ [g], 0⟩ = notCount C + if g.op = GateOp.not then 1 else 0 := by
  unfold notCount
  simp only [List.filter_append, List.length_append]
  by_cases h : g.op = GateOp.not <;> simp [h]

open Classical in
lemma notCount_eq_card_filter (C : Circuit) :
    notCount C = ((Finset.range C.size).filter fun p => (gateAt C p).op = GateOp.not).card := by
  have h : ∀ gs : List Gate,
      (gs.filter fun g => decide (g.op = GateOp.not)).length =
      ((Finset.range gs.length).filter fun p => (gs.getD p ⟨GateOp.or, []⟩).op = GateOp.not).card := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [List.filter_append, List.length_append, ih, List.length_append, List.length_singleton,
        Finset.range_add_one, Finset.filter_insert]
      have hcongr : ((Finset.range gs.length).filter fun p =>
          ((gs ++ [g]).getD p ⟨GateOp.or, []⟩).op = GateOp.not) =
          ((Finset.range gs.length).filter fun p => (gs.getD p ⟨GateOp.or, []⟩).op = GateOp.not) := by
        ext p; simp only [Finset.mem_filter, Finset.mem_range]
        constructor <;> rintro ⟨hp, hop⟩
        · rw [getD_append_left_lt gs [g] p _ hp] at hop; exact ⟨hp, hop⟩
        · rw [getD_append_left_lt gs [g] p _ hp]; exact ⟨hp, hop⟩
      rw [hcongr, getD_append_right_eq]
      by_cases hnot : g.op = GateOp.not <;> simp [hnot]
  unfold notCount Circuit.size
  have hcard : ((Finset.range C.gates.length).filter fun p => (gateAt C p).op = GateOp.not).card =
      ((Finset.range C.gates.length).filter fun p => (C.gates.getD p ⟨GateOp.or, []⟩).op = GateOp.not).card := by
    congr 1
  rw [hcard, ← h C.gates]
  congr 1
  exact List.filter_congr fun g _ => decide_eq_decide.mpr Iff.rfl

open Classical in
lemma posCount_eq_card_filter (C : Circuit) :
    C.size - notCount C = ((Finset.range C.size).filter fun p => (gateAt C p).op ≠ GateOp.not).card := by
  have h1 := notCount_eq_card_filter C
  have hpart :
      ((Finset.range C.size).filter fun p => (gateAt C p).op = GateOp.not).card +
      ((Finset.range C.size).filter fun p => (gateAt C p).op ≠ GateOp.not).card = C.size := by
    have hd : Disjoint
        ((Finset.range C.size).filter fun p => (gateAt C p).op = GateOp.not)
        ((Finset.range C.size).filter fun p => (gateAt C p).op ≠ GateOp.not) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hu :
        ((Finset.range C.size).filter fun p => (gateAt C p).op = GateOp.not) ∪
        ((Finset.range C.size).filter fun p => (gateAt C p).op ≠ GateOp.not) =
        Finset.range C.size := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]
  omega

open Classical in
lemma push_gate {K : Nat} (C : Circuit) (hFan : FanInTwo C) (hBack : ReadsBack K C)
    (g : Gate)
    (hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hgBack : ∀ a ∈ g.inputs, a < K + C.size) :
    FanInTwo ⟨C.gates ++ [g], 0⟩ ∧ ReadsBack K ⟨C.gates ++ [g], 0⟩ ∧
      (Circuit.mk (C.gates ++ [g]) 0).size = C.size + 1 ∧
      notCount ⟨C.gates ++ [g], 0⟩ = notCount C + (if g.op = GateOp.not then 1 else 0) ∧
      (∀ (x : List Bool), x.length = K → ∀ w < K + C.size,
        ((Circuit.mk (C.gates ++ [g]) 0).wires x).getD w false = (C.wires x).getD w false) ∧
      (∀ (x : List Bool), x.length = K →
        ((Circuit.mk (C.gates ++ [g]) 0).wires x).getD (K + C.size) false =
          g.op.eval (g.inputs.map fun a => (C.wires x).getD a false)) := by
  let C' : Circuit := ⟨C.gates ++ [g], 0⟩
  have hsize : C'.size = C.size + 1 := by simp [C', Circuit.size]
  have hFan' : FanInTwo C' := by
    intro g' hg'
    simp only [C', List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hFan g' hg'
    · exact hgFan
  have hBack' : ReadsBack K C' := by
    intro p hp a ha
    simp only [C', List.length_append, List.length_singleton] at hp
    by_cases hlt : p < C.gates.length
    · have hget : gateAt C' p = gateAt C p := getD_append_left_lt C.gates [g] p _ hlt
      rw [hget] at ha; exact hBack p hlt a ha
    · have hpeq : p = C.gates.length := by omega
      subst hpeq
      have hget : gateAt C' C.gates.length = g := getD_append_right_eq C.gates g _
      rw [hget] at ha; exact hgBack a ha
  have hkeep : ∀ (x : List Bool), x.length = K → ∀ w < K + C.size,
      (C'.wires x).getD w false = (C.wires x).getD w false := by
    intro x hx w hw
    have hCeq : (Circuit.mk C.gates 0).wires x = C.wires x := rfl
    change ((Circuit.mk (C.gates ++ [g]) 0).wires x).getD w false = _
    rw [wires_snoc, hCeq, getD_append_left_lt _ _ _ _ (by rw [wires_length, hx]; exact hw)]
  have hnew : ∀ (x : List Bool), x.length = K →
      (C'.wires x).getD (K + C.size) false =
        g.op.eval (g.inputs.map fun a => (C.wires x).getD a false) := by
    intro x hx
    have hCeq : (Circuit.mk C.gates 0).wires x = C.wires x := rfl
    have hlen : (C.wires x).length = K + C.size := by rw [wires_length, hx]; rfl
    change ((Circuit.mk (C.gates ++ [g]) 0).wires x).getD (K + C.size) false = _
    rw [wires_snoc, hCeq, ← hlen, getD_append_right_eq]
  exact ⟨hFan', hBack', hsize, notCount_snoc C g, hkeep, hnew⟩

lemma push_and {K : Nat} (C : Circuit) (hFan : FanInTwo C) (hBack : ReadsBack K C)
    (a b : Nat) (ha : a < K + C.size) (hb : b < K + C.size) :
    ∃ C' : Circuit, FanInTwo C' ∧ ReadsBack K C' ∧
      C'.size = C.size + 1 ∧ notCount C' = notCount C ∧
      (∀ x : List Bool, x.length = K → ∀ w < K + C.size,
        (C'.wires x).getD w false = (C.wires x).getD w false) ∧
      (∀ x : List Bool, x.length = K →
        (C'.wires x).getD (K + C.size) false = ((C.wires x).getD a false && (C.wires x).getD b false)) := by
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  have hpg := push_gate (K := K) C hFan hBack g ⟨by simp [g], by simp [g]⟩
    (fun u hu => by simp [g] at hu; rcases hu with rfl | rfl <;> assumption)
  refine ⟨⟨C.gates ++ [g], 0⟩, hpg.1, hpg.2.1, hpg.2.2.1, by simpa [g] using hpg.2.2.2.1,
    hpg.2.2.2.2.1, fun x hx => ?_⟩
  rw [hpg.2.2.2.2.2 x hx]; simp [g, GateOp.eval]

lemma push_or {K : Nat} (C : Circuit) (hFan : FanInTwo C) (hBack : ReadsBack K C)
    (a b : Nat) (ha : a < K + C.size) (hb : b < K + C.size) :
    ∃ C' : Circuit, FanInTwo C' ∧ ReadsBack K C' ∧
      C'.size = C.size + 1 ∧ notCount C' = notCount C ∧
      (∀ x : List Bool, x.length = K → ∀ w < K + C.size,
        (C'.wires x).getD w false = (C.wires x).getD w false) ∧
      (∀ x : List Bool, x.length = K →
        (C'.wires x).getD (K + C.size) false = ((C.wires x).getD a false || (C.wires x).getD b false)) := by
  let g : Gate := ⟨GateOp.or, [a, b]⟩
  have hpg := push_gate (K := K) C hFan hBack g ⟨by simp [g], by simp [g]⟩
    (fun u hu => by simp [g] at hu; rcases hu with rfl | rfl <;> assumption)
  refine ⟨⟨C.gates ++ [g], 0⟩, hpg.1, hpg.2.1, hpg.2.2.1, by simpa [g] using hpg.2.2.2.1,
    hpg.2.2.2.2.1, fun x hx => ?_⟩
  rw [hpg.2.2.2.2.2 x hx]; simp [g, GateOp.eval]

/-! ### Part 2: Input Encodings `baseF` and `rawF` -/

def baseF {m : Nat} (Y : Finset (Fin m)) : List Bool :=
  List.ofFn (fun i : Fin m => decide (i ∈ Y)) ++ [false, true]

def rawF {n k m : Nat} (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ M)) ++
    List.ofFn (fun i : Fin k => decide (i ∉ H)) ++ baseF Y

lemma baseF_length {m : Nat} (Y : Finset (Fin m)) : (baseF Y).length = m + 2 := by
  simp [baseF]

lemma rawF_length {n k m : Nat} (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)) :
    (rawF M H Y).length = n + k + m + 2 := by
  simp [rawF, baseF]; omega

lemma rawF_getD_M {n k m : Nat} (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m))
    (i : Nat) (hi : i < n) :
    (rawF M H Y).getD i false = decide (⟨i, hi⟩ ∈ M) := by
  dsimp only [rawF]
  rw [List.append_assoc, getD_append_left_lt _ _ i false (by simp; exact hi)]
  simp [List.getD, hi]

lemma rawF_getD_H {n k m : Nat} (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m))
    (j : Nat) (hj : j < k) :
    (rawF M H Y).getD (n + j) false = decide (⟨j, hj⟩ ∉ H) := by
  dsimp only [rawF]
  rw [List.append_assoc, getD_append_right_ge _ _ (n + j) false (by simp),
    List.length_ofFn, Nat.add_sub_cancel_left,
    getD_append_left_lt _ _ j false (by simp; exact hj)]
  simp [List.getD, hj]

lemma rawF_getD_base {n k m : Nat} (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m))
    (r : Nat) (hr : r < m + 2) :
    (rawF M H Y).getD (n + k + r) false = (baseF Y).getD r false := by
  dsimp only [rawF]
  rw [getD_append_right_ge _ _ (n + k + r) false (by simp),
    List.length_append, List.length_ofFn, List.length_ofFn, Nat.add_sub_cancel_left]

lemma baseF_getD_false {m : Nat} (Y : Finset (Fin m)) : (baseF Y).getD m false = false := by
  dsimp only [baseF]; rw [getD_append_right_ge _ _ m false (by simp)]; simp

lemma baseF_getD_true {m : Nat} (Y : Finset (Fin m)) : (baseF Y).getD (m + 1) false = true := by
  dsimp only [baseF]; rw [getD_append_right_ge _ _ (m + 1) false (by simp)]; simp

/-! ### Part 3: Direction `RHS → LHS` (Constructive Circuit Builders) -/

-- Fold OR of list of wires starting from wire `w0` (adds `ws.length` OR gates)
lemma fold_or_wires {K : Nat} :
    ∀ (ws : List Nat) (C : Circuit) (w0 : Nat), FanInTwo C → ReadsBack K C →
      w0 < K + C.size → (∀ u ∈ ws, u < K + C.size) →
    ∃ (C' : Circuit) (wOut : Nat),
      FanInTwo C' ∧ ReadsBack K C' ∧
      C'.size = C.size + ws.length ∧ notCount C' = notCount C ∧
      wOut < K + C'.size ∧
      (∀ x : List Bool, x.length = K → ∀ w < K + C.size,
        (C'.wires x).getD w false = (C.wires x).getD w false) ∧
      (∀ x : List Bool, x.length = K →
        (C'.wires x).getD wOut false =
          ((C.wires x).getD w0 false || ws.any (fun u => (C.wires x).getD u false))) := by
  intro ws
  induction ws with
  | nil =>
    intro C w0 hFan hBack hw0 _
    refine ⟨C, w0, hFan, hBack, by simp, rfl, hw0, fun _ _ _ _ => rfl, fun x _ => by simp⟩
  | cons u rest ih =>
    intro C w0 hFan hBack hw0 hws
    obtain ⟨C1, hFan1, hBack1, hSize1, hNot1, hKeep1, hNew1⟩ :=
      push_or C hFan hBack w0 u hw0 (hws u (by simp))
    let w1 := K + C.size
    obtain ⟨C2, wOut, hFan2, hBack2, hSize2, hNot2, hwOut, hKeep2, hVal2⟩ :=
      ih C1 w1 hFan1 hBack1 (by dsimp [w1]; omega)
        (fun v hv => by have := hws v (by simp [hv]); omega)
    refine ⟨C2, wOut, hFan2, hBack2, by simp; omega, by omega, hwOut, ?_, ?_⟩
    · intro x hx w hw
      rw [hKeep2 x hx w (by omega), hKeep1 x hx w hw]
    · intro x hx
      rw [hVal2 x hx, hNew1 x hx]
      have hany_gen : ∀ l : List Nat, (∀ v ∈ l, v < K + C.size) →
          l.any (fun v => (C1.wires x).getD v false) = l.any (fun v => (C.wires x).getD v false) := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons a t iht =>
          intro hl
          simp only [List.any_cons]
          rw [hKeep1 x hx a (hl a (by simp)), iht (fun v hv => hl v (by simp [hv]))]
      rw [hany_gen rest (fun v hv => hws v (by simp [hv]))]
      simp [List.any_cons, Bool.or_assoc]

-- Fold AND of list of wires starting from wire `w0` (adds `ws.length` AND gates)
lemma fold_and_wires {K : Nat} :
    ∀ (ws : List Nat) (C : Circuit) (w0 : Nat), FanInTwo C → ReadsBack K C →
      w0 < K + C.size → (∀ u ∈ ws, u < K + C.size) →
    ∃ (C' : Circuit) (wOut : Nat),
      FanInTwo C' ∧ ReadsBack K C' ∧
      C'.size = C.size + ws.length ∧ notCount C' = notCount C ∧
      wOut < K + C'.size ∧
      (∀ x : List Bool, x.length = K → ∀ w < K + C.size,
        (C'.wires x).getD w false = (C.wires x).getD w false) ∧
      (∀ x : List Bool, x.length = K →
        (C'.wires x).getD wOut false =
          ((C.wires x).getD w0 false && ws.all (fun u => (C.wires x).getD u false))) := by
  intro ws
  induction ws with
  | nil =>
    intro C w0 hFan hBack hw0 _
    refine ⟨C, w0, hFan, hBack, by simp, rfl, hw0, fun _ _ _ _ => rfl, fun x _ => by simp⟩
  | cons u rest ih =>
    intro C w0 hFan hBack hw0 hws
    obtain ⟨C1, hFan1, hBack1, hSize1, hNot1, hKeep1, hNew1⟩ :=
      push_and C hFan hBack w0 u hw0 (hws u (by simp))
    let w1 := K + C.size
    obtain ⟨C2, wOut, hFan2, hBack2, hSize2, hNot2, hwOut, hKeep2, hVal2⟩ :=
      ih C1 w1 hFan1 hBack1 (by dsimp [w1]; omega)
        (fun v hv => by have := hws v (by simp [hv]); omega)
    refine ⟨C2, wOut, hFan2, hBack2, by simp; omega, by omega, hwOut, ?_, ?_⟩
    · intro x hx w hw
      rw [hKeep2 x hx w (by omega), hKeep1 x hx w hw]
    · intro x hx
      rw [hVal2 x hx, hNew1 x hx]
      have hall_gen : ∀ l : List Nat, (∀ v ∈ l, v < K + C.size) →
          l.all (fun v => (C1.wires x).getD v false) = l.all (fun v => (C.wires x).getD v false) := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons a t iht =>
          intro hl
          simp only [List.all_cons]
          rw [hKeep1 x hx a (hl a (by simp)), iht (fun v hv => hl v (by simp [hv]))]
      rw [hall_gen rest (fun v hv => hws v (by simp [hv]))]
      simp [List.all_cons, Bool.and_assoc]

-- Shift a circuit D on `m + 2` inputs by offset `off = n + k` into a circuit on `off + m + 2` inputs
lemma shift_circuit {off m : Nat} (D : Circuit)
    (hFan : FanInTwo D) (hBack : ReadsBack (m + 2) D) (hout : D.output < m + 2 + D.size) :
    let C : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map (· + off)⟩), D.output + off⟩
    FanInTwo C ∧ ReadsBack (off + m + 2) C ∧ C.output < off + m + 2 + C.size ∧
      C.size = D.size ∧ notCount C = notCount D ∧
      ∀ (x y : List Bool), x.length = off + m + 2 → y.length = m + 2 →
        (∀ r < m + 2, x.getD (off + r) false = y.getD r false) →
        ∀ w < m + 2 + D.size, (C.wires x).getD (w + off) false = (D.wires y).getD w false := by
  dsimp only
  let C : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map (· + off)⟩), D.output + off⟩
  have hSize : C.size = D.size := by simp [C, Circuit.size]
  have hNot : notCount C = notCount D := by
    unfold notCount
    simp only [C, List.filter_map, List.length_map]
    rfl
  have hFanC : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_map] at hg
    rcases hg with ⟨gD, hgD, rfl⟩
    obtain ⟨hop, hlen⟩ := hFan gD hgD
    exact ⟨hop, by simp [hlen]⟩
  have hBackC : ReadsBack (off + m + 2) C := by
    intro p hp a ha
    simp only [C, List.length_map] at hp
    have hget : gateAt C p = ⟨(gateAt D p).op, (gateAt D p).inputs.map (· + off)⟩ := by
      dsimp only [gateAt, C]
      simp [List.getD, hp]
    rw [hget] at ha
    simp only [List.mem_map] at ha
    rcases ha with ⟨b, hb, rfl⟩
    have := hBack p hp b hb
    omega
  refine ⟨hFanC, hBackC, by rw [hSize]; omega, hSize, hNot, ?_⟩
  intro x y hx hy hxy
  have hstep : ∀ (gs : List Gate), ReadsBack (m + 2) ⟨gs, 0⟩ →
      ∀ w < m + 2 + gs.length,
        ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map (· + off)⟩) 0).wires x).getD (w + off) false =
        ((Circuit.mk gs 0).wires y).getD w false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ w hw
      simp only [List.map_nil, Circuit.wires, List.foldl_nil, List.length_nil, Nat.add_zero] at hw ⊢
      rw [Nat.add_comm w off, hxy w hw]
    | append_singleton gs g ih =>
      intro hB w hw
      have hB0 : ReadsBack (m + 2) ⟨gs, 0⟩ := fun p hp a ha => by
        dsimp only at hp
        have hget : gateAt ⟨gs ++ [g], 0⟩ p = gateAt ⟨gs, 0⟩ p := getD_append_left_lt gs [g] p _ hp
        exact hB p (by simp; omega) a (by rwa [hget])
      have hgB : ∀ a ∈ g.inputs, a < m + 2 + gs.length := fun a ha => by
        have hget : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := getD_append_right_eq gs g _
        exact hB gs.length (by simp) a (by rwa [hget])
      rw [List.map_append, List.map_singleton, wires_snoc, wires_snoc]
      have hlen1 : ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map (· + off)⟩) 0).wires x).length =
          off + m + 2 + gs.length := by rw [wires_length, hx, List.length_map]
      have hlen2 : ((Circuit.mk gs 0).wires y).length = m + 2 + gs.length := by
        rw [wires_length, hy]
      by_cases hwlt : w < m + 2 + gs.length
      · rw [getD_append_left_lt _ _ _ _ (by omega), getD_append_left_lt _ _ _ _ (by omega)]
        exact ih hB0 w hwlt
      · have hweq : w = m + 2 + gs.length := by simp at hw; omega
        subst hweq
        have hidx : m + 2 + gs.length + off = off + m + 2 + gs.length := by omega
        rw [hidx, ← hlen1, getD_append_right_eq, ← hlen2, getD_append_right_eq]
        congr 1
        rw [List.map_map]
        refine List.map_congr_left fun a ha => ?_
        exact ih hB0 a (hgB a ha)
  exact hstep D.gates hBack

lemma rhs_to_lhs_case1 {n k m : Nat}
    (A : Finset (Finset (Fin m) × Bool))
    (P : Finset (Finset (Fin n) × Finset (Fin m)))
    (Q : Finset (Finset (Fin k) × Finset (Fin m)))
    (b p s e₀ e₁ : Nat)
    (hag : ∀ a ∈ A, false = a.2)
    (S : Finset (Fin n)) (hSp : S.card - 1 ≤ p) (hSs : S.card - 1 ≤ s)
    (hmiss : (P.filter fun z => Disjoint z.1 S).card ≤ e₀) :
    ∃ C : Circuit,
      (FanInTwo C ∧ ReadsBack (n + k + m + 2) C ∧ C.output < n + k + m + 2 + C.size) ∧
      notCount C ≤ b ∧ C.size - notCount C ≤ p ∧ C.size ≤ s ∧
      (∀ a ∈ A, C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = a.2) ∧
      (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false).card ≤ e₀ ∧
      (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true).card ≤ e₁ := by
  let K := n + k + m + 2
  by_cases hS : S = ∅
  · subst hS
    let C : Circuit := ⟨[], n + k + m⟩
    refine ⟨C, ⟨fun _ h => by simp [C] at h, fun _ h => by simp [C] at h, by dsimp [C, Circuit.size]; omega⟩,
      by simp [C, notCount], by simp [C, Circuit.size], by simp [C, Circuit.size], ?_, ?_, ?_⟩
    · intro a ha
      have hev : C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = false := by
        dsimp only [Circuit.eval, C, Circuit.wires, List.foldl_nil]
        rw [rawF_getD_base ∅ ∅ a.1 m (by omega), baseF_getD_false]
      rw [hev]; exact hag a ha
    · have hfilt : (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false) =
          (P.filter fun z => Disjoint z.1 ∅) := by
        ext z; simp only [Finset.mem_filter, Finset.disjoint_empty_right, and_congr_right_iff]
        intro _
        have hev : C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false := by
          dsimp only [Circuit.eval, C, Circuit.wires, List.foldl_nil]
          rw [rawF_getD_base z.1 ∅ z.2 m (by omega), baseF_getD_false]
        simp [hev]
      rw [hfilt]; exact hmiss
    · have hfilt : (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true) = ∅ := by
        ext z; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _
        have hev : C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = false := by
          dsimp only [Circuit.eval, C, Circuit.wires, List.foldl_nil]
          rw [rawF_getD_base ∅ z.1 z.2 m (by omega), baseF_getD_false]
        simp [hev]
      rw [hfilt]; simp
  · have hlS_len : S.toList.length = S.card := Finset.length_toList S
    have hlS_ne : S.toList ≠ [] := by
      intro h; rw [h] at hlS_len; exact hS (Finset.card_eq_zero.mp hlS_len.symm)
    cases hlS : S.toList with
    | nil => exact absurd hlS hlS_ne
    | cons i0 rest =>
      let C0 : Circuit := ⟨[], 0⟩
      obtain ⟨C1, wOut, hFan1, hBack1, hSize1, hNot1, hwOut, _, hVal1⟩ :=
        fold_or_wires (K := K) (rest.map Fin.val) C0 i0.val
          (fun _ h => by simp [C0] at h) (fun _ h => by simp [C0] at h)
          (by dsimp [K, C0]; omega)
          (by intro u hu; simp only [List.mem_map] at hu; rcases hu with ⟨i, _, rfl⟩; dsimp [K, C0]; omega)
      let C : Circuit := ⟨C1.gates, wOut⟩
      have hCsize : C.size = S.card - 1 := by
        change C1.size = S.card - 1
        rw [hSize1, List.length_map]
        have hlen : rest.length + 1 = S.card := by rw [← hlS_len, hlS]; simp
        dsimp [C0, Circuit.size]; omega
      have hCnot : notCount C = 0 := by change notCount C1 = 0; rw [hNot1]; rfl
      have heval : ∀ (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)),
          C.eval (rawF M H Y) = true ↔ ¬ Disjoint M S := by
        intro M H Y
        change (C1.wires (rawF M H Y)).getD wOut false = true ↔ ¬ Disjoint M S
        rw [hVal1 (rawF M H Y) (rawF_length M H Y)]
        have h0 : (C0.wires (rawF M H Y)).getD i0.val false = decide (i0 ∈ M) := by
          dsimp [C0, Circuit.wires]; exact rawF_getD_M M H Y i0.val i0.isLt
        have hr : (rest.map Fin.val).any (fun u => (C0.wires (rawF M H Y)).getD u false) = true ↔
            ∃ i ∈ rest, i ∈ M := by
          simp only [List.any_eq_true, List.mem_map]
          constructor
          · rintro ⟨_, ⟨i, hi, rfl⟩, hv⟩
            dsimp [C0, Circuit.wires] at hv
            rw [rawF_getD_M M H Y i.val i.isLt, decide_eq_true_eq] at hv
            exact ⟨i, hi, hv⟩
          · rintro ⟨i, hi, hiM⟩
            refine ⟨i.val, ⟨i, hi, rfl⟩, ?_⟩
            dsimp [C0, Circuit.wires]
            rw [rawF_getD_M M H Y i.val i.isLt, decide_eq_true_eq]; exact hiM
        rw [Bool.or_eq_true, h0, decide_eq_true_eq, hr, Finset.not_disjoint_iff]
        constructor
        · rintro (h | ⟨i, hi, hiM⟩)
          · exact ⟨i0, h, (Finset.mem_toList).mp (by rw [hlS]; simp)⟩
          · exact ⟨i, hiM, (Finset.mem_toList).mp (by rw [hlS]; simp [hi])⟩
        · rintro ⟨i, hiM, hiS⟩
          have hm : i ∈ i0 :: rest := by rw [← hlS]; exact (Finset.mem_toList).mpr hiS
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hrest
          · exact Or.inl hiM
          · exact Or.inr ⟨i, hrest, hiM⟩
      refine ⟨C, ⟨hFan1, hBack1, hwOut⟩, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro a ha
        have hf : C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = false := by
          cases hv : C.eval (rawF (n := n) (k := k) ∅ ∅ a.1)
          · rfl
          · exfalso; exact ((heval ∅ ∅ a.1).mp hv) (Finset.disjoint_empty_left S)
        rw [hf]; exact hag a ha
      · have hfilt : (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false) =
            (P.filter fun z => Disjoint z.1 S) := by
          ext z; simp only [Finset.mem_filter, and_congr_right_iff]; intro _
          cases hv : C.eval (rawF (n := n) (k := k) z.1 ∅ z.2)
          · simp only [true_iff]; by_contra hnd; exact Bool.false_ne_true (hv ▸ (heval z.1 ∅ z.2).mpr hnd)
          · simp only [Bool.true_eq_false, false_iff]; exact (heval z.1 ∅ z.2).mp hv
        rw [hfilt]; exact hmiss
      · have hfilt : (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true) = ∅ := by
          ext z; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro _ h
          exact ((heval ∅ z.1 z.2).mp h) (Finset.disjoint_empty_left S)
        rw [hfilt]; simp

lemma rhs_to_lhs_case2 {n k m : Nat}
    (A : Finset (Finset (Fin m) × Bool))
    (P : Finset (Finset (Fin n) × Finset (Fin m)))
    (Q : Finset (Finset (Fin k) × Finset (Fin m)))
    (b p s e₀ e₁ : Nat)
    (hag : ∀ a ∈ A, true = a.2)
    (T : Finset (Fin k)) (hTp : T.card - 1 ≤ p) (hTs : T.card - 1 ≤ s)
    (hextra : (Q.filter fun z => Disjoint z.1 T).card ≤ e₁) :
    ∃ C : Circuit,
      (FanInTwo C ∧ ReadsBack (n + k + m + 2) C ∧ C.output < n + k + m + 2 + C.size) ∧
      notCount C ≤ b ∧ C.size - notCount C ≤ p ∧ C.size ≤ s ∧
      (∀ a ∈ A, C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = a.2) ∧
      (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false).card ≤ e₀ ∧
      (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true).card ≤ e₁ := by
  let K := n + k + m + 2
  by_cases hT : T = ∅
  · subst hT
    let C : Circuit := ⟨[], n + k + m + 1⟩
    refine ⟨C, ⟨fun _ h => by simp [C] at h, fun _ h => by simp [C] at h, by dsimp [C, Circuit.size]; omega⟩,
      by simp [C, notCount], by simp [C, Circuit.size], by simp [C, Circuit.size], ?_, ?_, ?_⟩
    · intro a ha
      have hev : C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = true := by
        dsimp only [Circuit.eval, C, Circuit.wires, List.foldl_nil]
        rw [Nat.add_assoc (n + k) m 1, rawF_getD_base ∅ ∅ a.1 (m + 1) (by omega), baseF_getD_true]
      rw [hev]; exact hag a ha
    · have hfilt : (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false) = ∅ := by
        ext z; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro _
        have hev : C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = true := by
          dsimp only [Circuit.eval, C, Circuit.wires, List.foldl_nil]
          rw [Nat.add_assoc (n + k) m 1, rawF_getD_base z.1 ∅ z.2 (m + 1) (by omega), baseF_getD_true]
        simp [hev]
      rw [hfilt]; simp
    · have hfilt : (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true) =
          (Q.filter fun z => Disjoint z.1 ∅) := by
        ext z; simp only [Finset.mem_filter, Finset.disjoint_empty_right, and_congr_right_iff]; intro _
        have hev : C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true := by
          dsimp only [Circuit.eval, C, Circuit.wires, List.foldl_nil]
          rw [Nat.add_assoc (n + k) m 1, rawF_getD_base ∅ z.1 z.2 (m + 1) (by omega), baseF_getD_true]
        simp [hev]
      rw [hfilt]; exact hextra
  · have hlT_len : T.toList.length = T.card := Finset.length_toList T
    have hlT_ne : T.toList ≠ [] := by
      intro h; rw [h] at hlT_len; exact hT (Finset.card_eq_zero.mp hlT_len.symm)
    cases hlT : T.toList with
    | nil => exact absurd hlT hlT_ne
    | cons j0 rest =>
      let C0 : Circuit := ⟨[], 0⟩
      obtain ⟨C1, wOut, hFan1, hBack1, hSize1, hNot1, hwOut, _, hVal1⟩ :=
        fold_and_wires (K := K) (rest.map fun j => n + j.val) C0 (n + j0.val)
          (fun _ h => by simp [C0] at h) (fun _ h => by simp [C0] at h)
          (by dsimp [K, C0]; omega)
          (by intro u hu; simp only [List.mem_map] at hu; rcases hu with ⟨j, _, rfl⟩; dsimp [K, C0]; omega)
      let C : Circuit := ⟨C1.gates, wOut⟩
      have hCsize : C.size = T.card - 1 := by
        change C1.size = T.card - 1
        rw [hSize1, List.length_map]
        have hlen : rest.length + 1 = T.card := by rw [← hlT_len, hlT]; simp
        dsimp [C0, Circuit.size]; omega
      have hCnot : notCount C = 0 := by change notCount C1 = 0; rw [hNot1]; rfl
      have heval : ∀ (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)),
          C.eval (rawF M H Y) = true ↔ Disjoint H T := by
        intro M H Y
        change (C1.wires (rawF M H Y)).getD wOut false = true ↔ Disjoint H T
        rw [hVal1 (rawF M H Y) (rawF_length M H Y)]
        have h0 : (C0.wires (rawF M H Y)).getD (n + j0.val) false = decide (j0 ∉ H) := by
          dsimp [C0, Circuit.wires]; exact rawF_getD_H M H Y j0.val j0.isLt
        have hr : (rest.map fun j => n + j.val).all (fun u => (C0.wires (rawF M H Y)).getD u false) = true ↔
            ∀ j ∈ rest, j ∉ H := by
          simp only [List.all_eq_true, List.mem_map]
          constructor
          · intro hall j hj
            have hv := hall (n + j.val) ⟨j, hj, rfl⟩
            dsimp [C0, Circuit.wires] at hv
            rwa [rawF_getD_H M H Y j.val j.isLt, decide_eq_true_eq] at hv
          · rintro hall _ ⟨j, hj, rfl⟩
            dsimp [C0, Circuit.wires]
            rw [rawF_getD_H M H Y j.val j.isLt, decide_eq_true_eq]; exact hall j hj
        rw [Bool.and_eq_true, h0, decide_eq_true_eq, hr, Finset.disjoint_right]
        constructor
        · rintro ⟨h0, hrest⟩ j hjT
          have hm : j ∈ j0 :: rest := by rw [← hlT]; exact (Finset.mem_toList).mpr hjT
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hmem
          · exact h0
          · exact hrest j hmem
        · intro hall
          exact ⟨hall ((Finset.mem_toList).mp (by rw [hlT]; simp)),
            fun j hj => hall ((Finset.mem_toList).mp (by rw [hlT]; simp [hj]))⟩
      refine ⟨C, ⟨hFan1, hBack1, hwOut⟩, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro a ha
        have ht : C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = true :=
          (heval ∅ ∅ a.1).mpr (Finset.disjoint_empty_left T)
        rw [ht]; exact hag a ha
      · have hfilt : (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false) = ∅ := by
          ext z; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro _ h
          have ht := (heval z.1 ∅ z.2).mpr (Finset.disjoint_empty_left T)
          rw [ht] at h; cases h
        rw [hfilt]; simp
      · have hfilt : (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true) =
            (Q.filter fun z => Disjoint z.1 T) := by
          ext z; simp only [Finset.mem_filter, and_congr_right_iff]; intro _
          exact heval ∅ z.1 z.2
        rw [hfilt]; exact hextra

lemma rhs_to_lhs_case3 {n k m : Nat}
    (A : Finset (Finset (Fin m) × Bool))
    (P : Finset (Finset (Fin n) × Finset (Fin m)))
    (Q : Finset (Finset (Fin k) × Finset (Fin m)))
    (b p s e₀ e₁ : Nat)
    (D : Circuit) (S : Finset (Fin n)) (T : Finset (Fin k))
    (hFanD : FanInTwo D) (hBackD : ReadsBack (m + 2) D) (houtD : D.output < m + 2 + D.size)
    (hag : ∀ a ∈ A, D.eval (baseF a.1) = a.2)
    (hDb : notCount D ≤ b)
    (hDp : (D.size - notCount D) + S.card + T.card ≤ p)
    (hDs : D.size + S.card + T.card ≤ s)
    (hmiss : (P.filter fun z => D.eval (baseF z.2) = false ∧ Disjoint z.1 S).card ≤ e₀)
    (hextra : (Q.filter fun z => D.eval (baseF z.2) = true ∧ Disjoint z.1 T).card ≤ e₁) :
    ∃ C : Circuit,
      (FanInTwo C ∧ ReadsBack (n + k + m + 2) C ∧ C.output < n + k + m + 2 + C.size) ∧
      notCount C ≤ b ∧ C.size - notCount C ≤ p ∧ C.size ≤ s ∧
      (∀ a ∈ A, C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = a.2) ∧
      (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false).card ≤ e₀ ∧
      (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true).card ≤ e₁ := by
  let K := n + k + m + 2
  have hsh := shift_circuit (off := n + k) D hFanD hBackD houtD
  let C1 : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map (· + (n + k))⟩), D.output + (n + k)⟩
  obtain ⟨hFan1, hBack1, hout1, hSize1, hNot1, hVal1⟩ := hsh
  -- Fold OR over S.toList
  obtain ⟨C2, w2, hFan2, hBack2, hSize2, hNot2, hw2, hKeep2, hVal2⟩ :=
    fold_or_wires (K := K) (S.toList.map Fin.val) C1 C1.output hFan1 hBack1 hout1
      (by intro u hu; simp only [List.mem_map] at hu; rcases hu with ⟨i, _, rfl⟩; dsimp [K]; omega)
  -- Fold AND over T.toList
  obtain ⟨C3, w3, hFan3, hBack3, hSize3, hNot3, hw3, _, hVal3⟩ :=
    fold_and_wires (K := K) (T.toList.map fun j => n + j.val) C2 w2 hFan2 hBack2 hw2
      (by intro u hu; simp only [List.mem_map] at hu; rcases hu with ⟨j, _, rfl⟩; dsimp [K]; omega)
  let C : Circuit := ⟨C3.gates, w3⟩
  have hCsize : C.size = D.size + S.card + T.card := by
    change C3.size = D.size + S.card + T.card
    rw [hSize3, hSize2, hSize1, List.length_map, List.length_map,
      Finset.length_toList, Finset.length_toList]
  have hCnot : notCount C = notCount D := by change notCount C3 = notCount D; rw [hNot3, hNot2, hNot1]
  have hnotle : notCount D ≤ D.size := notCount_le_size D
  -- Exact evaluation of C on rawF M H Y
  have heval : ∀ (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)),
      C.eval (rawF M H Y) =
        ((D.eval (baseF Y) || decide (¬ Disjoint M S)) && decide (Disjoint H T)) := by
    intro M H Y
    change (C3.wires (rawF M H Y)).getD w3 false = _
    rw [hVal3 (rawF M H Y) (rawF_length M H Y), hVal2 (rawF M H Y) (rawF_length M H Y)]
    have hD : (C1.wires (rawF M H Y)).getD C1.output false = D.eval (baseF Y) := by
      dsimp only [Circuit.eval, C1]
      exact hVal1 (rawF M H Y) (baseF Y) (rawF_length M H Y) (baseF_length Y)
        (fun r hr => rawF_getD_base M H Y r hr) D.output houtD
    have hS : (S.toList.map Fin.val).any (fun u => (C1.wires (rawF M H Y)).getD u false) =
        decide (¬ Disjoint M S) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, Finset.not_disjoint_iff]
      constructor
      · rintro ⟨_, hmem, hv⟩
        simp only [List.mem_map] at hmem
        rcases hmem with ⟨i, hi, rfl⟩
        rw [wires_getD_input C1 (rawF M H Y) i.val (by rw [rawF_length]; omega),
          rawF_getD_M M H Y i.val i.isLt, decide_eq_true_eq] at hv
        exact ⟨i, hv, (Finset.mem_toList).mp hi⟩
      · rintro ⟨i, hiM, hiS⟩
        refine ⟨i.val, List.mem_map.mpr ⟨i, (Finset.mem_toList).mpr hiS, rfl⟩, ?_⟩
        rw [wires_getD_input C1 (rawF M H Y) i.val (by rw [rawF_length]; omega),
          rawF_getD_M M H Y i.val i.isLt, decide_eq_true_eq]
        exact hiM
    have hT : (T.toList.map fun j => n + j.val).all (fun u => (C2.wires (rawF M H Y)).getD u false) =
        decide (Disjoint H T) := by
      rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, Finset.disjoint_right]
      constructor
      · intro hall j hjT
        have hv := hall (n + j.val) (List.mem_map.mpr ⟨j, (Finset.mem_toList).mpr hjT, rfl⟩)
        rw [wires_getD_input C2 (rawF M H Y) (n + j.val) (by rw [rawF_length]; omega),
          rawF_getD_H M H Y j.val j.isLt, decide_eq_true_eq] at hv
        exact hv
      · intro hall u hu
        simp only [List.mem_map] at hu
        rcases hu with ⟨j, hj, rfl⟩
        rw [wires_getD_input C2 (rawF M H Y) (n + j.val) (by rw [rawF_length]; omega),
          rawF_getD_H M H Y j.val j.isLt, decide_eq_true_eq]
        exact hall ((Finset.mem_toList).mp hj)
    rw [hD, hS, hT]
  refine ⟨C, ⟨hFan3, hBack3, hw3⟩, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro a ha
    rw [heval ∅ ∅ a.1]; simp [Finset.disjoint_empty_left, hag a ha]
  · have hfilt : (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false) =
        (P.filter fun z => D.eval (baseF z.2) = false ∧ Disjoint z.1 S) := by
      ext z; simp only [Finset.mem_filter, and_congr_right_iff]; intro _
      rw [heval z.1 ∅ z.2]
      simp [Finset.disjoint_empty_left]
    rw [hfilt]; exact hmiss
  · have hfilt : (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true) =
        (Q.filter fun z => D.eval (baseF z.2) = true ∧ Disjoint z.1 T) := by
      ext z; simp only [Finset.mem_filter, and_congr_right_iff]; intro _
      rw [heval ∅ z.1 z.2]
      simp [Finset.disjoint_empty_left]
    rw [hfilt]; exact hextra

/-! ### Part 4: Direction `LHS → RHS` (Effective Inputs, Backward Reachability, Constant Elimination, Degree Count) -/

open Classical in
noncomputable def effInputs (g : Gate) : List Nat :=
  if g.op = GateOp.not then g.inputs.take 1 else g.inputs

open Classical in
lemma effInputs_subset (g : Gate) : ∀ a ∈ effInputs g, a ∈ g.inputs := by
  intro a ha; dsimp only [effInputs] at ha
  split_ifs at ha
  · exact List.mem_of_mem_take ha
  · exact ha

open Classical in
lemma effInputs_length_not (g : Gate) (h : g.op = GateOp.not) : (effInputs g).length ≤ 1 := by
  dsimp only [effInputs]; rw [if_pos h]; simp

open Classical in
lemma effInputs_length_le_two (g : Gate) (h : g.inputs.length ≤ 2) : (effInputs g).length ≤ 2 := by
  dsimp only [effInputs]; split_ifs
  · have := List.length_take_le 1 g.inputs; omega
  · exact h

open Classical in
lemma effInputs_eval (g : Gate) (v : Nat → Bool) :
    g.op.eval (g.inputs.map v) = g.op.eval ((effInputs g).map v) := by
  dsimp only [effInputs]
  split_ifs with hnot
  · rw [hnot]
    cases g.inputs with
    | nil => rfl
    | cons a rest => simp [GateOp.eval]
  · rfl

-- Backward reachability from output via effInputs
open Classical in
noncomputable def reachAux (K : Nat) (C : Circuit) : Nat → Finset Nat → Finset Nat
  | 0, R => R
  | p + 1, R =>
    let R' := if K + p ∈ R then R ∪ (effInputs (gateAt C p)).toFinset else R
    reachAux K C p R'

open Classical in
lemma subset_reachAux (K : Nat) (C : Circuit) :
    ∀ p R, R ⊆ reachAux K C p R := by
  intro p
  induction p with
  | zero => intro R; exact Finset.Subset.rfl
  | succ p ih =>
    intro R
    dsimp only [reachAux]
    have hsub : R ⊆ if K + p ∈ R then R ∪ (effInputs (gateAt C p)).toFinset else R := by
      split_ifs
      · exact Finset.subset_union_left
      · exact Finset.Subset.rfl
    exact hsub.trans (ih _)

open Classical in
lemma reachAux_added_lt (K : Nat) (C : Circuit) (hBack : ReadsBack K C) :
    ∀ p ≤ C.size, ∀ R v, v ∈ reachAux K C p R → v ∉ R → v < K + p := by
  intro p
  induction p with
  | zero => intro _ R v hv hnr; exact absurd hv hnr
  | succ p ih =>
    intro hp R v hv hnr
    dsimp only [reachAux] at hv
    set R' := if K + p ∈ R then R ∪ (effInputs (gateAt C p)).toFinset else R
    by_cases hvR' : v ∈ R'
    · dsimp only [R'] at hvR'
      split_ifs at hvR' with hmem
      · rcases Finset.mem_union.mp hvR' with h1 | h2
        · exact absurd h1 hnr
        · have hin : v ∈ (gateAt C p).inputs := effInputs_subset _ _ (List.mem_toFinset.mp h2)
          have hlt := hBack p (by dsimp [Circuit.size] at hp; omega) v hin
          omega
      · exact absurd hvR' hnr
    · have hlt := ih (by omega) R' v hv hvR'
      omega

open Classical in
lemma reachAux_closed (K : Nat) (C : Circuit) (hBack : ReadsBack K C) :
    ∀ p ≤ C.size, ∀ R q, q < p → K + q ∈ reachAux K C p R →
      ∀ a ∈ effInputs (gateAt C q), a ∈ reachAux K C p R := by
  intro p
  induction p with
  | zero => intro _ _ _ hq; omega
  | succ p ih =>
    intro hp R q hqp hqmem a ha
    dsimp only [reachAux] at hqmem ⊢
    set R' := if K + p ∈ R then R ∪ (effInputs (gateAt C p)).toFinset else R
    by_cases hqlt : q < p
    · exact ih (by omega) R' q hqlt hqmem a ha
    · have hqeq : q = p := by omega
      subst hqeq
      have hKpR : K + q ∈ R := by
        by_contra hnr
        have hlt := reachAux_added_lt K C hBack q (by omega) R' (K + q) hqmem (by
          dsimp only [R']; rw [if_neg hnr]; exact hnr)
        omega
      have haR' : a ∈ R' := by
        dsimp only [R']; rw [if_pos hKpR]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)
      exact subset_reachAux K C q R' haR'

open Classical in
lemma reachAux_has_out_edge (K : Nat) (C : Circuit) (hBack : ReadsBack K C) :
    ∀ p ≤ C.size, ∀ R v, v ∈ reachAux K C p R → v ∉ R →
      ∃ q < p, K + q ∈ reachAux K C p R ∧ v ∈ effInputs (gateAt C q) := by
  intro p
  induction p with
  | zero => intro _ R v hv hnr; exact absurd hv hnr
  | succ p ih =>
    intro hp R v hv hnr
    dsimp only [reachAux] at hv ⊢
    set R' := if K + p ∈ R then R ∪ (effInputs (gateAt C p)).toFinset else R
    by_cases hvR' : v ∈ R'
    · dsimp only [R'] at hvR'
      split_ifs at hvR' with hKp
      · rcases Finset.mem_union.mp hvR' with h1 | h2
        · exact absurd h1 hnr
        · exact ⟨p, by omega, subset_reachAux K C p R' (by dsimp only [R']; rw [if_pos hKp]; exact Finset.mem_union_left _ hKp),
            List.mem_toFinset.mp h2⟩
      · exact absurd hvR' hnr
    · obtain ⟨q, hqp, hqmem, hva⟩ := ih (by omega) R' v hv hvR'
      exact ⟨q, by omega, hqmem, hva⟩

-- If two input vectors agree on all inputs `< K` that are in ReachOut, then C.eval agrees!
open Classical in
lemma eval_eq_of_agree_on_reach {K : Nat} (C : Circuit)
    (hBack : ReadsBack K C) (hout : C.output < K + C.size)
    (v₁ v₂ : List Bool) (hv₁ : v₁.length = K) (hv₂ : v₂.length = K)
    (hagree : ∀ w < K, w ∈ reachAux K C C.size {C.output} → v₁.getD w false = v₂.getD w false) :
    C.eval v₁ = C.eval v₂ := by
  let R := reachAux K C C.size {C.output}
  have hall : ∀ w < K + C.size, w ∈ R → (C.wires v₁).getD w false = (C.wires v₂).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwR
      by_cases hwK : w < K
      · rw [wires_getD_input C v₁ w (by omega), wires_getD_input C v₂ w (by omega)]
        exact hagree w hwK hwR
      · let p := w - K
        have hp_lt : p < C.gates.length := by dsimp [Circuit.size] at hw; omega
        have hweq : w = K + p := by omega
        rw [hweq, wires_gate_eval C hBack v₁ hv₁ p hp_lt, wires_gate_eval C hBack v₂ hv₂ p hp_lt,
          effInputs_eval, effInputs_eval]
        congr 1
        refine List.map_congr_left fun a ha => ?_
        have ha_lt : a < K + p := hBack p hp_lt a (effInputs_subset _ _ ha)
        have ha_R : a ∈ R := reachAux_closed K C hBack C.size le_rfl {C.output} p hp_lt (by rwa [← hweq]) a ha
        exact ih a (by omega) (by omega) ha_R
  exact hall C.output hout (subset_reachAux K C C.size {C.output} (Finset.mem_singleton_self _))

-- Main LHS → RHS theorem
open Classical in
lemma lhs_to_rhs_core {n k m : Nat}
    (A : Finset (Finset (Fin m) × Bool))
    (P : Finset (Finset (Fin n) × Finset (Fin m)))
    (Q : Finset (Finset (Fin k) × Finset (Fin m)))
    (b p s e₀ e₁ : Nat)
    (C : Circuit)
    (hFan : FanInTwo C) (hBack : ReadsBack (n + k + m + 2) C)
    (hout : C.output < n + k + m + 2 + C.size)
    (hCnot : notCount C ≤ b) (hCpos : C.size - notCount C ≤ p) (hCsize : C.size ≤ s)
    (hag : ∀ a ∈ A, C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = a.2)
    (hP : (P.filter fun z => C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = false).card ≤ e₀)
    (hQ : (Q.filter fun z => C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = true).card ≤ e₁) :
    ((∀ a ∈ A, false = a.2) ∧ ∃ S : Finset (Fin n), S.card - 1 ≤ p ∧ S.card - 1 ≤ s ∧
        (P.filter fun z => Disjoint z.1 S).card ≤ e₀) ∨
    ((∀ a ∈ A, true = a.2) ∧ ∃ T : Finset (Fin k), T.card - 1 ≤ p ∧ T.card - 1 ≤ s ∧
        (Q.filter fun z => Disjoint z.1 T).card ≤ e₁) ∨
    ∃ (D : Circuit) (S : Finset (Fin n)) (T : Finset (Fin k)),
      let f := fun Y : Finset (Fin m) => D.eval (baseF Y)
      (FanInTwo D ∧ ReadsBack (m + 2) D ∧ D.output < m + 2 + D.size) ∧
      (∃ Y Z, f Y ≠ f Z) ∧ (∀ a ∈ A, f a.1 = a.2) ∧ notCount D ≤ b ∧
      (D.size - notCount D) + S.card + T.card ≤ p ∧ D.size + S.card + T.card ≤ s ∧
      (P.filter fun z => f z.2 = false ∧ Disjoint z.1 S).card ≤ e₀ ∧
      (Q.filter fun z => f z.2 = true ∧ Disjoint z.1 T).card ≤ e₁ := by
  let K := n + k + m + 2
  let f : Finset (Fin m) → Bool := fun Y => C.eval (rawF (n := n) (k := k) ∅ ∅ Y)
  let R : Finset Nat := reachAux K C C.size {C.output}
  let S : Finset (Fin n) := Finset.univ.filter fun i => i.val ∈ R
  let T : Finset (Fin k) := Finset.univ.filter fun j => n + j.val ∈ R
  -- Step 1: Prove miss f S ≤ e₀ and extra f T ≤ e₁
  have hmiss : (P.filter fun z => f z.2 = false ∧ Disjoint z.1 S).card ≤ e₀ := by
    refine le_trans (Finset.card_le_card ?_) hP
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    have heq : C.eval (rawF (n := n) (k := k) z.1 ∅ z.2) = f z.2 := by
      refine eval_eq_of_agree_on_reach C hBack hout _ _ (rawF_length _ _ _) (rawF_length _ _ _) ?_
      intro w hwK hwR
      by_cases hwn : w < n
      · rw [rawF_getD_M z.1 ∅ z.2 w hwn, rawF_getD_M ∅ ∅ z.2 w hwn]
        have hiS : (⟨w, hwn⟩ : Fin n) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwR⟩
        have hni : (⟨w, hwn⟩ : Fin n) ∉ z.1 := Finset.disjoint_right.mp hz.2.2 hiS
        simp [hni]
      · by_cases hwk : w < n + k
        · have hj : w - n < k := by omega
          have hwe : w = n + (w - n) := by omega
          rw [hwe, rawF_getD_H z.1 ∅ z.2 _ hj, rawF_getD_H ∅ ∅ z.2 _ hj]
        · have hr : w - (n + k) < m + 2 := by omega
          have hwe : w = n + k + (w - (n + k)) := by omega
          rw [hwe, rawF_getD_base z.1 ∅ z.2 _ hr, rawF_getD_base ∅ ∅ z.2 _ hr]
    rw [heq]; exact hz.2.1
  have hextra : (Q.filter fun z => f z.2 = true ∧ Disjoint z.1 T).card ≤ e₁ := by
    refine le_trans (Finset.card_le_card ?_) hQ
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    have heq : C.eval (rawF (n := n) (k := k) ∅ z.1 z.2) = f z.2 := by
      refine eval_eq_of_agree_on_reach C hBack hout _ _ (rawF_length _ _ _) (rawF_length _ _ _) ?_
      intro w hwK hwR
      by_cases hwn : w < n
      · rw [rawF_getD_M ∅ z.1 z.2 w hwn, rawF_getD_M ∅ ∅ z.2 w hwn]
      · by_cases hwk : w < n + k
        · have hj : w - n < k := by omega
          have hwe : w = n + (w - n) := by omega
          rw [hwe, rawF_getD_H ∅ z.1 z.2 _ hj, rawF_getD_H ∅ ∅ z.2 _ hj]
          have hjT : (⟨w - n, hj⟩ : Fin k) ∈ T := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rwa [← hwe]
          have hnj : (⟨w - n, hj⟩ : Fin k) ∉ z.1 := Finset.disjoint_right.mp hz.2.2 hjT
          simp [hnj]
        · have hr : w - (n + k) < m + 2 := by omega
          have hwe : w = n + k + (w - (n + k)) := by omega
          rw [hwe, rawF_getD_base ∅ z.1 z.2 _ hr, rawF_getD_base ∅ ∅ z.2 _ hr]
    rw [heq]; exact hz.2.1
  -- Step 2: Classify base-constant wires and gates
  let isConst (w : Nat) : Prop :=
    ∀ Y Z : Finset (Fin m),
      (C.wires (rawF (n := n) (k := k) ∅ ∅ Y)).getD w false =
      (C.wires (rawF (n := n) (k := k) ∅ ∅ Z)).getD w false
  let cVal (w : Nat) : Bool := (C.wires (rawF (n := n) (k := k) (m := m) ∅ ∅ ∅)).getD w false
  have hcVal : ∀ w, isConst w → ∀ Y, (C.wires (rawF (n := n) (k := k) ∅ ∅ Y)).getD w false = cVal w :=
    fun w hw Y => hw Y ∅
  have hM_const : ∀ i : Fin n, isConst i.val := fun i Y Z => by
    rw [wires_getD_input C _ i.val (by rw [rawF_length]; omega),
      wires_getD_input C _ i.val (by rw [rawF_length]; omega),
      rawF_getD_M ∅ ∅ Y i.val i.isLt, rawF_getD_M ∅ ∅ Z i.val i.isLt]
  have hH_const : ∀ j : Fin k, isConst (n + j.val) := fun j Y Z => by
    rw [wires_getD_input C _ (n + j.val) (by rw [rawF_length]; omega),
      wires_getD_input C _ (n + j.val) (by rw [rawF_length]; omega),
      rawF_getD_H ∅ ∅ Y j.val j.isLt, rawF_getD_H ∅ ∅ Z j.val j.isLt]
  have hF_const : isConst (n + k + m) := fun Y Z => by
    rw [wires_getD_input C _ (n + k + m) (by rw [rawF_length]; omega),
      wires_getD_input C _ (n + k + m) (by rw [rawF_length]; omega),
      rawF_getD_base ∅ ∅ Y m (by omega), rawF_getD_base ∅ ∅ Z m (by omega),
      baseF_getD_false, baseF_getD_false]
  have hT_const : isConst (n + k + m + 1) := fun Y Z => by
    rw [wires_getD_input C _ (n + k + m + 1) (by rw [rawF_length]; omega),
      wires_getD_input C _ (n + k + m + 1) (by rw [rawF_length]; omega),
      Nat.add_assoc (n + k) m 1,
      rawF_getD_base ∅ ∅ Y (m + 1) (by omega), rawF_getD_base ∅ ∅ Z (m + 1) (by omega),
      baseF_getD_true, baseF_getD_true]
  -- Gate subsets of Finset.range C.size
  let Vpos : Finset Nat :=
    (Finset.range C.size).filter fun q => K + q ∈ R ∧ isConst (K + q) ∧ (gateAt C q).op ≠ GateOp.not
  let Vnot : Finset Nat :=
    (Finset.range C.size).filter fun q => K + q ∈ R ∧ isConst (K + q) ∧ (gateAt C q).op = GateOp.not
  let Bridge : Finset Nat :=
    (Finset.range C.size).filter fun q => ¬ isConst (K + q) ∧ ∃ a ∈ effInputs (gateAt C q), isConst a
  let Vbr : Finset Nat := Bridge.filter fun q => K + q ∈ R
  let Pure : Finset Nat :=
    (Finset.range C.size).filter fun q => ¬ isConst (K + q) ∧ ∀ a ∈ effInputs (gateAt C q), ¬ isConst a
  -- Structure lemma for Bridge gates
  have hbridge_struct : ∀ q ∈ Bridge,
      (gateAt C q).op ≠ GateOp.not ∧
      (∃ b ∈ effInputs (gateAt C q), ¬ isConst b ∧
        ∀ Y : Finset (Fin m),
          (C.wires (rawF (n := n) (k := k) ∅ ∅ Y)).getD (K + q) false =
          (C.wires (rawF (n := n) (k := k) ∅ ∅ Y)).getD b false) ∧
      ((effInputs (gateAt C q)).toFinset.filter isConst).card ≤ 1 := by
    intro q hq
    simp only [Bridge, Finset.mem_filter, Finset.mem_range] at hq
    rcases hq with ⟨hq_lt, hnc, a0, ha0_mem, ha0_c⟩
    have hgFan := hFan (gateAt C q) (by
      dsimp only [gateAt]; rw [List.getD_eq_getElem _ _ hq_lt]; exact List.getElem_mem hq_lt)
    have hnot_ne : (gateAt C q).op ≠ GateOp.not := by
      intro hnot
      apply hnc; intro Y Z
      rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
        wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
        effInputs_eval, effInputs_eval]
      have hlen1 := effInputs_length_not (gateAt C q) hnot
      cases heff : effInputs (gateAt C q) with
      | nil => rw [heff] at ha0_mem; simp at ha0_mem
      | cons x rest =>
        have hrnil : rest = [] := by rw [heff] at hlen1; simp at hlen1; exact hlen1
        subst hrnil
        rw [heff] at ha0_mem; simp only [List.mem_singleton] at ha0_mem; rw [ha0_mem] at ha0_c
        simp only [List.map_cons, List.map_nil]
        rw [hcVal x ha0_c Y, hcVal x ha0_c Z]
    have hop_ao : (gateAt C q).op = GateOp.and ∨ (gateAt C q).op = GateOp.or := by
      rcases hgFan.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hnot_ne
    have heff_eq : effInputs (gateAt C q) = (gateAt C q).inputs := by
      dsimp only [effInputs]; rw [if_neg hnot_ne]
    cases hgi : (gateAt C q).inputs with
    | nil => rw [heff_eq, hgi] at ha0_mem; simp at ha0_mem
    | cons u rest =>
      cases rest with
      | nil =>
        exfalso; apply hnc; intro Y Z
        rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
          wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi]
        rw [heff_eq, hgi] at ha0_mem; simp only [List.mem_singleton] at ha0_mem; rw [ha0_mem] at ha0_c
        simp only [List.map_cons, List.map_nil]
        rw [hcVal u ha0_c Y, hcVal u ha0_c Z]
      | cons v rest2 =>
        have hr2 : rest2 = [] := by
          have hlen := hgFan.2; rw [hgi] at hlen; simp at hlen; exact hlen
        subst hr2
        have hnot_both : ¬ (isConst u ∧ isConst v) := by
          rintro ⟨hu, hv⟩; apply hnc; intro Y Z
          rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
            wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi]
          simp only [List.map_cons, List.map_nil]
          rw [hcVal u hu Y, hcVal u hu Z, hcVal v hv Y, hcVal v hv Z]
        have hcard1 : ((effInputs (gateAt C q)).toFinset.filter isConst).card ≤ 1 := by
          rw [heff_eq, hgi]
          by_cases hu : isConst u
          · have hnv : ¬ isConst v := fun hv => hnot_both ⟨hu, hv⟩
            have hsub : ([u, v].toFinset.filter isConst) ⊆ {u} := by
              intro x hx; simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
                List.not_mem_nil, or_false] at hx
              rcases hx.1 with rfl | rfl
              · exact Finset.mem_singleton_self _
              · exact absurd hx.2 hnv
            exact (Finset.card_le_card hsub).trans (by simp)
          · have hsub : ([u, v].toFinset.filter isConst) ⊆ {v} := by
              intro x hx; simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons,
                List.not_mem_nil, or_false] at hx
              rcases hx.1 with rfl | rfl
              · exact absurd hx.2 hu
              · exact Finset.mem_singleton_self _
            exact (Finset.card_le_card hsub).trans (by simp)
        refine ⟨hnot_ne, ?_, hcard1⟩
        have hpair : (isConst u ∧ ¬ isConst v) ∨ (isConst v ∧ ¬ isConst u) := by
          rw [heff_eq, hgi] at ha0_mem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha0_mem
          rcases ha0_mem with rfl | rfl
          · exact Or.inl ⟨ha0_c, fun hv => hnot_both ⟨ha0_c, hv⟩⟩
          · exact Or.inr ⟨ha0_c, fun hu => hnot_both ⟨hu, ha0_c⟩⟩
        rcases hpair with ⟨hu, hnv⟩ | ⟨hv, hnu⟩
        · refine ⟨v, by rw [heff_eq, hgi]; simp, hnv, fun Y => ?_⟩
          rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi]
          rcases hop_ao with hand | hor
          · have hct : cVal u = true := by
              cases hc : cVal u
              · exfalso; apply hnc; intro Y₁ Y₂
                rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
                  wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi, hand]
                simp only [List.map_cons, List.map_nil]
                rw [hcVal u hu Y₁, hcVal u hu Y₂, hc]; simp [GateOp.eval]
              · rfl
            rw [hand]; simp only [List.map_cons, List.map_nil]
            rw [hcVal u hu Y, hct]; simp [GateOp.eval]
          · have hcf : cVal u = false := by
              cases hc : cVal u
              · rfl
              · exfalso; apply hnc; intro Y₁ Y₂
                rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
                  wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi, hor]
                simp only [List.map_cons, List.map_nil]
                rw [hcVal u hu Y₁, hcVal u hu Y₂, hc]; simp [GateOp.eval]
            rw [hor]; simp only [List.map_cons, List.map_nil]
            rw [hcVal u hu Y, hcf]; simp [GateOp.eval]
        · refine ⟨u, by rw [heff_eq, hgi]; simp, hnu, fun Y => ?_⟩
          rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi]
          rcases hop_ao with hand | hor
          · have hct : cVal v = true := by
              cases hc : cVal v
              · exfalso; apply hnc; intro Y₁ Y₂
                rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
                  wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi, hand]
                simp only [List.map_cons, List.map_nil]
                rw [hcVal v hv Y₁, hcVal v hv Y₂, hc]; simp [GateOp.eval]
              · rfl
            rw [hand]; simp only [List.map_cons, List.map_nil]
            rw [hcVal v hv Y, hct]; simp [GateOp.eval]
          · have hcf : cVal v = false := by
              cases hc : cVal v
              · rfl
              · exfalso; apply hnc; intro Y₁ Y₂
                rw [wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt,
                  wires_gate_eval C hBack _ (rawF_length _ _ _) q hq_lt, hgi, hor]
                simp only [List.map_cons, List.map_nil]
                rw [hcVal v hv Y₁, hcVal v hv Y₂, hc]; simp [GateOp.eval]
            rw [hor]; simp only [List.map_cons, List.map_nil]
            rw [hcVal v hv Y, hcf]; simp [GateOp.eval]
  -- Step 3: Degree-counting bound on S.card + T.card
  let VinM : Finset Nat := S.image Fin.val
  let VinH : Finset Nat := T.image fun j => n + j.val
  let VposW : Finset Nat := Vpos.image (K + ·)
  let VnotW : Finset Nat := Vnot.image (K + ·)
  let V : Finset Nat := (VinM ∪ VinH) ∪ (VposW ∪ VnotW)
  have hV_card : V.card = S.card + T.card + Vpos.card + Vnot.card := by
    have hdisj1 : Disjoint VinM VinH := by
      rw [Finset.disjoint_left]; intro w h1 h2
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩; omega
    have hdisj2 : Disjoint VposW VnotW := by
      rw [Finset.disjoint_left]; intro w h1 h2
      rcases Finset.mem_image.mp h1 with ⟨q1, hq1, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨q2, hq2, heq⟩
      have hqe : q1 = q2 := by omega
      subst hqe
      exact (Finset.mem_filter.mp hq1).2.2.2 (Finset.mem_filter.mp hq2).2.2.2
    have hdisj3 : Disjoint (VinM ∪ VinH) (VposW ∪ VnotW) := by
      rw [Finset.disjoint_left]; intro w h1 h2
      have hlt : w < K := by
        rcases Finset.mem_union.mp h1 with h | h
        · rcases Finset.mem_image.mp h with ⟨i, _, rfl⟩; dsimp [K]; omega
        · rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩; dsimp [K]; omega
      have hge : K ≤ w := by
        rcases Finset.mem_union.mp h2 with h | h <;>
        · rcases Finset.mem_image.mp h with ⟨q, _, rfl⟩; omega
      omega
    rw [Finset.card_union_of_disjoint hdisj3, Finset.card_union_of_disjoint hdisj1,
      Finset.card_union_of_disjoint hdisj2,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun j₁ j₂ h => Fin.ext (by omega)),
      Finset.card_image_of_injective _ (fun q₁ q₂ h => by omega),
      Finset.card_image_of_injective _ (fun q₁ q₂ h => by omega)]
    omega
  have hV_sub_R : ∀ v ∈ V, v ∈ R ∧ isConst v := by
    intro v hv
    rcases Finset.mem_union.mp hv with h1 | h2
    · rcases Finset.mem_union.mp h1 with hm | hh
      · rcases Finset.mem_image.mp hm with ⟨i, hi, rfl⟩
        exact ⟨(Finset.mem_filter.mp hi).2, hM_const i⟩
      · rcases Finset.mem_image.mp hh with ⟨j, hj, rfl⟩
        exact ⟨(Finset.mem_filter.mp hj).2, hH_const j⟩
    · rcases Finset.mem_union.mp h2 with hp | hn
      · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        exact ⟨(Finset.mem_filter.mp hq).2.1, (Finset.mem_filter.mp hq).2.2.1⟩
      · rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
        exact ⟨(Finset.mem_filter.mp hq).2.1, (Finset.mem_filter.mp hq).2.2.1⟩
  let Gtgt : Finset Nat := Vpos ∪ Vnot ∪ Vbr
  let E : Finset (Nat × Nat) := (V.product Gtgt).filter fun e => e.1 ∈ effInputs (gateAt C e.2)
  -- Lower bound: (V.erase C.output).card ≤ E.card
  have hE_lo : (V.erase C.output).card ≤ E.card := by
    have hex : ∀ v ∈ V.erase C.output, ∃ q ∈ Gtgt, (v, q) ∈ E := by
      intro v hv
      have hne : v ≠ C.output := (Finset.mem_erase.mp hv).1
      have hvV : v ∈ V := (Finset.mem_erase.mp hv).2
      obtain ⟨hvR, hvc⟩ := hV_sub_R v hvV
      have hvnot0 : v ∉ ({C.output} : Finset Nat) := by simp [hne]
      obtain ⟨q, hq_lt, hqR, hvq⟩ := reachAux_has_out_edge K C hBack C.size le_rfl {C.output} v hvR hvnot0
      have hqG : q ∈ Gtgt := by
        by_cases hqc : isConst (K + q)
        · by_cases hqn : (gateAt C q).op = GateOp.not
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq_lt, hqR, hqc, hqn⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq_lt, hqR, hqc, hqn⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq_lt, hqc, v, hvq, hvc⟩, hqR⟩)
      exact ⟨q, hqG, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvV, hqG⟩, hvq⟩⟩
    have hsub : V.erase C.output ⊆ E.image Prod.fst := by
      intro v hv
      obtain ⟨q, _, he⟩ := hex v hv
      exact Finset.mem_image.mpr ⟨(v, q), he, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- Upper bound: E.card ≤ 2 * Vpos.card + Vnot.card + Vbr.card
  have hE_hi : E.card ≤ 2 * Vpos.card + Vnot.card + Vbr.card := by
    have hfib : E.card = Gtgt.sum fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card := by
      have hH : ∀ e ∈ E, e.2 ∈ Gtgt := fun e he => by
        simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at he
        exact he.1.2
      rw [Finset.card_eq_sum_card_fiberwise hH]
      refine Finset.sum_congr rfl fun q hq => ?_
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at he
        exact Finset.mem_filter.mpr ⟨he.1.1.1, he.2 ▸ he.1.2⟩
      · intro e₁ he₁ e₂ he₂ h1
        have h2a := (Finset.mem_filter.mp he₁).2
        have h2b := (Finset.mem_filter.mp he₂).2
        exact Prod.ext h1 (h2a.trans h2b.symm)
      · intro v hv
        simp only [Finset.mem_filter] at hv
        refine ⟨(v, q), ?_, rfl⟩
        simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
        exact ⟨⟨⟨hv.1, hq⟩, hv.2⟩, trivial⟩
    rw [hfib]
    have hd_pn : Disjoint Vpos Vnot := by
      rw [Finset.disjoint_left]; intro q h1 h2
      exact (Finset.mem_filter.mp h1).2.2.2 (Finset.mem_filter.mp h2).2.2.2
    have hd_pnb : Disjoint (Vpos ∪ Vnot) Vbr := by
      rw [Finset.disjoint_left]; intro q h1 h2
      have hnc : ¬ isConst (K + q) := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.1
      rcases Finset.mem_union.mp h1 with h | h
      · exact hnc (Finset.mem_filter.mp h).2.2.1
      · exact hnc (Finset.mem_filter.mp h).2.2.1
    dsimp only [Gtgt]
    rw [Finset.sum_union hd_pnb, Finset.sum_union hd_pn]
    have h1 : Vpos.sum (fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card) ≤ 2 * Vpos.card := by
      calc Vpos.sum (fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card)
          ≤ Vpos.sum (fun _ => 2) := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hq_lt : q < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
            have hgFan := hFan (gateAt C q) (by
              dsimp only [gateAt]; rw [List.getD_eq_getElem _ _ hq_lt]; exact List.getElem_mem hq_lt)
            have hsub : (V.filter fun v => v ∈ effInputs (gateAt C q)) ⊆ (effInputs (gateAt C q)).toFinset :=
              fun v hv => List.mem_toFinset.mpr (Finset.mem_filter.mp hv).2
            exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans (effInputs_length_le_two _ hgFan.2))
        _ = 2 * Vpos.card := by simp [mul_comm]
    have h2 : Vnot.sum (fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card) ≤ Vnot.card := by
      calc Vnot.sum (fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card)
          ≤ Vnot.sum (fun _ => 1) := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hnot : (gateAt C q).op = GateOp.not := (Finset.mem_filter.mp hq).2.2.2
            have hsub : (V.filter fun v => v ∈ effInputs (gateAt C q)) ⊆ (effInputs (gateAt C q)).toFinset :=
              fun v hv => List.mem_toFinset.mpr (Finset.mem_filter.mp hv).2
            exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans (effInputs_length_not _ hnot))
        _ = Vnot.card := by simp
    have h3 : Vbr.sum (fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card) ≤ Vbr.card := by
      calc Vbr.sum (fun q => (V.filter fun v => v ∈ effInputs (gateAt C q)).card)
          ≤ Vbr.sum (fun _ => 1) := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hqB : q ∈ Bridge := (Finset.mem_filter.mp hq).1
            have hsub : (V.filter fun v => v ∈ effInputs (gateAt C q)) ⊆
                (effInputs (gateAt C q)).toFinset.filter isConst := fun v hv =>
              Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (Finset.mem_filter.mp hv).2,
                (hV_sub_R v (Finset.mem_filter.mp hv).1).2⟩
            exact (Finset.card_le_card hsub).trans (hbridge_struct q hqB).2.2
        _ = Vbr.card := by simp
    omega
  -- Also Vpos and Vbr are disjoint positive gates of C
  have hdisj_pb : Disjoint Vpos Vbr := by
    rw [Finset.disjoint_left]; intro q h1 h2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.1 (Finset.mem_filter.mp h1).2.2.1
  have hpb_sub_pos : Vpos ∪ Vbr ⊆ (Finset.range C.size).filter fun q => (gateAt C q).op ≠ GateOp.not := by
    intro q hq
    rcases Finset.mem_union.mp hq with h1 | h2
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h1).2.2.2⟩
    · have hqB : q ∈ Bridge := (Finset.mem_filter.mp h2).1
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqB).1, (hbridge_struct q hqB).1⟩
  have hpb_le_pos : Vpos.card + Vbr.card ≤ C.size - notCount C := by
    rw [posCount_eq_card_filter, ← Finset.card_union_of_disjoint hdisj_pb]
    exact Finset.card_le_card hpb_sub_pos
  -- Step 4: Split on whether C.output is base-constant!
  by_cases hout_c : isConst C.output
  · -- Cases 1 and 2: f is constant!
    have hST_bound : S.card + T.card - 1 ≤ Vpos.card + Vbr.card := by
      have her : V.card - 1 ≤ (V.erase C.output).card := Finset.pred_card_le_card_erase
      omega
    have hnot_le : notCount C ≤ C.size := notCount_le_size C
    cases hcv : cVal C.output
    · -- Constant false -> Case 1
      left
      have hf_false : ∀ Y, f Y = false := fun Y => by
        dsimp only [f, Circuit.eval]; rw [hcVal C.output hout_c Y, hcv]
      refine ⟨fun a ha => by rw [← hf_false a.1]; exact hag a ha, S, by omega, by omega, ?_⟩
      have hfeq : (P.filter fun z => Disjoint z.1 S) = (P.filter fun z => f z.2 = false ∧ Disjoint z.1 S) := by
        ext z; simp [hf_false]
      rw [hfeq]; exact hmiss
    · -- Constant true -> Case 2
      right; left
      have hf_true : ∀ Y, f Y = true := fun Y => by
        dsimp only [f, Circuit.eval]; rw [hcVal C.output hout_c Y, hcv]
      refine ⟨fun a ha => by rw [← hf_true a.1]; exact hag a ha, T, by omega, by omega, ?_⟩
      have hfeq : (Q.filter fun z => Disjoint z.1 T) = (Q.filter fun z => f z.2 = true ∧ Disjoint z.1 T) := by
        ext z; simp [hf_true]
      rw [hfeq]; exact hextra
  · -- Case 3: C.output is non-constant!
    right; right
    have hout_notV : C.output ∉ V := fun h => hout_c (hV_sub_R C.output h).2
    have hST_bound : S.card + T.card ≤ Vpos.card + Vbr.card := by
      rw [Finset.erase_eq_of_notMem hout_notV] at hE_lo
      omega
    -- Build D by induction on r ≤ C.size emitting ONLY Pure gates!
    have hbuildD : ∀ r ≤ C.size,
        ∃ (Dr : Circuit) (phi : Nat → Nat),
          FanInTwo Dr ∧ ReadsBack (m + 2) Dr ∧
          notCount Dr ≤ ((Finset.range r).filter fun q => q ∈ Pure ∧ (gateAt C q).op = GateOp.not).card ∧
          Dr.size - notCount Dr ≤ ((Finset.range r).filter fun q => q ∈ Pure ∧ (gateAt C q).op ≠ GateOp.not).card ∧
          ∀ w < K + r, ¬ isConst w →
            phi w < m + 2 + Dr.size ∧
            ∀ Y : Finset (Fin m), (Dr.wires (baseF Y)).getD (phi w) false =
              (C.wires (rawF (n := n) (k := k) ∅ ∅ Y)).getD w false := by
      intro r
      induction r with
      | zero =>
        intro _
        let D0 : Circuit := ⟨[], 0⟩
        refine ⟨D0, fun w => w - (n + k), fun _ h => by simp [D0] at h, fun _ h => by simp [D0] at h,
          by simp [D0, notCount], by simp [D0, Circuit.size], fun w hw hnc => ?_⟩
        have hge : n + k ≤ w := by
          by_contra hlt; push Not at hlt
          by_cases hwn : w < n
          · exact hnc (hM_const ⟨w, hwn⟩)
          · exact hnc (by simpa [Nat.add_sub_cancel' (show n ≤ w by omega)] using hH_const ⟨w - n, by omega⟩)
        have hwlt : w - (n + k) < m + 2 := by dsimp [K] at hw; omega
        refine ⟨by dsimp [D0, Circuit.size]; omega, fun Y => ?_⟩
        rw [wires_getD_input C _ w (by rw [rawF_length]; dsimp [K] at hw; omega)]
        dsimp only [D0, Circuit.wires, List.foldl_nil]
        have hweq : w = n + k + (w - (n + k)) := by omega
        conv_rhs => rw [hweq]
        exact (rawF_getD_base ∅ ∅ Y (w - (n + k)) hwlt).symm
      | succ r ih =>
        intro hr
        obtain ⟨Dr, phi, hFanr, hBackr, hNotr, hPosr, hPhir⟩ := ih (by omega)
        have hnot_le_r : notCount Dr ≤ Dr.size := notCount_le_size Dr
        have hmono_not : ((Finset.range r).filter fun q => q ∈ Pure ∧ (gateAt C q).op = GateOp.not).card ≤
            ((Finset.range (r + 1)).filter fun q => q ∈ Pure ∧ (gateAt C q).op = GateOp.not).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
        have hmono_pos : ((Finset.range r).filter fun q => q ∈ Pure ∧ (gateAt C q).op ≠ GateOp.not).card ≤
            ((Finset.range (r + 1)).filter fun q => q ∈ Pure ∧ (gateAt C q).op ≠ GateOp.not).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
        by_cases hrc : isConst (K + r)
        · refine ⟨Dr, phi, hFanr, hBackr, le_trans hNotr hmono_not, le_trans hPosr hmono_pos,
            fun w hw hnc => ?_⟩
          have hwlt : w < K + r := by
            by_contra hge; have : w = K + r := by omega
            subst this; exact hnc hrc
          exact hPhir w hwlt hnc
        · by_cases hrP : r ∈ Pure
          · -- Emit one gate for r ∈ Pure
            have hr_lt : r < C.gates.length := by dsimp [Circuit.size] at hr; omega
            have hgFan := hFan (gateAt C r) (by
              dsimp only [gateAt]; rw [List.getD_eq_getElem _ _ hr_lt]; exact List.getElem_mem hr_lt)
            have hall_nc : ∀ a ∈ effInputs (gateAt C r), ¬ isConst a := (Finset.mem_filter.mp hrP).2.2
            let g' : Gate := ⟨(gateAt C r).op, (effInputs (gateAt C r)).map phi⟩
            have hg'Fan : g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
              ⟨hgFan.1, by dsimp [g']; rw [List.length_map]; exact effInputs_length_le_two _ hgFan.2⟩
            have hg'Back : ∀ u ∈ g'.inputs, u < m + 2 + Dr.size := by
              intro u hu; simp only [g', List.mem_map] at hu
              rcases hu with ⟨a, ha, rfl⟩
              exact (hPhir a (hBack r hr_lt a (effInputs_subset _ _ ha)) (hall_nc a ha)).1
            have hpg := push_gate (K := m + 2) Dr hFanr hBackr g' hg'Fan hg'Back
            let Dr' : Circuit := ⟨Dr.gates ++ [g'], 0⟩
            let phi' : Nat → Nat := fun w => if w = K + r then m + 2 + Dr.size else phi w
            refine ⟨Dr', phi', hpg.1, hpg.2.1, ?_, ?_, ?_⟩
            · rw [hpg.2.2.2.1, Finset.range_add_one, Finset.filter_insert]
              by_cases hnot : (gateAt C r).op = GateOp.not
              · have hr_notin : r ∉ (Finset.range r).filter (fun q => q ∈ Pure ∧ (gateAt C q).op = GateOp.not) := by simp
                simp only [g', hnot, hrP, and_self, ↓reduceIte, Finset.card_insert_of_notMem hr_notin]; omega
              · simp only [g', hnot, and_false, ↓reduceIte, Nat.add_zero]; exact hNotr
            · rw [hpg.2.2.1, hpg.2.2.2.1, Finset.range_add_one, Finset.filter_insert]
              by_cases hnot : (gateAt C r).op = GateOp.not
              · simp only [g', hnot, ↓reduceIte]; rw [if_neg (fun h => h.2 rfl)]; omega
              · have hr_notin : r ∉ (Finset.range r).filter (fun q => q ∈ Pure ∧ (gateAt C q).op ≠ GateOp.not) := by simp
                simp only [g', hnot, ↓reduceIte, Nat.add_zero]
                rw [if_pos ⟨hrP, hnot⟩, Finset.card_insert_of_notMem hr_notin]; omega
            · intro w hw hnc
              dsimp only [phi']
              by_cases hweq : w = K + r
              · subst hweq; rw [if_pos rfl]
                refine ⟨by rw [hpg.2.2.1]; omega, fun Y => ?_⟩
                rw [hpg.2.2.2.2.2 (baseF Y) (baseF_length Y),
                  wires_gate_eval C hBack _ (rawF_length _ _ _) r hr_lt]
                conv_rhs => rw [effInputs_eval]
                dsimp only [g']; rw [List.map_map]
                congr 1
                refine List.map_congr_left fun a ha => ?_
                exact (hPhir a (hBack r hr_lt a (effInputs_subset _ _ ha)) (hall_nc a ha)).2 Y
              · rw [if_neg hweq]
                have hwlt : w < K + r := by omega
                obtain ⟨h1, h2⟩ := hPhir w hwlt hnc
                refine ⟨by rw [hpg.2.2.1]; omega, fun Y => ?_⟩
                rw [hpg.2.2.2.2.1 (baseF Y) (baseF_length Y) (phi w) h1, h2 Y]
          · -- r ∈ Bridge!
            have hrB : r ∈ Bridge := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrc, ?_⟩
              by_contra hno; push Not at hno
              exact hrP (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrc, hno⟩)
            obtain ⟨_, ⟨b0, hb0_mem, hb0_nc, hb0_eq⟩, _⟩ := hbridge_struct r hrB
            have hb0_lt : b0 < K + r := hBack r (by dsimp [Circuit.size] at hr; omega) b0 (effInputs_subset _ _ hb0_mem)
            let phi' : Nat → Nat := fun w => if w = K + r then phi b0 else phi w
            refine ⟨Dr, phi', hFanr, hBackr, le_trans hNotr hmono_not, le_trans hPosr hmono_pos,
              fun w hw hnc => ?_⟩
            dsimp only [phi']
            by_cases hweq : w = K + r
            · subst hweq; rw [if_pos rfl]
              obtain ⟨h1, h2⟩ := hPhir b0 hb0_lt hb0_nc
              exact ⟨h1, fun Y => by rw [h2 Y, ← hb0_eq Y]⟩
            · rw [if_neg hweq]
              exact hPhir w (by omega) hnc
    obtain ⟨DC, phi, hFanD, hBackD, hNotD_card, hPosD_card, hPhiC⟩ := hbuildD C.size le_rfl
    let D : Circuit := ⟨DC.gates, phi C.output⟩
    obtain ⟨houtD, hDeval⟩ := hPhiC C.output hout hout_c
    -- Bound notCount D ≤ notCount C and (D.size - notCount D) + Vpos.card + Vbr.card ≤ C.size - notCount C
    have hnotD_le : notCount D ≤ notCount C := by
      change notCount DC ≤ notCount C
      conv_rhs => rw [notCount_eq_card_filter]
      refine le_trans hNotD_card (Finset.card_le_card ?_)
      intro q hq; simp only [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.2⟩
    have hposD_add : (D.size - notCount D) + Vpos.card + Vbr.card ≤ C.size - notCount C := by
      change (DC.size - notCount DC) + Vpos.card + Vbr.card ≤ C.size - notCount C
      let Ppos := (Finset.range C.size).filter fun q => q ∈ Pure ∧ (gateAt C q).op ≠ GateOp.not
      have hd1 : Disjoint Ppos (Vpos ∪ Vbr) := by
        rw [Finset.disjoint_left]; intro q h1 h2
        have hqP : q ∈ Pure := (Finset.mem_filter.mp h1).2.1
        rcases Finset.mem_union.mp h2 with hp | hb
        · exact (Finset.mem_filter.mp hqP).2.1 (Finset.mem_filter.mp hp).2.2.1
        · obtain ⟨a, ha, hac⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.2
          exact (Finset.mem_filter.mp hqP).2.2 a ha hac
      have hsub : Ppos ∪ (Vpos ∪ Vbr) ⊆ (Finset.range C.size).filter fun q => (gateAt C q).op ≠ GateOp.not :=
        Finset.union_subset (fun q hq => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2.2⟩)
          hpb_sub_pos
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hdisj_pb, ← posCount_eq_card_filter] at hcard
      change DC.size - notCount DC ≤ Ppos.card at hPosD_card
      omega
    have hnot_le_D : notCount D ≤ D.size := notCount_le_size D
    have hnot_le_C : notCount C ≤ C.size := notCount_le_size C
    have hf_eq : ∀ Y : Finset (Fin m), D.eval (baseF Y) = f Y := fun Y => hDeval Y
    have hnonconst : ∃ Y Z : Finset (Fin m), D.eval (baseF Y) ≠ D.eval (baseF Z) := by
      by_contra hconst; push Not at hconst
      apply hout_c; intro Y Z
      have h1 := hconst Y Z
      rwa [hf_eq Y, hf_eq Z] at h1
    refine ⟨D, S, T, ⟨hFanD, hBackD, houtD⟩, hnonconst,
      fun a ha => by dsimp only; rw [hf_eq a.1]; exact hag a ha,
      by omega, by omega, by omega, ?_, ?_⟩
    · have hfeq : (P.filter fun z => D.eval (baseF z.2) = false ∧ Disjoint z.1 S) =
          (P.filter fun z => f z.2 = false ∧ Disjoint z.1 S) := by ext z; simp [hf_eq]
      rw [hfeq]; exact hmiss
    · have hfeq : (Q.filter fun z => D.eval (baseF z.2) = true ∧ Disjoint z.1 T) =
          (Q.filter fun z => f z.2 = true ∧ Disjoint z.1 T) := by ext z; simp [hf_eq]
      rw [hfeq]; exact hextra

/-! ### Part 5: Wrapper Matching Target Statement Exactly -/

lemma card_filter_congr_inst {α : Type*} (s : Finset α) (p q : α → Prop)
    (dp : DecidablePred p) (dq : DecidablePred q) (h : ∀ a ∈ s, p a ↔ q a) :
    (@Finset.filter α p dp s).card = (@Finset.filter α q dq s).card := by
  congr 1; ext a
  rw [@Finset.mem_filter α p dp s a, @Finset.mem_filter α q dq s a]
  exact and_congr_right (h a)

theorem solve_1355 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
  C.output < n+2+C.size
let neg := PEqualNP.NotBracket.notCount
let pos := fun C : PEqualNP.CircuitLowerBounds.Circuit => C.size - neg C
∀ (n k m : Nat) (A : Finset (Finset (Fin m) × Bool))
    (P : Finset (Finset (Fin n) × Finset (Fin m))) (Q : Finset (Finset (Fin k) × Finset (Fin m))),
  let base := fun Y : Finset (Fin m) => List.ofFn (fun i : Fin m => decide (i ∈ Y)) ++ [false,true]
  let raw := fun (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)) =>
    List.ofFn (fun i : Fin n => decide (i ∈ M)) ++
    List.ofFn (fun i : Fin k => decide (i ∉ H)) ++ base Y
  let agrees := fun (f : Finset (Fin m) → Bool) => ∀ a ∈ A, f a.1 = a.2
  let miss := fun (f : Finset (Fin m) → Bool) (S : Finset (Fin n)) =>
    (P.filter (fun z => f z.2 = false ∧ Disjoint z.1 S)).card
  let extra := fun (f : Finset (Fin m) → Bool) (T : Finset (Fin k)) =>
    (Q.filter (fun z => f z.2 = true ∧ Disjoint z.1 T)).card
  ∀ b p s e₀ e₁ : Nat,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, valid (n+k+m) C ∧
      neg C ≤ b ∧ pos C ≤ p ∧ C.size ≤ s ∧
      agrees (fun Y => C.eval (raw ∅ ∅ Y)) ∧
      (P.filter (fun z => C.eval (raw z.1 ∅ z.2) = false)).card ≤ e₀ ∧
      (Q.filter (fun z => C.eval (raw ∅ z.1 z.2) = true)).card ≤ e₁) ↔
    (agrees (fun _ => false) ∧ ∃ S, S.card-1 ≤ p ∧ S.card-1 ≤ s ∧ miss (fun _ => false) S ≤ e₀) ∨
    (agrees (fun _ => true) ∧ ∃ T, T.card-1 ≤ p ∧ T.card-1 ≤ s ∧ extra (fun _ => true) T ≤ e₁) ∨
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (S : Finset (Fin n)) (T : Finset (Fin k)),
      let f := fun Y => D.eval (base Y)
      valid m D ∧ (∃ Y Z, f Y ≠ f Z) ∧ agrees f ∧ neg D ≤ b ∧
      pos D + S.card + T.card ≤ p ∧ D.size + S.card + T.card ≤ s ∧
      miss f S ≤ e₀ ∧ extra f T ≤ e₁ := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro valid neg pos n k m A P Q base raw agrees miss extra b p s e₀ e₁
  have hbase_eq : ∀ Y : Finset (Fin m), base Y = baseF Y := fun Y => by
    dsimp only [base, baseF]
    refine congrArg (· ++ [false, true]) (congrArg List.ofFn (funext fun i => ?_))
    exact decide_eq_decide.mpr Iff.rfl
  have hraw_eq : ∀ (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)),
      raw M H Y = rawF M H Y := fun M H Y => by
    dsimp only [raw, rawF]
    rw [hbase_eq Y]
    refine congrArg (· ++ baseF Y) (congrArg₂ (· ++ ·)
      (congrArg List.ofFn (funext fun i => decide_eq_decide.mpr Iff.rfl))
      (congrArg List.ofFn (funext fun i => decide_eq_decide.mpr Iff.rfl)))
  constructor
  · rintro ⟨C, hval, hb, hp, hs, hag, hP, hQ⟩
    have hag' : ∀ a ∈ A, C.eval (rawF (n := n) (k := k) ∅ ∅ a.1) = a.2 := fun a ha => by
      rw [← hraw_eq]; exact hag a ha
    rcases lhs_to_rhs_core A P Q b p s e₀ e₁ C hval.1 hval.2.1 hval.2.2 hb hp hs hag'
        (le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by rw [hraw_eq]) hP)
        (le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by rw [hraw_eq]) hQ)
      with ⟨hf, S, hSp, hSs, hm⟩ | ⟨ht, T, hTp, hTs, hx⟩ | ⟨D, S, T, hDv, hnc, hDag, hDb, hDp, hDs, hm, hx⟩
    · left; refine ⟨hf, S, hSp, hSs, ?_⟩
      dsimp only [miss]
      exact le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by simp) hm
    · right; left; refine ⟨ht, T, hTp, hTs, ?_⟩
      dsimp only [extra]
      exact le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by simp) hx
    · right; right
      refine ⟨D, S, T, hDv, ?_, ?_, hDb, hDp, hDs, ?_, ?_⟩
      · rcases hnc with ⟨Y, Z, hne⟩; exact ⟨Y, Z, by simpa only [hbase_eq] using hne⟩
      · intro a ha; dsimp only; rw [hbase_eq]; exact hDag a ha
      · dsimp only [miss]
        exact le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by rw [hbase_eq]) hm
      · dsimp only [extra]
        exact le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by rw [hbase_eq]) hx
  · rintro (⟨hf, S, hSp, hSs, hm⟩ | ⟨ht, T, hTp, hTs, hx⟩ | ⟨D, S, T, hDv, _, hDag, hDb, hDp, hDs, hm, hx⟩)
    · obtain ⟨C, hCv, hCb, hCp, hCs, hCag, hCP, hCQ⟩ :=
        rhs_to_lhs_case1 A P Q b p s e₀ e₁ hf S hSp hSs
          (le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by simp) hm)
      refine ⟨C, hCv, hCb, hCp, hCs, fun a ha => by dsimp only; rw [hraw_eq]; exact hCag a ha,
        le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by rw [hraw_eq]) hCP,
        le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by rw [hraw_eq]) hCQ⟩
    · obtain ⟨C, hCv, hCb, hCp, hCs, hCag, hCP, hCQ⟩ :=
        rhs_to_lhs_case2 A P Q b p s e₀ e₁ ht T hTp hTs
          (le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by simp) hx)
      refine ⟨C, hCv, hCb, hCp, hCs, fun a ha => by dsimp only; rw [hraw_eq]; exact hCag a ha,
        le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by rw [hraw_eq]) hCP,
        le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by rw [hraw_eq]) hCQ⟩
    · have hDag' : ∀ a ∈ A, D.eval (baseF a.1) = a.2 := fun a ha => by
        rw [← hbase_eq]; exact hDag a ha
      obtain ⟨C, hCv, hCb, hCp, hCs, hCag, hCP, hCQ⟩ :=
        rhs_to_lhs_case3 A P Q b p s e₀ e₁ D S T hDv.1 hDv.2.1 hDv.2.2 hDag' hDb hDp hDs
          (le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by dsimp only; rw [hbase_eq]) hm)
          (le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by dsimp only; rw [hbase_eq]) hx)
      refine ⟨C, hCv, hCb, hCp, hCs, fun a ha => by dsimp only; rw [hraw_eq]; exact hCag a ha,
        le_of_eq_of_le (card_filter_congr_inst P _ _ _ _ fun z _ => by rw [hraw_eq]) hCP,
        le_of_eq_of_le (card_filter_congr_inst Q _ _ _ _ fun z _ => by rw [hraw_eq]) hCQ⟩

end PEqualNP.Outside.L_lib_1355

theorem PEqualNP.Outside.L_lib_1355 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
  C.output < n+2+C.size
let neg := PEqualNP.NotBracket.notCount
let pos := fun C : PEqualNP.CircuitLowerBounds.Circuit => C.size - neg C
∀ (n k m : Nat) (A : Finset (Finset (Fin m) × Bool))
    (P : Finset (Finset (Fin n) × Finset (Fin m))) (Q : Finset (Finset (Fin k) × Finset (Fin m))),
  let base := fun Y : Finset (Fin m) => List.ofFn (fun i : Fin m => decide (i ∈ Y)) ++ [false,true]
  let raw := fun (M : Finset (Fin n)) (H : Finset (Fin k)) (Y : Finset (Fin m)) =>
    List.ofFn (fun i : Fin n => decide (i ∈ M)) ++
    List.ofFn (fun i : Fin k => decide (i ∉ H)) ++ base Y
  let agrees := fun (f : Finset (Fin m) → Bool) => ∀ a ∈ A, f a.1 = a.2
  let miss := fun (f : Finset (Fin m) → Bool) (S : Finset (Fin n)) =>
    (P.filter (fun z => f z.2 = false ∧ Disjoint z.1 S)).card
  let extra := fun (f : Finset (Fin m) → Bool) (T : Finset (Fin k)) =>
    (Q.filter (fun z => f z.2 = true ∧ Disjoint z.1 T)).card
  ∀ b p s e₀ e₁ : Nat,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, valid (n+k+m) C ∧
      neg C ≤ b ∧ pos C ≤ p ∧ C.size ≤ s ∧
      agrees (fun Y => C.eval (raw ∅ ∅ Y)) ∧
      (P.filter (fun z => C.eval (raw z.1 ∅ z.2) = false)).card ≤ e₀ ∧
      (Q.filter (fun z => C.eval (raw ∅ z.1 z.2) = true)).card ≤ e₁) ↔
    (agrees (fun _ => false) ∧ ∃ S, S.card-1 ≤ p ∧ S.card-1 ≤ s ∧ miss (fun _ => false) S ≤ e₀) ∨
    (agrees (fun _ => true) ∧ ∃ T, T.card-1 ≤ p ∧ T.card-1 ≤ s ∧ extra (fun _ => true) T ≤ e₁) ∨
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (S : Finset (Fin n)) (T : Finset (Fin k)),
      let f := fun Y => D.eval (base Y)
      valid m D ∧ (∃ Y Z, f Y ≠ f Z) ∧ agrees f ∧ neg D ≤ b ∧
      pos D + S.card + T.card ≤ p ∧ D.size + S.card + T.card ≤ s ∧
      miss f S ≤ e₀ ∧ extra f T ≤ e₁ :=
  PEqualNP.Outside.L_lib_1355.solve_1355
