import Mathlib
import PEqualNP.Defs

-- Circuit builder, NOT-code lower-bound tool and monotone synthesis adapted from
-- lean/PEqualNP/Outside/L_lib_1281.lean (merged on main, Apache-2.0).

namespace PEqualNP.Outside.L_lib_1398_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section CircuitBasics

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_take {α : Type*} (l : List α) (m k : ℕ) (d : α) (hk : k < m) :
    (l.take m).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

lemma getD_drop {α : Type*} (l : List α) (m k : ℕ) (d : α) :
    (l.drop m).getD k d = l.getD (m + k) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_mem {α : Type*} (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma notCount_le_length (gs : List Gate) (o : ℕ) :
    notCount ⟨gs, o⟩ ≤ gs.length :=
  List.length_filter_le _ _

def nonNot (gs : List Gate) : ℕ := gs.length - notCount ⟨gs, 0⟩

lemma nonNot_nil : nonNot [] = 0 := rfl

lemma nonNot_append (gs1 gs2 : List Gate) :
    nonNot (gs1 ++ gs2) = nonNot gs1 + nonNot gs2 := by
  dsimp only [nonNot]
  rw [List.length_append, notCount_append]
  have h1 := notCount_le_length gs1 0
  have h2 := notCount_le_length gs2 0
  omega

lemma notCount_singleton_and (ins : List ℕ) : notCount ⟨[⟨GateOp.and, ins⟩], 0⟩ = 0 := by
  simp [notCount]

lemma notCount_singleton_or (ins : List ℕ) : notCount ⟨[⟨GateOp.or, ins⟩], 0⟩ = 0 := by
  simp [notCount]

lemma notCount_singleton_not (ins : List ℕ) : notCount ⟨[⟨GateOp.not, ins⟩], 0⟩ = 1 := by
  simp [notCount]

lemma nonNot_singleton_and (ins : List ℕ) : nonNot [⟨GateOp.and, ins⟩] = 1 := by
  simp [nonNot, notCount_singleton_and]

lemma nonNot_singleton_or (ins : List ℕ) : nonNot [⟨GateOp.or, ins⟩] = 1 := by
  simp [nonNot, notCount_singleton_or]

lemma nonNot_singleton_not (ins : List ℕ) : nonNot [⟨GateOp.not, ins⟩] = 0 := by
  simp [nonNot, notCount_singleton_not]

lemma fanInTwo_nil (o : ℕ) : FanInTwo ⟨[], o⟩ := by
  intro g hg; cases hg

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma readsBack_nil (m o : ℕ) : ReadsBack m ⟨[], o⟩ := by
  intro j hj; cases hj

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

def inpVec {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length {n : ℕ} (x : Finset (Fin n)) : (inpVec x).length = n + 2 := by
  simp [inpVec]

lemma inpVec_getD_fin {n : ℕ} (x : Finset (Fin n)) (i : Fin n) :
    (inpVec x).getD i.val false = decide (i ∈ x) := by
  dsimp only [inpVec]
  rw [getD_append_left _ _ i.val false (by simp [i.isLt])]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma inpVec_getD_false {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD n false = false := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ n false (by simp)]
  simp

lemma inpVec_getD_true {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD (n + 1) false = true := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ (n + 1) false (by simp)]
  have hsub : n + 1 - n = 1 := by omega
  simp [hsub]

lemma bool_le_iff (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma not_true_le_false (h : (true : Bool) ≤ false) : False := by
  have := (bool_le_iff true false).mp h rfl
  cases this

lemma inpVec_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) (k : ℕ) :
    (inpVec u).getD k false ≤ (inpVec v).getD k false := by
  by_cases hk1 : k < n
  · have hu := inpVec_getD_fin u ⟨k, hk1⟩
    have hv := inpVec_getD_fin v ⟨k, hk1⟩
    dsimp only at hu hv
    rw [hu, hv, bool_le_iff]
    intro h
    exact decide_eq_true (huv (of_decide_eq_true h))
  · by_cases hk2 : k = n
    · subst hk2; rw [inpVec_getD_false, inpVec_getD_false]
    · by_cases hk3 : k = n + 1
      · subst hk3; rw [inpVec_getD_true, inpVec_getD_true]
      · rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]
        rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]

lemma all_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).all id ≤ (l.map g).all id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).all id <;> cases h2 : (tl.map g).all id <;> simp_all

lemma any_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).any id ≤ (l.map g).any id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).any id <;> cases h2 : (tl.map g).any id <;> simp_all

lemma not_headD_anti (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (!((l.map g).headD false)) ≤ (!((l.map f).headD false)) := by
  cases l with
  | nil => simp
  | cons a tl =>
    simp only [List.map_cons, List.headD_cons]
    have ha := h a (List.mem_cons_self ..)
    cases hfa : f a <;> cases hga : g a <;> simp_all

end CircuitBasics

section LowerBound

def evalNotCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := evalNotCode gs (w ++ [v])
    match g.op with
    | GateOp.not => (if v then 2 ^ (notCount ⟨gs, 0⟩) else 0) + rest
    | _ => rest

lemma evalNotCode_lt (gs : List Gate) (w : List Bool) :
    evalNotCode gs w < 2 ^ (notCount ⟨gs, 0⟩) := by
  induction gs generalizing w with
  | nil => simp [evalNotCode, notCount]
  | cons g gs ih =>
    dsimp only [evalNotCode]
    cases hg : g.op with
    | not =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ + 1 := by simp [notCount, hg]
      rw [hnc, pow_succ]
      cases hv : GateOp.not.eval (g.inputs.map fun i => w.getD i false) with
      | false =>
        have hrest := ih (w ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        omega
      | true =>
        have hrest := ih (w ++ [true])
        simp only [↓reduceIte]
        omega
    | and =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | or =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | mod k =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | maj =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _

lemma append_singleton_getD_mono (w1 w2 : List Bool) (v1 v2 : Bool)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false ≤ w2.getD i false)
    (hv : v1 ≤ v2) (i : ℕ) :
    (w1 ++ [v1]).getD i false ≤ (w2 ++ [v2]).getD i false := by
  by_cases hi : i < w1.length
  · rw [getD_append_left w1 [v1] i false hi]
    rw [getD_append_left w2 [v2] i false (by omega)]
    exact hw i
  · rw [getD_append_right w1 [v1] i false (by omega)]
    rw [getD_append_right w2 [v2] i false (by omega)]
    rw [hlen]
    by_cases h0 : i - w2.length = 0
    · rw [h0]; simpa using hv
    · rw [getD_ge_length [v1] _ false (by simp; omega)]
      rw [getD_ge_length [v2] _ false (by simp; omega)]

lemma evalNotCode_dichotomy (gs : List Gate) (w1 w2 : List Bool)
    (hfit : FanInTwo ⟨gs, 0⟩)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false ≤ w2.getD i false) :
    evalNotCode gs w2 < evalNotCode gs w1 ∨
    (evalNotCode gs w2 = evalNotCode gs w1 ∧
      ∀ i, (wiresFrom gs w1).getD i false ≤ (wiresFrom gs w2).getD i false) := by
  induction gs generalizing w1 w2 with
  | nil => exact Or.inr ⟨rfl, hw⟩
  | cons g gs ih =>
    have hgfit := hfit g (List.mem_cons_self ..)
    have hgsfit : FanInTwo ⟨gs, 0⟩ := fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')
    dsimp only [evalNotCode, wiresFrom_cons]
    rcases hgfit.1 with h_and | h_or | h_not
    · rw [h_and]
      have hv : GateOp.and.eval (g.inputs.map fun i => w1.getD i false) ≤
          GateOp.and.eval (g.inputs.map fun i => w2.getD i false) :=
        all_map_mono g.inputs _ _ (fun i _ => hw i)
      exact ih _ _ hgsfit (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [h_or]
      have hv : GateOp.or.eval (g.inputs.map fun i => w1.getD i false) ≤
          GateOp.or.eval (g.inputs.map fun i => w2.getD i false) :=
        any_map_mono g.inputs _ _ (fun i _ => hw i)
      exact ih _ _ hgsfit (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [h_not]
      set v1 := GateOp.not.eval (g.inputs.map fun i => w1.getD i false)
      set v2 := GateOp.not.eval (g.inputs.map fun i => w2.getD i false)
      have hvanti : v2 ≤ v1 := not_headD_anti g.inputs _ _ (fun i _ => hw i)
      cases hv1 : v1 <;> cases hv2 : v2
      · have hw' := append_singleton_getD_mono w1 w2 false false hlen hw (le_refl false)
        rcases ih (w1 ++ [false]) (w2 ++ [false]) hgsfit (by simp [hlen]) hw' with hlt | ⟨heq, hle⟩
        · left; simpa using hlt
        · right; exact ⟨by simpa using heq, hle⟩
      · rw [hv1, hv2] at hvanti
        exact absurd hvanti not_true_le_false
      · left
        have hlt2 := evalNotCode_lt gs (w2 ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        omega
      · have hw' := append_singleton_getD_mono w1 w2 true true hlen hw (le_refl true)
        rcases ih (w1 ++ [true]) (w2 ++ [true]) hgsfit (by simp [hlen]) hw' with hlt | ⟨heq, hle⟩
        · left; simp only [↓reduceIte]; omega
        · right; exact ⟨by simp only [↓reduceIte, heq], hle⟩

end LowerBound

section Builder

def Extends (base : ℕ) (gs1 gs2 : List Gate) : Prop :=
  ∃ extra : List Gate, gs2 = gs1 ++ extra ∧ FanInTwo ⟨extra, 0⟩ ∧
    ReadsBack (base + gs1.length) ⟨extra, 0⟩

lemma Extends.refl (base : ℕ) (gs : List Gate) : Extends base gs gs :=
  ⟨[], by simp, fanInTwo_nil 0, readsBack_nil _ 0⟩

lemma Extends.trans {base : ℕ} {gs1 gs2 gs3 : List Gate}
    (h1 : Extends base gs1 gs2) (h2 : Extends base gs2 gs3) :
    Extends base gs1 gs3 := by
  rcases h1 with ⟨e1, rfl, hf1, hr1⟩
  rcases h2 with ⟨e2, rfl, hf2, hr2⟩
  refine ⟨e1 ++ e2, by rw [List.append_assoc], fanInTwo_append hf1 hf2, ?_⟩
  have hr2' : ReadsBack ((base + gs1.length) + e1.length) ⟨e2, 0⟩ := by
    simpa [List.length_append, Nat.add_assoc] using hr2
  exact readsBack_append hr1 hr2'

lemma Extends.length_le {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl, _, _⟩; simp

lemma Extends.wire_eq {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2)
    (w : List Bool) (hw : w.length = base) (i : ℕ) (hi : i < base + gs1.length) :
    (wiresFrom gs2 w).getD i false = (wiresFrom gs1 w).getD i false := by
  rcases h with ⟨e, rfl, _, _⟩
  rw [wiresFrom_append]
  exact wiresFrom_getD_lt e (wiresFrom gs1 w) i (by rw [wiresFrom_length, hw]; exact hi)

def emitAnd (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], base + gs.length)

def emitOr (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], base + gs.length)

def emitNot (base : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], base + gs.length)

lemma emitAnd_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitAnd base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [emitAnd]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.and, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append, notCount_singleton_and, add_zero]
  · rw [nonNot_append, nonNot_singleton_and]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitOr base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) := by
  dsimp only [emitOr]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.or, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append, notCount_singleton_or, add_zero]
  · rw [nonNot_append, nonNot_singleton_or]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitNot_spec (base : ℕ) (gs : List Gate) (a : ℕ)
    (ha : a < base + gs.length) :
    let r := emitNot base gs a
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧
    nonNot r.1 = nonNot gs ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false = !((wiresFrom gs w).getD a false) := by
  dsimp only [emitNot]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.not, [a]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_singleton] at hi
      subst hi; omega
  · rw [notCount_append, notCount_singleton_not]
  · rw [nonNot_append, nonNot_singleton_not, add_zero]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

def mapAndWith (base c : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, z :: zs =>
    let r := emitAnd base gs c z
    let rest := mapAndWith base c r.1 zs
    (rest.1, r.2 :: rest.2)

lemma mapAndWith_spec (base c : ℕ) (zs : List ℕ) (gs : List Gate)
    (hc : c < base + gs.length) (hzs : ∀ i ∈ zs, i < base + gs.length) :
    let r := mapAndWith base c gs zs
    Extends base gs r.1 ∧
    r.2.length = zs.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + zs.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < zs.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          ((wiresFrom gs w).getD c false && (wiresFrom gs w).getD (zs.getD t 0) false) := by
  induction zs generalizing gs with
  | nil =>
    dsimp only [mapAndWith]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons z zs ih =>
    dsimp only [mapAndWith]
    have hz : z < base + gs.length := hzs z (List.mem_cons_self ..)
    have hzs' : ∀ i ∈ zs, i < base + gs.length := fun i hi => hzs i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs c z with hr1
    have h1 := emitAnd_spec base gs c z hc hz
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set rest := mapAndWith base c r1.1 zs with hrest
    have h2 := ih r1.1 (by omega) (fun i hi => lt_of_lt_of_le (hzs' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro w hw t ht
      cases t with
      | zero =>
        change (wiresFrom rest.1 w).getD r1.2 false = _
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
      | succ t' =>
        have ht' : t' < zs.length := by simp at ht; omega
        change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
        rw [hval2 w hw t' ht', hext1.wire_eq w hw c hc,
            hext1.wire_eq w hw _ (hzs' _ (getD_mem zs t' 0 ht'))]; rfl

def mapOrWith (base c : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, z :: zs =>
    let r := emitOr base gs c z
    let rest := mapOrWith base c r.1 zs
    (rest.1, r.2 :: rest.2)

lemma mapOrWith_spec (base c : ℕ) (zs : List ℕ) (gs : List Gate)
    (hc : c < base + gs.length) (hzs : ∀ i ∈ zs, i < base + gs.length) :
    let r := mapOrWith base c gs zs
    Extends base gs r.1 ∧
    r.2.length = zs.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + zs.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < zs.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          ((wiresFrom gs w).getD c false || (wiresFrom gs w).getD (zs.getD t 0) false) := by
  induction zs generalizing gs with
  | nil =>
    dsimp only [mapOrWith]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons z zs ih =>
    dsimp only [mapOrWith]
    have hz : z < base + gs.length := hzs z (List.mem_cons_self ..)
    have hzs' : ∀ i ∈ zs, i < base + gs.length := fun i hi => hzs i (List.mem_cons_of_mem _ hi)
    set r1 := emitOr base gs c z with hr1
    have h1 := emitOr_spec base gs c z hc hz
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set rest := mapOrWith base c r1.1 zs with hrest
    have h2 := ih r1.1 (by omega) (fun i hi => lt_of_lt_of_le (hzs' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro w hw t ht
      cases t with
      | zero =>
        change (wiresFrom rest.1 w).getD r1.2 false = _
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
      | succ t' =>
        have ht' : t' < zs.length := by simp at ht; omega
        change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
        rw [hval2 w hw t' ht', hext1.wire_eq w hw c hc,
            hext1.wire_eq w hw _ (hzs' _ (getD_mem zs t' 0 ht'))]; rfl

def emitAndList (base oneWire : ℕ) : List Gate → List ℕ → List Gate × ℕ
  | gs, [] => (gs, oneWire)
  | gs, w :: ws =>
    let r := emitAnd base gs oneWire w
    emitAndList base r.2 r.1 ws

lemma emitAndList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (oneWire : ℕ) (gs : List Gate),
      oneWire < base + gs.length →
      (∀ i ∈ ws, i < base + gs.length) →
      let r := emitAndList base oneWire gs ws
      Extends base gs r.1 ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + ws.length ∧
      ∀ (w : List Bool), w.length = base →
        (wiresFrom r.1 w).getD r.2 false =
          ((wiresFrom gs w).getD oneWire false && ws.all (fun i => (wiresFrom gs w).getD i false)) := by
  intro ws
  induction ws with
  | nil =>
    intro oneWire gs ho _
    dsimp only [emitAndList]
    refine ⟨Extends.refl base gs, ho, rfl, by omega, fun _ _ => by simp⟩
  | cons a ws ih =>
    intro oneWire gs ho hws
    dsimp only [emitAndList]
    have ha : a < base + gs.length := hws a (List.mem_cons_self ..)
    have hws' : ∀ i ∈ ws, i < base + gs.length := fun i hi => hws i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs oneWire a with hr1
    have h1 := emitAnd_spec base gs oneWire a ho ha
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    have h2 := ih r1.2 r1.1 hlt1 (fun i hi => lt_of_lt_of_le (hws' i hi) (by omega))
    rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    refine ⟨hext1.trans hext2, hlt2, by omega, by simp only [List.length_cons]; omega, ?_⟩
    intro w hw
    rw [hval2 w hw, hval1 w hw]
    simp only [List.all_cons]
    have hcongr_aux : ∀ ws' : List ℕ, (∀ i ∈ ws', i < base + gs.length) →
        ws'.all (fun i => (wiresFrom r1.1 w).getD i false) =
        ws'.all (fun i => (wiresFrom gs w).getD i false) := by
      intro ws'
      induction ws' with
      | nil => intro _; rfl
      | cons b bs ihb =>
        intro hbs
        simp only [List.all_cons]
        rw [hext1.wire_eq w hw b (hbs b (List.mem_cons_self ..))]
        congr 1
        exact ihb (fun i hi => hbs i (List.mem_cons_of_mem _ hi))
    rw [hcongr_aux ws hws', Bool.and_assoc]

def emitOrList (base zeroWire : ℕ) : List Gate → List ℕ → List Gate × ℕ
  | gs, [] => (gs, zeroWire)
  | gs, w :: ws =>
    let r := emitOr base gs zeroWire w
    emitOrList base r.2 r.1 ws

lemma emitOrList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (zeroWire : ℕ) (gs : List Gate),
      zeroWire < base + gs.length →
      (∀ i ∈ ws, i < base + gs.length) →
      let r := emitOrList base zeroWire gs ws
      Extends base gs r.1 ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + ws.length ∧
      ∀ (w : List Bool), w.length = base →
        (wiresFrom r.1 w).getD r.2 false =
          ((wiresFrom gs w).getD zeroWire false || ws.any (fun i => (wiresFrom gs w).getD i false)) := by
  intro ws
  induction ws with
  | nil =>
    intro zeroWire gs hz _
    dsimp only [emitOrList]
    refine ⟨Extends.refl base gs, hz, rfl, by omega, fun _ _ => by simp⟩
  | cons a ws ih =>
    intro zeroWire gs hz hws
    dsimp only [emitOrList]
    have ha : a < base + gs.length := hws a (List.mem_cons_self ..)
    have hws' : ∀ i ∈ ws, i < base + gs.length := fun i hi => hws i (List.mem_cons_of_mem _ hi)
    set r1 := emitOr base gs zeroWire a with hr1
    have h1 := emitOr_spec base gs zeroWire a hz ha
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    have h2 := ih r1.2 r1.1 hlt1 (fun i hi => lt_of_lt_of_le (hws' i hi) (by omega))
    rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    refine ⟨hext1.trans hext2, hlt2, by omega, by simp only [List.length_cons]; omega, ?_⟩
    intro w hw
    rw [hval2 w hw, hval1 w hw]
    simp only [List.any_cons]
    have hcongr : ws.any (fun i => (wiresFrom r1.1 w).getD i false) =
        ws.any (fun i => (wiresFrom gs w).getD i false) := by
      apply list_any_congr
      intro i hi
      exact hext1.wire_eq w hw i (hws' i hi)
    rw [hcongr, Bool.or_assoc]

def padNots (base zeroWire : ℕ) : List Gate → ℕ → List Gate
  | gs, 0 => gs
  | gs, k + 1 =>
    let r := emitNot base gs zeroWire
    padNots base zeroWire r.1 k

lemma padNots_spec (base zeroWire : ℕ) (hz : zeroWire < base) :
    ∀ (k : ℕ) (gs : List Gate),
      Extends base gs (padNots base zeroWire gs k) ∧
      notCount ⟨padNots base zeroWire gs k, 0⟩ = notCount ⟨gs, 0⟩ + k ∧
      nonNot (padNots base zeroWire gs k) = nonNot gs := by
  intro k
  induction k with
  | zero => intro gs; exact ⟨Extends.refl base gs, by simp [padNots], rfl⟩
  | succ k ih =>
    intro gs
    dsimp only [padNots]
    have h1 := emitNot_spec base gs zeroWire (by omega)
    rcases h1 with ⟨hext1, _, hnc1, hnn1, _⟩
    have h2 := ih (emitNot base gs zeroWire).1
    exact ⟨hext1.trans h2.1, by omega, by omega⟩

end Builder

section PairEval

def bits (l : ℕ) (x : Finset (Fin l)) : List Bool :=
  List.ofFn (fun i : Fin l => decide (i ∈ x))

def pairVec (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) : List Bool :=
  bits n x ++ bits m z ++ [false, true]

lemma pairVec_length (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairVec n m x z).length = n + m + 2 := by
  simp [pairVec, bits]; omega

lemma pairVec_getD_left (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) (i : Fin n) :
    (pairVec n m x z).getD i.val false = decide (i ∈ x) := by
  dsimp only [pairVec, bits]
  rw [getD_append_left _ _ i.val false (by simp; omega)]
  rw [getD_append_left _ _ i.val false (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma pairVec_getD_right (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) (j : Fin m) :
    (pairVec n m x z).getD (n + j.val) false = decide (j ∈ z) := by
  dsimp only [pairVec, bits]
  rw [getD_append_left _ _ (n + j.val) false (by simp)]
  rw [getD_append_right _ _ (n + j.val) false (by simp)]
  have hlen : (List.ofFn fun i : Fin n => decide (i ∈ x)).length = n := by simp
  rw [hlen, Nat.add_sub_cancel_left]
  simp [List.getD_eq_getElem?_getD, j.isLt]

lemma pairVec_getD_false (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairVec n m x z).getD (n + m) false = false := by
  dsimp only [pairVec, bits]
  rw [getD_append_right _ _ (n + m) false (by simp)]
  have hlen : (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++
      List.ofFn (fun i : Fin m => decide (i ∈ z))).length = n + m := by simp
  rw [hlen, Nat.sub_self]
  rfl

lemma pairVec_getD_true (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairVec n m x z).getD (n + m + 1) false = true := by
  dsimp only [pairVec, bits]
  rw [getD_append_right _ _ (n + m + 1) false (by simp)]
  have hlen : (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++
      List.ofFn (fun i : Fin m => decide (i ∈ z))).length = n + m := by simp
  rw [hlen, show n + m + 1 - (n + m) = 1 by omega]
  rfl

lemma pairVec_mono {n m : ℕ} {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)}
    (hx : x1 ⊆ x2) (hz : z1 ⊆ z2) (k : ℕ) :
    (pairVec n m x1 z1).getD k false ≤ (pairVec n m x2 z2).getD k false := by
  by_cases h1 : k < n
  · have a := pairVec_getD_left n m x1 z1 ⟨k, h1⟩
    have b := pairVec_getD_left n m x2 z2 ⟨k, h1⟩
    dsimp only at a b
    rw [a, b, bool_le_iff]
    intro h; exact decide_eq_true (hx (of_decide_eq_true h))
  · by_cases h2 : k < n + m
    · have hk' : k - n < m := by omega
      have hkeq : n + (k - n) = k := by omega
      have a := pairVec_getD_right n m x1 z1 ⟨k - n, hk'⟩
      have b := pairVec_getD_right n m x2 z2 ⟨k - n, hk'⟩
      dsimp only at a b
      rw [hkeq] at a b
      rw [a, b, bool_le_iff]
      intro h; exact decide_eq_true (hz (of_decide_eq_true h))
    · by_cases h3 : k = n + m
      · subst h3; rw [pairVec_getD_false, pairVec_getD_false]
      · by_cases h4 : k = n + m + 1
        · subst h4; rw [pairVec_getD_true, pairVec_getD_true]
        · rw [getD_ge_length _ k false (by rw [pairVec_length]; omega)]
          rw [getD_ge_length _ k false (by rw [pairVec_length]; omega)]

lemma wiresFrom_mono (gs : List Gate) (hmono : Monotone2 ⟨gs, 0⟩) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (hw : ∀ i, w1.getD i false ≤ w2.getD i false) (i : ℕ) :
    (wiresFrom gs w1).getD i false ≤ (wiresFrom gs w2).getD i false := by
  induction gs generalizing w1 w2 with
  | nil => exact hw i
  | cons g gs ih =>
    have hg := hmono g (List.mem_cons_self ..)
    have hgs : Monotone2 ⟨gs, 0⟩ := fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    rcases hg.1 with h_and | h_or
    · rw [wiresFrom_cons, wiresFrom_cons]
      have hv : g.op.eval (g.inputs.map fun k => w1.getD k false) ≤
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        rw [h_and]
        exact all_map_mono g.inputs _ _ (fun k _ => hw k)
      exact ih hgs _ _ (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [wiresFrom_cons, wiresFrom_cons]
      have hv : g.op.eval (g.inputs.map fun k => w1.getD k false) ≤
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        rw [h_or]
        exact any_map_mono g.inputs _ _ (fun k _ => hw k)
      exact ih hgs _ _ (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)

lemma notCount_cons (g : Gate) (gs : List Gate) :
    notCount ⟨g :: gs, 0⟩ = notCount ⟨[g], 0⟩ + notCount ⟨gs, 0⟩ := by
  have heq : g :: gs = [g] ++ gs := rfl
  rw [heq, notCount_append]

lemma notCount_pos_of_mem (gs : List Gate) (g : Gate) (hg : g ∈ gs) (hn : g.op = GateOp.not) :
    0 < notCount ⟨gs, 0⟩ := by
  induction gs with
  | nil => cases hg
  | cons a tl ih =>
    rw [notCount_cons]
    simp only [List.mem_cons] at hg
    rcases hg with hga | hg
    · subst hga
      rcases g with ⟨op, ins⟩
      dsimp at hn; subst hn
      rw [notCount_singleton_not]; omega
    · have := ih hg; omega

lemma monotone2_of_fanInTwo_notZero (gs : List Gate) (hfit : FanInTwo ⟨gs, 0⟩)
    (h0 : notCount ⟨gs, 0⟩ = 0) : Monotone2 ⟨gs, 0⟩ := by
  intro g hg
  have hf := hfit g hg
  refine ⟨?_, hf.2⟩
  rcases hf.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (notCount_pos_of_mem gs g hg h) (by omega)

lemma split_first_not : ∀ (gs : List Gate), 0 < notCount ⟨gs, 0⟩ →
    ∃ pre g post, gs = pre ++ g :: post ∧ notCount ⟨pre, 0⟩ = 0 ∧
      g.op = GateOp.not ∧ notCount ⟨gs, 0⟩ = notCount ⟨post, 0⟩ + 1 := by
  intro gs
  induction gs with
  | nil => intro h; simp [notCount] at h
  | cons g gs ih =>
    intro h
    by_cases hn : g.op = GateOp.not
    · refine ⟨[], g, gs, rfl, rfl, hn, ?_⟩
      rcases g with ⟨op, ins⟩
      dsimp at hn; subst hn
      rw [notCount_cons, notCount_singleton_not]; omega
    · have hsing0 : notCount ⟨[g], 0⟩ = 0 := by
        rcases g with ⟨op, ins⟩
        cases ho : op with
        | not => exact absurd ho hn
        | and => exact notCount_singleton_and _
        | or => exact notCount_singleton_or _
        | mod _ => simp [notCount, ho]
        | maj => simp [notCount, ho]
      rw [notCount_cons, hsing0, zero_add] at h
      obtain ⟨pre, g1, post, heq, hpre0, hg1, hcnt⟩ := ih h
      refine ⟨g :: pre, g1, post, by rw [heq]; rfl, ?_, hg1, ?_⟩
      · rw [notCount_cons, hsing0, hpre0]
      · rw [notCount_cons, hsing0, zero_add]; exact hcnt

end PairEval
section MonotoneSynth

noncomputable def emitCube (base oneWire n : ℕ) {m : ℕ} (gs : List Gate)
    (p1 : Finset (Fin n)) (p2 : Finset (Fin m)) : List Gate × ℕ :=
  let ws := (p1.toList.map Fin.val) ++ (p2.toList.map (fun j : Fin m => n + j.val))
  emitAndList base oneWire gs ws

lemma emitCube_spec (n m : ℕ) (base oneWire : ℕ) (hbas : base = n + m + 2)
    (ho : oneWire < base) (gs : List Gate)
    (p1 : Finset (Fin n)) (p2 : Finset (Fin m)) :
    let r := emitCube base oneWire n gs p1 p2
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom r.1 (pairVec n m x z)).getD r.2 false =
        ((pairVec n m x z).getD oneWire false && decide (p1 ⊆ x ∧ p2 ⊆ z)) := by
  dsimp only [emitCube]
  set ws := (p1.toList.map Fin.val) ++ (p2.toList.map (fun j : Fin m => n + j.val))
  have hws : ∀ i ∈ ws, i < base + gs.length := by
    intro i hi
    simp only [ws, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
    · have := a.isLt; omega
    · have := b.isLt; omega
  have h1 := emitAndList_spec base ws oneWire gs (by omega) hws
  rcases h1 with ⟨hext, hlt, hnc, _, hval⟩
  refine ⟨hext, hlt, hnc, ?_⟩
  intro x z
  have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
  rw [hval (pairVec n m x z) hlen]
  have hone : (wiresFrom gs (pairVec n m x z)).getD oneWire false = (pairVec n m x z).getD oneWire false :=
    wiresFrom_getD_lt gs (pairVec n m x z) oneWire (by rw [hlen]; exact ho)
  rw [hone]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq, ws, List.mem_append, List.mem_map, Finset.mem_toList]
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have h0 := h a.val (Or.inl ⟨a, ha, rfl⟩)
      rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := a.isLt; omega), pairVec_getD_left] at h0
      exact of_decide_eq_true h0
    · have h0 := h (n + b.val) (Or.inr ⟨b, hb, rfl⟩)
      rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := b.isLt; omega), pairVec_getD_right] at h0
      exact of_decide_eq_true h0
  · rintro ⟨hx, hz⟩ i (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := a.isLt; omega), pairVec_getD_left]
      exact decide_eq_true (hx ha)
    · rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := b.isLt; omega), pairVec_getD_right]
      exact decide_eq_true (hz hb)

noncomputable def emitMonoAux (n m base zeroWire oneWire : ℕ) :
    List Gate → List (Finset (Fin n) × Finset (Fin m)) → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, p :: ps =>
    let rc := emitCube base oneWire n gs p.1 p.2
    let rr := emitMonoAux n m base zeroWire oneWire rc.1 ps
    (rr.1, rc.2 :: rr.2)

lemma emitMonoAux_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (ho : oneWire < base) :
    ∀ (ps : List (Finset (Fin n) × Finset (Fin m))) (gs : List Gate),
      let r := emitMonoAux n m base zeroWire oneWire gs ps
      Extends base gs r.1 ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
        (r.2.any (fun w => (wiresFrom r.1 (pairVec n m x z)).getD w false)) =
          ps.any (fun p => (pairVec n m x z).getD oneWire false && decide (p.1 ⊆ x ∧ p.2 ⊆ z)) := by
  intro ps
  induction ps with
  | nil =>
    intro gs
    dsimp only [emitMonoAux]
    refine ⟨Extends.refl base gs, (fun _ h => by cases h), rfl, fun _ _ => rfl⟩
  | cons p ps ih =>
    intro gs
    dsimp only [emitMonoAux]
    set rc := emitCube base oneWire n gs p.1 p.2 with hrc
    have hc := emitCube_spec n m base oneWire hbas ho gs p.1 p.2
    rw [← hrc] at hc
    rcases hc with ⟨hext1, hlt1, hnc1, hval1⟩
    set rr := emitMonoAux n m base zeroWire oneWire rc.1 ps with hrr
    have hr := ih rc.1
    rw [← hrr] at hr
    rcases hr with ⟨hext2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, ?_, by omega, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · have := hext2.length_le; omega
      · exact hlt2 w hw
    · intro x z
      have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
      simp only [List.any_cons]
      rw [hext2.wire_eq _ hlen _ hlt1, hval1 x z, hval2 x z]

noncomputable def emitMonoQ (n m base zeroWire oneWire : ℕ) (gs : List Gate)
    (Q : Finset (Fin n) → Finset (Fin m) → Bool) : List Gate × ℕ :=
  let ps := (Finset.univ.filter (fun p : Finset (Fin n) × Finset (Fin m) => Q p.1 p.2 = true)).toList
  let r1 := emitMonoAux n m base zeroWire oneWire gs ps
  emitOrList base zeroWire r1.1 r1.2

lemma emitMonoQ_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (hz : zeroWire < base) (ho : oneWire < base) (gs : List Gate)
    (Q : Finset (Fin n) → Finset (Fin m) → Bool)
    (hQmono : ∀ (x1 x2 : Finset (Fin n)) (z1 z2 : Finset (Fin m)), x1 ⊆ x2 → z1 ⊆ z2 → Q x1 z1 = true → Q x2 z2 = true)
    (hzero : ∀ x z, (pairVec n m x z).getD zeroWire false = false)
    (hone : ∀ x z, (pairVec n m x z).getD oneWire false = true) :
    let r := emitMonoQ n m base zeroWire oneWire gs Q
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom r.1 (pairVec n m x z)).getD r.2 false = Q x z := by
  dsimp only [emitMonoQ]
  set ps := (Finset.univ.filter (fun p : Finset (Fin n) × Finset (Fin m) => Q p.1 p.2 = true)).toList
  set r1 := emitMonoAux n m base zeroWire oneWire gs ps with hr1
  have h1 := emitMonoAux_spec n m base zeroWire oneWire hbas ho ps gs
  rw [← hr1] at h1
  rcases h1 with ⟨hext1, hlt1, hnc1, hval1⟩
  have hz' : zeroWire < base + r1.1.length := by omega
  have h2 := emitOrList_spec base r1.2 zeroWire r1.1 hz' hlt1
  rcases h2 with ⟨hext2, hlt2, hnc2, _, hval2⟩
  refine ⟨hext1.trans hext2, hlt2, by omega, ?_⟩
  intro x z
  have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
  rw [hval2 _ hlen, wiresFrom_getD_lt _ _ _ (by rw [hlen]; exact hz), hzero x z, Bool.false_or, hval1 x z]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, ps, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hpQ, _, hx, hz'⟩
    exact hQmono p.1 x p.2 z hx hz' hpQ
  · intro hQx
    refine ⟨(x, z), hQx, hone x z, Finset.Subset.refl _, Finset.Subset.refl _⟩

end MonotoneSynth

section FitLower

def capP (r b : ℕ) : ℕ := 2^(min r b) * (r - min r b + 1)

def fitP (n m q r b p : ℕ) (F : Fin q → Finset (Fin n) → Finset (Fin m) → Bool) : Prop :=
  ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin r → Nat) (out : Fin q → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+m+2) D ∧
    C.output < n+2+C.size ∧ D.output < r+m+2+D.size ∧
    (∀ i, tap i < n+2+C.size) ∧ (∀ t, out t < r+m+2+D.size) ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D = 0 ∧
    C.size-PEqualNP.NotBracket.notCount C+D.size ≤ p ∧
    ∀ A B, let c := C.wires (List.ofFn (fun i : Fin n => decide (i ∈ A)) ++ [false,true])
           let w := D.wires (List.ofFn (fun i => c.getD (tap i) false) ++
             List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true])
           ∀ t, w.getD (out t) false = F t A B
lemma arith_aux (a s d : ℕ) (h : s ≤ d + 1) : 2^a*s ≤ 2^a*a + 2^d := by
  rcases Nat.lt_or_ge a s with hs | hs
  · obtain ⟨e, rfl⟩ : ∃ e, s = a + e + 1 := ⟨s - a - 1, by omega⟩
    have h1 : e + 1 ≤ 2^e := by
      induction e with
      | zero => simp
      | succ k ih => rw [pow_succ]; omega
    have h2 : 2^(a+e) ≤ 2^d := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add] at h2
    have h3 : 2^a*(e+1) ≤ 2^a*2^e := Nat.mul_le_mul_left _ h1
    calc 2^a*(a+e+1) = 2^a*a + 2^a*(e+1) := by ring
      _ ≤ 2^a*a + 2^d := by omega
  · have := Nat.mul_le_mul_left (2^a) hs
    exact le_trans this (Nat.le_add_right _ _)

lemma comb (r b h : ℕ) (X : Fin (h+1) → Finset (Fin r)) (c : Fin (h+1) → ℕ)
    (hc : ∀ i, c i < 2^b)
    (hmono : ∀ i j, i ≤ j → c j < c i ∨ (c j = c i ∧ X i ⊆ X j))
    (hsep : ∀ i j, i < j → ¬ X j ⊆ X i) :
    h + 1 ≤ 2^(min r b) * (r - min r b + 1) := by
  rcases le_or_gt r b with hrb | hrb
  · rw [min_eq_left hrb, Nat.sub_self, zero_add, mul_one]
    have hinj : Function.Injective X := by
      intro i j hij
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exfalso; apply hsep i j hlt; rw [hij]
      · exact heq
      · exfalso; apply hsep j i hgt; rw [hij]
    have := Fintype.card_le_of_injective X hinj
    simpa [Fintype.card_finset] using this
  · rw [min_eq_right hrb.le]
    set a := r - b with ha
    set V := Finset.univ.image c with hV
    let S : ℕ → Finset (Fin (h+1)) := fun v => Finset.univ.filter (fun i => c i = v)
    have hSne : ∀ v ∈ V, (S v).Nonempty := by
      intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i, by simp [S]⟩
    let lo : ℕ → Finset (Fin r) := fun v => if hv : (S v).Nonempty then X ((S v).min' hv) else ∅
    let hi : ℕ → Finset (Fin r) := fun v => if hv : (S v).Nonempty then X ((S v).max' hv) else ∅
    have hmem : ∀ v i, i ∈ S v → c i = v := by intro v i hi; simpa [S] using hi
    have hbetween : ∀ v i, i ∈ S v → lo v ⊆ X i ∧ X i ⊆ hi v := by
      intro v i hiS
      have hne : (S v).Nonempty := ⟨i, hiS⟩
      have hc1 := hmem v _ ((S v).min'_mem hne)
      have hc2 := hmem v _ ((S v).max'_mem hne)
      have hci := hmem v i hiS
      refine ⟨?_, ?_⟩
      · simp only [lo, dif_pos hne]
        rcases hmono _ i ((S v).min'_le i hiS) with h1 | h1
        · omega
        · exact h1.2
      · simp only [hi, dif_pos hne]
        rcases hmono i _ ((S v).le_max' i hiS) with h1 | h1
        · omega
        · exact h1.2
    have hsize : ∀ v ∈ V, (S v).card ≤ (hi v).card - (lo v).card + 1 := by
      intro v hv
      have hinj : Set.InjOn (fun i => (X i).card) (S v) := by
        intro i hi' j hj' hij
        simp only at hij
        by_contra hne
        have hci := hmem v i hi'
        have hcj := hmem v j hj'
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · rcases hmono i j hlt.le with h1 | h1
          · omega
          · exact hsep i j hlt (Finset.eq_of_subset_of_card_le h1.2 (by omega)).symm.subset
        · rcases hmono j i hlt.le with h1 | h1
          · omega
          · exact hsep j i hlt (Finset.eq_of_subset_of_card_le h1.2 (by omega)).symm.subset
      have hmaps : ∀ i ∈ S v, (fun i => (X i).card) i ∈ Finset.Icc (lo v).card (hi v).card := by
        intro i hi'
        obtain ⟨h1, h2⟩ := hbetween v i hi'
        simp only [Finset.mem_Icc]
        exact ⟨Finset.card_le_card h1, Finset.card_le_card h2⟩
      have := Finset.card_le_card_of_injOn _ hmaps hinj
      simp only [Nat.card_Icc] at this
      omega
    have hlohi : ∀ v ∈ V, lo v ⊆ hi v := by
      intro v hv
      obtain ⟨i, hi'⟩ := hSne v hv
      exact (hbetween v i hi').1.trans (hbetween v i hi').2
    have hcross : ∀ v ∈ V, ∀ w ∈ V, w < v → ∀ Y, lo w ⊆ Y → Y ⊆ hi v → False := by
      intro v hv w hw hwv Y h1 h2
      have hnv := hSne v hv
      have hnw := hSne w hw
      simp only [lo, hi, dif_pos hnv, dif_pos hnw] at h1 h2
      set i := (S v).max' hnv
      set j := (S w).min' hnw
      have hci := hmem v i ((S v).max'_mem hnv)
      have hcj := hmem w j ((S w).min'_mem hnw)
      have hij : i < j := by
        by_contra hle
        rcases hmono j i (not_lt.mp hle) with h | h <;> omega
      exact hsep i j hij (h1.trans h2)
    let I : ℕ → Finset (Finset (Fin r)) := fun v => Finset.Icc (lo v) (hi v)
    have hdisj : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → Disjoint (I v) (I w) := by
      intro v hv w hw hvw
      rw [Finset.disjoint_left]
      intro Y hY1 hY2
      simp only [I, Finset.mem_Icc] at hY1 hY2
      rcases lt_or_gt_of_ne hvw with hlt | hlt
      · exact hcross w hw v hv hlt Y hY1.1 hY2.2
      · exact hcross v hv w hw hlt Y hY2.1 hY1.2
    have hvol : ∑ v ∈ V, 2^((hi v).card - (lo v).card) ≤ 2^r := by
      have heq : ∑ v ∈ V, 2^((hi v).card - (lo v).card) = (V.biUnion I).card := by
        rw [Finset.card_biUnion (by intro v hv w hw hvw; exact hdisj v hv w hw hvw)]
        apply Finset.sum_congr rfl
        intro v hv
        simp only [I]
        rw [Finset.card_Icc_finset (hlohi v hv)]
      rw [heq]
      have := Finset.card_le_univ (V.biUnion I)
      simpa [Fintype.card_finset] using this
    have hVcard : V.card ≤ 2^b := by
      have : V ⊆ Finset.range (2^b) := by
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        simpa using hc i
      simpa using Finset.card_le_card this
    have htot : h + 1 = ∑ v ∈ V, (S v).card := by
      have := Finset.card_eq_sum_card_image c (Finset.univ : Finset (Fin (h+1)))
      rw [hV]
      simpa [S] using this
    have hkey : 2^a * (h+1) ≤ V.card * (2^a * a) + 2^r := by
      rw [htot, Finset.mul_sum]
      calc ∑ v ∈ V, 2^a * (S v).card ≤ ∑ v ∈ V, (2^a*a + 2^((hi v).card - (lo v).card)) :=
            Finset.sum_le_sum (fun v hv => arith_aux a _ _ (hsize v hv))
        _ = V.card * (2^a * a) + ∑ v ∈ V, 2^((hi v).card - (lo v).card) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
        _ ≤ V.card * (2^a * a) + 2^r := by omega
    have hr : 2^r = 2^a * 2^b := by rw [← pow_add]; congr 1; omega
    have h2 : V.card * (2^a * a) ≤ 2^b * (2^a * a) := Nat.mul_le_mul_right _ hVcard
    have h3 : 2^a * (h+1) ≤ 2^a * (2^b * (a+1)) := by
      calc 2^a * (h+1) ≤ V.card * (2^a * a) + 2^r := hkey
        _ ≤ 2^b * (2^a * a) + 2^a * 2^b := by omega
        _ = 2^a * (2^b * (a+1)) := by ring
    exact Nat.le_of_mul_le_mul_left h3 (by positivity)

lemma inlist_mono (r m : ℕ) (u v : Fin r → Bool) (huv : ∀ k, u k ≤ v k) (B : Finset (Fin m)) (k : ℕ) :
    (List.ofFn u ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true]).getD k false ≤
    (List.ofFn v ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true]).getD k false := by
  simp only [List.append_assoc]
  by_cases hk : k < r
  · rw [getD_append_left _ _ _ _ (by simpa using hk), getD_append_left _ _ _ _ (by simpa using hk)]
    simpa [List.getD_eq_getElem?_getD, hk] using huv ⟨k, hk⟩
  · rw [getD_append_right (List.ofFn u) _ k false (by rw [List.length_ofFn]; omega),
      getD_append_right (List.ofFn v) _ k false (by rw [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]
    exact le_refl _

lemma fit_lower (n m q r b p h : ℕ) (F : Fin q → Finset (Fin n) → Finset (Fin m) → Bool)
    (chain : Fin (h+1) → Finset (Fin n))
    (hchain : ∀ i j, i ≤ j → chain i ⊆ chain j)
    (hsep : ∀ i j : Fin (h+1), i < j → ∃ t B, F t (chain i) B = false ∧ F t (chain j) B = true)
    (hfit : fitP n m q r b p F) : h + 1 ≤ capP r b := by
  obtain ⟨C, D, tap, out, hCf, _, hDf, _, _, _, _, _, hCn, hDn, _, hall⟩ := hfit
  let val : Fin (h+1) → Fin r → Bool := fun i k => (C.wires (inpVec (chain i))).getD (tap k) false
  let X : Fin (h+1) → Finset (Fin r) := fun i => Finset.univ.filter (fun k => val i k = true)
  let c : Fin (h+1) → ℕ := fun i => evalNotCode C.gates (inpVec (chain i))
  have hCf' : FanInTwo ⟨C.gates, 0⟩ := fun g hg => hCf g hg
  unfold capP
  apply comb r b h X c
  · intro i
    have h1 := evalNotCode_lt C.gates (inpVec (chain i))
    have h2 : 2 ^ (notCount ⟨C.gates, 0⟩) ≤ 2^b := Nat.pow_le_pow_right (by norm_num) hCn
    exact lt_of_lt_of_le h1 h2
  · intro i j hij
    have hsub := hchain i j hij
    rcases evalNotCode_dichotomy C.gates (inpVec (chain i)) (inpVec (chain j)) hCf'
      (by rw [inpVec_length, inpVec_length]) (inpVec_mono hsub) with hlt | ⟨heq, hle⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      intro k hk
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact (bool_le_iff _ _).mp (hle (tap k)) hk
  · intro i j hij hXs
    obtain ⟨t, B, hFi, hFj⟩ := hsep i j hij
    have hDm : Monotone2 ⟨D.gates, 0⟩ :=
      monotone2_of_fanInTwo_notZero D.gates (fun g hg => hDf g hg) hDn
    have hj := hall (chain j) B t
    have hi := hall (chain i) B t
    have hmono := wiresFrom_mono D.gates hDm
      (List.ofFn (val j) ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true])
      (List.ofFn (val i) ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true])
      (by simp)
      (inlist_mono r m (val j) (val i) (fun k => by
        rw [bool_le_iff]; intro hk
        have : k ∈ X j := by simp [X, hk]
        have := hXs this
        simpa [X] using this) B) (out t)
    have e1 : (wiresFrom D.gates (List.ofFn (val j) ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true])).getD (out t) false = true := by
      exact hj.trans hFj
    have e2 : (wiresFrom D.gates (List.ofFn (val i) ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true])).getD (out t) false = false := by
      exact hi.trans hFi
    rw [e1, e2] at hmono
    exact not_true_le_false hmono

end FitLower

section Cons

def vals (gs : List Gate) (w : List Bool) (L : List ℕ) : List Bool :=
  L.map (fun i => (wiresFrom gs w).getD i false)

lemma vals_frame {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2) (w : List Bool)
    (hw : w.length = base) (L : List ℕ) (hL : ∀ i ∈ L, i < base + gs1.length) :
    vals gs2 w L = vals gs1 w L := by
  unfold vals
  apply List.map_congr_left
  intro i hi
  exact h.wire_eq w hw i (hL i hi)

lemma vals_getD (gs : List Gate) (w : List Bool) (L : List ℕ) (V : List Bool)
    (h : vals gs w L = V) (i : ℕ) (hi : i < L.length) :
    (wiresFrom gs w).getD (L.getD i 0) false = V.getD i false := by
  subst h
  unfold vals
  rw [List.getD_eq_getElem L 0 hi,
    List.getD_eq_getElem (L.map (fun i => (wiresFrom gs w).getD i false)) false (by simpa using hi),
    List.getElem_map]

def emitBin (op : GateOp) (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨op, [a, b]⟩], base + gs.length)

lemma emitBin_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (base : ℕ)
    (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitBin op base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    r.1.length = gs.length + 1 ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        op.eval [(wiresFrom gs w).getD a false, (wiresFrom gs w).getD b false] := by
  dsimp only [emitBin]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨op, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg
      rcases hop with rfl | rfl <;> simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]
    rcases hop with rfl | rfl <;> simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen]

def zipBin (op : GateOp) (base : ℕ) : List Gate → List ℕ → List ℕ → List Gate × List ℕ
  | gs, [], _ => (gs, [])
  | gs, _ :: _, [] => (gs, [])
  | gs, x :: xs, y :: ys =>
    let e := emitBin op base gs x y
    let r := zipBin op base e.1 xs ys
    (r.1, e.2 :: r.2)

lemma zipBin_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (base : ℕ) :
    ∀ (xs ys : List ℕ) (gs : List Gate),
      (∀ i ∈ xs, i < base + gs.length) → (∀ i ∈ ys, i < base + gs.length) →
      let r := zipBin op base gs xs ys
      Extends base gs r.1 ∧
      r.1.length = gs.length + min xs.length ys.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      (∀ i ∈ r.2, i < base + r.1.length) ∧
      ∀ w, w.length = base →
        vals r.1 w r.2 = List.zipWith (fun p q => op.eval [p, q]) (vals gs w xs) (vals gs w ys) := by
  intro xs
  induction xs with
  | nil =>
    intro ys gs _ _
    exact ⟨Extends.refl _ _, by simp [zipBin], rfl, by simp [zipBin], fun w _ => by simp [zipBin, vals]⟩
  | cons x xs ih =>
    intro ys gs hx hy
    cases ys with
    | nil =>
      exact ⟨Extends.refl _ _, by simp [zipBin], rfl, by simp [zipBin], fun w _ => by simp [zipBin, vals]⟩
    | cons y ys =>
      dsimp only [zipBin]
      obtain ⟨he, hlt, hlen, hnc, hv⟩ :=
        emitBin_spec op hop base gs x y (hx x (by simp)) (hy y (by simp))
      obtain ⟨he2, hlen2, hnc2, hlt2, hv2⟩ := ih ys (emitBin op base gs x y).1
        (fun i hi => by have := hx i (by simp [hi]); omega)
        (fun i hi => by have := hy i (by simp [hi]); omega)
      refine ⟨he.trans he2, by simp only [hlen2, hlen, List.length_cons]; omega,
        by rw [hnc2, hnc], ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · have := he2.length_le; omega
        · exact hlt2 i hi
      · intro w hw
        have e1 : vals (zipBin op base (emitBin op base gs x y).1 xs ys).1 w
            ((emitBin op base gs x y).2 :: (zipBin op base (emitBin op base gs x y).1 xs ys).2) =
            (wiresFrom (zipBin op base (emitBin op base gs x y).1 xs ys).1 w).getD
              (emitBin op base gs x y).2 false ::
            vals (zipBin op base (emitBin op base gs x y).1 xs ys).1 w
              (zipBin op base (emitBin op base gs x y).1 xs ys).2 := rfl
        rw [e1, he2.wire_eq w hw _ hlt, hv w hw, hv2 w hw,
          vals_frame he w hw xs (fun i hi => hx i (by simp [hi])),
          vals_frame he w hw ys (fun i hi => hy i (by simp [hi]))]
        simp [vals]

/-! ### Folding thresholds: one NOT per halving -/

def foldLevel (base N : ℕ) (gs : List Gate) (L : List ℕ) : List Gate × ℕ × List ℕ :=
  let e := emitNot base gs (L.getD N 0)
  let a := zipBin GateOp.and base e.1 (L.take N) (List.replicate N e.2)
  let o := zipBin GateOp.or base a.1 a.2 (L.drop N)
  (o.1, L.getD N 0, o.2)

lemma fold_pure (N x : ℕ) (hx : x < 2 * N) :
    List.zipWith (fun p q => GateOp.or.eval [p, q])
      (List.zipWith (fun p q => GateOp.and.eval [p, q])
        (((List.range (2 * N)).map (fun k => decide (k ≤ x))).take N)
        (List.replicate N (!decide (N ≤ x))))
      (((List.range (2 * N)).map (fun k => decide (k ≤ x))).drop N) =
    (List.range N).map (fun k => decide (k ≤ (if N ≤ x then x - N else x))) := by
  apply List.ext_getElem
  · simp; omega
  · intro t h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp [GateOp.eval]
    by_cases hN : N ≤ x
    · simp [hN]; omega
    · simp [hN]; omega

lemma foldLevel_spec (base N : ℕ) (gs : List Gate) (L : List ℕ) (hL : L.length = 2 * N)
    (hN : 0 < N) (hLw : ∀ i ∈ L, i < base + gs.length) :
    let r := foldLevel base N gs L
    Extends base gs r.1 ∧ r.1.length = gs.length + 1 + 2 * N ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧ r.2.1 < base + gs.length ∧
    r.2.2.length = N ∧ (∀ i ∈ r.2.2, i < base + r.1.length) ∧
    ∀ w x, w.length = base → x < 2 * N →
      vals gs w L = (List.range (2 * N)).map (fun k => decide (k ≤ x)) →
      (wiresFrom r.1 w).getD r.2.1 false = decide (N ≤ x) ∧
      vals r.1 w r.2.2 = (List.range N).map (fun k => decide (k ≤ (if N ≤ x then x - N else x))) := by
  dsimp only [foldLevel]
  have hNL : N < L.length := by omega
  have hmem : L.getD N 0 ∈ L := getD_mem L N 0 hNL
  have hLN := hLw _ hmem
  obtain ⟨he, hlt, hnc, hnn, hv⟩ := emitNot_spec base gs (L.getD N 0) hLN
  have hel := he.length_le
  have hlenE : (emitNot base gs (L.getD N 0)).1.length = gs.length + 1 := by simp [emitNot]
  set E := emitNot base gs (L.getD N 0) with hE
  have htk : ∀ i ∈ L.take N, i < base + E.1.length := fun i hi => by
    have := hLw i (List.mem_of_mem_take hi); omega
  have hrp : ∀ i ∈ List.replicate N E.2, i < base + E.1.length := fun i hi => by
    rw [List.eq_of_mem_replicate hi]; exact hlt
  obtain ⟨ha, hlena, hnca, hlta, hva⟩ := zipBin_spec GateOp.and (Or.inl rfl) base _ _ E.1 htk hrp
  set A := zipBin GateOp.and base E.1 (L.take N) (List.replicate N E.2) with hA
  have hal := ha.length_le
  have hdr : ∀ i ∈ L.drop N, i < base + A.1.length := fun i hi => by
    have := hLw i (List.mem_of_mem_drop hi); omega
  obtain ⟨ho, hleno, hnco, hlto, hvo⟩ := zipBin_spec GateOp.or (Or.inr rfl) base _ _ A.1 hlta hdr
  set O := zipBin GateOp.or base A.1 A.2 (L.drop N) with hO
  have hA2len : A.2.length = N := by
    have : ∀ (xs ys : List ℕ) (gs : List Gate),
        (zipBin GateOp.and base gs xs ys).2.length = min xs.length ys.length := by
      intro xs; induction xs with
      | nil => intro ys gs; simp [zipBin]
      | cons x xs ih => intro ys gs; cases ys with
        | nil => simp [zipBin]
        | cons y ys => simp [zipBin, ih]
    rw [hA, this]; simp; omega
  have hO2len : O.2.length = N := by
    have : ∀ (xs ys : List ℕ) (gs : List Gate),
        (zipBin GateOp.or base gs xs ys).2.length = min xs.length ys.length := by
      intro xs; induction xs with
      | nil => intro ys gs; simp [zipBin]
      | cons x xs ih => intro ys gs; cases ys with
        | nil => simp [zipBin]
        | cons y ys => simp [zipBin, ih]
    rw [hO, this, hA2len]; simp; omega
  refine ⟨he.trans (ha.trans ho), ?_, ?_, hLN, hO2len, hlto, ?_⟩
  · rw [hleno, hlena, hlenE, hA2len]; simp; omega
  · rw [hnco, hnca, hnc]
  · intro w x hw hx hval
    have hβ : (wiresFrom gs w).getD (L.getD N 0) false = decide (N ≤ x) := by
      rw [vals_getD gs w L _ hval N hNL]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    constructor
    · rw [(he.trans (ha.trans ho)).wire_eq w hw _ hLN, hβ]
    · rw [hvo w hw, hva w hw, vals_frame ha w hw _ (fun i hi => by have := hLw i (List.mem_of_mem_drop hi); omega), vals_frame he w hw _ (fun i hi => hLw i (List.mem_of_mem_drop hi)),
        vals_frame he w hw _ (fun i hi => hLw i (List.mem_of_mem_take hi))]
      have hrep : vals E.1 w (List.replicate N E.2) = List.replicate N (!decide (N ≤ x)) := by
        simp only [vals, List.map_replicate]
        rw [hv w hw, hβ]
      rw [hrep]
      have htake : vals gs w (L.take N) = (vals gs w L).take N := by simp [vals, List.map_take]
      have hdrop : vals gs w (L.drop N) = (vals gs w L).drop N := by simp [vals, List.map_drop]
      rw [htake, hdrop, hval]
      exact fold_pure N x hx

def cbits (a : ℕ) : ℕ → ℕ → List Bool
  | 0, _ => []
  | u + 1, x => decide (2 ^ u * (a + 1) ≤ x) ::
      cbits a u (if 2 ^ u * (a + 1) ≤ x then x - 2 ^ u * (a + 1) else x)

def cres (a : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | u + 1, x => cres a u (if 2 ^ u * (a + 1) ≤ x then x - 2 ^ u * (a + 1) else x)

lemma cbits_length (a : ℕ) : ∀ u x, (cbits a u x).length = u := by
  intro u; induction u with
  | zero => intro x; rfl
  | succ u ih => intro x; simp [cbits, ih]

lemma step_lt (u a x : ℕ) (hx : x < 2 ^ (u + 1) * (a + 1)) :
    (if 2 ^ u * (a + 1) ≤ x then x - 2 ^ u * (a + 1) else x) < 2 ^ u * (a + 1) := by
  rw [pow_succ] at hx
  have e : 2 ^ u * 2 * (a + 1) = 2 * (2 ^ u * (a + 1)) := by ring
  rw [e] at hx
  split_ifs with h <;> omega

lemma cres_le (a : ℕ) : ∀ u x, x < 2 ^ u * (a + 1) → cres a u x ≤ a := by
  intro u; induction u with
  | zero => intro x hx; simp [cres] at hx ⊢; omega
  | succ u ih => intro x hx; exact ih _ (step_lt u a x hx)

def foldAll (base a : ℕ) : ℕ → List Gate → List ℕ → List Gate × List ℕ × List ℕ
  | 0, gs, L => (gs, [], L)
  | u + 1, gs, L =>
    let f := foldLevel base (2 ^ u * (a + 1)) gs L
    let r := foldAll base a u f.1 f.2.2
    (r.1, f.2.1 :: r.2.1, r.2.2)

lemma foldAll_spec (base a : ℕ) : ∀ (u : ℕ) (gs : List Gate) (L : List ℕ),
    L.length = 2 ^ u * (a + 1) → (∀ i ∈ L, i < base + gs.length) →
    let r := foldAll base a u gs L
    Extends base gs r.1 ∧ r.1.length + 2 * (a + 1) = gs.length + u + 2 * (2 ^ u * (a + 1)) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + u ∧ r.2.1.length = u ∧ r.2.2.length = a + 1 ∧
    (∀ i ∈ r.2.1, i < base + r.1.length) ∧ (∀ i ∈ r.2.2, i < base + r.1.length) ∧
    ∀ w x, w.length = base → x < 2 ^ u * (a + 1) →
      vals gs w L = (List.range (2 ^ u * (a + 1))).map (fun k => decide (k ≤ x)) →
      vals r.1 w r.2.1 = cbits a u x ∧
      vals r.1 w r.2.2 = (List.range (a + 1)).map (fun k => decide (k ≤ cres a u x)) := by
  intro u
  induction u with
  | zero =>
    intro gs L hL hLw
    simp only [pow_zero, one_mul] at hL ⊢
    refine ⟨Extends.refl _ _, by simp [foldAll] <;> omega, by simp [foldAll], by simp [foldAll],
      by simpa [foldAll] using hL, by simp [foldAll], by simpa [foldAll] using hLw, ?_⟩
    intro w x _ _ hv
    exact ⟨rfl, hv⟩
  | succ u ih =>
    intro gs L hL hLw
    dsimp only [foldAll]
    set N := 2 ^ u * (a + 1) with hNdef
    have h2N : 2 ^ (u + 1) * (a + 1) = 2 * N := by rw [hNdef, pow_succ]; ring
    have hNpos : 0 < N := by positivity
    rw [h2N] at hL
    obtain ⟨hf, hflen, hfnc, hfb, hfl, hflw, hfv⟩ := foldLevel_spec base N gs L hL hNpos hLw
    set F := foldLevel base N gs L with hF
    obtain ⟨hr, hrlen, hrnc, hr1l, hr2l, hr1w, hr2w, hrv⟩ := ih F.1 F.2.2 hfl hflw
    set R := foldAll base a u F.1 F.2.2 with hR
    have hfl' := hf.length_le
    have hrl' := hr.length_le
    refine ⟨hf.trans hr, ?_, by rw [hrnc, hfnc]; ring, by simp [hr1l], hr2l, ?_, hr2w, ?_⟩
    · rw [h2N]; omega
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hr1w i hi
    · intro w x hw hx hv
      rw [h2N] at hx hv
      obtain ⟨hb, hl⟩ := hfv w x hw hx hv
      have hx' : (if N ≤ x then x - N else x) < N := by
        split_ifs <;> omega
      obtain ⟨hr1, hr2⟩ := hrv w _ hw hx' hl
      refine ⟨?_, ?_⟩
      · have e1 : vals R.1 w (F.2.1 :: R.2.1) = (wiresFrom R.1 w).getD F.2.1 false :: vals R.1 w R.2.1 := rfl
        rw [e1, hr.wire_eq w hw _ (by omega), hb, hr1]
        rfl
      · rw [hr2]; rfl

/-! ### Unfolding: rebuild all thresholds monotonically -/

def unfoldAll (base : ℕ) : List ℕ → List Gate → List ℕ → List Gate × List ℕ
  | [], gs, L => (gs, L)
  | β :: bs, gs, L =>
    let r := unfoldAll base bs gs L
    let o := zipBin GateOp.or base r.1 (List.replicate r.2.length β) r.2
    let n := zipBin GateOp.and base o.1 (List.replicate r.2.length β) r.2
    (n.1, o.2 ++ n.2)

lemma zipBin_len2 (op : GateOp) (base : ℕ) : ∀ (xs ys : List ℕ) (gs : List Gate),
    (zipBin op base gs xs ys).2.length = min xs.length ys.length := by
  intro xs; induction xs with
  | nil => intro ys gs; simp [zipBin]
  | cons x xs ih => intro ys gs; cases ys with
    | nil => simp [zipBin]
    | cons y ys => simp [zipBin, ih]

lemma unfold_pure (N x : ℕ) (hx : x < 2 * N) :
    List.zipWith (fun p q => GateOp.or.eval [p, q]) (List.replicate N (decide (N ≤ x)))
        ((List.range N).map (fun k => decide (k ≤ (if N ≤ x then x - N else x)))) ++
      List.zipWith (fun p q => GateOp.and.eval [p, q]) (List.replicate N (decide (N ≤ x)))
        ((List.range N).map (fun k => decide (k ≤ (if N ≤ x then x - N else x)))) =
    (List.range (2 * N)).map (fun k => decide (k ≤ x)) := by
  apply List.ext_getElem
  · simp; omega
  · intro t h1 h2
    simp only [List.length_map, List.length_range] at h2
    by_cases ht : t < N
    · rw [List.getElem_append_left (by simpa using ht)]
      simp [GateOp.eval]
      by_cases hN : N ≤ x <;> simp [hN] <;> omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp [GateOp.eval]
      by_cases hN : N ≤ x <;> simp [hN] <;> omega

lemma unfoldAll_spec (base a : ℕ) : ∀ (bs : List ℕ) (gs : List Gate) (L : List ℕ),
    L.length = a + 1 → (∀ i ∈ bs, i < base + gs.length) → (∀ i ∈ L, i < base + gs.length) →
    let r := unfoldAll base bs gs L
    Extends base gs r.1 ∧
    r.1.length + 2 * (a + 1) = gs.length + 2 * (2 ^ bs.length * (a + 1)) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ r.2.length = 2 ^ bs.length * (a + 1) ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    ∀ w x, w.length = base → x < 2 ^ bs.length * (a + 1) →
      vals gs w bs = cbits a bs.length x →
      vals gs w L = (List.range (a + 1)).map (fun k => decide (k ≤ cres a bs.length x)) →
      vals r.1 w r.2 = (List.range (2 ^ bs.length * (a + 1))).map (fun k => decide (k ≤ x)) := by
  intro bs
  induction bs with
  | nil =>
    intro gs L hL _ hLw
    simp only [List.length_nil, pow_zero, one_mul]
    refine ⟨Extends.refl _ _, by simp [unfoldAll], rfl, by simpa [unfoldAll] using hL,
      by simpa [unfoldAll] using hLw, ?_⟩
    intro w x _ _ _ hv
    exact hv
  | cons β bs ih =>
    intro gs L hL hbw hLw
    dsimp only [unfoldAll]
    have hβ : β < base + gs.length := hbw β (by simp)
    obtain ⟨hr, hrlen, hrnc, hr2l, hr2w, hrv⟩ :=
      ih gs L hL (fun i hi => hbw i (by simp [hi])) hLw
    set R := unfoldAll base bs gs L with hR
    set N := 2 ^ bs.length * (a + 1) with hNdef
    have hrl := hr.length_le
    have hrep : ∀ i ∈ List.replicate R.2.length β, i < base + R.1.length := fun i hi => by
      rw [List.eq_of_mem_replicate hi]; omega
    obtain ⟨ho, holen, honc, how, hov⟩ := zipBin_spec GateOp.or (Or.inr rfl) base _ _ R.1 hrep hr2w
    set O := zipBin GateOp.or base R.1 (List.replicate R.2.length β) R.2 with hO
    have hol := ho.length_le
    have hrep2 : ∀ i ∈ List.replicate R.2.length β, i < base + O.1.length := fun i hi => by
      rw [List.eq_of_mem_replicate hi]; omega
    obtain ⟨hn, hnlen, hnnc, hnw, hnv⟩ := zipBin_spec GateOp.and (Or.inl rfl) base _ _ O.1 hrep2
      (fun i hi => by have := hr2w i hi; omega)
    set Nn := zipBin GateOp.and base O.1 (List.replicate R.2.length β) R.2 with hNn
    have hnl := hn.length_le
    have h2N : 2 ^ (bs.length + 1) * (a + 1) = 2 * N := by rw [hNdef, pow_succ]; ring
    have hO2 : O.2.length = N := by rw [hO, zipBin_len2]; simp [hr2l]
    have hN2 : Nn.2.length = N := by rw [hNn, zipBin_len2]; simp [hr2l]
    refine ⟨hr.trans (ho.trans hn), ?_, by rw [hnnc, honc, hrnc], ?_, ?_, ?_⟩
    · simp only [List.length_cons]; rw [h2N, hnlen, holen]; simp [hr2l]; omega
    · simp only [List.length_cons, List.length_append, hO2, hN2]; rw [h2N]; ring
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · have := how i hi; omega
      · exact hnw i hi
    · intro w x hw hx hvb hvL
      simp only [List.length_cons] at hx hvb hvL ⊢
      rw [h2N] at hx ⊢
      have hvb' : vals gs w (β :: bs) = (wiresFrom gs w).getD β false :: vals gs w bs := rfl
      rw [hvb'] at hvb
      have hcb : cbits a (bs.length + 1) x = decide (N ≤ x) ::
          cbits a bs.length (if N ≤ x then x - N else x) := rfl
      rw [hcb] at hvb
      obtain ⟨hb1, hb2⟩ := List.cons.inj hvb
      have hvL' : vals gs w L = (List.range (a + 1)).map
          (fun k => decide (k ≤ cres a bs.length (if N ≤ x then x - N else x))) := hvL
      have hx' : (if N ≤ x then x - N else x) < N := by split_ifs <;> omega
      have hR2 := hrv w _ hw hx' hb2 hvL'
      have happ : vals Nn.1 w (O.2 ++ Nn.2) = vals Nn.1 w O.2 ++ vals Nn.1 w Nn.2 := by
        simp [vals]
      have hrepv : ∀ G : List Gate, Extends base R.1 G →
          vals G w (List.replicate R.2.length β) = List.replicate N (decide (N ≤ x)) := by
        intro G hG
        simp only [vals, List.map_replicate, hr2l]
        rw [hG.wire_eq w hw _ (by omega), hr.wire_eq w hw _ hβ, hb1]
      rw [happ, vals_frame hn w hw _ how, hov w hw, hnv w hw, hrepv R.1 (Extends.refl _ _),
        hrepv O.1 ho, vals_frame ho w hw _ hr2w, hR2]
      exact unfold_pure N x hx

end Cons
section Assemble

lemma extends_nil_props {base : ℕ} {gs : List Gate} (h : Extends base [] gs) (o : ℕ) :
    FanInTwo ⟨gs, o⟩ ∧ ReadsBack base ⟨gs, o⟩ := by
  rcases h with ⟨e, rfl, hf, hr⟩
  refine ⟨fun g hg => hf g (by simpa using hg), ?_⟩
  intro j hj i hi
  have := hr j (by simpa using hj) i (by simpa [gateAt] using hi)
  simpa using this

noncomputable def monoList (n m : ℕ) :
    List Gate → List (Finset (Fin n) → Finset (Fin m) → Bool) → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, Q :: Qs =>
    let e := emitMonoQ n m (n + m + 2) (n + m) (n + m + 1) gs Q
    let r := monoList n m e.1 Qs
    (r.1, e.2 :: r.2)

lemma monoList_spec (n m : ℕ) : ∀ (Qs : List (Finset (Fin n) → Finset (Fin m) → Bool))
    (gs : List Gate),
    (∀ Q ∈ Qs, ∀ (x1 x2 : Finset (Fin n)) (z1 z2 : Finset (Fin m)),
      x1 ⊆ x2 → z1 ⊆ z2 → Q x1 z1 = true → Q x2 z2 = true) →
    let r := monoList n m gs Qs
    Extends (n + m + 2) gs r.1 ∧ notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    r.2.length = Qs.length ∧ (∀ i ∈ r.2, i < n + m + 2 + r.1.length) ∧
    ∀ x z, vals r.1 (pairVec n m x z) r.2 = Qs.map (fun Q => Q x z) := by
  intro Qs
  induction Qs with
  | nil => intro gs _; exact ⟨Extends.refl _ _, rfl, rfl, by simp [monoList], fun _ _ => rfl⟩
  | cons Q Qs ih =>
    intro gs hQ
    dsimp only [monoList]
    obtain ⟨he, hlt, hnc, hv⟩ := emitMonoQ_spec n m (n + m + 2) (n + m) (n + m + 1) rfl
      (by omega) (by omega) gs Q (hQ Q (by simp)) (fun x z => pairVec_getD_false n m x z)
      (fun x z => pairVec_getD_true n m x z)
    obtain ⟨hr, hrnc, hrl, hrw, hrv⟩ := ih (emitMonoQ n m (n + m + 2) (n + m) (n + m + 1) gs Q).1
      (fun Q' hQ' => hQ Q' (by simp [hQ']))
    refine ⟨he.trans hr, by rw [hrnc, hnc], by simp [hrl], ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · have := hr.length_le; omega
      · exact hrw i hi
    · intro x z
      have e1 : ∀ (G : List Gate) (a : ℕ) (l : List ℕ) (w : List Bool),
          vals G w (a :: l) = (wiresFrom G w).getD a false :: vals G w l := fun _ _ _ _ => rfl
      rw [e1, hrv, hr.wire_eq _ (pairVec_length n m x z) _ hlt, hv]
      rfl

def sufOrK (base z : ℕ) : ℕ → ℕ → List Gate → List Gate × List ℕ
  | _, 0, gs => (gs, [])
  | s, k + 1, gs =>
    let r := sufOrK base z (s + 1) k gs
    let e := emitBin GateOp.or base r.1 s (r.2.headD z)
    (e.1, e.2 :: r.2)

lemma sufOrK_spec (n : ℕ) : ∀ (k s : ℕ), s + k = n →
    let r := sufOrK (n + 2) n s k []
    Extends (n + 2) [] r.1 ∧ r.1.length = k ∧ notCount ⟨r.1, 0⟩ = 0 ∧ r.2.length = k ∧
    (∀ i ∈ r.2, i < n + 2 + r.1.length) ∧
    ∀ A : Finset (Fin n), vals r.1 (inpVec A) r.2 =
      (List.range k).map (fun t => decide (∃ i ∈ A, s + t ≤ i.val)) := by
  intro k
  induction k with
  | zero => intro s _; exact ⟨Extends.refl _ _, rfl, rfl, rfl, by simp [sufOrK], fun _ => rfl⟩
  | succ k ih =>
    intro s hs
    dsimp only [sufOrK]
    obtain ⟨hr, hrl, hrnc, hr2l, hrw, hrv⟩ := ih (s + 1) (by omega)
    set R := sufOrK (n + 2) n (s + 1) k [] with hR
    have hhd : R.2.headD n < n + 2 + R.1.length := by
      cases hc : R.2 with
      | nil => simp only [List.headD_nil]; omega
      | cons y ys => simp only [List.headD_cons]; exact hrw y (by rw [hc]; simp)
    obtain ⟨he, hlt, hlen, hnc, hv⟩ := emitBin_spec GateOp.or (Or.inr rfl) (n + 2) R.1 s
      (R.2.headD n) (by omega) hhd
    refine ⟨hr.trans he, by rw [hlen, hrl], by rw [hnc, hrnc], by simp [hr2l], ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hlt
      · have := hrw i hi; omega
    · intro A
      have hw : (inpVec A).length = n + 2 := inpVec_length A
      have e1 : ∀ (G : List Gate) (a : ℕ) (l : List ℕ) (w : List Bool),
          vals G w (a :: l) = (wiresFrom G w).getD a false :: vals G w l := fun _ _ _ _ => rfl
      rw [e1, hv _ hw, vals_frame he _ hw _ hrw, hrv A]
      have hsv : (wiresFrom R.1 (inpVec A)).getD s false = decide (∃ i ∈ A, s ≤ i.val ∧ i.val ≤ s) := by
        rw [wiresFrom_getD_lt _ _ _ (by omega)]
        have := inpVec_getD_fin A ⟨s, by omega⟩
        simp only at this
        rw [this]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro h; exact ⟨_, h, le_refl _, le_refl _⟩
        · rintro ⟨i, hi, h1, h2⟩
          have : i = ⟨s, by omega⟩ := Fin.ext (by simp; omega)
          rw [← this]; exact hi
      have hhv : (wiresFrom R.1 (inpVec A)).getD (R.2.headD n) false =
          decide (∃ i ∈ A, s + 1 ≤ i.val) := by
        cases hc : R.2 with
        | nil =>
          have hk : k = 0 := by rw [← hr2l, hc]; rfl
          simp only [List.headD_nil]
          rw [wiresFrom_getD_lt _ _ _ (by omega), inpVec_getD_false]
          symm; simp only [decide_eq_false_iff_not, not_exists, not_and, not_le]
          intro i _; have := i.isLt; omega
        | cons y ys =>
          simp only [List.headD_cons]
          have h1 := hrv A
          rw [hc] at h1
          have hk : 0 < k := by rw [← hr2l, hc]; simp
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [List.range_succ_eq_map] at h1
          have h2 := (List.cons.inj h1).1
          simp only at h2
          rw [h2]
      rw [hsv, hhv, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      · simp only [GateOp.eval]
        apply Bool.eq_iff_iff.mpr
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false,
          id_eq, Bool.or_eq_true, decide_eq_true_eq, add_zero]
        constructor
        · rintro (⟨i, hi, h1, _⟩ | ⟨i, hi, h1⟩)
          · exact ⟨i, hi, h1⟩
          · exact ⟨i, hi, by omega⟩
        · rintro ⟨i, hi, h1⟩
          by_cases hh : i.val ≤ s
          · exact Or.inl ⟨i, hi, h1, hh⟩
          · exact Or.inr ⟨i, hi, by omega⟩
      · apply List.map_congr_left
        intro t _
        simp only [Function.comp, Nat.succ_eq_add_one]
        congr 1
        apply propext
        constructor
        · rintro ⟨i, hi, h1⟩; exact ⟨i, hi, by omega⟩
        · rintro ⟨i, hi, h1⟩; exact ⟨i, hi, by omega⟩

/-! ### Parameters -/

lemma params (r b h : ℕ) (hc : h + 1 ≤ capP r b) :
    ∃ u a, u ≤ b ∧ u + a ≤ r ∧ h + 1 ≤ 2 ^ u * (a + 1) ∧ 2 ^ u * (a + 1) ≤ 2 * h + 1 := by
  classical
  have hex : ∃ u, u ≤ min r b ∧ h + 1 ≤ 2 ^ u * (r - u + 1) := ⟨min r b, le_refl _, hc⟩
  set u := Nat.find hex with hu
  obtain ⟨hu1, hu2⟩ := Nat.find_spec hex
  rw [← hu] at hu1 hu2
  have hexa : ∃ a, h + 1 ≤ 2 ^ u * (a + 1) := ⟨r - u, hu2⟩
  set a := Nat.find hexa with ha
  have ha2 := Nat.find_spec hexa
  rw [← ha] at ha2
  have ha3 : a ≤ r - u := Nat.find_min' hexa hu2
  have hM : 2 ^ u ≤ h + 1 := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0]; simp
    · obtain ⟨v, hvu⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
      have hv : ¬ (v ≤ min r b ∧ h + 1 ≤ 2 ^ v * (r - v + 1)) := Nat.find_min hex (by omega)
      have hv1 : v ≤ min r b := by omega
      have hv2 : 2 ^ v * (r - v + 1) < h + 1 := by
        by_contra hcon; exact hv ⟨hv1, by omega⟩
      have : 2 ^ v * 2 ≤ 2 ^ v * (r - v + 1) := Nat.mul_le_mul_left _ (by omega)
      rw [hvu, pow_succ]; omega
  refine ⟨u, a, by omega, by omega, ha2, ?_⟩
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0]; omega
  · obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hmin : ¬ (h + 1 ≤ 2 ^ u * (a' + 1)) := Nat.find_min hexa (by omega)
    rw [ha']
    have : 2 ^ u * (a' + 1 + 1) = 2 ^ u * (a' + 1) + 2 ^ u := by ring
    omega

/-! ### Codes -/

def codeVec (u a pd x : ℕ) : List Bool :=
  cbits a u x ++ ((List.range (a + 1)).map (fun k => decide (k ≤ cres a u x))).tail ++
    List.replicate pd false

def cset (r u a pd x : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => (codeVec u a pd x).getD i.val false = true)

lemma codeVec_length (u a pd x : ℕ) : (codeVec u a pd x).length = u + a + pd := by
  simp [codeVec, cbits_length]; omega

lemma codeVec_bits (u a pd x i : ℕ) (hi : i < u) :
    (codeVec u a pd x).getD i false = (cbits a u x).getD i false := by
  unfold codeVec
  rw [List.append_assoc, getD_append_left _ _ _ _ (by rw [cbits_length]; exact hi)]

lemma codeVec_un (u a pd x j : ℕ) (hj : j < a) :
    (codeVec u a pd x).getD (u + j) false = decide (j + 1 ≤ cres a u x) := by
  unfold codeVec
  rw [List.append_assoc, getD_append_right _ _ _ _ (by rw [cbits_length]; omega), cbits_length,
    getD_append_left _ _ _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

lemma cbits_order (a : ℕ) : ∀ u x y, x < 2 ^ u * (a + 1) → y < 2 ^ u * (a + 1) →
    (∀ i < u, (cbits a u x).getD i false = true → (cbits a u y).getD i false = true) →
    cres a u x ≤ cres a u y → x ≤ y := by
  intro u
  induction u with
  | zero => intro x y _ _ _ h; simpa [cres] using h
  | succ u ih =>
    intro x y hx hy hb hc
    have hx' := step_lt u a x hx
    have hy' := step_lt u a y hy
    have h0 := hb 0 (by omega)
    simp only [cbits, List.getD_cons_zero] at h0
    have ih' := ih _ _ hx' hy' (fun i hi h => by
      have := hb (i + 1) (by omega)
      simp only [cbits, List.getD_cons_succ] at this
      exact this h) hc
    by_cases hNx : 2 ^ u * (a + 1) ≤ x
    · have hNy : 2 ^ u * (a + 1) ≤ y := by simpa using h0 (by simpa using hNx)
      rw [if_pos hNx, if_pos hNy] at ih'
      omega
    · rw [if_neg hNx] at ih'
      split_ifs at ih' <;> omega

lemma cset_order (r u a pd x y : ℕ) (hr : u + a + pd = r) (hx : x < 2 ^ u * (a + 1))
    (hy : y < 2 ^ u * (a + 1)) (hs : cset r u a pd x ⊆ cset r u a pd y) : x ≤ y := by
  have hg : ∀ i < r, (codeVec u a pd x).getD i false = true →
      (codeVec u a pd y).getD i false = true := by
    intro i hi h
    have := hs (show (⟨i, hi⟩ : Fin r) ∈ cset r u a pd x from by
      simp only [cset, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
    simp only [cset, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  apply cbits_order a u x y hx hy
  · intro i hi h
    have := hg i (by omega) (by rw [codeVec_bits _ _ _ _ _ hi]; exact h)
    rwa [codeVec_bits _ _ _ _ _ hi] at this
  · by_contra hcon
    have hcx := cres_le a u x hx
    have hj : cres a u y < a := by omega
    have := hg (u + cres a u y) (by omega)
      (by rw [codeVec_un _ _ _ _ _ hj]; simp; omega)
    rw [codeVec_un _ _ _ _ _ hj] at this
    simp at this

/-! ### The encoder: thresholds, then folding -/

lemma buildC (n r u a : ℕ) (hr : u + a ≤ r) (gs0 : List Gate) (L : List ℕ)
    (xf : Finset (Fin n) → ℕ) (h0 : Extends (n + 2) [] gs0) (hnc : notCount ⟨gs0, 0⟩ = 0)
    (hL : L.length = 2 ^ u * (a + 1)) (hLw : ∀ i ∈ L, i < n + 2 + gs0.length)
    (hx : ∀ A, xf A < 2 ^ u * (a + 1))
    (hv : ∀ A, vals gs0 (inpVec A) L = (List.range (2 ^ u * (a + 1))).map (fun k => decide (k ≤ xf A))) :
    ∃ (C : Circuit) (tap : Fin r → ℕ), FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧ notCount C = u ∧
      C.size - notCount C ≤ gs0.length + 2 * (2 ^ u * (a + 1)) ∧
      ∀ A, ∀ i : Fin r, (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ A)) ++ [false, true])).getD
        (tap i) false = (codeVec u a (r - u - a) (xf A)).getD i.val false := by
  obtain ⟨hf, hflen, hfnc, hf1l, hf2l, hf1w, hf2w, hfv⟩ := foldAll_spec (n + 2) a u gs0 L hL hLw
  set F := foldAll (n + 2) a u gs0 L with hF
  set pd := r - u - a with hpd
  set tapL := F.2.1 ++ F.2.2.tail ++ List.replicate pd n with htapL
  have hfl := hf.length_le
  have htl : tapL.length = r := by simp [tapL, hf1l, hf2l]; omega
  have htw : ∀ i ∈ tapL, i < n + 2 + F.1.length := by
    intro i hi
    simp only [tapL, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact hf1w i hi
    · exact hf2w i (List.mem_of_mem_tail hi)
    · rw [List.eq_of_mem_replicate hi]; omega
  obtain ⟨hfan, hrb⟩ := extends_nil_props (h0.trans hf) n
  refine ⟨⟨F.1, n⟩, fun i => tapL.getD i.val 0, hfan, hrb, by show n < n + 2 + F.1.length; omega, ?_, ?_, ?_, ?_⟩
  · intro i
    exact htw _ (getD_mem _ _ _ (by omega))
  · show notCount ⟨F.1, 0⟩ = u
    rw [hfnc, hnc]; simp
  · show F.1.length - notCount ⟨F.1, 0⟩ ≤ _
    rw [hfnc, hnc]; omega
  · intro A i
    have hw : (inpVec A).length = n + 2 := inpVec_length A
    obtain ⟨h1, h2⟩ := hfv (inpVec A) (xf A) hw (hx A) (hv A)
    have hval : vals F.1 (inpVec A) tapL = codeVec u a pd (xf A) := by
      simp only [tapL, codeVec, vals, List.map_append, List.map_tail, List.map_replicate]
      simp only [vals] at h1 h2
      rw [h1, h2, wiresFrom_getD_lt _ _ _ (by omega), inpVec_getD_false]
    exact vals_getD F.1 (inpVec A) tapL _ hval i.val (by omega)

lemma dvec_eq (r m : ℕ) (c : List Bool) (tap : Fin r → ℕ) (cv : List Bool) (B : Finset (Fin m))
    (hc : ∀ i : Fin r, c.getD (tap i) false = cv.getD i.val false) :
    List.ofFn (fun i => c.getD (tap i) false) ++ List.ofFn (fun i : Fin m => decide (i ∈ B)) ++
      [false, true] = pairVec r m (Finset.univ.filter (fun i : Fin r => cv.getD i.val false = true)) B := by
  have : (fun i => c.getD (tap i) false) = (fun i : Fin r =>
      decide (i ∈ Finset.univ.filter (fun i : Fin r => cv.getD i.val false = true))) := by
    funext i; rw [hc i]; simp
  simp only [pairVec, bits]; rw [this]

end Assemble
section Parts

lemma pairVec_zero (n : ℕ) (A : Finset (Fin n)) : pairVec n 0 A ∅ = inpVec A := by
  simp [pairVec, bits, inpVec]

lemma map_range_getD (l : List Bool) : (List.range l.length).map (fun i => l.getD i false) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

lemma thr_pure (h P x : ℕ) (hx : x ≤ h) (f : ℕ → Bool) (hf : ∀ t, f t = decide (t + 1 ≤ x)) :
    true :: ((List.range h).map f ++ List.replicate P false) =
      (List.range (h + 1 + P)).map (fun k => decide (k ≤ x)) := by
  rw [List.range_add, List.range_succ_eq_map]
  simp only [List.map_append, List.map_cons, List.map_map, List.cons_append]
  congr 1
  congr 1
  · apply List.map_congr_left; intro t _; simp [hf]
  · symm; apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro y hy
    simp only [List.mem_map, List.mem_range, Function.comp] at hy
    obtain ⟨j, _, rfl⟩ := hy
    simp; omega

lemma final_pure (h W x : ℕ) (hW : h + 1 ≤ W) (bf : ℕ → Bool) :
    (List.zipWith (fun p q => GateOp.and.eval [p, q]) ((List.range h).map bf)
      ((List.range W).map (fun k => decide (k ≤ x))).tail).any id =
    decide (∃ j < h, bf j = true ∧ j + 1 ≤ x) := by
  have : List.zipWith (fun p q => GateOp.and.eval [p, q]) ((List.range h).map bf)
      ((List.range W).map (fun k => decide (k ≤ x))).tail =
      (List.range h).map (fun j => bf j && decide (j + 1 ≤ x)) := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp [GateOp.eval]
  rw [this]
  apply Bool.eq_iff_iff.mpr; simp [List.any_eq_true]

lemma part2_conv (h r b : ℕ) (hc : h + 1 ≤ capP r b) :
    fitP h h 1 r b (32 * (h + 1)) (fun _ A B => decide (∃ i ∈ A, ∃ j ∈ B, j ≤ i)) := by
  obtain ⟨u, a, hub, hur, hW1, hW2⟩ := params r b h hc
  set W := 2 ^ u * (a + 1) with hW
  obtain ⟨hs, hsl, hsnc, hs2l, hsw, hsv⟩ := sufOrK_spec h h 0 (by omega)
  set S := sufOrK (h + 2) h 0 h [] with hS
  set L := (h + 1) :: (S.2 ++ List.replicate (W - (h + 1)) h) with hL
  set xf : Finset (Fin h) → ℕ := fun A => A.sup (fun i => i.val + 1) with hxf
  have hxle : ∀ A, xf A ≤ h := fun A => Finset.sup_le (fun i _ => i.isLt)
  have hxiff : ∀ A (t : ℕ), (∃ i ∈ A, t ≤ i.val) ↔ t + 1 ≤ xf A := by
    intro A t
    rw [hxf]
    simp only
    rw [Finset.le_sup_iff (Nat.succ_pos t)]
    constructor <;> rintro ⟨i, hi, h1⟩ <;> exact ⟨i, hi, by omega⟩
  have hLv : ∀ A, vals S.1 (inpVec A) L = (List.range W).map (fun k => decide (k ≤ xf A)) := by
    intro A
    have hw : (inpVec A).length = h + 2 := inpVec_length A
    have e1 : vals S.1 (inpVec A) L = (wiresFrom S.1 (inpVec A)).getD (h + 1) false ::
        (vals S.1 (inpVec A) S.2 ++ List.replicate (W - (h + 1)) ((wiresFrom S.1 (inpVec A)).getD h false)) := by
      simp [L, vals, List.map_replicate]
    rw [e1, hsv A, wiresFrom_getD_lt _ _ _ (by omega), wiresFrom_getD_lt _ _ _ (by omega),
      inpVec_getD_true, inpVec_getD_false]
    have hWe : W = h + 1 + (W - (h + 1)) := by omega
    rw [congrArg List.range hWe]
    exact thr_pure h _ (xf A) (hxle A) (fun t => decide (∃ i ∈ A, 0 + t ≤ i.val)) (fun t => by
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, zero_add]; exact hxiff A t)
  have hLl : L.length = W := by simp [L, hs2l]; omega
  have hLw : ∀ i ∈ L, i < h + 2 + S.1.length := by
    intro i hi
    simp only [L, List.mem_cons, List.mem_append] at hi
    rcases hi with rfl | hi | hi
    · omega
    · exact hsw i hi
    · rw [List.eq_of_mem_replicate hi]; omega
  obtain ⟨C, tap, hCf, hCr, hCo, hCt, hCn, hCs, hCv⟩ := buildC h r u a hur S.1 L xf hs hsnc hLl hLw
    (fun A => by have := hxle A; omega) hLv
  set pd := r - u - a with hpd
  -- the decoder
  set base' := r + h + 2 with hbase'
  have hbl : ∀ i ∈ List.range u, i < base' + ([] : List Gate).length := by
    intro i hi; simp at hi ⊢; omega
  have hL0 : ∀ i ∈ (r + h + 1) :: (List.range a).map (fun j => u + j),
      i < base' + ([] : List Gate).length := by
    intro i hi; simp at hi ⊢; rcases hi with rfl | ⟨j, hj, rfl⟩ <;> omega
  obtain ⟨hU, hUl, hUnc, hU2l, hU2w, hUv⟩ := unfoldAll_spec base' a (List.range u) []
    ((r + h + 1) :: (List.range a).map (fun j => u + j)) (by simp) hbl hL0
  simp only [List.length_range] at hUl hU2l hUv
  set U := unfoldAll base' (List.range u) [] ((r + h + 1) :: (List.range a).map (fun j => u + j)) with hUdef
  have hUll := hU.length_le
  have hBw : ∀ i ∈ (List.range h).map (fun j => r + j), i < base' + U.1.length := by
    intro i hi; simp at hi; omega
  have hUt : ∀ i ∈ U.2.tail, i < base' + U.1.length := fun i hi => hU2w i (List.mem_of_mem_tail hi)
  obtain ⟨hZ, hZl, hZnc, hZw, hZv⟩ := zipBin_spec GateOp.and (Or.inl rfl) base' _ _ U.1 hBw hUt
  set Z := zipBin GateOp.and base' U.1 ((List.range h).map (fun j => r + j)) U.2.tail with hZdef
  have hZll := hZ.length_le
  obtain ⟨hO, hOlt, hOnc, hOnn, hOv⟩ := emitOrList_spec base' Z.2 (r + h) Z.1 (by omega) hZw
  set O := emitOrList base' (r + h) Z.1 Z.2 with hOdef
  have hZ2l : Z.2.length = h := by
    rw [hZdef, zipBin_len2]; simp [hU2l]; omega
  obtain ⟨hDf, hDr⟩ := extends_nil_props (hU.trans (hZ.trans hO)) O.2
  have hDnc : notCount ⟨O.1, O.2⟩ = 0 := by
    show notCount ⟨O.1, 0⟩ = 0
    rw [hOnc, hZnc, hUnc]; rfl
  refine ⟨C, ⟨O.1, O.2⟩, tap, fun _ => O.2, hCf, hCr, hDf, hDr, hCo, hOlt, hCt,
    fun _ => hOlt, by omega, hDnc, ?_, ?_⟩
  · -- size
    have hOs : O.1.length ≤ Z.1.length + h := by
      have h1 : nonNot O.1 = O.1.length := by
        unfold nonNot; rw [show notCount ⟨O.1, 0⟩ = 0 from hDnc]; simp
      have h2 : nonNot Z.1 = Z.1.length := by
        unfold nonNot; rw [hZnc, hUnc]; simp [notCount]
      rw [← h1]; rw [h2, hZ2l] at hOnn; exact hOnn
    have hZs : Z.1.length ≤ U.1.length + h := by
      rw [hZl]; have : ((List.range h).map (fun j => r + j)).length = h := by simp
      omega
    show C.size - notCount C + O.1.length ≤ 32 * (h + 1)
    simp only [List.length_nil] at hUl
    have hvl : ((List.range h).map (fun j => r + j)).length = h := by simp
    omega
  · intro A B
    simp only
    intro t
    rw [dvec_eq r h _ tap _ B (hCv A)]
    set X := Finset.univ.filter (fun i : Fin r => (codeVec u a pd (xf A)).getD i.val false = true) with hX
    set dv := pairVec r h X B with hdv
    have hdl : dv.length = base' := by rw [hdv, pairVec_length]
    have hcv : ∀ i < r, dv.getD i false = (codeVec u a pd (xf A)).getD i false := by
      intro i hi
      rw [hdv, pairVec_getD_left r h X B ⟨i, hi⟩]
      simp [hX]
    have hxW : xf A < W := by have := hxle A; omega
    have hb : vals [] dv (List.range u) = cbits a u (xf A) := by
      simp only [vals, wiresFrom_nil]
      rw [← map_range_getD (cbits a u (xf A)), cbits_length]
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [hcv i (by omega), codeVec_bits _ _ _ _ _ hi]
    have hl0 : vals [] dv ((r + h + 1) :: (List.range a).map (fun j => u + j)) =
        (List.range (a + 1)).map (fun k => decide (k ≤ cres a u (xf A))) := by
      simp only [vals, wiresFrom_nil, List.map_cons, List.map_map]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      · rw [hdv, pairVec_getD_true]; simp
      · apply List.map_congr_left
        intro j hj
        rw [List.mem_range] at hj
        simp only [Function.comp]
        rw [hcv _ (by omega), codeVec_un _ _ _ _ _ hj]
    have hUv' := hUv dv (xf A) hdl hxW hb hl0
    have hval := hOv dv hdl
    show (wiresFrom O.1 dv).getD O.2 false = _
    rw [hval]
    rw [wiresFrom_getD_lt _ _ _ (by omega), hdv, pairVec_getD_false, Bool.false_or, ← hdv]
    have hany : Z.2.any (fun i => (wiresFrom Z.1 dv).getD i false) = (vals Z.1 dv Z.2).any id := by
      simp [vals, List.any_map]
    rw [hany, hZv dv hdl]
    have hbv : vals U.1 dv ((List.range h).map (fun j => r + j)) =
        (List.range h).map (fun j => decide (j ∈ B.image Fin.val)) := by
      simp only [vals, List.map_map]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      simp only [Function.comp]
      rw [wiresFrom_getD_lt _ _ _ (by omega)]
      have := pairVec_getD_right r h X B ⟨j, hj⟩
      simp only at this
      rw [← hdv] at this
      rw [this]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Finset.mem_image]
      constructor
      · intro hm; exact ⟨_, hm, rfl⟩
      · rintro ⟨y, hy, hye⟩
        have : y = ⟨j, hj⟩ := Fin.ext hye
        rw [← this]; exact hy
    have htl : vals U.1 dv U.2.tail = (vals U.1 dv U.2).tail := by simp [vals, List.map_tail]
    rw [hbv, htl, hUv', final_pure h W (xf A) hW1]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, ⟨y, hy, rfl⟩, hle⟩
      obtain ⟨i, hi, hji⟩ := (hxiff A y.val).mpr hle
      exact ⟨i, hi, y, hy, Fin.le_iff_val_le_val.mpr hji⟩
    · rintro ⟨i, hi, y, hy, hyi⟩
      exact ⟨y.val, y.isLt, ⟨y, hy, rfl⟩, (hxiff A y.val).mp ⟨i, hi, Fin.le_iff_val_le_val.mp hyi⟩⟩

lemma part1_conv (n m q r b h : ℕ) (rank : Finset (Fin n) → Fin (h + 1))
    (G : Fin q → Fin (h + 1) → Finset (Fin m) → Bool)
    (hrank : ∀ A B, A ⊆ B → rank A ≤ rank B)
    (hG : ∀ t i j B U, i ≤ j → B ⊆ U → G t i B = true → G t j U = true)
    (hc : h + 1 ≤ capP r b) :
    ∃ p, fitP n m q r b p (fun t A B => G t (rank A) B) := by
  obtain ⟨u, a, hub, hur, hW1, _⟩ := params r b h hc
  set W := 2 ^ u * (a + 1) with hW
  set Qs : List (Finset (Fin n) → Finset (Fin 0) → Bool) :=
    (List.range W).map (fun k => fun x _ => decide (k ≤ (rank x).val)) with hQs
  obtain ⟨hM, hMnc, hMl, hMw, hMv⟩ := monoList_spec n 0 Qs [] (by
    intro Q hQ x1 x2 z1 z2 hx _ hq
    simp only [hQs, List.mem_map, List.mem_range] at hQ
    obtain ⟨k, _, rfl⟩ := hQ
    simp only [decide_eq_true_eq] at hq ⊢
    exact le_trans hq (Fin.le_iff_val_le_val.mp (hrank _ _ hx)))
  set M := monoList n 0 [] Qs with hMdef
  set pd := r - u - a with hpd
  obtain ⟨C, tap, hCf, hCr, hCo, hCt, hCn, _, hCv⟩ := buildC n r u a hur M.1 M.2
    (fun A => (rank A).val) hM hMnc (by rw [hMl, hQs]; simpa using hW) hMw
    (fun A => by have := (rank A).isLt; omega)
    (fun A => by rw [← pairVec_zero, hMv, hQs, List.map_map, ← hW]; rfl)
  set Qt : Fin q → Finset (Fin r) → Finset (Fin m) → Bool := fun t X B =>
    decide (∃ k : Fin (h + 1), cset r u a pd k.val ⊆ X ∧ G t k B = true) with hQt
  obtain ⟨hN, hNnc, hNl, hNw, hNv⟩ := monoList_spec r m ((List.finRange q).map Qt) [] (by
    intro Q hQ x1 x2 z1 z2 hx hz hq
    simp only [List.mem_map] at hQ
    obtain ⟨t, _, rfl⟩ := hQ
    simp only [hQt, decide_eq_true_eq] at hq ⊢
    obtain ⟨k, hk1, hk2⟩ := hq
    exact ⟨k, hk1.trans hx, hG t k k z1 z2 le_rfl hz hk2⟩)
  set N := monoList r m [] ((List.finRange q).map Qt) with hNdef
  obtain ⟨hDf, hDr⟩ := extends_nil_props hN (r + m)
  refine ⟨_, C, ⟨N.1, r + m⟩, tap, fun t => N.2.getD t.val 0, hCf, hCr, hDf, hDr, hCo,
    by show r + m < r + m + 2 + N.1.length; omega, hCt, ?_, by omega, by show notCount ⟨N.1, 0⟩ = 0; rw [hNnc]; rfl,
    le_rfl, ?_⟩
  · intro t
    exact hNw _ (getD_mem _ _ _ (by rw [hNl]; simp))
  · intro A B
    simp only
    intro t
    rw [dvec_eq r m _ tap _ B (hCv A)]
    have hv := hNv (Finset.univ.filter (fun i : Fin r =>
      (codeVec u a pd (rank A).val).getD i.val false = true)) B
    show (wiresFrom N.1 _).getD _ false = _
    rw [vals_getD _ _ _ _ hv t.val (by rw [hNl]; simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_map, List.getElem_finRange]
    have hX : Finset.univ.filter (fun i : Fin r =>
        (codeVec u a pd (rank A).val).getD i.val false = true) = cset r u a pd (rank A).val := rfl
    simp only [Fin.cast_mk, Fin.eta]
    rw [hX, hQt]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨k, hk1, hk2⟩
      have hle := cset_order r u a pd k.val (rank A).val (by omega)
        (by have := k.isLt; omega) (by have := (rank A).isLt; omega) hk1
      exact hG t k (rank A) B B (Fin.le_iff_val_le_val.mpr hle) (Finset.Subset.refl _) hk2
    · intro hg
      exact ⟨rank A, Finset.Subset.refl _, hg⟩

end Parts
end PEqualNP.Outside.L_lib_1398_aux

theorem PEqualNP.Outside.L_lib_1398 :
let cap := fun (r b : Nat) => let u := min r b; 2^u*(r-u+1)
let fit := fun (n m q r b p : Nat) (F : Fin q → Finset (Fin n) → Finset (Fin m) → Bool) =>
  ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin r → Nat) (out : Fin q → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+m+2) D ∧
    C.output < n+2+C.size ∧ D.output < r+m+2+D.size ∧
    (∀ i, tap i < n+2+C.size) ∧ (∀ t, out t < r+m+2+D.size) ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D = 0 ∧
    C.size-PEqualNP.NotBracket.notCount C+D.size ≤ p ∧
    ∀ A B, let c := C.wires (List.ofFn (fun i : Fin n => decide (i ∈ A)) ++ [false,true])
           let w := D.wires (List.ofFn (fun i => c.getD (tap i) false) ++
             List.ofFn (fun i : Fin m => decide (i ∈ B)) ++ [false,true])
           ∀ t, w.getD (out t) false = F t A B
(∀ (n m q r b h : Nat) (rank : Finset (Fin n) → Fin (h+1))
    (chain : Fin (h+1) → Finset (Fin n)) (G : Fin q → Fin (h+1) → Finset (Fin m) → Bool),
  (∀ A B, A ⊆ B → rank A ≤ rank B) → (∀ i j, i ≤ j → chain i ⊆ chain j) →
  (∀ i, rank (chain i) = i) →
  (∀ t i j B U, i ≤ j → B ⊆ U → G t i B = true → G t j U = true) →
  (∀ i : Fin h, ∃ t B, G t i.castSucc B = false ∧ G t i.succ B = true) →
  ((∃ p, fit n m q r b p (fun t A B => G t (rank A) B)) ↔ h+1 ≤ cap r b)) ∧
∀ h r b : Nat,
  let F := fun (_ : Fin 1) (A B : Finset (Fin h)) => decide (∃ i ∈ A, ∃ j ∈ B, j ≤ i)
  (fit h h 1 r b (32*(h+1)) F ↔ h+1 ≤ cap r b) := by
  intro cap fit
  refine ⟨?_, ?_⟩
  · intro n m q r b h rank chain G hrank hchain hrc hG hstep
    constructor
    · rintro ⟨p, hp⟩
      refine PEqualNP.Outside.L_lib_1398_aux.fit_lower n m q r b p h _ chain hchain ?_ hp
      intro i j hij
      obtain ⟨t, B, h1, h2⟩ := hstep ⟨i.val, by have := j.isLt; omega⟩
      refine ⟨t, B, ?_, ?_⟩
      · simp only [hrc]
        have : (Fin.castSucc ⟨i.val, by have := j.isLt; omega⟩ : Fin (h + 1)) = i := Fin.ext rfl
        rw [this] at h1; exact h1
      · simp only [hrc]
        exact hG t _ j B B (by rw [Fin.le_iff_val_le_val]; simp; omega) (Finset.Subset.refl _) h2
    · intro hc
      exact PEqualNP.Outside.L_lib_1398_aux.part1_conv n m q r b h rank G hrank hG hc
  · intro h r b F
    constructor
    · intro hfit
      refine PEqualNP.Outside.L_lib_1398_aux.fit_lower h h 1 r b _ h F
        (fun i => Finset.univ.filter (fun j : Fin h => j.val < i.val)) ?_ ?_ hfit
      · intro i j hij x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [Fin.le_iff_val_le_val] at hij; omega
      · intro i j hij
        rw [Fin.lt_iff_val_lt_val] at hij
        have hi : i.val < h := by have := j.isLt; omega
        refine ⟨0, {⟨i.val, hi⟩}, ?_, ?_⟩
        · simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            decide_eq_false_iff_not, not_exists, not_and]
          intro x hx y hy
          subst hy
          rw [Fin.le_iff_val_le_val]; simp; omega
        · simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            decide_eq_true_eq]
          exact ⟨⟨i.val, hi⟩, hij, ⟨i.val, hi⟩, rfl, le_rfl⟩
    · intro hc
      exact PEqualNP.Outside.L_lib_1398_aux.part2_conv h r b hc
