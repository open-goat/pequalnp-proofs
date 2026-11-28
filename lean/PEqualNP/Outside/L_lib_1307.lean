import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1307_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section CircuitEngine

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

lemma getD_eq_of_lt {α : Type*} (l : List α) (i : ℕ) (d1 d2 : α) (hi : i < l.length) :
    l.getD i d1 = l.getD i d2 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma getD_mem {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

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
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [emitAnd]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.and, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitOr base gs a b
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) := by
  dsimp only [emitOr]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.or, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitNot_spec (base : ℕ) (gs : List Gate) (a : ℕ)
    (ha : a < base + gs.length) :
    let r := emitNot base gs a
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false = !((wiresFrom gs w).getD a false) := by
  dsimp only [emitNot]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.not, [a]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_singleton] at hi
      subst hi; omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

def emitOrList (base : ℕ) : List Gate → ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitOr base gs acc w
    emitOrList base r.1 r.2 ws

lemma emitOrList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate) (acc : ℕ),
      acc < base + gs.length →
      (∀ w ∈ ws, w < base + gs.length) →
      let r := emitOrList base gs acc ws
      Extends base gs r.1 ∧
      r.1.length = gs.length + ws.length ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (v : List Bool), v.length = base →
        (wiresFrom r.1 v).getD r.2 false =
          ((wiresFrom gs v).getD acc false || ws.any (fun w => (wiresFrom gs v).getD w false)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs acc hacc _
    dsimp only [emitOrList]
    refine ⟨Extends.refl base gs, by simp, hacc, rfl, fun v _ => by simp⟩
  | cons w rest ih =>
    intro gs acc hacc hws
    dsimp only [emitOrList]
    have hw_lt : w < base + gs.length := hws w (List.mem_cons_self ..)
    set r1 := emitOr base gs acc w with hr1
    have h1 := emitOr_spec base gs acc w hacc hw_lt
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hrest_lt : ∀ u ∈ rest, u < base + r1.1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem w hu); omega
    have h2 := ih r1.1 r1.2 hlt1 hrest_lt
    dsimp only at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by simp [hlen2, hlen1]; omega, hlt2, by omega, ?_⟩
    intro v hv
    rw [hval2 v hv, hval1 v hv]
    have hany : rest.any (fun u => (wiresFrom r1.1 v).getD u false) =
        rest.any (fun u => (wiresFrom gs v).getD u false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨u, hu, ht⟩ <;> refine ⟨u, hu, ?_⟩
      · rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))] at ht
      · rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))]
    rw [hany, List.any_cons, Bool.or_assoc]

def emitAndList (base : ℕ) : List Gate → ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitAnd base gs acc w
    emitAndList base r.1 r.2 ws

lemma emitAndList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate) (acc : ℕ),
      acc < base + gs.length →
      (∀ w ∈ ws, w < base + gs.length) →
      let r := emitAndList base gs acc ws
      Extends base gs r.1 ∧
      r.1.length = gs.length + ws.length ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (v : List Bool), v.length = base →
        (wiresFrom r.1 v).getD r.2 false =
          ((wiresFrom gs v).getD acc false && ws.all (fun w => (wiresFrom gs v).getD w false)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs acc hacc _
    dsimp only [emitAndList]
    refine ⟨Extends.refl base gs, by simp, hacc, rfl, fun v _ => by simp⟩
  | cons w rest ih =>
    intro gs acc hacc hws
    dsimp only [emitAndList]
    have hw_lt : w < base + gs.length := hws w (List.mem_cons_self ..)
    set r1 := emitAnd base gs acc w with hr1
    have h1 := emitAnd_spec base gs acc w hacc hw_lt
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hrest_lt : ∀ u ∈ rest, u < base + r1.1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem w hu); omega
    have h2 := ih r1.1 r1.2 hlt1 hrest_lt
    dsimp only at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by simp [hlen2, hlen1]; omega, hlt2, by omega, ?_⟩
    intro v hv
    rw [hval2 v hv, hval1 v hv]
    have hall : rest.all (fun u => (wiresFrom r1.1 v).getD u false) =
        rest.all (fun u => (wiresFrom gs v).getD u false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h u hu
      · have := h u hu; rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))] at this
      · have := h u hu; rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))]
    rw [hall, List.all_cons, Bool.and_assoc]

noncomputable def notIndices (gs : List Gate) : List ℕ :=
  (List.range gs.length).filter (fun g =>
    @decide ((gs.getD g ⟨GateOp.or, []⟩).op = GateOp.not) (Classical.propDecidable _))

lemma notIndices_append (gs1 gs2 : List Gate) :
    notIndices (gs1 ++ gs2) = notIndices gs1 ++ (notIndices gs2).map (fun k => gs1.length + k) := by
  dsimp only [notIndices]
  rw [List.length_append, List.range_add, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro g hg; rw [List.mem_range] at hg; rw [getD_append_left gs1 gs2 g _ hg]
  · rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro k hk; rw [List.mem_range] at hk
    simp only [Function.comp_def]
    rw [getD_append_right gs1 gs2 (gs1.length + k) _ (by omega)]
    have : gs1.length + k - gs1.length = k := by omega
    rw [this]

lemma notIndices_length (gs : List Gate) : (notIndices gs).length = notCount ⟨gs, 0⟩ := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    have hsp : g :: rest = [g] ++ rest := rfl
    rw [hsp, notIndices_append, List.length_append, List.length_map, ih, notCount_append]
    congr 1
    dsimp only [notIndices, notCount]
    simp only [List.length_singleton, List.range_one, List.filter_cons, List.filter_nil, List.getD_cons_zero]
    by_cases hgn : g.op = GateOp.not
    · have h1 : @decide (g.op = GateOp.not) (Classical.propDecidable _) = true :=
        (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr hgn
      rw [h1]; rw [hgn]; simp
    · have h1 : @decide (g.op = GateOp.not) (Classical.propDecidable _) = false :=
        (@decide_eq_false_iff_not _ (Classical.propDecidable _)).mpr hgn
      rw [h1]
      cases hgop : g.op <;> simp [hgop] at hgn ⊢

lemma notIndices_eq_nil_of_notCount_zero (gs : List Gate) (hnc : notCount ⟨gs, 0⟩ = 0) :
    notIndices gs = [] := by
  have h := notIndices_length gs
  rw [hnc] at h
  exact List.eq_nil_of_length_eq_zero h

lemma notIndices_append_zero (gs1 gs2 : List Gate) (hnc : notCount ⟨gs2, 0⟩ = 0) :
    notIndices (gs1 ++ gs2) = notIndices gs1 := by
  rw [notIndices_append, notIndices_eq_nil_of_notCount_zero gs2 hnc]; simp

lemma notIndices_append_not (gs : List Gate) (a : ℕ) :
    notIndices (gs ++ [⟨GateOp.not, [a]⟩]) = notIndices gs ++ [gs.length] := by
  rw [notIndices_append]
  have h1 : notIndices [⟨GateOp.not, [a]⟩] = [0] := by
    dsimp only [notIndices]
    simp only [List.length_singleton, List.range_one, List.filter_cons, List.filter_nil]
    have ht : @decide ((([⟨GateOp.not, [a]⟩] : List Gate).getD 0 ⟨GateOp.or, []⟩).op = GateOp.not)
        (Classical.propDecidable _) = true :=
      (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr rfl
    rw [ht]; rfl
  rw [h1]; simp

lemma notIndices_pairwise_lt (gs : List Gate) : (notIndices gs).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma notIndices_strictMono (gs : List Gate) {i j : ℕ} (hi : i < j) (hj : j < (notIndices gs).length) :
    (notIndices gs).getD i gs.length < (notIndices gs).getD j gs.length := by
  have hi' : i < (notIndices gs).length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.pairwise_iff_getElem.mp (notIndices_pairwise_lt gs) i j hi' hj hi

lemma mem_notIndices_iff (gs : List Gate) (g : ℕ) :
    g ∈ notIndices gs ↔ g < gs.length ∧ (gs.getD g ⟨GateOp.or, []⟩).op = GateOp.not := by
  dsimp only [notIndices]
  rw [List.mem_filter, List.mem_range]
  exact and_congr_right fun _ => iff_of_eq (@decide_eq_true_eq _ (Classical.propDecidable _))

lemma nat_lt_of_high_bit {a b k0 : ℕ}
    (hhigh : ∀ k, k0 < k → a.testBit k = b.testBit k)
    (ha : a.testBit k0 = false) (hb : b.testBit k0 = true) : a < b := by
  have hdiv_eq : a / 2 ^ (k0 + 1) = b / 2 ^ (k0 + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact hhigh (i + (k0 + 1)) (by omega)
  have hda : a / 2 ^ k0 = 2 * (a / 2 ^ (k0 + 1)) := by
    have h1 : a / 2 ^ k0 / 2 = a / 2 ^ (k0 + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hmod : (a / 2 ^ k0) % 2 = 0 := by
      have ht : a.testBit k0 = decide (a / 2 ^ k0 % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
      rw [ha] at ht
      have hne : (a / 2 ^ k0) % 2 ≠ 1 := by intro h1'; rw [h1'] at ht; simp at ht
      omega
    omega
  have hdb : b / 2 ^ k0 = 2 * (b / 2 ^ (k0 + 1)) + 1 := by
    have h1 : b / 2 ^ k0 / 2 = b / 2 ^ (k0 + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hmod : (b / 2 ^ k0) % 2 = 1 := by
      have ht : b.testBit k0 = decide (b / 2 ^ k0 % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
      rw [hb] at ht; exact of_decide_eq_true ht.symm
    omega
  have hlt_div : a / 2 ^ k0 < b / 2 ^ k0 := by omega
  have hpos : 0 < 2 ^ k0 := Nat.pow_pos (by omega)
  have ha_lt : a < (a / 2 ^ k0 + 1) * 2 ^ k0 := by
    have hmod : a % 2 ^ k0 < 2 ^ k0 := Nat.mod_lt a hpos
    have hdm := Nat.div_add_mod a (2 ^ k0)
    have hmul : (a / 2 ^ k0 + 1) * 2 ^ k0 = 2 ^ k0 * (a / 2 ^ k0) + 2 ^ k0 := by ring
    omega
  have hb_ge : (a / 2 ^ k0 + 1) * 2 ^ k0 ≤ b :=
    le_trans (Nat.mul_le_mul_right (2 ^ k0) hlt_div) (Nat.div_mul_le_self b (2 ^ k0))
  omega

lemma eq_of_testBit_lt_pow {r a b : ℕ} (ha : a < 2 ^ r) (hb : b < 2 ^ r)
    (heq : ∀ k < r, a.testBit k = b.testBit k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < r
  · exact heq k hk
  · have hge : r ≤ k := Nat.le_of_not_lt hk
    have ha' : a < 2 ^ k := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hge)
    have hb' : b < 2 ^ k := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hge)
    rw [Nat.testBit_lt_two_pow ha', Nat.testBit_lt_two_pow hb']

def VecLe (w1 w2 : List Bool) : Prop :=
  w1.length = w2.length ∧ ∀ k, w1.getD k false = true → w2.getD k false = true

lemma gateOp_mono {op : GateOp}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    {w1 w2 : List Bool} (hle : VecLe w1 w2) (inputs : List ℕ)
    (ht : op.eval (inputs.map fun i => w1.getD i false) = true) :
    op.eval (inputs.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at ht ⊢
    rintro _ ⟨i, hi, rfl⟩; exact hle.2 i (ht _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
    rcases ht with ⟨_, ⟨i, hi, rfl⟩, hti⟩; exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle.2 i hti⟩

lemma gateOp_not_antitone {w1 w2 : List Bool} (hle : VecLe w1 w2) (inputs : List ℕ)
    (ht : GateOp.not.eval (inputs.map fun i => w2.getD i false) = true) :
    GateOp.not.eval (inputs.map fun i => w1.getD i false) = true := by
  cases inputs with
  | nil => simp [GateOp.eval]
  | cons u rest =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true'] at ht ⊢
    cases h1 : w1.getD u false
    · rfl
    · have h2 := hle.2 u h1; rw [h2] at ht; cases ht

lemma vecLe_snoc {w1 w2 : List Bool} (hle : VecLe w1 w2) {b1 b2 : Bool}
    (hb : b1 = true → b2 = true) : VecLe (w1 ++ [b1]) (w2 ++ [b2]) := by
  refine ⟨by simp [hle.1], ?_⟩
  intro k hk
  have hlen12 := hle.1
  by_cases hkl : k < w1.length
  · rw [getD_append_left _ _ k false hkl] at hk
    rw [getD_append_left _ _ k false (by omega)]
    exact hle.2 k hk
  · have hle1 : w1.length ≤ k := Nat.le_of_not_lt hkl
    rw [getD_append_right _ _ k false hle1] at hk
    rw [getD_append_right _ _ k false (by omega), ← hle.1]
    by_cases hkeq : k - w1.length = 0
    · rw [hkeq] at hk ⊢; simp only [List.getD_cons_zero] at hk ⊢; exact hb hk
    · have : ([b1]).getD (k - w1.length) false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
      rw [this] at hk; cases hk

lemma take_succ_eq_append {α : Type*} (l : List α) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]; simp

lemma wires_gate_val (C : Circuit) (w : List Bool) (g : ℕ) (hg : g < C.gates.length) :
    (C.wires w).getD (w.length + g) false =
      (C.gates[g]).op.eval ((C.gates[g]).inputs.map fun i => (wiresFrom (C.gates.take g) w).getD i false) := by
  have hw : wiresFrom C.gates w = wiresFrom (C.gates.drop (g + 1)) (wiresFrom (C.gates.take (g + 1)) w) := by
    rw [← wiresFrom_append, List.take_append_drop]
  change (wiresFrom C.gates w).getD (w.length + g) false = _
  rw [hw]
  have hlen_take : (wiresFrom (C.gates.take (g + 1)) w).length = w.length + (g + 1) := by
    rw [wiresFrom_length, List.length_take]; omega
  rw [wiresFrom_getD_lt _ _ (w.length + g) (by omega)]
  rw [take_succ_eq_append C.gates g hg, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen_g : (wiresFrom (C.gates.take g) w).length = w.length + g := by
    rw [wiresFrom_length, List.length_take]; omega
  rw [getD_append_right _ _ (w.length + g) false (by omega), hlen_g]
  simp

lemma prefix_mono_of_not_le (C : Circuit) (hfit : FanInTwo C)
    {w1 w2 : List Bool} (hle : VecLe w1 w2) :
    ∀ L ≤ C.gates.length,
      (∀ g < L, (C.gates.getD g ⟨GateOp.or, []⟩).op = GateOp.not →
        (C.wires w1).getD (w1.length + g) false = true →
        (C.wires w2).getD (w2.length + g) false = true) →
      VecLe (wiresFrom (C.gates.take L) w1) (wiresFrom (C.gates.take L) w2) := by
  intro L
  induction L with
  | zero => intro _ _; exact hle
  | succ k ih =>
    intro hk hnot
    have hk_lt : k < C.gates.length := by omega
    have hpre : VecLe (wiresFrom (C.gates.take k) w1) (wiresFrom (C.gates.take k) w2) :=
      ih (by omega) (fun g hg => hnot g (by omega))
    rw [take_succ_eq_append C.gates k hk_lt, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
        wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    apply vecLe_snoc hpre
    intro h1
    have hg_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk_lt
    have hop := (hfit C.gates[k] hg_mem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor | hnt
    · exact gateOp_mono (Or.inl hand) hpre _ h1
    · exact gateOp_mono (Or.inr hor) hpre _ h1
    · have hget : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
      have h1' : (C.wires w1).getD (w1.length + k) false = true := by
        rw [wires_gate_val C w1 k hk_lt]; exact h1
      have h2' := hnot k (by omega) (by rw [hget]; exact hnt) h1'
      rwa [wires_gate_val C w2 k hk_lt] at h2'

noncomputable def inVec {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun a : Fin n => @decide (a ∈ s) (Classical.propDecidable _)) ++ [false, true]

lemma inVec_len {n : ℕ} (s : Finset (Fin n)) : (inVec s).length = n + 2 := by simp [inVec]

lemma inVec_getD_lt {n : ℕ} (s : Finset (Fin n)) (a : Fin n) :
    (inVec s).getD a.val false = @decide (a ∈ s) (Classical.propDecidable _) := by
  dsimp only [inVec]
  rw [getD_append_left _ _ a.val false (by simp)]
  simp [List.getD_eq_getElem?_getD, a.isLt]

lemma inVec_getD_z {n : ℕ} (s : Finset (Fin n)) : (inVec s).getD n false = false := by
  dsimp only [inVec]; rw [getD_append_right _ _ n false (by simp)]; simp

lemma inVec_getD_o {n : ℕ} (s : Finset (Fin n)) : (inVec s).getD (n + 1) false = true := by
  dsimp only [inVec]; rw [getD_append_right _ _ (n + 1) false (by simp)]
  have : n + 1 - n = 1 := by omega
  simp [this]

lemma vecLe_inVec {n : ℕ} {s1 s2 : Finset (Fin n)} (hsub : s1 ⊆ s2) :
    VecLe (inVec s1) (inVec s2) := by
  refine ⟨by rw [inVec_len, inVec_len], ?_⟩
  intro k hk
  by_cases hkn : k < n
  · rw [inVec_getD_lt s1 ⟨k, hkn⟩] at hk
    rw [inVec_getD_lt s2 ⟨k, hkn⟩]
    exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr
      (hsub ((@decide_eq_true_eq _ (Classical.propDecidable _)).mp hk))
  · by_cases hk0 : k = n
    · rw [hk0, inVec_getD_z] at hk; cases hk
    · by_cases hk1 : k = n + 1
      · rw [hk1, inVec_getD_o]
      · have hge : (inVec s1).length ≤ k := by rw [inVec_len]; omega
        have : (inVec s1).getD k false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
        rw [this] at hk; cases hk

def bitsToNat : (r : ℕ) → (Fin r → Bool) → ℕ
  | 0, _ => 0
  | r + 1, f => (if f 0 then 2 ^ r else 0) + bitsToNat r (fun i => f i.succ)

lemma bitsToNat_lt : ∀ (r : ℕ) (f : Fin r → Bool), bitsToNat r f < 2 ^ r
  | 0, _ => by simp [bitsToNat]
  | r + 1, f => by
    dsimp only [bitsToNat]
    have ih := bitsToNat_lt r (fun i => f i.succ)
    have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
    cases f 0 <;> simp <;> omega

lemma bitsToNat_testBit : ∀ (r : ℕ) (f : Fin r → Bool) (b : Fin r),
    (bitsToNat r f).testBit (r - 1 - b.val) = f b
  | 0, _, b => Fin.elim0 b
  | r + 1, f, b => by
    dsimp only [bitsToNat]
    set lo := bitsToNat r (fun i => f i.succ)
    have hlo : lo < 2 ^ r := bitsToNat_lt r _
    cases b using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
      have hdiv : ((if f 0 then 2 ^ r else 0) + lo) / 2 ^ r = if f 0 then 1 else 0 := by
        cases f 0
        · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
          exact Nat.div_eq_of_lt hlo
        · simp only [↓reduceIte]
          have h1 : (2 ^ r + lo) / 2 ^ r = 1 + lo / 2 ^ r := by
            rw [Nat.add_div_left _ (Nat.pow_pos (by omega))]; omega
          rw [h1, Nat.div_eq_of_lt hlo]
      have ht : ((if f 0 then 2 ^ r else 0) + lo).testBit r =
          decide (((if f 0 then 2 ^ r else 0) + lo) / 2 ^ r % 2 = 1) :=
        Nat.testBit_eq_decide_div_mod_eq
      rw [ht, hdiv]
      cases f 0 <;> rfl
    | succ b' =>
      have hsub : r + 1 - 1 - b'.succ.val = r - 1 - b'.val := by simp; omega
      rw [hsub]
      have hlt_r : r - 1 - b'.val < r := by omega
      have hmod : ((if f 0 then 2 ^ r else 0) + lo).testBit (r - 1 - b'.val) = lo.testBit (r - 1 - b'.val) := by
        cases f 0
        · simp
        · simp only [↓reduceIte]
          have h1 : (2 ^ r + lo) / 2 ^ (r - 1 - b'.val) =
              2 ^ (r - (r - 1 - b'.val)) + lo / 2 ^ (r - 1 - b'.val) := by
            have hpow : 2 ^ r = 2 ^ (r - 1 - b'.val) * 2 ^ (r - (r - 1 - b'.val)) := by
              rw [← pow_add]; congr 1; omega
            rw [hpow, Nat.mul_add_div (Nat.pow_pos (by omega))]
          have heven : 2 ^ (r - (r - 1 - b'.val)) % 2 = 0 := by
            have hpos : 1 ≤ r - (r - 1 - b'.val) := by omega
            have h2 : 2 ^ (r - (r - 1 - b'.val)) = 2 * 2 ^ (r - (r - 1 - b'.val) - 1) := by
              rw [← pow_succ']; congr 1; omega
            rw [h2]; omega
          have ht1 : (2 ^ r + lo).testBit (r - 1 - b'.val) =
              decide ((2 ^ r + lo) / 2 ^ (r - 1 - b'.val) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
          have ht2 : lo.testBit (r - 1 - b'.val) =
              decide (lo / 2 ^ (r - 1 - b'.val) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
          rw [ht1, ht2, h1]
          have hmod2 : (2 ^ (r - (r - 1 - b'.val)) + lo / 2 ^ (r - 1 - b'.val)) % 2 =
              lo / 2 ^ (r - 1 - b'.val) % 2 := by omega
          rw [hmod2]
      rw [hmod]
      exact bitsToNat_testBit r (fun i => f i.succ) b'

noncomputable def circuitLevel {n : ℕ} (C : Circuit) (s : Finset (Fin n)) : Fin (2 ^ notCount C) :=
  let r := notCount C
  let ns := notIndices C.gates
  let f : Fin r → Bool := fun b => !((C.wires (inVec s)).getD (n + 2 + ns.getD b.val C.size) false)
  ⟨bitsToNat r f, bitsToNat_lt r f⟩

lemma circuitLevel_mono {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    {s1 s2 : Finset (Fin n)} (hsub : s1 ⊆ s2) :
    (circuitLevel C s1).val ≤ (circuitLevel C s2).val ∧
    (circuitLevel C s1 = circuitLevel C s2 →
      ∀ q, (C.wires (inVec s1)).getD q false = true → (C.wires (inVec s2)).getD q false = true) := by
  set r := notCount C
  have hns_len : (notIndices C.gates).length = r := notIndices_length C.gates
  have hnotW : ∀ (s : Finset (Fin n)) (b : Fin r),
      (C.wires (inVec s)).getD (n + 2 + (notIndices C.gates).getD b.val C.size) false =
        !((circuitLevel C s).val.testBit (r - 1 - b.val)) := by
    intro s b
    dsimp only [circuitLevel]
    rw [bitsToNat_testBit r _ b, Bool.not_not]
  have hle_in : VecLe (inVec s1) (inVec s2) := vecLe_inVec hsub
  by_cases hall : ∀ b : Fin r, (circuitLevel C s1).val.testBit (r - 1 - b.val) =
      (circuitLevel C s2).val.testBit (r - 1 - b.val)
  · have hlv_eq : circuitLevel C s1 = circuitLevel C s2 := by
      apply Fin.ext
      apply eq_of_testBit_lt_pow (circuitLevel C s1).isLt (circuitLevel C s2).isLt
      intro k hk
      have h1 := hall ⟨r - 1 - k, by omega⟩
      have h2 : r - 1 - (r - 1 - k) = k := by omega
      rwa [h2] at h1
    refine ⟨by rw [hlv_eq], ?_⟩
    intro _ q hq
    have hpre := prefix_mono_of_not_le C hfit hle_in C.gates.length (le_refl _) (by
      intro g hg hgn h1
      have hmem : g ∈ notIndices C.gates := (mem_notIndices_iff C.gates g).mpr ⟨hg, hgn⟩
      rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
      have hidx_r : idx < r := by omega
      have hge : (notIndices C.gates).getD idx C.size = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; exact hget
      rw [inVec_len] at h1 ⊢
      rw [← hge] at h1 ⊢
      rw [hnotW s1 ⟨idx, hidx_r⟩] at h1
      rw [hnotW s2 ⟨idx, hidx_r⟩, ← hall ⟨idx, hidx_r⟩]
      exact h1)
    rw [List.take_length] at hpre
    exact hpre.2 q hq
  · push Not at hall
    have hex : ∃ b : ℕ, ∃ hb : b < r,
        (circuitLevel C s1).val.testBit (r - 1 - b) ≠ (circuitLevel C s2).val.testBit (r - 1 - b) := by
      rcases hall with ⟨b, hb⟩; exact ⟨b.val, b.isLt, hb⟩
    let b0 := Nat.find hex
    rcases Nat.find_spec hex with ⟨hb0_lt, hb0_ne⟩
    have hb0_min : ∀ b < b0, (circuitLevel C s1).val.testBit (r - 1 - b) =
        (circuitLevel C s2).val.testBit (r - 1 - b) := by
      intro b hb; by_contra hne; exact Nat.find_min hex hb ⟨by omega, hne⟩
    set g0 := (notIndices C.gates).getD b0 C.size with hg0
    have hg0_spec := (mem_notIndices_iff C.gates g0).mp (getD_mem _ b0 C.size (by omega))
    have hg0_lt : g0 < C.gates.length := hg0_spec.1
    have hg0_op : (C.gates[g0]).op = GateOp.not := by
      have h1 := hg0_spec.2
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg0_lt] at h1
    have hpre : VecLe (wiresFrom (C.gates.take g0) (inVec s1))
        (wiresFrom (C.gates.take g0) (inVec s2)) := by
      apply prefix_mono_of_not_le C hfit hle_in g0 (le_of_lt hg0_lt)
      intro g hg hgn h1
      have hmem : g ∈ notIndices C.gates := (mem_notIndices_iff C.gates g).mpr ⟨by omega, hgn⟩
      rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
      have hidx_r : idx < r := by omega
      have hge : (notIndices C.gates).getD idx C.size = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; exact hget
      have hidx_lt : idx < b0 := by
        by_contra hnot_lt
        have hle_b : b0 ≤ idx := Nat.le_of_not_lt hnot_lt
        rcases eq_or_lt_of_le hle_b with rfl | hlt_b
        · rw [← hg0] at hge; omega
        · have := notIndices_strictMono C.gates hlt_b hidx
          change (notIndices C.gates).getD b0 C.size < (notIndices C.gates).getD idx C.size at this
          rw [← hg0, hge] at this; omega
      rw [inVec_len] at h1 ⊢; rw [← hge] at h1 ⊢
      rw [hnotW s1 ⟨idx, hidx_r⟩] at h1
      rw [hnotW s2 ⟨idx, hidx_r⟩, ← hb0_min idx hidx_lt]
      exact h1
    have hanti : (C.wires (inVec s2)).getD (n + 2 + g0) false = true →
        (C.wires (inVec s1)).getD (n + 2 + g0) false = true := by
      intro h2
      have hi_val := wires_gate_val C (inVec s1) g0 hg0_lt
      have hj_val := wires_gate_val C (inVec s2) g0 hg0_lt
      rw [inVec_len] at hi_val hj_val
      rw [hj_val, hg0_op] at h2
      rw [hi_val, hg0_op]
      exact gateOp_not_antitone hpre (C.gates[g0]).inputs h2
    have hwi := hnotW s1 ⟨b0, hb0_lt⟩
    have hwj := hnotW s2 ⟨b0, hb0_lt⟩
    rw [← hg0] at hwi hwj
    have hbi : (circuitLevel C s1).val.testBit (r - 1 - b0) = false := by
      cases hc1 : (circuitLevel C s1).val.testBit (r - 1 - b0)
      · rfl
      · cases hc2 : (circuitLevel C s2).val.testBit (r - 1 - b0)
        · have hj1 : (C.wires (inVec s2)).getD (n + 2 + g0) false = true := by rw [hwj, hc2]; rfl
          have hi1 := hanti hj1; rw [hwi, hc1] at hi1; cases hi1
        · exact absurd (hc1.trans hc2.symm) hb0_ne
    have hbj : (circuitLevel C s2).val.testBit (r - 1 - b0) = true := by
      cases hc2 : (circuitLevel C s2).val.testBit (r - 1 - b0)
      · exact absurd (hbi.trans hc2.symm) hb0_ne
      · rfl
    have hlt : (circuitLevel C s1).val < (circuitLevel C s2).val := by
      apply nat_lt_of_high_bit (k0 := r - 1 - b0) _ hbi hbj
      intro k hk
      by_cases hkr : k < r
      · have h1 := hb0_min (r - 1 - k) (by omega)
        have h2 : r - 1 - (r - 1 - k) = k := by omega
        rwa [h2] at h1
      · have hge : r ≤ k := Nat.le_of_not_lt hkr
        have hi_lt : (circuitLevel C s1).val < 2 ^ k := lt_of_lt_of_le (circuitLevel C s1).isLt (Nat.pow_le_pow_right (by omega) hge)
        have hj_lt : (circuitLevel C s2).val < 2 ^ k := lt_of_lt_of_le (circuitLevel C s2).isLt (Nat.pow_le_pow_right (by omega) hge)
        rw [Nat.testBit_lt_two_pow hi_lt, Nat.testBit_lt_two_pow hj_lt]
    refine ⟨le_of_lt hlt, fun heq => by rw [heq] at hlt; omega⟩

def prefEq {m r : ℕ} (level : Fin m → Fin (2 ^ r)) (k : ℕ) (i j : Fin m) : Prop :=
  ∀ b < k, (level i).val.testBit (r - 1 - b) = (level j).val.testBit (r - 1 - b)

lemma nextBit_of_orderOK {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val)
    {k : ℕ} (hk : k < r) {i j : Fin m}
    (hsub : x i ⊆ x j) (hpref : prefEq level k i j)
    (hi : (level i).val.testBit (r - 1 - k) = true) :
    (level j).val.testBit (r - 1 - k) = true := by
  cases hj : (level j).val.testBit (r - 1 - k)
  · exfalso
    have hlt : (level j).val < (level i).val := by
      apply nat_lt_of_high_bit (k0 := r - 1 - k) _ hj hi
      intro pos hpos
      by_cases hpr : pos < r
      · have h1 := (hpref (r - 1 - pos) (by omega)).symm
        have h2 : r - 1 - (r - 1 - pos) = pos := by omega
        rwa [h2] at h1
      · have hge : r ≤ pos := Nat.le_of_not_lt hpr
        have hi_lt : (level i).val < 2 ^ pos := lt_of_lt_of_le (level i).isLt (Nat.pow_le_pow_right (by omega) hge)
        have hj_lt : (level j).val < 2 ^ pos := lt_of_lt_of_le (level j).isLt (Nat.pow_le_pow_right (by omega) hge)
        rw [Nat.testBit_lt_two_pow hj_lt, Nat.testBit_lt_two_pow hi_lt]
    have hle := hord i j hsub
    omega
  · rfl

noncomputable def maskWires {n : ℕ} (s : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter (fun a => @decide (a ∈ s) (Classical.propDecidable _))).map (fun a => a.val)

lemma maskWires_lt {n : ℕ} (s : Finset (Fin n)) : ∀ w ∈ maskWires s, w < n + 2 := by
  intro w hw; rcases List.mem_map.mp hw with ⟨a, _, rfl⟩; omega

lemma maskWires_all_inVec {n : ℕ} (s t : Finset (Fin n)) :
    (maskWires s).all (fun w => (inVec t).getD w false) = decide (s ⊆ t) := by
  apply Bool.eq_iff_iff.mpr
  dsimp only [maskWires]
  simp only [List.all_map, List.all_eq_true, List.mem_filter, List.mem_finRange, true_and,
    Function.comp_def, decide_eq_true_eq]
  constructor
  · intro h a ha
    have h1 := h a ha; rw [inVec_getD_lt] at h1
    exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mp h1
  · intro hsub a ha
    rw [inVec_getD_lt]
    exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr (hsub ha)

noncomputable def buildInitAux (n : ℕ) : List (Finset (Fin n)) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | s :: rest, gs =>
    let r1 := emitAndList (n + 2) gs (n + 1) (maskWires s)
    let r2 := buildInitAux n rest r1.1
    (r2.1, r1.2 :: r2.2)

lemma buildInitAux_spec (n : ℕ) :
    ∀ (ss : List (Finset (Fin n))) (gs : List Gate),
      let r := buildInitAux n ss gs
      Extends (n + 2) gs r.1 ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      r.2.length = ss.length ∧
      (∀ w ∈ r.2, w < (n + 2) + r.1.length) ∧
      ∀ (idx : ℕ) (hidx : idx < ss.length) (t : Finset (Fin n)),
        (wiresFrom r.1 (inVec t)).getD (r.2.getD idx 0) false = decide (ss[idx] ⊆ t) := by
  intro ss
  induction ss with
  | nil =>
    intro gs; dsimp only [buildInitAux]
    refine ⟨Extends.refl _ _, rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons s rest ih =>
    intro gs; dsimp only [buildInitAux]
    set r1 := emitAndList (n + 2) gs (n + 1) (maskWires s) with hr1
    have h1 := emitAndList_spec (n + 2) (maskWires s) gs (n + 1) (by omega)
      (fun w hw => by have := maskWires_lt s w hw; omega)
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, _, hlt1, hnc1, hval1⟩
    set r2 := buildInitAux n rest r1.1 with hr2
    have h2 := ih r1.1
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨hext2, hnc2, hlen_w2, hlt2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by omega, by simp [hlen_w2], ?_, ?_⟩
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · exact hlt2 w hw'
    · intro idx hidx t
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hext2.wire_eq (inVec t) (inVec_len t) r1.2 hlt1, hval1 (inVec t) (inVec_len t),
            wiresFrom_getD_lt gs (inVec t) (n + 1) (by rw [inVec_len]; omega), inVec_getD_o, Bool.true_and]
        have hall : (maskWires s).all (fun w => (wiresFrom gs (inVec t)).getD w false) =
            (maskWires s).all (fun w => (inVec t).getD w false) := by
          apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
          constructor <;> intro h w hw
          · have := h w hw; rwa [wiresFrom_getD_lt gs (inVec t) w (by rw [inVec_len]; exact maskWires_lt s w hw)] at this
          · have := h w hw; rwa [wiresFrom_getD_lt gs (inVec t) w (by rw [inVec_len]; exact maskWires_lt s w hw)]
        rw [hall, maskWires_all_inVec]
      | succ idx' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        exact hval2 idx' (by simp at hidx; omega) t

def updateIndsAux (base notW : ℕ) : List (ℕ × Bool) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | (w, reqBit) :: rest, gs =>
    if reqBit then
      let r2 := updateIndsAux base notW rest gs
      (r2.1, w :: r2.2)
    else
      let r1 := emitAnd base gs w notW
      let r2 := updateIndsAux base notW rest r1.1
      (r2.1, r1.2 :: r2.2)

lemma updateIndsAux_spec (base notW : ℕ) :
    ∀ (items : List (ℕ × Bool)) (gs : List Gate),
      notW < base + gs.length →
      (∀ p ∈ items, p.1 < base + gs.length) →
      let r := updateIndsAux base notW items gs
      Extends base gs r.1 ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      r.2.length = items.length ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      ∀ (idx : ℕ) (hidx : idx < items.length) (v : List Bool), v.length = base →
        (wiresFrom r.1 v).getD (r.2.getD idx 0) false =
          if (items[idx]).2 then (wiresFrom gs v).getD (items[idx]).1 false
          else ((wiresFrom gs v).getD (items[idx]).1 false && (wiresFrom gs v).getD notW false) := by
  intro items
  induction items with
  | nil =>
    intro gs _ _; dsimp only [updateIndsAux]
    refine ⟨Extends.refl _ _, rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons p rest ih =>
    intro gs hnotW hitems; rcases p with ⟨w, reqBit⟩; dsimp only [updateIndsAux]
    have hw_lt : w < base + gs.length := hitems (w, reqBit) (List.mem_cons_self ..)
    have hrest_lt : ∀ q ∈ rest, q.1 < base + gs.length := fun q hq => hitems q (List.mem_cons_of_mem _ hq)
    cases reqBit
    · simp only [Bool.false_eq_true, ↓reduceIte]
      set r1 := emitAnd base gs w notW with hr1
      have h1 := emitAnd_spec base gs w notW hw_lt hnotW
      dsimp only at h1; rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
      set r2 := updateIndsAux base notW rest r1.1 with hr2
      have h2 := ih r1.1 (by omega) (fun q hq => by have := hrest_lt q hq; omega)
      dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨hext2, hnc2, hlen_w2, hlt2, hval2⟩
      have hgl2 := hext2.length_le
      refine ⟨hext1.trans hext2, by omega, by simp [hlen_w2], ?_, ?_⟩
      · intro u hu; rcases List.mem_cons.mp hu with rfl | hu'
        · omega
        · exact hlt2 u hu'
      · intro idx hidx v hv
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte]
          rw [hext2.wire_eq v hv r1.2 hlt1, hval1 v hv]
        | succ idx' =>
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          have hidx' : idx' < rest.length := by simp at hidx; omega
          rw [hval2 idx' hidx' v hv]
          have hq := hrest_lt rest[idx'] (List.getElem_mem hidx')
          rw [hext1.wire_eq v hv (rest[idx']).1 hq, hext1.wire_eq v hv notW hnotW]
    · simp only [↓reduceIte]
      set r2 := updateIndsAux base notW rest gs with hr2
      have h2 := ih gs hnotW hrest_lt
      dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨hext2, hnc2, hlen_w2, hlt2, hval2⟩
      have hgl2 := hext2.length_le
      refine ⟨hext2, hnc2, by simp [hlen_w2], ?_, ?_⟩
      · intro u hu; rcases List.mem_cons.mp hu with rfl | hu'
        · omega
        · exact hlt2 u hu'
      · intro idx hidx v hv
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero, ↓reduceIte]
          exact hext2.wire_eq v hv w hw_lt
        | succ idx' =>
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          exact hval2 idx' (by simp at hidx; omega) v hv

def roundStep (n m r : ℕ) (level : Fin m → Fin (2 ^ r)) (k : ℕ) (st : List Gate × List ℕ) :
    List Gate × List ℕ :=
  let gs := st.1
  let inds := st.2
  let reqs := ((List.finRange m).filter (fun i => (level i).val.testBit (r - 1 - k))).map
    (fun i => inds.getD i.val 0)
  let rU := emitOrList (n + 2) gs n reqs
  let rNot := emitNot (n + 2) rU.1 rU.2
  let items := (List.finRange m).map (fun i => (inds.getD i.val 0, (level i).val.testBit (r - 1 - k)))
  updateIndsAux (n + 2) rNot.2 items rNot.1

def roundLoop (n m r : ℕ) (level : Fin m → Fin (2 ^ r)) :
    ℕ → List Gate × List ℕ → List Gate × List ℕ
  | 0, st => st
  | k + 1, st => roundStep n m r level k (roundLoop n m r level k st)

lemma roundStep_spec {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val)
    (k : ℕ) (hk : k < r) (gs : List Gate) (inds : List ℕ)
    (hnc : notCount ⟨gs, 0⟩ = k)
    (hinds_len : inds.length = m)
    (hinds_lt : ∀ w ∈ inds, w < (n + 2) + gs.length)
    (hinds_self : ∀ i : Fin m, (wiresFrom gs (inVec (x i))).getD (inds.getD i.val 0) false = true)
    (hinds_sound : ∀ i j : Fin m,
      (wiresFrom gs (inVec (x j))).getD (inds.getD i.val 0) false = true →
      x i ⊆ x j ∧ prefEq level k i j) :
    let res := roundStep n m r level k (gs, inds)
    Extends (n + 2) gs res.1 ∧
    notCount ⟨res.1, 0⟩ = k + 1 ∧
    res.2.length = m ∧
    (∀ w ∈ res.2, w < (n + 2) + res.1.length) ∧
    (∀ i : Fin m, (wiresFrom res.1 (inVec (x i))).getD (res.2.getD i.val 0) false = true) ∧
    (∀ i j : Fin m,
      (wiresFrom res.1 (inVec (x j))).getD (res.2.getD i.val 0) false = true →
      x i ⊆ x j ∧ prefEq level (k + 1) i j) := by
  let reqs := ((List.finRange m).filter (fun i => (level i).val.testBit (r - 1 - k))).map
    (fun i => inds.getD i.val 0)
  have hreqs_lt : ∀ w ∈ reqs, w < (n + 2) + gs.length := by
    intro w hw; rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
    exact hinds_lt _ (getD_mem inds i.val 0 (by omega))
  set rU := emitOrList (n + 2) gs n reqs with hrU
  have hUs := emitOrList_spec (n + 2) reqs gs n (by omega) hreqs_lt
  dsimp only at hUs; rw [← hrU] at hUs
  rcases hUs with ⟨hextU, _, hltU, hncU, hvalU⟩
  set rNot := emitNot (n + 2) rU.1 rU.2 with hrNot
  have hNots := emitNot_spec (n + 2) rU.1 rU.2 hltU
  dsimp only at hNots; rw [← hrNot] at hNots
  rcases hNots with ⟨hextNot, _, hltNot, hncNot, hvalNot⟩
  let items := (List.finRange m).map (fun i => (inds.getD i.val 0, (level i).val.testBit (r - 1 - k)))
  have hitems_len : items.length = m := by simp [items]
  have hglUN := (hextU.trans hextNot).length_le
  have hitems_lt : ∀ p ∈ items, p.1 < (n + 2) + rNot.1.length := by
    intro p hp; rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    have := hinds_lt _ (getD_mem inds i.val 0 (by omega)); omega
  set rUp := updateIndsAux (n + 2) rNot.2 items rNot.1 with hrUp
  have hUps := updateIndsAux_spec (n + 2) rNot.2 items rNot.1 hltNot hitems_lt
  dsimp only at hUps; rw [← hrUp] at hUps
  rcases hUps with ⟨hextUp, hncUp, hlen_wUp, hltUp, hvalUp⟩
  have hstep_eq : roundStep n m r level k (gs, inds) = rUp := rfl
  dsimp only; rw [hstep_eq]
  have hU_eval : ∀ j : Fin m, (wiresFrom rU.1 (inVec (x j))).getD rU.2 false = (level j).val.testBit (r - 1 - k) := by
    intro j
    rw [hvalU (inVec (x j)) (inVec_len _),
        wiresFrom_getD_lt gs (inVec (x j)) n (by rw [inVec_len]; omega), inVec_getD_z, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    dsimp only [reqs]
    simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, Function.comp_def]
    constructor
    · rintro ⟨i, hbi, hfi⟩
      rcases hinds_sound i j hfi with ⟨hsub, hpref⟩
      exact nextBit_of_orderOK hord hk hsub hpref hbi
    · intro hbj; exact ⟨j, hbj, hinds_self j⟩
  have hNot_eval : ∀ j : Fin m,
      (wiresFrom rNot.1 (inVec (x j))).getD rNot.2 false = !((level j).val.testBit (r - 1 - k)) := by
    intro j; rw [hvalNot (inVec (x j)) (inVec_len _), hU_eval j]
  have hitem_get : ∀ i : Fin m,
      items[i.val]'(by rw [hitems_len]; exact i.isLt) = (inds.getD i.val 0, (level i).val.testBit (r - 1 - k)) := by
    intro i; simp [items]
  have hUp_eval : ∀ (i j : Fin m),
      (wiresFrom rUp.1 (inVec (x j))).getD (rUp.2.getD i.val 0) false =
        if (level i).val.testBit (r - 1 - k) then
          (wiresFrom gs (inVec (x j))).getD (inds.getD i.val 0) false
        else
          ((wiresFrom gs (inVec (x j))).getD (inds.getD i.val 0) false &&
            !((level j).val.testBit (r - 1 - k))) := by
    intro i j
    have h1 := hvalUp i.val (by rw [hitems_len]; exact i.isLt) (inVec (x j)) (inVec_len _)
    rw [hitem_get i] at h1
    rw [h1, hNot_eval j, (hextU.trans hextNot).wire_eq (inVec (x j)) (inVec_len _)
      (inds.getD i.val 0) (hinds_lt _ (getD_mem inds i.val 0 (by omega)))]
  refine ⟨(hextU.trans hextNot).trans hextUp, by omega, by omega, hltUp, ?_, ?_⟩
  · intro i; rw [hUp_eval i i, hinds_self i]; cases (level i).val.testBit (r - 1 - k) <;> rfl
  · intro i j hfire
    rw [hUp_eval i j] at hfire
    cases hbi : (level i).val.testBit (r - 1 - k)
    · simp only [hbi, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hfire
      rcases hinds_sound i j hfire.1 with ⟨hsub, hpref⟩
      refine ⟨hsub, fun b hb => ?_⟩
      by_cases hbk : b < k
      · exact hpref b hbk
      · have hbeq : b = k := by omega
        rw [hbeq, hbi, hfire.2]
    · simp only [hbi, ↓reduceIte] at hfire
      rcases hinds_sound i j hfire with ⟨hsub, hpref⟩
      have hbj := nextBit_of_orderOK hord hk hsub hpref hbi
      refine ⟨hsub, fun b hb => ?_⟩
      by_cases hbk : b < k
      · exact hpref b hbk
      · have hbeq : b = k := by omega
        rw [hbeq, hbi, hbj]

lemma roundLoop_spec {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val)
    (gs0 : List Gate) (inds0 : List ℕ)
    (hnc0 : notCount ⟨gs0, 0⟩ = 0)
    (hinds0_len : inds0.length = m)
    (hinds0_lt : ∀ w ∈ inds0, w < (n + 2) + gs0.length)
    (hinds0_self : ∀ i : Fin m, (wiresFrom gs0 (inVec (x i))).getD (inds0.getD i.val 0) false = true)
    (hinds0_sound : ∀ i j : Fin m,
      (wiresFrom gs0 (inVec (x j))).getD (inds0.getD i.val 0) false = true → x i ⊆ x j) :
    ∀ k ≤ r,
      let res := roundLoop n m r level k (gs0, inds0)
      Extends (n + 2) gs0 res.1 ∧
      notCount ⟨res.1, 0⟩ = k ∧
      res.2.length = m ∧
      (∀ w ∈ res.2, w < (n + 2) + res.1.length) ∧
      (∀ i : Fin m, (wiresFrom res.1 (inVec (x i))).getD (res.2.getD i.val 0) false = true) ∧
      (∀ i j : Fin m,
        (wiresFrom res.1 (inVec (x j))).getD (res.2.getD i.val 0) false = true →
        x i ⊆ x j ∧ prefEq level k i j) := by
  intro k
  induction k with
  | zero =>
    intro _; dsimp only [roundLoop]
    refine ⟨Extends.refl _ _, hnc0, hinds0_len, hinds0_lt, hinds0_self,
      (fun i j h => ⟨hinds0_sound i j h, fun _ hb => by cases hb⟩)⟩
  | succ k ih =>
    intro hkr; dsimp only [roundLoop]
    set prev := roundLoop n m r level k (gs0, inds0) with hprev
    have hp := ih (by omega); dsimp only at hp
    rcases hp with ⟨hextP, hncP, hlen_wP, hltP, hselfP, hsoundP⟩
    have hs := roundStep_spec hord k (by omega) prev.1 prev.2 hncP hlen_wP hltP hselfP hsoundP
    dsimp only at hs
    rcases hs with ⟨hextS, hncS, hlen_wS, hltS, hselfS, hsoundS⟩
    exact ⟨hextP.trans hextS, hncS, hlen_wS, hltS, hselfS, hsoundS⟩

def buildTapsAux (n m : ℕ) (inds : List ℕ) : List (Fin m → Bool) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | f :: rest, gs =>
    let ws := ((List.finRange m).filter f).map (fun i => inds.getD i.val 0)
    let r1 := emitOrList (n + 2) gs n ws
    let r2 := buildTapsAux n m inds rest r1.1
    (r2.1, r1.2 :: r2.2)

lemma buildTapsAux_spec (n m : ℕ) (inds : List ℕ) (hinds_len : inds.length = m) :
    ∀ (fs : List (Fin m → Bool)) (gs : List Gate),
      (∀ w ∈ inds, w < (n + 2) + gs.length) →
      let r := buildTapsAux n m inds fs gs
      Extends (n + 2) gs r.1 ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      r.2.length = fs.length ∧
      (∀ w ∈ r.2, w < (n + 2) + r.1.length) ∧
      ∀ (idx : ℕ) (hidx : idx < fs.length) (v : List Bool),
        v.length = n + 2 → v.getD n false = false →
        (wiresFrom r.1 v).getD (r.2.getD idx 0) false =
          (List.finRange m).any (fun i => fs[idx] i && (wiresFrom gs v).getD (inds.getD i.val 0) false) := by
  intro fs
  induction fs with
  | nil =>
    intro gs _; dsimp only [buildTapsAux]
    refine ⟨Extends.refl _ _, rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons f rest ih =>
    intro gs hinds_lt; dsimp only [buildTapsAux]
    let ws := ((List.finRange m).filter f).map (fun i => inds.getD i.val 0)
    have hws_lt : ∀ w ∈ ws, w < (n + 2) + gs.length := by
      intro w hw; rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
      exact hinds_lt _ (getD_mem inds i.val 0 (by omega))
    set r1 := emitOrList (n + 2) gs n ws with hr1
    have h1 := emitOrList_spec (n + 2) ws gs n (by omega) hws_lt
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    set r2 := buildTapsAux n m inds rest r1.1 with hr2
    have h2 := ih r1.1 (fun w hw => by have := hinds_lt w hw; omega)
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨hext2, hnc2, hlen_w2, hlt2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by omega, by simp [hlen_w2], ?_, ?_⟩
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · exact hlt2 w hw'
    · intro idx hidx v hv hvz
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hext2.wire_eq v hv r1.2 hlt1, hval1 v hv,
            wiresFrom_getD_lt gs v n (by rw [hv]; omega), hvz, Bool.false_or]
        apply Bool.eq_iff_iff.mpr; dsimp only [ws]
        simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and,
          Function.comp_def, Bool.and_eq_true]
      | succ idx' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hidx' : idx' < rest.length := by simp at hidx; omega
        rw [hval2 idx' hidx' v hv hvz]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
        constructor <;> rintro ⟨i, hf, hw⟩ <;> refine ⟨i, hf, ?_⟩
        · rwa [hext1.wire_eq v hv (inds.getD i.val 0) (hinds_lt _ (getD_mem inds i.val 0 (by omega)))] at hw
        · rwa [hext1.wire_eq v hv (inds.getD i.val 0) (hinds_lt _ (getD_mem inds i.val 0 (by omega)))]

lemma build_circuit_of_orderOK {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)} {w : Fin m → Fin 2 → Bool}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
      (level i = level j → ∀ a, w i a = true → w j a = true)) :
    ∃ (C : Circuit) (tap : Fin 2 → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      (∀ a, tap a < n + 2 + C.size) ∧ notCount C ≤ r ∧
      ∀ i a, (C.wires (inVec (x i))).getD (tap a) false = w i a := by
  let ss : List (Finset (Fin n)) := (List.finRange m).map x
  have hss_len : ss.length = m := by simp [ss]
  have hss_get : ∀ i : Fin m, ss[i.val]'(by rw [hss_len]; exact i.isLt) = x i := fun i => by simp [ss]
  set r0 := buildInitAux n ss [] with hr0
  have h0 := buildInitAux_spec n ss []
  dsimp only at h0; rw [← hr0] at h0
  rcases h0 with ⟨hext0, hnc0, hlen_w0, hlt0, hval0⟩
  simp only [notCount_nil] at hnc0
  have h0_self : ∀ i : Fin m, (wiresFrom r0.1 (inVec (x i))).getD (r0.2.getD i.val 0) false = true := by
    intro i; have h1 := hval0 i.val (by rw [hss_len]; exact i.isLt) (x i)
    rw [hss_get i] at h1; rw [h1]; exact decide_eq_true (Finset.Subset.refl _)
  have h0_sound : ∀ i j : Fin m,
      (wiresFrom r0.1 (inVec (x j))).getD (r0.2.getD i.val 0) false = true → x i ⊆ x j := by
    intro i j hf; have h1 := hval0 i.val (by rw [hss_len]; exact i.isLt) (x j)
    rw [hss_get i] at h1; rw [h1] at hf; exact of_decide_eq_true hf
  set rL := roundLoop n m r level r (r0.1, r0.2) with hrL
  have hL := roundLoop_spec (fun i j hs => (hord i j hs).1) r0.1 r0.2 hnc0 (by omega) hlt0 h0_self h0_sound r (le_refl r)
  dsimp only at hL; rw [← hrL] at hL
  rcases hL with ⟨hextL, hncL, hlen_wL, hltL, hselfL, hsoundL⟩
  let fs : List (Fin m → Bool) := (List.finRange 2).map (fun a i => w i a)
  have hfs_len : fs.length = 2 := by simp [fs]
  have hfs_get : ∀ a : Fin 2, fs[a.val]'(by rw [hfs_len]; exact a.isLt) = (fun i => w i a) := fun a => by simp [fs]
  set rT := buildTapsAux n m rL.2 fs rL.1 with hrT
  have hT := buildTapsAux_spec n m rL.2 hlen_wL fs rL.1 hltL
  dsimp only at hT; rw [← hrT] at hT
  rcases hT with ⟨hextT, hncT, hlen_wT, hltT, hvalT⟩
  have hextAll : Extends (n + 2) [] rT.1 := (hext0.trans hextL).trans hextT
  rcases hextAll with ⟨e, heq, hfitC, hrbC⟩
  simp only [List.nil_append, List.length_nil, add_zero] at heq hfitC hrbC
  subst heq
  let C : Circuit := ⟨rT.1, 0⟩
  let tap : Fin 2 → ℕ := fun a => rT.2.getD a.val 0
  refine ⟨C, tap, hfitC, hrbC, by dsimp only [C]; omega,
    fun a => hltT _ (getD_mem rT.2 a.val 0 (by omega)), by change notCount ⟨rT.1, 0⟩ ≤ r; omega, ?_⟩
  intro j a
  change (wiresFrom rT.1 (inVec (x j))).getD (rT.2.getD a.val 0) false = w j a
  have h1 := hvalT a.val (by rw [hfs_len]; exact a.isLt) (inVec (x j)) (inVec_len _) (inVec_getD_z _)
  rw [hfs_get a] at h1; rw [h1]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hwia, hfi⟩
    rcases hsoundL i j hfi with ⟨hsub, hpref⟩
    have hlv : level i = level j := by
      apply Fin.ext
      apply eq_of_testBit_lt_pow (level i).isLt (level j).isLt
      intro pos hpos
      have h1' := hpref (r - 1 - pos) (by omega)
      have h2' : r - 1 - (r - 1 - pos) = pos := by omega
      rwa [h2'] at h1'
    exact (hord i j hsub).2 hlv a hwia
  · intro hwja; exact ⟨j, hwja, hselfL j⟩

end CircuitEngine

section BinaryTree

inductive TreeNode (d : ℕ) where
  | leaf (p : Fin (2 ^ d)) : TreeNode d
  | merge (k : Fin d) (p : Fin (2 ^ k.val)) : TreeNode d
  | tag (k : Fin (d - 1)) (p : Fin (2 ^ (k.val + 1))) : TreeNode d
  deriving DecidableEq

def treeNodeEquiv (d : ℕ) :
    TreeNode d ≃ (Fin (2 ^ d) ⊕ (Σ k : Fin d, Fin (2 ^ k.val))) ⊕ (Σ k : Fin (d - 1), Fin (2 ^ (k.val + 1))) where
  toFun
    | .leaf p => Sum.inl (Sum.inl p)
    | .merge k p => Sum.inl (Sum.inr ⟨k, p⟩)
    | .tag k p => Sum.inr ⟨k, p⟩
  invFun
    | Sum.inl (Sum.inl p) => .leaf p
    | Sum.inl (Sum.inr ⟨k, p⟩) => .merge k p
    | Sum.inr ⟨k, p⟩ => .tag k p
  left_inv u := by cases u <;> rfl
  right_inv x := by rcases x with (p | ⟨k, p⟩) | ⟨k, p⟩ <;> rfl

noncomputable instance instFintypeTreeNode (d : ℕ) : Fintype (TreeNode d) :=
  Fintype.ofEquiv _ (treeNodeEquiv d).symm

lemma sum_two_pow : ∀ n : ℕ, ∑ k : Fin n, 2 ^ k.val = 2 ^ n - 1
  | 0 => by simp
  | n + 1 => by
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [sum_two_pow n]
    have hpos : 1 ≤ 2 ^ n := Nat.pow_pos (by omega)
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    omega

lemma card_treeNode {d : ℕ} (hd : 1 ≤ d) : Fintype.card (TreeNode d) = 3 * 2 ^ d - 3 := by
  rw [Fintype.card_congr (treeNodeEquiv d)]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  have h1 := sum_two_pow d
  have h2 : ∑ k : Fin (d - 1), 2 ^ (k.val + 1) = 2 * (2 ^ (d - 1) - 1) := by
    have : ∀ k : Fin (d - 1), 2 ^ (k.val + 1) = 2 * 2 ^ k.val := fun k => by rw [pow_succ]; ring
    simp_rw [this, ← Finset.mul_sum, sum_two_pow (d - 1)]
  rw [h1, h2]
  have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    have : d = (d - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  have hpos : 1 ≤ 2 ^ (d - 1) := Nat.pow_pos (by omega)
  omega

def nodeDepth {d : ℕ} : TreeNode d → ℕ
  | .leaf _ => d
  | .merge k _ => k.val
  | .tag k _ => k.val + 1

def nodePath {d : ℕ} : TreeNode d → ℕ
  | .leaf p => p.val
  | .merge _ p => p.val
  | .tag _ p => p.val

def nodeIsTag {d : ℕ} : TreeNode d → Bool
  | .tag _ _ => true
  | _ => false

def nodeHeight {d : ℕ} (u : TreeNode d) : ℕ := d - nodeDepth u

lemma nodeDepth_le {d : ℕ} (u : TreeNode d) : nodeDepth u ≤ d := by
  cases u with
  | leaf _ => exact le_refl d
  | merge k _ => exact le_of_lt k.isLt
  | tag k _ => have := k.isLt; simp only [nodeDepth]; omega

lemma nodePath_lt {d : ℕ} (u : TreeNode d) : nodePath u < 2 ^ nodeDepth u := by
  cases u with
  | leaf p => exact p.isLt
  | merge k p => exact p.isLt
  | tag k p => exact p.isLt

def nodeKind {d : ℕ} : TreeNode d → Fin 3
  | .leaf p => if p.val.testBit (d - 1) then 1 else 0
  | .merge _ _ => 2
  | .tag k p => if p.val.testBit k.val then 1 else 0

def nodeMask {d : ℕ} (u : TreeNode d) : Finset (Fin (3 * d)) :=
  Finset.univ.filter fun q : Fin (3 * d) =>
    let s := q.val / 3
    let r := q.val % 3
    nodeDepth u ≤ s ∨
      (r = 0 ∧ (nodePath u).testBit s = false) ∨
      (r = 1 ∧ (nodePath u).testBit s = true) ∨
      (r = 2 ∧ nodeIsTag u = true ∧ s + 1 = nodeDepth u)

lemma mem_nodeMask_iff {d : ℕ} (u : TreeNode d) (q : Fin (3 * d)) :
    q ∈ nodeMask u ↔
      nodeDepth u ≤ q.val / 3 ∨
        (q.val % 3 = 0 ∧ (nodePath u).testBit (q.val / 3) = false) ∨
        (q.val % 3 = 1 ∧ (nodePath u).testBit (q.val / 3) = true) ∨
        (q.val % 3 = 2 ∧ nodeIsTag u = true ∧ q.val / 3 + 1 = nodeDepth u) := by
  simp [nodeMask]

lemma nodeMask_subset_iff {d : ℕ} (u v : TreeNode d) :
    nodeMask u ⊆ nodeMask v ↔
      nodeDepth v ≤ nodeDepth u ∧
      (∀ s < nodeDepth v, (nodePath u).testBit s = (nodePath v).testBit s) ∧
      (nodeDepth u = nodeDepth v → nodeIsTag u = true → nodeIsTag v = true) := by
  constructor
  · intro hsub
    have hdepth : nodeDepth v ≤ nodeDepth u := by
      by_cases hdu : nodeDepth u < d
      · have h0_in : (⟨3 * nodeDepth u, by omega⟩ : Fin (3 * d)) ∈ nodeMask u := by
          rw [mem_nodeMask_iff]; left; dsimp only; omega
        have h1_in : (⟨3 * nodeDepth u + 1, by omega⟩ : Fin (3 * d)) ∈ nodeMask u := by
          rw [mem_nodeMask_iff]; left; dsimp only; omega
        have h0_v := (mem_nodeMask_iff v _).mp (hsub h0_in)
        have h1_v := (mem_nodeMask_iff v _).mp (hsub h1_in)
        have hd0 : (3 * nodeDepth u) / 3 = nodeDepth u := by omega
        have hm0 : (3 * nodeDepth u) % 3 = 0 := by omega
        have hd1 : (3 * nodeDepth u + 1) / 3 = nodeDepth u := by omega
        have hm1 : (3 * nodeDepth u + 1) % 3 = 1 := by omega
        simp only [hd0, hm0] at h0_v
        simp only [hd1, hm1] at h1_v
        rcases h0_v with h | ⟨_, hf⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · rcases h1_v with h' | ⟨h', _⟩ | ⟨_, ht⟩ | ⟨h', _⟩
          · exact h'
          · omega
          · rw [hf] at ht; cases ht
          · omega
        · omega
        · omega
      · have := nodeDepth_le u; have := nodeDepth_le v; omega
    have hpath : ∀ s < nodeDepth v, (nodePath u).testBit s = (nodePath v).testBit s := by
      intro s hs
      have hsd : s < d := lt_of_lt_of_le hs (nodeDepth_le v)
      cases hbu : (nodePath u).testBit s
      · have hin : (⟨3 * s, by omega⟩ : Fin (3 * d)) ∈ nodeMask u := by
          rw [mem_nodeMask_iff]; right; left; dsimp only; exact ⟨by omega, by simpa [show 3 * s / 3 = s by omega] using hbu⟩
        have hv := (mem_nodeMask_iff v _).mp (hsub hin)
        have hdv : (3 * s) / 3 = s := by omega
        have hmv : (3 * s) % 3 = 0 := by omega
        simp only [hdv, hmv] at hv
        rcases hv with h | ⟨_, hf⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · omega
        · exact hf.symm
        · omega
        · omega
      · have hin : (⟨3 * s + 1, by omega⟩ : Fin (3 * d)) ∈ nodeMask u := by
          rw [mem_nodeMask_iff]; right; right; left; dsimp only
          exact ⟨by omega, by simpa [show (3 * s + 1) / 3 = s by omega] using hbu⟩
        have hv := (mem_nodeMask_iff v _).mp (hsub hin)
        have hdv : (3 * s + 1) / 3 = s := by omega
        have hmv : (3 * s + 1) % 3 = 1 := by omega
        simp only [hdv, hmv] at hv
        rcases hv with h | ⟨h, _⟩ | ⟨_, ht⟩ | ⟨h, _⟩
        · omega
        · omega
        · exact ht.symm
        · omega
    refine ⟨hdepth, hpath, ?_⟩
    intro hdeq htu
    have hdu_pos : 1 ≤ nodeDepth u := by
      cases u <;> simp [nodeIsTag] at htu; simp [nodeDepth]
    have hdu_le := nodeDepth_le u
    let s := nodeDepth u - 1
    have hsd : s < d := by omega
    have hin : (⟨3 * s + 2, by omega⟩ : Fin (3 * d)) ∈ nodeMask u := by
      rw [mem_nodeMask_iff]; right; right; right; dsimp only
      refine ⟨by omega, htu, by omega⟩
    have hv := (mem_nodeMask_iff v _).mp (hsub hin)
    have hdv : (3 * s + 2) / 3 = s := by omega
    have hmv : (3 * s + 2) % 3 = 2 := by omega
    simp only [hdv, hmv] at hv
    rcases hv with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, htv, _⟩
    · omega
    · omega
    · omega
    · exact htv
  · rintro ⟨hdepth, hpath, htag⟩ q hq
    rw [mem_nodeMask_iff] at hq ⊢
    by_cases hs : nodeDepth v ≤ q.val / 3
    · exact Or.inl hs
    · have hsv : q.val / 3 < nodeDepth v := Nat.lt_of_not_ge hs
      rcases hq with hdu | ⟨hr0, hb⟩ | ⟨hr1, hb⟩ | ⟨hr2, htu, hsu⟩
      · omega
      · right; left; exact ⟨hr0, by rw [← hpath (q.val / 3) hsv]; exact hb⟩
      · right; right; left; exact ⟨hr1, by rw [← hpath (q.val / 3) hsv]; exact hb⟩
      · right; right; right
        have hdeq : nodeDepth u = nodeDepth v := by omega
        exact ⟨hr2, htag hdeq htu, by omega⟩

lemma nodeMask_injective {d : ℕ} : Function.Injective (@nodeMask d) := by
  intro u v hEq
  have h1 := (nodeMask_subset_iff u v).mp (by rw [hEq])
  have h2 := (nodeMask_subset_iff v u).mp (by rw [hEq])
  have hd : nodeDepth u = nodeDepth v := le_antisymm h2.1 h1.1
  have hp : nodePath u = nodePath v :=
    eq_of_testBit_lt_pow (nodePath_lt u) (by rw [hd]; exact nodePath_lt v)
      (fun s hs => h1.2.1 s (by omega))
  have ht : nodeIsTag u = nodeIsTag v :=
    Bool.eq_iff_iff.mpr ⟨h1.2.2 hd, h2.2.2 hd.symm⟩
  cases u with
  | leaf pu =>
    cases v with
    | leaf pv => congr 1; exact Fin.ext hp
    | merge kv _ => simp [nodeDepth] at hd; omega
    | tag kv _ => simp [nodeIsTag] at ht
  | merge ku pu =>
    cases v with
    | leaf _ => simp [nodeDepth] at hd; omega
    | merge kv pv =>
      simp only [nodeDepth] at hd
      have hk : ku = kv := Fin.ext hd
      subst hk; congr 1; exact Fin.ext hp
    | tag _ _ => simp [nodeIsTag] at ht
  | tag ku pu =>
    cases v with
    | leaf _ => simp [nodeIsTag] at ht
    | merge _ _ => simp [nodeIsTag] at ht
    | tag kv pv =>
      simp only [nodeDepth] at hd
      have hk : ku = kv := Fin.ext (by omega)
      subst hk; congr 1; exact Fin.ext hp

def childNode {d : ℕ} (k : Fin d) (p : Fin (2 ^ k.val)) (dir : Bool) : TreeNode d :=
  let p' := p.val + if dir then 2 ^ k.val else 0
  have hp' : p' < 2 ^ (k.val + 1) := by
    dsimp only [p']; have := p.isLt; rw [pow_succ]; cases dir <;> simp <;> omega
  if hk : k.val + 1 = d then
    TreeNode.leaf ⟨p', by rw [← hk]; exact hp'⟩
  else
    TreeNode.tag ⟨k.val, by omega⟩ ⟨p', hp'⟩

lemma childNode_depth {d : ℕ} (k : Fin d) (p : Fin (2 ^ k.val)) (dir : Bool) :
    nodeDepth (childNode k p dir) = k.val + 1 := by
  dsimp only [childNode]
  by_cases hk : k.val + 1 = d
  · rw [dif_pos hk]; simp [nodeDepth, hk]
  · rw [dif_neg hk]; simp [nodeDepth]

lemma childNode_path_testBit_lt {d : ℕ} (k : Fin d) (p : Fin (2 ^ k.val)) (dir : Bool)
    {s : ℕ} (hs : s < k.val) :
    (nodePath (childNode k p dir)).testBit s = p.val.testBit s := by
  have hpeq : nodePath (childNode k p dir) = p.val + if dir then 2 ^ k.val else 0 := by
    dsimp only [childNode]; split_ifs <;> rfl
  rw [hpeq]
  cases dir
  · simp
  · simp only [↓reduceIte]
    have hpow : 2 ^ k.val = 2 ^ (k.val - s) * 2 ^ s := by rw [← pow_add]; congr 1; omega
    have hdiv : (p.val + 2 ^ k.val) / 2 ^ s = p.val / 2 ^ s + 2 ^ (k.val - s) := by
      generalize (p.val : ℕ) = pv
      rw [hpow, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega))]
    have heven : 2 ^ (k.val - s) % 2 = 0 := by
      have h2 : 2 ^ (k.val - s) = 2 * 2 ^ (k.val - s - 1) := by rw [← pow_succ']; congr 1; omega
      rw [h2]; omega
    have ht1 : (p.val + 2 ^ k.val).testBit s = decide ((p.val + 2 ^ k.val) / 2 ^ s % 2 = 1) :=
      Nat.testBit_eq_decide_div_mod_eq
    have ht2 : p.val.testBit s = decide (p.val / 2 ^ s % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    rw [ht1, ht2, hdiv]
    have hmod2 : (p.val / 2 ^ s + 2 ^ (k.val - s)) % 2 = p.val / 2 ^ s % 2 := by omega
    rw [hmod2]

lemma childNode_path_testBit_eq {d : ℕ} (k : Fin d) (p : Fin (2 ^ k.val)) (dir : Bool) :
    (nodePath (childNode k p dir)).testBit k.val = dir := by
  have hpeq : nodePath (childNode k p dir) = p.val + if dir then 2 ^ k.val else 0 := by
    dsimp only [childNode]; split_ifs <;> rfl
  rw [hpeq]
  have ht : (p.val + if dir then 2 ^ k.val else 0).testBit k.val =
      decide ((p.val + if dir then 2 ^ k.val else 0) / 2 ^ k.val % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  rw [ht]
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [Nat.div_eq_of_lt p.isLt]; rfl
  · simp only [↓reduceIte]
    rw [Nat.add_div_right _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt p.isLt]; rfl

lemma childNode_subset_merge {d : ℕ} (k : Fin d) (p : Fin (2 ^ k.val)) (dir : Bool) :
    nodeMask (childNode k p dir) ⊆ nodeMask (TreeNode.merge k p) := by
  rw [nodeMask_subset_iff]
  refine ⟨by rw [childNode_depth]; simp [nodeDepth], fun s hs => ?_, fun h => ?_⟩
  · exact childNode_path_testBit_lt k p dir hs
  · rw [childNode_depth] at h; simp [nodeDepth] at h

lemma childNode_kind {d : ℕ} (k : Fin d) (p : Fin (2 ^ k.val)) (dir : Bool) :
    nodeKind (childNode k p dir) = if dir then 1 else 0 := by
  have hbit := childNode_path_testBit_eq k p dir
  dsimp only [childNode] at hbit ⊢
  by_cases hk : k.val + 1 = d
  · rw [dif_pos hk] at hbit ⊢
    dsimp only [nodeKind, nodePath] at hbit ⊢
    have h1 : d - 1 = k.val := by omega
    rw [h1, hbit]
  · rw [dif_neg hk] at hbit ⊢
    dsimp only [nodeKind, nodePath] at hbit ⊢
    rw [hbit]

lemma merge_subset_tag {d : ℕ} (k : Fin (d - 1)) (p : Fin (2 ^ (k.val + 1))) :
    nodeMask (TreeNode.merge ⟨k.val + 1, by omega⟩ p) ⊆ nodeMask (TreeNode.tag k p) := by
  rw [nodeMask_subset_iff]
  refine ⟨by simp [nodeDepth], fun _ _ => rfl, fun _ h => by simp [nodeIsTag] at h⟩

lemma intact_subtree_level_lb {d : ℕ} (C : Circuit) (tap : Fin 2 → ℕ)
    (hfit : FanInTwo C) (S : Finset (TreeNode d))
    (hsat : ∀ u ∈ S,
      let v := fun a : Fin 2 => (C.wires (inVec (nodeMask u))).getD (tap a) false
      if (nodeKind u).val = 0 then v 0 = true
      else if (nodeKind u).val = 1 then v 1 = true
      else ¬ (v 0 = true ∧ v 1 = true)) :
    ∀ h : ℕ, ∀ (k : Fin d) (p : Fin (2 ^ k.val)),
      d - k.val = h →
      (∀ u : TreeNode d, nodeMask u ⊆ nodeMask (TreeNode.merge k p) → u ∈ S) →
      h ≤ (circuitLevel C (nodeMask (TreeNode.merge k p))).val := by
  intro h
  induction h with
  | zero => intro k _ hk; omega
  | succ h' ih =>
    intro k p hk hintact
    set uM := TreeNode.merge k p
    set c0 := childNode k p false
    set c1 := childNode k p true
    have hsub0 : nodeMask c0 ⊆ nodeMask uM := childNode_subset_merge k p false
    have hsub1 : nodeMask c1 ⊆ nodeMask uM := childNode_subset_merge k p true
    have hc0_in : c0 ∈ S := hintact c0 hsub0
    have hc1_in : c1 ∈ S := hintact c1 hsub1
    have huM_in : uM ∈ S := hintact uM (Finset.Subset.refl _)
    have hchild_lb : ∀ dir : Bool, h' ≤ (circuitLevel C (nodeMask (childNode k p dir))).val := by
      intro dir
      cases h' with
      | zero => omega
      | succ h'' =>
        have hne : k.val + 1 ≠ d := by omega
        let k' : Fin d := ⟨k.val + 1, by omega⟩
        let p' : Fin (2 ^ k'.val) := ⟨p.val + if dir then 2 ^ k.val else 0, by
          have := p.isLt; dsimp only [k']; rw [pow_succ]; cases dir <;> simp <;> omega⟩
        have hcm : nodeMask (TreeNode.merge k' p') ⊆ nodeMask (childNode k p dir) := by
          dsimp only [childNode]; rw [dif_neg hne]
          exact merge_subset_tag ⟨k.val, by omega⟩ p'
        have hsub_uM : nodeMask (TreeNode.merge k' p') ⊆ nodeMask uM :=
          Finset.Subset.trans hcm (childNode_subset_merge k p dir)
        have hlb_m := ih k' p' (by dsimp only [k']; omega) (fun u hu => hintact u (Finset.Subset.trans hu hsub_uM))
        have hmono := (circuitLevel_mono C hfit hcm).1
        omega
    have hlb0 : h' ≤ (circuitLevel C (nodeMask c0)).val := hchild_lb false
    have hlb1 : h' ≤ (circuitLevel C (nodeMask c1)).val := hchild_lb true
    have hm0 := circuitLevel_mono C hfit hsub0
    have hm1 := circuitLevel_mono C hfit hsub1
    have hsat0 := hsat c0 hc0_in
    have hsat1 := hsat c1 hc1_in
    have hsatM := hsat uM huM_in
    rw [childNode_kind k p false] at hsat0
    rw [childNode_kind k p true] at hsat1
    simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_zero] at hsat0
    simp only [↓reduceIte, Fin.val_one] at hsat1
    dsimp only [uM, nodeKind] at hsatM
    simp only [Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one] at hsatM
    by_contra hlt
    have hleM : (circuitLevel C (nodeMask uM)).val ≤ h' := by omega
    have hm0_le := hm0.1
    have hm1_le := hm1.1
    have heq0 : circuitLevel C (nodeMask c0) = circuitLevel C (nodeMask uM) := Fin.ext (by omega)
    have heq1 : circuitLevel C (nodeMask c1) = circuitLevel C (nodeMask uM) := Fin.ext (by omega)
    exact hsatM ⟨hm0.2 heq0 (tap 0) hsat0, hm1.2 heq1 (tap 1) hsat1⟩

def bitWord (dir : Bool) : Fin 2 → Bool := fun a => decide (a.val = if dir then 1 else 0)

def fullLevel {d : ℕ} {b : ℕ} (hb : d < 2 ^ b) (u : TreeNode d) : Fin (2 ^ b) :=
  ⟨nodeHeight u, lt_of_le_of_lt (Nat.sub_le d _) hb⟩

def fullWord {d : ℕ} : TreeNode d → Fin 2 → Bool
  | .leaf p => bitWord (p.val.testBit (d - 1))
  | .merge _ _ => fun _ => false
  | .tag k p => bitWord (p.val.testBit k.val)

lemma full_orderOK {d b : ℕ} (hb : d < 2 ^ b) (u v : TreeNode d) (hsub : nodeMask u ⊆ nodeMask v) :
    (fullLevel hb u).val ≤ (fullLevel hb v).val ∧
    (fullLevel hb u = fullLevel hb v → ∀ a, fullWord u a = true → fullWord v a = true) := by
  have h1 := (nodeMask_subset_iff u v).mp hsub
  have hdu := nodeDepth_le u
  have hdv := nodeDepth_le v
  refine ⟨by dsimp only [fullLevel, nodeHeight]; omega, ?_⟩
  intro heq a hua
  have hdeq : nodeDepth u = nodeDepth v := by
    have := congrArg Fin.val heq; dsimp only [fullLevel, nodeHeight] at this; omega
  by_cases huv : u = v
  · subst huv; exact hua
  · cases u with
    | leaf pu =>
      cases v with
      | leaf pv =>
        exfalso; apply huv; congr 1; apply Fin.ext
        exact eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs)
      | merge kv _ => simp [nodeDepth] at hdeq; omega
      | tag kv _ => simp [nodeDepth] at hdeq; omega
    | merge ku pu =>
      simp [fullWord] at hua
    | tag ku pu =>
      have htv := h1.2.2 hdeq rfl
      cases v with
      | leaf _ => simp [nodeIsTag] at htv
      | merge _ _ => simp [nodeIsTag] at htv
      | tag kv pv =>
        exfalso; apply huv
        simp only [nodeDepth] at hdeq
        have hk : ku = kv := Fin.ext (by omega)
        subst hk; congr 1; apply Fin.ext
        exact eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs)

def delLevel {d b : ℕ} (hb : d - 1 < 2 ^ b) (del : TreeNode d) (u : TreeNode d) : Fin (2 ^ b) :=
  ⟨if nodeMask del ⊆ nodeMask u then nodeHeight u - 1 else nodeHeight u, by
    by_cases hsub : nodeMask del ⊆ nodeMask u
    · rw [if_pos hsub]; have := Nat.sub_le d (nodeDepth u); dsimp only [nodeHeight]; omega
    · rw [if_neg hsub]
      by_cases hu0 : nodeDepth u = 0
      · exfalso; apply hsub; rw [nodeMask_subset_iff]
        refine ⟨by omega, fun _ h => by omega, fun h => ?_⟩
        cases del with
        | leaf _ => simp [nodeIsTag]
        | merge _ _ => simp [nodeIsTag]
        | tag _ _ => rw [hu0] at h; simp [nodeDepth] at h
      · dsimp only [nodeHeight]; omega⟩

def delWord {d : ℕ} (del : TreeNode d) (u : TreeNode d) : Fin 2 → Bool :=
  match u with
  | .leaf p => bitWord (p.val.testBit (d - 1))
  | .merge k _ =>
    if nodeMask del ⊆ nodeMask u then bitWord (!((nodePath del).testBit k.val))
    else fun _ => false
  | .tag k p =>
    if nodeMask del ⊆ nodeMask u then fun _ => true
    else bitWord (p.val.testBit k.val)

lemma del_orderOK {d b : ℕ} (hb : d - 1 < 2 ^ b) (del u v : TreeNode d)
    (hu : u ≠ del) (hv : v ≠ del) (hsub : nodeMask u ⊆ nodeMask v) :
    (delLevel hb del u).val ≤ (delLevel hb del v).val ∧
    (delLevel hb del u = delLevel hb del v → ∀ a, delWord del u a = true → delWord del v a = true) := by
  have h1 := (nodeMask_subset_iff u v).mp hsub
  have hdu := nodeDepth_le u
  have hdv := nodeDepth_le v
  by_cases hdu_sub : nodeMask del ⊆ nodeMask u
  · have hdv_sub : nodeMask del ⊆ nodeMask v := Finset.Subset.trans hdu_sub hsub
    have hdu_lt : nodeDepth u < d := by
      have hdd := (nodeMask_subset_iff del u).mp hdu_sub
      by_contra hge
      have hdu_eq : nodeDepth u = d := by omega
      have hdel_eq : nodeDepth del = d := by have := nodeDepth_le del; omega
      apply hu
      apply nodeMask_injective
      apply Finset.Subset.antisymm _ hdu_sub
      rw [nodeMask_subset_iff]
      refine ⟨by omega, fun s hs => (hdd.2.1 s (by omega)).symm, fun _ htu => ?_⟩
      cases u with
      | leaf _ => simp [nodeIsTag] at htu
      | merge k _ => have := k.isLt; simp [nodeDepth] at hdu_eq; omega
      | tag k _ => have := k.isLt; simp [nodeDepth] at hdu_eq; omega
    refine ⟨by dsimp only [delLevel, nodeHeight]; rw [if_pos hdu_sub, if_pos hdv_sub]; omega, ?_⟩
    intro heq a hua
    have hdeq : nodeDepth u = nodeDepth v := by
      have := congrArg Fin.val heq
      dsimp only [delLevel, nodeHeight] at this
      rw [if_pos hdu_sub, if_pos hdv_sub] at this; omega
    by_cases huv : u = v
    · subst huv; exact hua
    · cases v with
      | leaf pv => change nodeDepth u = d at hdeq; omega
      | merge kv pv =>
        exfalso
        cases u with
        | leaf _ => have := kv.isLt; simp [nodeDepth] at hdeq; omega
        | merge ku pu =>
          apply huv; simp only [nodeDepth] at hdeq
          have hk : ku = kv := Fin.ext hdeq
          subst hk; congr 1; apply Fin.ext
          exact eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs)
        | tag ku pu =>
          have htv := h1.2.2 hdeq rfl; simp [nodeIsTag] at htv
      | tag kv pv =>
        dsimp only [delWord]; rw [if_pos hdv_sub]
  · by_cases hdv_sub : nodeMask del ⊆ nodeMask v
    · have hstrict : nodeDepth v < nodeDepth u := by
        by_contra hge
        have hdeq : nodeDepth u = nodeDepth v := by omega
        have hdv_info := (nodeMask_subset_iff del v).mp hdv_sub
        cases v with
        | leaf pv =>
          cases u with
          | leaf pu =>
            have hp : pu = pv := Fin.ext (eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs))
            subst hp; exact hdu_sub hdv_sub
          | merge k _ => have := k.isLt; simp [nodeDepth] at hdeq; omega
          | tag k _ => have := k.isLt; simp [nodeDepth] at hdeq; omega
        | merge kv pv =>
          cases u with
          | leaf _ => have := kv.isLt; simp [nodeDepth] at hdeq; omega
          | merge ku pu =>
            simp only [nodeDepth] at hdeq
            have hk : ku = kv := Fin.ext hdeq
            subst hk
            have hp : pu = pv := Fin.ext (eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs))
            subst hp; exact hdu_sub hdv_sub
          | tag _ _ => have := h1.2.2 hdeq rfl; simp [nodeIsTag] at this
        | tag kv pv =>
          apply hdu_sub
          rw [nodeMask_subset_iff]
          refine ⟨by omega, fun s hs => (hdv_info.2.1 s (by omega)).trans (h1.2.1 s (by omega)).symm, ?_⟩
          intro hdel_u htdel
          exfalso; apply hv
          apply nodeMask_injective
          apply Finset.Subset.antisymm _ hdv_sub
          rw [nodeMask_subset_iff]
          refine ⟨by omega, fun s hs => (hdv_info.2.1 s (by omega)).symm, fun _ _ => htdel⟩
      refine ⟨by dsimp only [delLevel, nodeHeight]; rw [if_neg hdu_sub, if_pos hdv_sub]; omega, ?_⟩
      intro heq a hua
      have hdepth_step : nodeDepth u = nodeDepth v + 1 := by
        have := congrArg Fin.val heq
        dsimp only [delLevel, nodeHeight] at this
        rw [if_neg hdu_sub, if_pos hdv_sub] at this; omega
      cases v with
      | leaf _ => change d < nodeDepth u at hstrict; omega
      | tag kv pv =>
        dsimp only [delWord]; rw [if_pos hdv_sub]
      | merge kv pv =>
        dsimp only [delWord]; rw [if_pos hdv_sub]
        have hdv_info := (nodeMask_subset_iff del (TreeNode.merge kv pv)).mp hdv_sub
        have hdel_gt : kv.val < nodeDepth del := by
          by_contra hle
          have hdeq : nodeDepth del = kv.val := by
            have hle' : kv.val ≤ nodeDepth del := hdv_info.1
            omega
          apply hv
          cases del with
          | leaf _ => have := kv.isLt; simp [nodeDepth] at hdeq; omega
          | merge kdel pdel =>
            simp only [nodeDepth] at hdeq
            have hk : kv = kdel := Fin.ext hdeq.symm
            subst hk; congr 1; apply Fin.ext
            exact eq_of_testBit_lt_pow pv.isLt pdel.isLt (fun s hs => (hdv_info.2.1 s hs).symm)
          | tag _ _ => have := hdv_info.2.2 hdeq rfl; simp [nodeIsTag] at this
        have hbit_ne : (nodePath u).testBit kv.val ≠ (nodePath del).testBit kv.val := by
          intro hbeq
          apply hdu_sub
          rw [nodeMask_subset_iff]
          have hdu_kv : nodeDepth u = kv.val + 1 := hdepth_step
          refine ⟨by omega, fun s hs => ?_, fun hdeq htdel => ?_⟩
          · by_cases hsk : s < kv.val
            · exact (hdv_info.2.1 s hsk).trans (h1.2.1 s hsk).symm
            · have hseq : s = kv.val := by omega
              rw [hseq]; exact hbeq.symm
          · cases u with
            | leaf pu =>
              exfalso; apply hu
              cases del with
              | leaf pdel =>
                congr 1; apply Fin.ext
                exact eq_of_testBit_lt_pow pu.isLt pdel.isLt (fun s hs => by
                  by_cases hsk : s < kv.val
                  · exact (h1.2.1 s hsk).trans (hdv_info.2.1 s hsk).symm
                  · have hseq : s = kv.val := by change d = kv.val + 1 at hdu_kv; omega
                    rw [hseq]; exact hbeq)
              | merge _ _ => simp [nodeIsTag] at htdel
              | tag kdel _ => have := kdel.isLt; simp [nodeDepth] at hdeq; omega
            | merge _ _ =>
              exfalso; simp only [delWord] at hua; rw [if_neg hdu_sub] at hua; cases hua
            | tag _ _ => rfl
        have hbit_eq : (nodePath u).testBit kv.val = !((nodePath del).testBit kv.val) := by
          cases h1' : (nodePath u).testBit kv.val <;> cases h2' : (nodePath del).testBit kv.val
          · exact absurd (h1'.trans h2'.symm) hbit_ne
          · rfl
          · rfl
          · exact absurd (h1'.trans h2'.symm) hbit_ne
        cases u with
        | leaf pu =>
          dsimp only [delWord] at hua
          simp only [nodeDepth] at hdepth_step
          have hdm : d - 1 = kv.val := by omega
          rw [hdm] at hua
          simp only [nodePath] at hbit_eq
          rwa [hbit_eq] at hua
        | merge ku pu =>
          dsimp only [delWord] at hua; rw [if_neg hdu_sub] at hua; cases hua
        | tag ku pu =>
          dsimp only [delWord] at hua; rw [if_neg hdu_sub] at hua
          simp only [nodeDepth] at hdepth_step
          have hk : ku.val = kv.val := by omega
          have hbit_u : pu.val.testBit ku.val = pu.val.testBit kv.val := congrArg (Nat.testBit pu.val) hk
          rw [hbit_u] at hua
          simp only [nodePath] at hbit_eq
          rwa [hbit_eq] at hua
    · refine ⟨by dsimp only [delLevel, nodeHeight]; rw [if_neg hdu_sub, if_neg hdv_sub]; omega, ?_⟩
      intro heq a hua
      have hdeq : nodeDepth u = nodeDepth v := by
        have := congrArg Fin.val heq
        dsimp only [delLevel, nodeHeight] at this
        rw [if_neg hdu_sub, if_neg hdv_sub] at this; omega
      by_cases huv : u = v
      · subst huv; exact hua
      · cases u with
        | leaf pu =>
          cases v with
          | leaf pv =>
            exfalso; apply huv; congr 1; apply Fin.ext
            exact eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs)
          | merge _ _ => simp [nodeDepth] at hdeq; omega
          | tag _ _ => simp [nodeDepth] at hdeq; omega
        | merge _ _ =>
          dsimp only [delWord] at hua; rw [if_neg hdu_sub] at hua; cases hua
        | tag ku pu =>
          have htv := h1.2.2 hdeq rfl
          cases v with
          | leaf _ => simp [nodeIsTag] at htv
          | merge _ _ => simp [nodeIsTag] at htv
          | tag kv pv =>
            exfalso; apply huv
            simp only [nodeDepth] at hdeq
            have hk : ku = kv := Fin.ext (by omega)
            subst hk; congr 1; apply Fin.ext
            exact eq_of_testBit_lt_pow pu.isLt pv.isLt (fun s hs => h1.2.1 s hs)

lemma bitWord_sat (dir : Bool) :
    if (if dir then (1 : Fin 3) else 0).val = 0 then bitWord dir 0 = true
    else if (if dir then (1 : Fin 3) else 0).val = 1 then bitWord dir 1 = true
    else ¬(bitWord dir 0 = true ∧ bitWord dir 1 = true) := by
  cases dir <;> decide

lemma bitWord_not_both (dir : Bool) : ¬(bitWord dir 0 = true ∧ bitWord dir 1 = true) := by
  cases dir <;> decide

lemma fullWord_sat {d : ℕ} (u : TreeNode d) :
    if (nodeKind u).val = 0 then fullWord u 0 = true
    else if (nodeKind u).val = 1 then fullWord u 1 = true
    else ¬(fullWord u 0 = true ∧ fullWord u 1 = true) := by
  cases u with
  | leaf p => exact bitWord_sat (p.val.testBit (d - 1))
  | merge _ _ => simp [nodeKind, fullWord]
  | tag k p => exact bitWord_sat (p.val.testBit k.val)

lemma delWord_sat {d : ℕ} (del u : TreeNode d) :
    if (nodeKind u).val = 0 then delWord del u 0 = true
    else if (nodeKind u).val = 1 then delWord del u 1 = true
    else ¬(delWord del u 0 = true ∧ delWord del u 1 = true) := by
  cases u with
  | leaf p => exact bitWord_sat (p.val.testBit (d - 1))
  | merge k p =>
    dsimp only [nodeKind, delWord]
    simp only [Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one]
    split_ifs
    · exact bitWord_not_both _
    · simp
  | tag k p =>
    dsimp only [nodeKind, delWord]
    by_cases hsub : nodeMask del ⊆ nodeMask (TreeNode.tag k p)
    · rw [if_pos hsub]; by_cases h : p.val.testBit k.val = true <;> simp [h]
    · rw [if_neg hsub]; exact bitWord_sat (p.val.testBit k.val)

lemma inVec_eq_ofFn {n : ℕ} (s : Finset (Fin n)) (inst : ∀ j : Fin n, Decidable (j ∈ s)) :
    List.ofFn (fun j : Fin n => @decide (j ∈ s) (inst j)) ++ [false, true] = inVec s := by
  simp only [inVec]
  congr 1; apply congrArg List.ofFn; funext j; exact decide_eq_decide.mpr Iff.rfl

lemma main_bridge :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ d : Nat, 1 ≤ d →
      let m := 3*2^d-3
      ∃ (x : Fin m → Finset (Fin (3*d))) (kind : Fin m → Fin 3), Function.Injective x ∧
        let fits := fun (S : Finset (Fin m)) (b : Nat) =>
          ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
            PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*d+2) C ∧
            C.output < 3*d+2+C.size ∧ (∀ a, tap a < 3*d+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
            ∀ i ∈ S, let v := fun (a : Fin 2) =>
              (C.wires (List.ofFn (fun j : Fin (3*d) => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false
              if (kind i).val = 0 then v 0 = true else if (kind i).val = 1 then v 1 = true
              else ¬ (v 0 = true ∧ v 1 = true)
        ∀ b, (fits Finset.univ b ↔ d < 2^b) ∧
          ∀ i, (fits (Finset.univ.erase i) b ↔ d-1 < 2^b) := by
  intro d hd
  dsimp only
  set m := 3 * 2 ^ d - 3
  let e : Fin m ≃ TreeNode d := (Fintype.equivFinOfCardEq (card_treeNode hd)).symm
  let x : Fin m → Finset (Fin (3 * d)) := fun i => nodeMask (e i)
  let kind : Fin m → Fin 3 := fun i => nodeKind (e i)
  refine ⟨x, kind, nodeMask_injective.comp e.injective, fun b => ⟨?_, ?_⟩⟩
  · constructor
    · rintro ⟨C, tap, hfit, _, _, _, hnc, hsat⟩
      have hsat_t : ∀ u ∈ (Finset.univ : Finset (TreeNode d)),
          let v := fun a : Fin 2 => (C.wires (inVec (nodeMask u))).getD (tap a) false
          if (nodeKind u).val = 0 then v 0 = true
          else if (nodeKind u).val = 1 then v 1 = true
          else ¬ (v 0 = true ∧ v 1 = true) := by
        intro u _
        have h1 := hsat (e.symm u) (Finset.mem_univ _)
        dsimp only [x, kind] at h1
        simp only [Equiv.apply_symm_apply, inVec_eq_ofFn] at h1
        split_ifs at h1 ⊢ <;> exact h1
      let root := TreeNode.merge (d := d) ⟨0, by omega⟩ ⟨0, by simp⟩
      have hlb := intact_subtree_level_lb C tap hfit Finset.univ hsat_t d ⟨0, by omega⟩ ⟨0, by simp⟩
        (by simp) (fun _ _ => Finset.mem_univ _)
      have hlt : (circuitLevel C (nodeMask root)).val < 2 ^ notCount C := (circuitLevel C _).isLt
      have hpow : 2 ^ notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnc
      omega
    · intro hb
      have hord : ∀ i j : Fin m, x i ⊆ x j →
          (fullLevel hb (e i)).val ≤ (fullLevel hb (e j)).val ∧
          (fullLevel hb (e i) = fullLevel hb (e j) → ∀ a, fullWord (e i) a = true → fullWord (e j) a = true) :=
        fun i j hs => full_orderOK hb (e i) (e j) hs
      rcases build_circuit_of_orderOK hord with ⟨C, tap, hfit, hrb, hout, htap, hnc, heval⟩
      refine ⟨C, tap, hfit, hrb, hout, htap, hnc, fun i _ => ?_⟩
      have hin := inVec_eq_ofFn (x i) (fun j => Classical.propDecidable (j ∈ x i))
      have h0 : (C.wires (List.ofFn (fun j : Fin (3 * d) => @decide (j ∈ x i) (Classical.propDecidable _)) ++ [false, true])).getD (tap 0) false = fullWord (e i) 0 := by
        rw [hin]; exact heval i 0
      have h1 : (C.wires (List.ofFn (fun j : Fin (3 * d) => @decide (j ∈ x i) (Classical.propDecidable _)) ++ [false, true])).getD (tap 1) false = fullWord (e i) 1 := by
        rw [hin]; exact heval i 1
      have hsat := fullWord_sat (e i)
      dsimp only [kind]
      split_ifs at hsat ⊢ <;> simpa only [h0, h1] using hsat
  · intro i
    constructor
    · rintro ⟨C, tap, hfit, _, _, _, hnc, hsat⟩
      by_cases hd1 : d = 1
      · subst hd1; exact Nat.pow_pos (by omega)
      · have hd2 : 2 ≤ d := by omega
        let del := e i
        let k1 : Fin d := ⟨1, by omega⟩
        let m0 := TreeNode.merge k1 ⟨0, by simp [k1]⟩
        let m1 := TreeNode.merge k1 ⟨1, by simp [k1]⟩
        have hdisj : ¬(nodeMask del ⊆ nodeMask m0 ∧ nodeMask del ⊆ nodeMask m1) := by
          rintro ⟨h0, h1⟩
          have ha := ((nodeMask_subset_iff del m0).mp h0).2.1 0 (by simp [m0, nodeDepth, k1])
          have hb := ((nodeMask_subset_iff del m1).mp h1).2.1 0 (by simp [m1, nodeDepth, k1])
          simp only [m0, m1, nodePath] at ha hb
          rw [ha] at hb
          exact absurd hb (by decide)
        let S : Finset (TreeNode d) := Finset.univ.erase del
        have hsat_t : ∀ u ∈ S,
            let v := fun a : Fin 2 => (C.wires (inVec (nodeMask u))).getD (tap a) false
            if (nodeKind u).val = 0 then v 0 = true
            else if (nodeKind u).val = 1 then v 1 = true
            else ¬ (v 0 = true ∧ v 1 = true) := by
          intro u hu
          have hne : e.symm u ≠ i := by
            intro heq
            have : u = del := by dsimp only [del]; rw [← heq, Equiv.apply_symm_apply]
            exact (Finset.mem_erase.mp hu).1 this
          have h1 := hsat (e.symm u) (by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact hne)
          dsimp only [x, kind] at h1
          simp only [Equiv.apply_symm_apply, inVec_eq_ofFn] at h1
          split_ifs at h1 ⊢ <;> exact h1
        have hpow : 2 ^ notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnc
        by_cases h0 : nodeMask del ⊆ nodeMask m0
        · have hnot1 : ¬(nodeMask del ⊆ nodeMask m1) := fun h1 => hdisj ⟨h0, h1⟩
          have hlb := intact_subtree_level_lb C tap hfit S hsat_t (d - 1) k1 ⟨1, by simp [k1]⟩
            (by simp [k1]) (fun u hu => Finset.mem_erase.mpr ⟨fun hEq => hnot1 (hEq ▸ hu), Finset.mem_univ _⟩)
          have hlt := (circuitLevel C (nodeMask m1)).isLt
          omega
        · have hlb := intact_subtree_level_lb C tap hfit S hsat_t (d - 1) k1 ⟨0, by simp [k1]⟩
            (by simp [k1]) (fun u hu => Finset.mem_erase.mpr ⟨fun hEq => h0 (hEq ▸ hu), Finset.mem_univ _⟩)
          have hlt := (circuitLevel C (nodeMask m0)).isLt
          omega
    · intro hb
      let Ssub := {j : Fin m // j ≠ i}
      let es : Fin (Fintype.card Ssub) ≃ Ssub := (Fintype.equivFin Ssub).symm
      let x' : Fin (Fintype.card Ssub) → Finset (Fin (3 * d)) := fun idx => x (es idx).val
      let lv' : Fin (Fintype.card Ssub) → Fin (2 ^ b) := fun idx => delLevel hb (e i) (e (es idx).val)
      let w' : Fin (Fintype.card Ssub) → Fin 2 → Bool := fun idx => delWord (e i) (e (es idx).val)
      have hord : ∀ a1 a2, x' a1 ⊆ x' a2 → (lv' a1).val ≤ (lv' a2).val ∧
          (lv' a1 = lv' a2 → ∀ c, w' a1 c = true → w' a2 c = true) := by
        intro a1 a2 hsub
        have hne1 : e (es a1).val ≠ e i := fun h => (es a1).property (e.injective h)
        have hne2 : e (es a2).val ≠ e i := fun h => (es a2).property (e.injective h)
        exact del_orderOK hb (e i) (e (es a1).val) (e (es a2).val) hne1 hne2 hsub
      rcases build_circuit_of_orderOK hord with ⟨C, tap, hfit, hrb, hout, htap, hnc, heval⟩
      refine ⟨C, tap, hfit, hrb, hout, htap, hnc, fun j hj => ?_⟩
      have hjne : j ≠ i := by simp only [Finset.mem_erase] at hj; exact hj.1
      let idx := es.symm ⟨j, hjne⟩
      have hidx : (es idx).val = j := congrArg Subtype.val (Equiv.apply_symm_apply es ⟨j, hjne⟩)
      have hin := inVec_eq_ofFn (x j) (fun q => Classical.propDecidable (q ∈ x j))
      have h0 : (C.wires (List.ofFn (fun q : Fin (3 * d) => @decide (q ∈ x j) (Classical.propDecidable _)) ++ [false, true])).getD (tap 0) false = delWord (e i) (e j) 0 := by
        rw [hin]; have := heval idx 0; dsimp only [x', w'] at this; rwa [hidx] at this
      have h1 : (C.wires (List.ofFn (fun q : Fin (3 * d) => @decide (q ∈ x j) (Classical.propDecidable _)) ++ [false, true])).getD (tap 1) false = delWord (e i) (e j) 1 := by
        rw [hin]; have := heval idx 1; dsimp only [x', w'] at this; rwa [hidx] at this
      have hsat := delWord_sat (e i) (e j)
      dsimp only [kind]
      split_ifs at hsat ⊢ <;> simpa only [h0, h1] using hsat

end BinaryTree

end PEqualNP.Outside.L_lib_1307_aux

theorem PEqualNP.Outside.L_lib_1307 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ d : Nat, 1 ≤ d →
  let m := 3*2^d-3
  ∃ (x : Fin m → Finset (Fin (3*d))) (kind : Fin m → Fin 3), Function.Injective x ∧
    let fits := fun (S : Finset (Fin m)) (b : Nat) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*d+2) C ∧
        C.output < 3*d+2+C.size ∧ (∀ a, tap a < 3*d+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        ∀ i ∈ S, let v := fun (a : Fin 2) =>
          (C.wires (List.ofFn (fun j : Fin (3*d) => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false
          if (kind i).val = 0 then v 0 = true else if (kind i).val = 1 then v 1 = true
          else ¬ (v 0 = true ∧ v 1 = true)
    ∀ b, (fits Finset.univ b ↔ d < 2^b) ∧
      ∀ i, (fits (Finset.univ.erase i) b ↔ d-1 < 2^b) :=
  PEqualNP.Outside.L_lib_1307_aux.main_bridge
