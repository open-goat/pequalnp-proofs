import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1423_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Classical

noncomputable section

/-! ## Evaluation of a gate list from local consistency -/

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem length_foldl (gs : List Gate) (x : List Bool) :
    (gs.foldl stepW x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_spec (x : List Bool) (v : ℕ → Bool)
    (hx : ∀ w < x.length, x.getD w false = v w) (gs : List Gate)
    (hg : ∀ p (hp : p < gs.length), (∀ i ∈ (gs[p]).inputs, i < x.length + p) ∧
        v (x.length + p) = (gs[p]).op.eval ((gs[p]).inputs.map v)) :
    ∀ w < x.length + gs.length, (gs.foldl stepW x).getD w false = v w := by
  induction gs using List.reverseRecOn with
  | nil => intro w hw; simpa using hx w (by simpa using hw)
  | append_singleton gs g ih =>
    intro w hw
    have hg' : ∀ p (hp : p < gs.length), (∀ i ∈ (gs[p]).inputs, i < x.length + p) ∧
        v (x.length + p) = (gs[p]).op.eval ((gs[p]).inputs.map v) := by
      intro p hp
      have := hg p (by simp; omega)
      rwa [List.getElem_append_left hp] at this
    have ih' := ih hg'
    have hlen := length_foldl gs x
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hs : ∀ W : List Bool, stepW W g = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] :=
      fun _ => rfl
    rw [hs]
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    rcases Nat.lt_or_ge w (x.length + gs.length) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]; exact ih' w h
    · have hw' : w = x.length + gs.length := by omega
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hlast := hg gs.length (by simp)
      rw [List.getElem_append_right (Nat.le_refl _)] at hlast
      simp only [Nat.sub_self, List.getElem_cons_zero] at hlast
      rw [show w - (gs.foldl stepW x).length = 0 by omega]
      simp only [List.getD_cons_zero]
      rw [hw', hlast.2]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih' i (hlast.1 i hi)

/-! ## Layered circuits over a finite set of states -/

inductive Src (α : Type) where
  | inp (w : ℕ)
  | node (t : ℕ) (b : α)

section Layered
variable {α : Type} [Inhabited α] (S : Finset α)

def enc (b : α) : ℕ := if h : b ∈ S then ((S.equivFin ⟨b, h⟩ : Fin S.card) : ℕ) else 0

def dec (q : ℕ) : α := if h : q < S.card then ((S.equivFin.symm ⟨q, h⟩ : S) : α) else default

theorem enc_lt {b : α} (hb : b ∈ S) : enc S b < S.card := by
  unfold enc; rw [dif_pos hb]; exact Fin.isLt _

theorem dec_mem {q : ℕ} (hq : q < S.card) : dec S q ∈ S := by
  unfold dec; rw [dif_pos hq]; exact Subtype.property _

theorem dec_enc {b : α} (hb : b ∈ S) : dec S (enc S b) = b := by
  have h1 : enc S b = ((S.equivFin ⟨b, hb⟩ : Fin S.card) : ℕ) := by unfold enc; rw [dif_pos hb]
  unfold dec
  rw [dif_pos (enc_lt S hb)]
  have : (⟨enc S b, enc_lt S hb⟩ : Fin S.card) = S.equivFin ⟨b, hb⟩ := Fin.ext h1
  rw [this, Equiv.symm_apply_apply]

theorem enc_dec {q : ℕ} (hq : q < S.card) : enc S (dec S q) = q := by
  have hm := dec_mem S hq
  have hd : dec S q = ((S.equivFin.symm ⟨q, hq⟩ : S) : α) := by unfold dec; rw [dif_pos hq]
  unfold enc; rw [dif_pos hm]
  have : (⟨dec S q, hm⟩ : S) = S.equivFin.symm ⟨q, hq⟩ := Subtype.ext hd
  rw [this, Equiv.apply_symm_apply]

def wireOf (N : ℕ) : Src α → ℕ
  | .inp w => w
  | .node t b => N + t * S.card + enc S b

def mkGate (N : ℕ) (spec : ℕ → α → GateOp × Src α × Src α) (p : ℕ) : Gate :=
  ⟨(spec (p / S.card) (dec S (p % S.card))).1,
   [wireOf S N (spec (p / S.card) (dec S (p % S.card))).2.1,
    wireOf S N (spec (p / S.card) (dec S (p % S.card))).2.2]⟩

def layered (N T : ℕ) (spec : ℕ → α → GateOp × Src α × Src α) (out : ℕ) : Circuit :=
  ⟨List.ofFn (fun p : Fin (T * S.card) => mkGate S N spec p), out⟩

def SrcOK (N t : ℕ) : Src α → Prop
  | .inp w => w < N
  | .node t' b => t' < t ∧ b ∈ S

def srcVal (x : List Bool) (M : ℕ → α → Bool) : Src α → Bool
  | .inp w => x.getD w false
  | .node t b => M t b

structure SpecOK (N T : ℕ) (spec : ℕ → α → GateOp × Src α × Src α) : Prop where
  op : ∀ t < T, ∀ b ∈ S, (spec t b).1 = GateOp.and ∨ (spec t b).1 = GateOp.or
  s1 : ∀ t < T, ∀ b ∈ S, SrcOK S N t (spec t b).2.1
  s2 : ∀ t < T, ∀ b ∈ S, SrcOK S N t (spec t b).2.2

theorem layered_size (N T : ℕ) (spec : ℕ → α → GateOp × Src α × Src α) (out : ℕ) :
    (layered S N T spec out).size = T * S.card := by
  simp [layered, Circuit.size]

theorem layered_len (N T : ℕ) (spec : ℕ → α → GateOp × Src α × Src α) (out : ℕ) :
    (layered S N T spec out).gates.length = T * S.card := by
  simp [layered]

theorem layered_gate {N T : ℕ} {spec : ℕ → α → GateOp × Src α × Src α} {out : ℕ} {p : ℕ}
    (hp : p < (layered S N T spec out).gates.length) :
    (layered S N T spec out).gates[p] = mkGate S N spec p := by
  simp [layered]

theorem wireOf_lt {N t p : ℕ} {src : Src α} (h : SrcOK S N t src) (htp : t * S.card ≤ p) :
    wireOf S N src < N + p := by
  cases src with
  | inp w => simp only [SrcOK] at h; simp only [wireOf]; omega
  | node t' b =>
    simp only [SrcOK] at h
    simp only [wireOf]
    have h1 := enc_lt S h.2
    have h2 : (t' + 1) * S.card ≤ t * S.card := Nat.mul_le_mul_right _ h.1
    rw [Nat.succ_mul] at h2
    omega

theorem dec_props {T p : ℕ} (hp : p < T * S.card) :
    p / S.card < T ∧ dec S (p % S.card) ∈ S ∧ p / S.card * S.card ≤ p := by
  have hQ : 0 < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · rw [h, Nat.mul_zero] at hp; omega
    · exact h
  exact ⟨(Nat.div_lt_iff_lt_mul hQ).2 hp, dec_mem S (Nat.mod_lt _ hQ), Nat.div_mul_le_self _ _⟩

theorem layered_fan {N T : ℕ} {spec : ℕ → α → GateOp × Src α × Src α} {out : ℕ}
    (hs : SpecOK S N T spec) : FanInTwo (layered S N T spec out) := by
  intro g hg
  simp only [layered, List.mem_ofFn] at hg
  obtain ⟨p, rfl⟩ := hg
  obtain ⟨h1, h2, -⟩ := dec_props S p.isLt
  refine ⟨?_, by simp [mkGate]⟩
  rcases hs.op _ h1 _ h2 with h | h <;> simp [mkGate, h]

theorem layered_reads {N T : ℕ} {spec : ℕ → α → GateOp × Src α × Src α} {out : ℕ}
    (hs : SpecOK S N T spec) : ReadsBack N (layered S N T spec out) := by
  intro j hj i hi
  have hj' : j < T * S.card := by rwa [layered_len] at hj
  rw [gateAt, List.getD_eq_getElem _ _ hj, layered_gate S hj] at hi
  obtain ⟨h1, h2, h3⟩ := dec_props S hj'
  simp only [mkGate, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact wireOf_lt S (hs.s1 _ h1 _ h2) h3
  · exact wireOf_lt S (hs.s2 _ h1 _ h2) h3

theorem layered_notCount {N T : ℕ} {spec : ℕ → α → GateOp × Src α × Src α} {out : ℕ}
    (hs : SpecOK S N T spec) : PEqualNP.NotBracket.notCount (layered S N T spec out) = 0 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp only [layered, List.mem_ofFn] at hg
  obtain ⟨p, rfl⟩ := hg
  obtain ⟨h1, h2, -⟩ := dec_props S p.isLt
  rcases hs.op _ h1 _ h2 with h | h <;> simp [mkGate, h]

theorem layered_wire {N T : ℕ} {spec : ℕ → α → GateOp × Src α × Src α} {out : ℕ}
    (hs : SpecOK S N T spec)
    (x : List Bool) (hx : x.length = N) (M : ℕ → α → Bool)
    (hM : ∀ t < T, ∀ b ∈ S, M t b =
      (spec t b).1.eval [srcVal x M (spec t b).2.1, srcVal x M (spec t b).2.2])
    {t : ℕ} (ht : t < T) {b : α} (hb : b ∈ S) :
    ((layered S N T spec out).wires x).getD (N + t * S.card + enc S b) false = M t b := by
  have hQ : 0 < S.card := Finset.card_pos.2 ⟨b, hb⟩
  let v : ℕ → Bool := fun w =>
    if w < N then x.getD w false else M ((w - N) / S.card) (dec S ((w - N) % S.card))
  have hv : ∀ t' b', b' ∈ S → v (N + t' * S.card + enc S b') = M t' b' := by
    intro t' b' hb'
    have he := enc_lt S hb'
    simp only [v, show ¬ (N + t' * S.card + enc S b' < N) by omega, if_false]
    have e1 : N + t' * S.card + enc S b' - N = enc S b' + t' * S.card := by omega
    rw [e1, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt he, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he, dec_enc S hb']
  have hsrc : ∀ t' src, SrcOK S N t' src → v (wireOf S N src) = srcVal x M src := by
    intro t' src h
    cases src with
    | inp w => simp only [SrcOK] at h; simp [v, wireOf, srcVal, h]
    | node t'' b' => simp only [SrcOK] at h; simp only [wireOf, srcVal]; exact hv t'' b' h.2
  rw [wires_eq]
  have key := foldl_spec x v (fun w hw => by simp [v, hx ▸ hw]) (layered S N T spec out).gates (by
    intro p hp
    have hp' : p < T * S.card := by rwa [layered_len] at hp
    obtain ⟨h1, h2, h3⟩ := dec_props S hp'
    rw [layered_gate S hp]
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [mkGate, List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [hx]
      rcases hi with rfl | rfl
      · exact wireOf_lt S (hs.s1 _ h1 _ h2) h3
      · exact wireOf_lt S (hs.s2 _ h1 _ h2) h3
    · simp only [mkGate, List.map_cons, List.map_nil]
      rw [hsrc _ _ (hs.s1 _ h1 _ h2), hsrc _ _ (hs.s2 _ h1 _ h2), ← hM _ h1 _ h2]
      have hdm := Nat.div_add_mod' p S.card
      have : x.length + p = N + p / S.card * S.card + enc S (dec S (p % S.card)) := by
        rw [enc_dec S (Nat.mod_lt _ hQ)]; omega
      rw [this, hv _ _ h2])
  rw [key _ ?_]
  · exact hv t b hb
  · rw [hx, layered_len]
    have := enc_lt S hb
    have h2 : (t + 1) * S.card ≤ T * S.card := Nat.mul_le_mul_right _ ht
    rw [Nat.succ_mul] at h2
    omega

end Layered

/-! ## The budget recursion -/

abbrev St (k : ℕ) := Fin k → ℕ × ℕ
abbrev Col (k : ℕ) := (Fin k → Bool) × (Fin k → Bool)

def Zb (x : List Bool) (r j i : ℕ) : Bool := x.getD (j * r + i) false
def Ob (x : List Bool) (r k j i : ℕ) : Bool := x.getD (k * r + j * r + i) false
def Lb (x : List Bool) (r k i : ℕ) : Bool := x.getD (k * r + k * r + i) false
def Ub (x : List Bool) (r k i : ℕ) : Bool := x.getD (k * r + k * r + r + i) false
def fW (r k : ℕ) : ℕ := k * r + k * r + r + r
def tW (r k : ℕ) : ℕ := k * r + k * r + r + r + 1

def perm (x : List Bool) (r k i : ℕ) (j : ℕ) (v : Bool) : Prop :=
  (v = false → Zb x r j i = true) ∧ (v = true → Ob x r k j i = true)

def colOK (x : List Bool) (r k i : ℕ) (cy : Col k) : Prop :=
  (∀ j j' : Fin k, j ≤ j' → cy.2 j = true → cy.2 j' = true) ∧
  (Lb x r k i = false → ∀ j, cy.2 j = true) ∧
  (Ub x r k i = false → ∀ j, cy.2 j = false) ∧
  ∀ j : Fin k, perm x r k i j (cy.1 j)

def cA {k : ℕ} (col : ℕ → Col k) (m : ℕ) (j : Fin k) : ℕ :=
  ∑ i ∈ Finset.range m, if (col i).1 j = true ∧ (col i).2 j = false then 1 else 0

def cF {k : ℕ} (col : ℕ → Col k) (m : ℕ) (j : Fin k) : ℕ :=
  ∑ i ∈ Finset.range m, if (col i).1 j = false ∧ (col i).2 j = true then 1 else 0

def R (x : List Bool) (r k m : ℕ) (b : St k) : Prop :=
  ∃ col : ℕ → Col k, (∀ i < m, colOK x r k i (col i)) ∧
    ∀ j, cA col m j ≤ (b j).1 ∧ cF col m j ≤ (b j).2

def qA (s : ℕ) (v : Bool) (j : ℕ) : ℕ := if v = true ∧ ¬ s ≤ j then 1 else 0
def qF (s : ℕ) (v : Bool) (j : ℕ) : ℕ := if v = false ∧ s ≤ j then 1 else 0

def pA {k : ℕ} (s : ℕ) (c : Fin k → Bool) (j : ℕ) (j' : Fin k) : ℕ :=
  if j'.val < j then qA s (c j') j'.val else 0
def pF {k : ℕ} (s : ℕ) (c : Fin k → Bool) (j : ℕ) (j' : Fin k) : ℕ :=
  if j'.val < j then qF s (c j') j'.val else 0

def allowL (x : List Bool) (r k i s : ℕ) : Prop := s = 0 ∨ Lb x r k i = true
def allowU (x : List Bool) (r k i s : ℕ) : Prop := s = k ∨ Ub x r k i = true

def Tm (x : List Bool) (r k i s j : ℕ) (b : St k) : Prop :=
  allowL x r k i s ∧ allowU x r k i s ∧ ∃ (c : Fin k → Bool) (b0 : St k),
    (∀ j' : Fin k, j'.val < j → perm x r k i j' (c j')) ∧ R x r k i b0 ∧
    ∀ j' : Fin k, (b0 j').1 + pA s c j j' ≤ (b j').1 ∧ (b0 j').2 + pF s c j j' ≤ (b j').2

def dF {k : ℕ} (j : ℕ) (b : St k) : St k :=
  fun j' => if j'.val = j then ((b j').1, (b j').2 - 1) else b j'
def dA {k : ℕ} (j : ℕ) (b : St k) : St k :=
  fun j' => if j'.val = j then ((b j').1 - 1, (b j').2) else b j'
def bget {k : ℕ} (b : St k) (j : ℕ) : ℕ × ℕ := if h : j < k then b ⟨j, h⟩ else (0, 0)

theorem R_mono {x : List Bool} {r k m : ℕ} {b b' : St k} (h : R x r k m b)
    (hle : ∀ j, (b j).1 ≤ (b' j).1 ∧ (b j).2 ≤ (b' j).2) : R x r k m b' := by
  obtain ⟨col, hv, hc⟩ := h
  exact ⟨col, hv, fun j => ⟨(hc j).1.trans (hle j).1, (hc j).2.trans (hle j).2⟩⟩

theorem R_zero (x : List Bool) (r k : ℕ) (b : St k) : R x r k 0 b :=
  ⟨fun _ => (fun _ => false, fun _ => false), fun i hi => absurd hi (Nat.not_lt_zero _),
    fun j => by simp [cA, cF]⟩

theorem T_zero (x : List Bool) (r k i s : ℕ) (b : St k) :
    Tm x r k i s 0 b ↔ allowL x r k i s ∧ allowU x r k i s ∧ R x r k i b := by
  constructor
  · rintro ⟨hl, hu, c, b0, -, hR, hle⟩
    refine ⟨hl, hu, R_mono hR fun j => ?_⟩
    have := hle j
    simp only [pA, pF, Nat.not_lt_zero, if_false, Nat.add_zero] at this
    exact this
  · rintro ⟨hl, hu, hR⟩
    exact ⟨hl, hu, fun _ => false, b, fun j' hj' => absurd hj' (Nat.not_lt_zero _), hR,
      fun j' => by simp [pA, pF]⟩

theorem T_ext {x : List Bool} {r k i s : ℕ} (jj : Fin k) {b b' : St k} (v : Bool)
    (hT : Tm x r k i s jj.val b') (hv : perm x r k i jj.val v)
    (hne : ∀ j' : Fin k, j' ≠ jj → (b' j').1 ≤ (b j').1 ∧ (b' j').2 ≤ (b j').2)
    (hA : (b' jj).1 + qA s v jj.val ≤ (b jj).1)
    (hF : (b' jj).2 + qF s v jj.val ≤ (b jj).2) :
    Tm x r k i s (jj.val + 1) b := by
  obtain ⟨hl, hu, c, b0, hp, hR, hle⟩ := hT
  refine ⟨hl, hu, fun j' => if j' = jj then v else c j', b0, ?_, hR, ?_⟩
  · intro j' hj'
    by_cases h : j' = jj
    · subst h; simpa using hv
    · have : j'.val < jj.val := by
        have : j'.val ≠ jj.val := fun e => h (Fin.ext e)
        omega
      simpa [h] using hp j' this
  · intro j'
    have h1 := hle j'
    by_cases h : j' = jj
    · subst h
      simp only [pA, pF, if_pos rfl, lt_irrefl, if_false, Nat.lt_succ_self, if_true,
        Nat.add_zero] at h1 ⊢
      omega
    · have hne' := hne j' h
      have hval : j'.val ≠ jj.val := fun e => h (Fin.ext e)
      have e1 : pA s (fun j'' => if j'' = jj then v else c j'') (jj.val + 1) j' = pA s c jj.val j' := by
        simp only [pA, if_neg h]
        rcases Nat.lt_or_gt_of_ne hval with h' | h'
        · simp [h', show j'.val < jj.val + 1 by omega]
        · simp [show ¬ j'.val < jj.val by omega, show ¬ j'.val < jj.val + 1 by omega]
      have e2 : pF s (fun j'' => if j'' = jj then v else c j'') (jj.val + 1) j' = pF s c jj.val j' := by
        simp only [pF, if_neg h]
        rcases Nat.lt_or_gt_of_ne hval with h' | h'
        · simp [h', show j'.val < jj.val + 1 by omega]
        · simp [show ¬ j'.val < jj.val by omega, show ¬ j'.val < jj.val + 1 by omega]
      rw [e1, e2]
      omega

theorem T_restrict {x : List Bool} {r k i s : ℕ} (jj : Fin k) {b : St k}
    (hT : Tm x r k i s (jj.val + 1) b) :
    ∃ v, perm x r k i jj.val v ∧ qA s v jj.val ≤ (b jj).1 ∧ qF s v jj.val ≤ (b jj).2 ∧
      ∀ b'' : St k, (∀ j' : Fin k, j' ≠ jj → b'' j' = b j') →
        (b jj).1 ≤ (b'' jj).1 + qA s v jj.val → (b jj).2 ≤ (b'' jj).2 + qF s v jj.val →
        Tm x r k i s jj.val b'' := by
  obtain ⟨hl, hu, c, b0, hp, hR, hle⟩ := hT
  have hjj := hle jj
  have ea : pA s c (jj.val + 1) jj = qA s (c jj) jj.val := by simp [pA]
  have ef : pF s c (jj.val + 1) jj = qF s (c jj) jj.val := by simp [pF]
  rw [ea, ef] at hjj
  refine ⟨c jj, hp jj (Nat.lt_succ_self _), by omega, by omega, fun b'' hb1 hb2 hb3 => ?_⟩
  refine ⟨hl, hu, c, b0, fun j' hj' => hp j' (by omega), hR, fun j' => ?_⟩
  by_cases h : j' = jj
  · subst h
    simp only [pA, pF, lt_irrefl, if_false, Nat.add_zero]
    omega
  · have hval : j'.val ≠ jj.val := fun e => h (Fin.ext e)
    have e1 : pA s c (jj.val + 1) j' = pA s c jj.val j' := by
      simp only [pA]
      rcases Nat.lt_or_gt_of_ne hval with h' | h'
      · simp [h', show j'.val < jj.val + 1 by omega]
      · simp [show ¬ j'.val < jj.val by omega, show ¬ j'.val < jj.val + 1 by omega]
    have e2 : pF s c (jj.val + 1) j' = pF s c jj.val j' := by
      simp only [pF]
      rcases Nat.lt_or_gt_of_ne hval with h' | h'
      · simp [h', show j'.val < jj.val + 1 by omega]
      · simp [show ¬ j'.val < jj.val by omega, show ¬ j'.val < jj.val + 1 by omega]
    rw [hb1 j' h, ← e1, ← e2]
    exact hle j'

theorem T_step (x : List Bool) (r k i s : ℕ) (jj : Fin k) (b : St k) :
    Tm x r k i s (jj.val + 1) b ↔
      (Zb x r jj.val i = true ∧ (if s ≤ jj.val then 1 ≤ (b jj).2 ∧ Tm x r k i s jj.val (dF jj.val b)
          else Tm x r k i s jj.val b)) ∨
      (Ob x r k jj.val i = true ∧ (if s ≤ jj.val then Tm x r k i s jj.val b
          else 1 ≤ (b jj).1 ∧ Tm x r k i s jj.val (dA jj.val b))) := by
  have dFo : ∀ j' : Fin k, j' ≠ jj → dF jj.val b j' = b j' := by
    intro j' h; simp [dF, show j'.val ≠ jj.val from fun e => h (Fin.ext e)]
  have dAo : ∀ j' : Fin k, j' ≠ jj → dA jj.val b j' = b j' := by
    intro j' h; simp [dA, show j'.val ≠ jj.val from fun e => h (Fin.ext e)]
  have dFj : dF jj.val b jj = ((b jj).1, (b jj).2 - 1) := by simp [dF]
  have dAj : dA jj.val b jj = ((b jj).1 - 1, (b jj).2) := by simp [dA]
  constructor
  · intro hT
    obtain ⟨v, hv, hqa, hqf, hfin⟩ := T_restrict jj hT
    cases v with
    | false =>
      left
      refine ⟨hv.1 rfl, ?_⟩
      have h0 : qA s false jj.val = 0 := by simp [qA]
      split_ifs with hs
      · have h1 : qF s false jj.val = 1 := by simp [qF, hs]
        refine ⟨by omega, hfin _ dFo ?_ ?_⟩
        · simp only [dFj, h0] <;> omega
        · simp only [dFj, h1] <;> omega
      · have h1 : qF s false jj.val = 0 := by simp [qF, hs]
        exact hfin _ (fun _ _ => rfl) (by omega) (by omega)
    | true =>
      right
      refine ⟨hv.2 rfl, ?_⟩
      have h0 : qF s true jj.val = 0 := by simp [qF]
      split_ifs with hs
      · have h1 : qA s true jj.val = 0 := by simp [qA, hs]
        exact hfin _ (fun _ _ => rfl) (by omega) (by omega)
      · have h1 : qA s true jj.val = 1 := by simp [qA, hs]
        refine ⟨by omega, hfin _ dAo ?_ ?_⟩
        · simp only [dAj, h1] <;> omega
        · simp only [dAj, h0] <;> omega
  · rintro (⟨hz, h⟩ | ⟨ho, h⟩)
    · have hv : perm x r k i jj.val false := ⟨fun _ => hz, fun h => absurd h (by simp)⟩
      have h0 : qA s false jj.val = 0 := by simp [qA]
      split_ifs at h with hs
      · have h1 : qF s false jj.val = 1 := by simp [qF, hs]
        refine T_ext jj false h.2 hv (fun j' hj' => by rw [dFo j' hj']; exact ⟨le_rfl, le_rfl⟩) ?_ ?_
        · simp only [dFj, h0] <;> omega
        · simp only [dFj, h1] <;> omega
      · have h1 : qF s false jj.val = 0 := by simp [qF, hs]
        refine T_ext jj false h hv (fun j' _ => ⟨le_rfl, le_rfl⟩) ?_ ?_
        · simp only [h0] <;> omega
        · simp only [h1] <;> omega
    · have hv : perm x r k i jj.val true := ⟨fun h => absurd h (by simp), fun _ => ho⟩
      have h0 : qF s true jj.val = 0 := by simp [qF]
      split_ifs at h with hs
      · have h1 : qA s true jj.val = 0 := by simp [qA, hs]
        refine T_ext jj true h hv (fun j' _ => ⟨le_rfl, le_rfl⟩) ?_ ?_
        · simp only [h1] <;> omega
        · simp only [h0] <;> omega
      · have h1 : qA s true jj.val = 1 := by simp [qA, hs]
        refine T_ext jj true h.2 hv (fun j' hj' => by rw [dAo j' hj']; exact ⟨le_rfl, le_rfl⟩) ?_ ?_
        · simp only [dAj, h1] <;> omega
        · simp only [dAj, h0] <;> omega

theorem cA_succ {k : ℕ} (col : ℕ → Col k) (m : ℕ) (j : Fin k) :
    cA col (m + 1) j = cA col m j + (if (col m).1 j = true ∧ (col m).2 j = false then 1 else 0) := by
  simp only [cA, Finset.sum_range_succ]

theorem cF_succ {k : ℕ} (col : ℕ → Col k) (m : ℕ) (j : Fin k) :
    cF col (m + 1) j = cF col m j + (if (col m).1 j = false ∧ (col m).2 j = true then 1 else 0) := by
  simp only [cF, Finset.sum_range_succ]

theorem R_step (x : List Bool) (r k i : ℕ) (b : St k) :
    R x r k (i + 1) b ↔ ∃ s ≤ k, Tm x r k i s k b := by
  constructor
  · rintro ⟨col, hv, hc⟩
    obtain ⟨hmono, hL, hU, hperm⟩ := hv i (Nat.lt_succ_self i)
    have hex : ∃ s, s = k ∨ ∃ h : s < k, (col i).2 ⟨s, h⟩ = true := ⟨k, Or.inl rfl⟩
    have hsk : Nat.find hex ≤ k := Nat.find_min' hex (Or.inl rfl)
    have hy : ∀ j : Fin k, (col i).2 j = true ↔ Nat.find hex ≤ j.val := by
      intro j; constructor
      · intro h; exact Nat.find_min' hex (Or.inr ⟨j.isLt, h⟩)
      · intro h
        rcases Nat.find_spec hex with h1 | ⟨h1, h2⟩
        · exact absurd j.isLt (by omega)
        · exact hmono ⟨_, h1⟩ j (Fin.le_def.2 h) h2
    refine ⟨Nat.find hex, hsk, ?_, ?_, (col i).1, fun j => (cA col i j, cF col i j),
      fun j' _ => hperm j', ⟨col, fun i' hi' => hv i' (by omega), fun j => ⟨le_rfl, le_rfl⟩⟩,
      fun j' => ?_⟩
    · by_cases hl : Lb x r k i = true
      · exact Or.inr hl
      · left
        have hall := hL (by simpa using hl)
        by_contra hs0
        have hk : 0 < k := by omega
        have : Nat.find hex ≤ 0 := (hy ⟨0, hk⟩).1 (hall _)
        omega
    · by_cases hu : Ub x r k i = true
      · exact Or.inr hu
      · left
        have hall := hU (by simpa using hu)
        rcases Nat.find_spec hex with h1 | ⟨h1, h2⟩
        · exact h1
        · rw [hall] at h2; exact absurd h2 (by simp)
    · have h1 := hc j'
      rw [cA_succ, cF_succ] at h1
      have hyj := hy j'
      simp only [pA, pF, qA, qF, if_pos j'.isLt]
      by_cases hs : Nat.find hex ≤ j'.val
      · have hy1 : (col i).2 j' = true := hyj.2 hs
        cases h2 : (col i).1 j' <;> simp [hy1, h2, hs] at h1 ⊢ <;> omega
      · have hy1 : (col i).2 j' = false := by
          cases h3 : (col i).2 j'
          · rfl
          · exact absurd (hyj.1 h3) hs
        cases h2 : (col i).1 j' <;> simp [hy1, h2, hs] at h1 ⊢ <;> omega
  · rintro ⟨s, hsk, hl, hu, c, b0, hp, ⟨col, hv, hc⟩, hle⟩
    set col' : ℕ → Col k := fun i' => if i' = i then (c, fun j => decide (s ≤ j.val)) else col i'
      with hcol'
    have hci : col' i = (c, fun j => decide (s ≤ j.val)) := by simp [hcol']
    have hco : ∀ i', i' ≠ i → col' i' = col i' := by intro i' h; simp [hcol', h]
    refine ⟨col', fun i' hi' => ?_, fun j => ?_⟩
    · by_cases h : i' = i
      · rw [h, hci]
        refine ⟨?_, ?_, ?_, fun j => hp j j.isLt⟩
        · intro j j' hjj' h
          simp only [decide_eq_true_eq] at h ⊢
          exact le_trans h (Fin.le_def.1 hjj')
        · intro hL j
          rcases hl with h0 | h0
          · simp [h0]
          · rw [h0] at hL; exact absurd hL (by simp)
        · intro hU j
          rcases hu with h0 | h0
          · simp [h0, j.isLt]
          · rw [h0] at hU; exact absurd hU (by simp)
      · rw [hco i' h]; exact hv i' (by omega)
    · have e1 : cA col' i j = cA col i j := by
        unfold cA; apply Finset.sum_congr rfl; intro i' hi'
        rw [hco i' (Finset.mem_range.1 hi').ne]
      have e2 : cF col' i j = cF col i j := by
        unfold cF; apply Finset.sum_congr rfl; intro i' hi'
        rw [hco i' (Finset.mem_range.1 hi').ne]
      rw [cA_succ, cF_succ, e1, e2, hci]
      have h1 := hc j
      have h2 := hle j
      simp only [pA, pF, qA, qF, if_pos j.isLt] at h2
      by_cases hs : s ≤ j.val <;> cases hcj : c j <;> simp [hs, hcj] at h2 ⊢ <;> omega

/-! ## The layer layout -/

def lay (k i s u : ℕ) : ℕ := (i * (k + 1) + s) * (3 * k + 3) + u
def dI (k t : ℕ) : ℕ := t / (3 * k + 3) / (k + 1)
def dS (k t : ℕ) : ℕ := t / (3 * k + 3) % (k + 1)
def dU (k t : ℕ) : ℕ := t % (3 * k + 3)

theorem dec_lay {k i s u : ℕ} (hs : s ≤ k) (hu : u < 3 * k + 3) :
    dI k (lay k i s u) = i ∧ dS k (lay k i s u) = s ∧ dU k (lay k i s u) = u := by
  have h1 : lay k i s u / (3 * k + 3) = i * (k + 1) + s := by
    unfold lay
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, Nat.zero_add]
  have h2 : lay k i s u % (3 * k + 3) = u := by
    unfold lay; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  refine ⟨?_, ?_, h2⟩
  · unfold dI
    rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  · unfold dS; rw [h1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem lay_dec (k t : ℕ) : lay k (dI k t) (dS k t) (dU k t) = t := by
  unfold lay dI dS dU
  rw [Nat.div_add_mod' (t / (3 * k + 3)) (k + 1), Nat.div_add_mod' t (3 * k + 3)]

theorem grp_lt {P g g' u u' : ℕ} (hg : g < g') (hu : u < P) : g * P + u < g' * P + u' := by
  have : (g + 1) * P ≤ g' * P := Nat.mul_le_mul_right _ hg
  rw [Nat.succ_mul] at this; omega

theorem dec_bounds {r k t : ℕ} (ht : t < r * (k + 1) * (3 * k + 3)) :
    dI k t < r ∧ dS k t ≤ k ∧ dU k t < 3 * k + 3 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dI
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.div_lt_iff_lt_mul (by omega)]
    exact ht
  · unfold dS; have := Nat.mod_lt (t / (3 * k + 3)) (show 0 < k + 1 by omega); omega
  · unfold dU; exact Nat.mod_lt _ (by omega)

def specD (r k i s u : ℕ) (b : St k) : GateOp × Src (St k) × Src (St k) :=
  if u = 0 then
    (GateOp.and, if s = 0 then Src.inp (tW r k) else Src.inp (k * r + k * r + i),
      if i = 0 then Src.inp (tW r k) else Src.node (lay k (i - 1) k (3 * k + 2)) b)
  else if u = 1 then
    (GateOp.and, if s = k then Src.inp (tW r k) else Src.inp (k * r + k * r + r + i),
      Src.node (lay k i s 0) b)
  else if u = 3 * k + 2 then
    (GateOp.or, if s = 0 then Src.inp (fW r k) else Src.node (lay k i (s - 1) (3 * k + 2)) b,
      Src.node (lay k i s (3 * k + 1)) b)
  else if (u - 2) % 3 = 0 then
    (GateOp.and, Src.inp ((u - 2) / 3 * r + i),
      if s ≤ (u - 2) / 3 then
        (if (bget b ((u - 2) / 3)).2 = 0 then Src.inp (fW r k)
          else Src.node (lay k i s (u - 1)) (dF ((u - 2) / 3) b))
      else Src.node (lay k i s (u - 1)) b)
  else if (u - 2) % 3 = 1 then
    (GateOp.and, Src.inp (k * r + (u - 2) / 3 * r + i),
      if s ≤ (u - 2) / 3 then Src.node (lay k i s (u - 2)) b
      else (if (bget b ((u - 2) / 3)).1 = 0 then Src.inp (fW r k)
          else Src.node (lay k i s (u - 2)) (dA ((u - 2) / 3) b)))
  else (GateOp.or, Src.node (lay k i s (u - 2)) b, Src.node (lay k i s (u - 1)) b)

def MD (x : List Bool) (r k i s u : ℕ) (b : St k) : Prop :=
  if u = 0 then allowL x r k i s ∧ R x r k i b
  else if u = 1 then Tm x r k i s 0 b
  else if u = 3 * k + 2 then ∃ s' ≤ s, Tm x r k i s' k b
  else if (u - 2) % 3 = 0 then Zb x r ((u - 2) / 3) i = true ∧
      (if s ≤ (u - 2) / 3 then
        1 ≤ (bget b ((u - 2) / 3)).2 ∧ Tm x r k i s ((u - 2) / 3) (dF ((u - 2) / 3) b)
        else Tm x r k i s ((u - 2) / 3) b)
  else if (u - 2) % 3 = 1 then Ob x r k ((u - 2) / 3) i = true ∧
      (if s ≤ (u - 2) / 3 then Tm x r k i s ((u - 2) / 3) b
        else 1 ≤ (bget b ((u - 2) / 3)).1 ∧ Tm x r k i s ((u - 2) / 3) (dA ((u - 2) / 3) b))
  else Tm x r k i s ((u - 2) / 3 + 1) b

def Mf (x : List Bool) (r k : ℕ) (t : ℕ) (b : St k) : Bool :=
  decide (MD x r k (dI k t) (dS k t) (dU k t) b)

def specF (r k : ℕ) (t : ℕ) (b : St k) : GateOp × Src (St k) × Src (St k) :=
  specD r k (dI k t) (dS k t) (dU k t) b

theorem Mf_lay {x : List Bool} {r k i s u : ℕ} {b : St k} (hs : s ≤ k) (hu : u < 3 * k + 3) :
    Mf x r k (lay k i s u) b = decide (MD x r k i s u b) := by
  obtain ⟨h1, h2, h3⟩ := dec_lay (i := i) hs hu
  simp only [Mf, h1, h2, h3]

theorem MD_zero {x : List Bool} {r k i s : ℕ} {b : St k} :
    MD x r k i s 0 b ↔ allowL x r k i s ∧ R x r k i b := by
  simp [MD]

theorem MD_T {x : List Bool} {r k i s j : ℕ} {b : St k} (hj : j ≤ k) :
    MD x r k i s (3 * j + 1) b ↔ Tm x r k i s j b := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [MD]
  · unfold MD
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    rw [show (3 * j + 1 - 2) / 3 + 1 = j by omega]

theorem MD_acc {x : List Bool} {r k i s : ℕ} {b : St k} :
    MD x r k i s (3 * k + 2) b ↔ ∃ s' ≤ s, Tm x r k i s' k b := by
  unfold MD
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem MD_Z {x : List Bool} {r k i s j : ℕ} {b : St k} (hj : j < k) :
    MD x r k i s (3 * j + 2) b ↔ (Zb x r j i = true ∧
      (if s ≤ j then 1 ≤ (bget b j).2 ∧ Tm x r k i s j (dF j b) else Tm x r k i s j b)) := by
  unfold MD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show (3 * j + 2 - 2) / 3 = j by omega]

theorem MD_O {x : List Bool} {r k i s j : ℕ} {b : St k} (hj : j < k) :
    MD x r k i s (3 * j + 3) b ↔ (Ob x r k j i = true ∧
      (if s ≤ j then Tm x r k i s j b else 1 ≤ (bget b j).1 ∧ Tm x r k i s j (dA j b))) := by
  unfold MD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  rw [show (3 * j + 3 - 2) / 3 = j by omega]

theorem MD_row {x : List Bool} {r k i s j : ℕ} {b : St k} (hj : j < k) :
    MD x r k i s (3 * j + 4) b ↔ Tm x r k i s (j + 1) b := by
  unfold MD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  rw [show (3 * j + 4 - 2) / 3 = j by omega]

theorem specD_zero (r k i s : ℕ) (b : St k) : specD r k i s 0 b =
    (GateOp.and, if s = 0 then Src.inp (tW r k) else Src.inp (k * r + k * r + i),
      if i = 0 then Src.inp (tW r k) else Src.node (lay k (i - 1) k (3 * k + 2)) b) := by
  simp [specD]

theorem specD_one (r k i s : ℕ) (b : St k) : specD r k i s 1 b =
    (GateOp.and, if s = k then Src.inp (tW r k) else Src.inp (k * r + k * r + r + i),
      Src.node (lay k i s 0) b) := by
  simp [specD]

theorem specD_acc (r k i s : ℕ) (b : St k) : specD r k i s (3 * k + 2) b =
    (GateOp.or, if s = 0 then Src.inp (fW r k) else Src.node (lay k i (s - 1) (3 * k + 2)) b,
      Src.node (lay k i s (3 * k + 1)) b) := by
  unfold specD
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem specD_Z (r k i s j : ℕ) (b : St k) (hj : j < k) : specD r k i s (3 * j + 2) b =
    (GateOp.and, Src.inp (j * r + i),
      if s ≤ j then
        (if (bget b j).2 = 0 then Src.inp (fW r k) else Src.node (lay k i s (3 * j + 1)) (dF j b))
      else Src.node (lay k i s (3 * j + 1)) b) := by
  unfold specD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show (3 * j + 2 - 2) / 3 = j by omega, show 3 * j + 2 - 1 = 3 * j + 1 by omega]

theorem specD_O (r k i s j : ℕ) (b : St k) (hj : j < k) : specD r k i s (3 * j + 3) b =
    (GateOp.and, Src.inp (k * r + j * r + i),
      if s ≤ j then Src.node (lay k i s (3 * j + 1)) b
      else (if (bget b j).1 = 0 then Src.inp (fW r k)
          else Src.node (lay k i s (3 * j + 1)) (dA j b))) := by
  unfold specD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  rw [show (3 * j + 3 - 2) / 3 = j by omega, show 3 * j + 3 - 2 = 3 * j + 1 by omega]

theorem specD_row (r k i s j : ℕ) (b : St k) (hj : j < k) : specD r k i s (3 * j + 4) b =
    (GateOp.or, Src.node (lay k i s (3 * j + 2)) b, Src.node (lay k i s (3 * j + 3)) b) := by
  unfold specD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  rw [show 3 * j + 4 - 2 = 3 * j + 2 by omega, show 3 * j + 4 - 1 = 3 * j + 3 by omega]

theorem u_cases {k u : ℕ} (hu : u < 3 * k + 3) :
    u = 0 ∨ u = 1 ∨ u = 3 * k + 2 ∨
      ∃ j < k, u = 3 * j + 2 ∨ u = 3 * j + 3 ∨ u = 3 * j + 4 := by
  by_cases h0 : u = 0
  · exact Or.inl h0
  by_cases h1 : u = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : u = 3 * k + 2
  · exact Or.inr (Or.inr (Or.inl h2))
  refine Or.inr (Or.inr (Or.inr ⟨(u - 2) / 3, by omega, by omega⟩))

theorem bget_eq {k : ℕ} (b : St k) {j : ℕ} (hj : j < k) : bget b j = b ⟨j, hj⟩ := by
  simp [bget, hj]

theorem MD_one {x : List Bool} {r k i s : ℕ} {b : St k} :
    MD x r k i s 1 b ↔ Tm x r k i s 0 b := by
  simp [MD]

theorem consist (x : List Bool) (r k : ℕ) (hf : x.getD (fW r k) false = false)
    (ht : x.getD (tW r k) false = true) {i s u : ℕ} (hs : s ≤ k) (hu : u < 3 * k + 3)
    (b : St k) (op : GateOp) (s1 s2 : Src (St k)) (hsp : specD r k i s u b = (op, s1, s2)) :
    decide (MD x r k i s u b) = op.eval [srcVal x (Mf x r k) s1, srcVal x (Mf x r k) s2] := by
  have hand : ∀ a c : Bool, GateOp.and.eval [a, c] = (a && c) := by intro a c; simp [GateOp.eval]
  have hor : ∀ a c : Bool, GateOp.or.eval [a, c] = (a || c) := by intro a c; simp [GateOp.eval]
  have hsi : ∀ w, srcVal x (Mf x r k) (Src.inp w) = x.getD w false := fun _ => rfl
  have hsn : ∀ t b', srcVal x (Mf x r k) (Src.node t b') = Mf x r k t b' := fun _ _ => rfl
  rcases u_cases hu with rfl | rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩
  · rw [specD_zero] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    rw [hand, Bool.eq_iff_iff, decide_eq_true_iff, MD_zero, Bool.and_eq_true]
    apply and_congr
    · unfold allowL
      split_ifs with h
      · rw [hsi, ht]; simp [h]
      · rw [hsi]; unfold Lb; simp [h]
    · split_ifs with h
      · subst h; rw [hsi, ht]; simp [R_zero]
      · rw [hsn, Mf_lay le_rfl (by omega), decide_eq_true_iff, MD_acc]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [R_step, Nat.add_sub_cancel]
  · rw [specD_one] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    rw [hand, Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, hsn, Mf_lay hs (by omega),
      decide_eq_true_iff, MD_zero, MD_one, T_zero]
    unfold allowU
    split_ifs with h
    · rw [hsi, ht]; simp [h]
    · rw [hsi]; unfold Ub; simp only [h, false_or]; tauto
  · rw [specD_acc] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    rw [hor, Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, MD_acc, hsn,
      Mf_lay hs (by omega), decide_eq_true_iff, MD_T le_rfl]
    split_ifs with h
    · subst h
      rw [hsi, hf]
      simp only [Bool.false_eq_true, false_or]
      constructor
      · rintro ⟨s', hs', h'⟩; rw [show s' = 0 by omega] at h'; exact h'
      · intro h'; exact ⟨0, le_rfl, h'⟩
    · rw [hsn, Mf_lay (by omega) (by omega), decide_eq_true_iff, MD_acc]
      constructor
      · rintro ⟨s', hs', h'⟩
        rcases Nat.lt_or_ge s' s with h1 | h1
        · exact Or.inl ⟨s', by omega, h'⟩
        · rw [show s' = s by omega] at h'; exact Or.inr h'
      · rintro (⟨s', hs', h'⟩ | h')
        · exact ⟨s', by omega, h'⟩
        · exact ⟨s, le_rfl, h'⟩
  · rw [specD_Z r k i s j b hj] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    rw [hand, Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, MD_Z hj, bget_eq b hj, hsi]
    apply and_congr Iff.rfl
    split_ifs with h1 h2
    · rw [hsi, hf]; simp [h2]
    · rw [hsn, Mf_lay hs (by omega), decide_eq_true_iff, MD_T hj.le]
      constructor
      · rintro ⟨-, h'⟩; exact h'
      · intro h'; exact ⟨by omega, h'⟩
    · rw [hsn, Mf_lay hs (by omega), decide_eq_true_iff, MD_T hj.le]
  · rw [specD_O r k i s j b hj] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    rw [hand, Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, MD_O hj, bget_eq b hj, hsi]
    apply and_congr Iff.rfl
    split_ifs with h1 h2
    · rw [hsn, Mf_lay hs (by omega), decide_eq_true_iff, MD_T hj.le]
    · rw [hsi, hf]; simp [h2]
    · rw [hsn, Mf_lay hs (by omega), decide_eq_true_iff, MD_T hj.le]
      constructor
      · rintro ⟨-, h'⟩; exact h'
      · intro h'; exact ⟨by omega, h'⟩
  · rw [specD_row r k i s j b hj] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    rw [hor, Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, MD_row hj, hsn, hsn,
      Mf_lay hs (by omega), Mf_lay hs (by omega), decide_eq_true_iff, decide_eq_true_iff,
      MD_Z hj, MD_O hj, bget_eq b hj]
    exact T_step x r k i s ⟨j, hj⟩ b

/-! ## The circuit -/

def Sset {k : ℕ} (A F : Fin k → ℕ) : Finset (St k) :=
  Fintype.piFinset (fun j => Finset.range (A j + 1) ×ˢ Finset.range (F j + 1))

theorem mem_Sset {k : ℕ} {A F : Fin k → ℕ} {b : St k} :
    b ∈ Sset A F ↔ ∀ j, (b j).1 ≤ A j ∧ (b j).2 ≤ F j := by
  simp only [Sset, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]

theorem card_Sset {k : ℕ} (A F : Fin k → ℕ) :
    (Sset A F).card = Finset.univ.prod (fun j => (A j + 1) * (F j + 1)) := by
  simp [Sset, Fintype.card_piFinset, Finset.card_product]

theorem dF_mem {k : ℕ} {A F : Fin k → ℕ} {b : St k} (hb : b ∈ Sset A F) (j : ℕ) :
    dF j b ∈ Sset A F := by
  rw [mem_Sset] at hb ⊢
  intro j'
  have := hb j'
  unfold dF
  split_ifs <;> (try simp only) <;> omega

theorem dA_mem {k : ℕ} {A F : Fin k → ℕ} {b : St k} (hb : b ∈ Sset A F) (j : ℕ) :
    dA j b ∈ Sset A F := by
  rw [mem_Sset] at hb ⊢
  intro j'
  have := hb j'
  unfold dA
  split_ifs <;> (try simp only) <;> omega

def NN (r k : ℕ) : ℕ := k * r + k * r + r + r + 2

theorem spec_okD {r k : ℕ} {A F : Fin k → ℕ} {i s u : ℕ} {b : St k} (hi : i < r) (hs : s ≤ k)
    (hu : u < 3 * k + 3) (hb : b ∈ Sset A F) (op : GateOp) (s1 s2 : Src (St k))
    (hsp : specD r k i s u b = (op, s1, s2)) :
    (op = GateOp.and ∨ op = GateOp.or) ∧
    SrcOK (Sset A F) (NN r k) (lay k i s u) s1 ∧ SrcOK (Sset A F) (NN r k) (lay k i s u) s2 := by
  have hkr : ∀ j, j < k → j * r + i < k * r := by
    intro j hj
    have : (j + 1) * r ≤ k * r := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this; omega
  have hlay : ∀ {g g' u u' : ℕ}, g < g' → u < 3 * k + 3 →
      (g * (3 * k + 3) + u < g' * (3 * k + 3) + u') := fun hg hu => grp_lt hg hu
  have hin : ∀ {t w : ℕ}, w < NN r k → SrcOK (Sset A F) (NN r k) t (Src.inp w) := fun h => h
  have hnd : ∀ {t t' : ℕ} {b' : St k}, t' < t → b' ∈ Sset A F →
      SrcOK (Sset A F) (NN r k) t (Src.node t' b') := fun h1 h2 => ⟨h1, h2⟩
  rcases u_cases hu with rfl | rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩
  · rw [specD_zero] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    refine ⟨Or.inl rfl, ?_, ?_⟩
    · split_ifs
      · exact hin (by unfold NN tW; omega)
      · exact hin (by unfold NN; omega)
    · split_ifs with h
      · exact hin (by unfold NN tW; omega)
      · refine hnd ?_ hb
        unfold lay
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        apply hlay _ (by omega)
        rw [Nat.add_sub_cancel, Nat.succ_mul]
        omega
  · rw [specD_one] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    refine ⟨Or.inl rfl, ?_, hnd (by unfold lay; omega) hb⟩
    split_ifs
    · exact hin (by unfold NN tW; omega)
    · exact hin (by unfold NN; omega)
  · rw [specD_acc] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    refine ⟨Or.inr rfl, ?_, hnd (by unfold lay; omega) hb⟩
    split_ifs with h
    · exact hin (by unfold NN fW; omega)
    · exact hnd (by unfold lay; exact hlay (by omega) (by omega)) hb
  · rw [specD_Z r k i s j b hj] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    refine ⟨Or.inl rfl, hin (by have := hkr j hj; unfold NN; omega), ?_⟩
    split_ifs
    · exact hin (by unfold NN fW; omega)
    · exact hnd (by unfold lay; omega) (dF_mem hb _)
    · exact hnd (by unfold lay; omega) hb
  · rw [specD_O r k i s j b hj] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    refine ⟨Or.inl rfl, hin (by have := hkr j hj; unfold NN; omega), ?_⟩
    split_ifs
    · exact hnd (by unfold lay; omega) hb
    · exact hin (by unfold NN fW; omega)
    · exact hnd (by unfold lay; omega) (dA_mem hb _)
  · rw [specD_row r k i s j b hj] at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl, rfl⟩ := hsp
    exact ⟨Or.inr rfl, hnd (by unfold lay; omega) hb, hnd (by unfold lay; omega) hb⟩

theorem spec_ok (r k : ℕ) (A F : Fin k → ℕ) :
    SpecOK (Sset A F) (NN r k) (r * (k + 1) * (3 * k + 3)) (specF r k) := by
  have key : ∀ t < r * (k + 1) * (3 * k + 3), ∀ b ∈ Sset A F,
      ((specF r k t b).1 = GateOp.and ∨ (specF r k t b).1 = GateOp.or) ∧
      SrcOK (Sset A F) (NN r k) t (specF r k t b).2.1 ∧
      SrcOK (Sset A F) (NN r k) t (specF r k t b).2.2 := by
    intro t ht b hb
    obtain ⟨h1, h2, h3⟩ := dec_bounds ht
    have := spec_okD (A := A) (F := F) h1 h2 h3 hb (specF r k t b).1 (specF r k t b).2.1
      (specF r k t b).2.2 rfl
    rwa [lay_dec] at this
  exact ⟨fun t ht b hb => (key t ht b hb).1, fun t ht b hb => (key t ht b hb).2.1,
    fun t ht b hb => (key t ht b hb).2.2⟩

def bmax {k : ℕ} (A F : Fin k → ℕ) : St k := fun j => (A j, F j)

def outW (r k : ℕ) (A F : Fin k → ℕ) : ℕ :=
  if r = 0 then tW r k else NN r k + lay k (r - 1) k (3 * k + 2) * (Sset A F).card + enc (Sset A F) (bmax A F)

def theCirc (r k : ℕ) (A F : Fin k → ℕ) : Circuit :=
  layered (Sset A F) (NN r k) (r * (k + 1) * (3 * k + 3)) (specF r k) (outW r k A F)

theorem bmax_mem {k : ℕ} (A F : Fin k → ℕ) : bmax A F ∈ Sset A F := by
  rw [mem_Sset]; intro j; exact ⟨le_rfl, le_rfl⟩

theorem lay_last (r k : ℕ) (hr : r ≠ 0) :
    lay k (r - 1) k (3 * k + 2) + 1 = r * (k + 1) * (3 * k + 3) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold lay
  rw [Nat.add_sub_cancel]
  ring

theorem circ_output (r k : ℕ) (A F : Fin k → ℕ) :
    (theCirc r k A F).output < NN r k + (theCirc r k A F).size := by
  unfold theCirc
  rw [layered_size]
  show outW r k A F < _
  unfold outW
  split_ifs with hr
  · simp only [tW, NN]; omega
  · have h1 := lay_last r k hr
    have h2 := enc_lt (Sset A F) (bmax_mem A F)
    have h3 : (lay k (r - 1) k (3 * k + 2) + 1) * (Sset A F).card ≤
        r * (k + 1) * (3 * k + 3) * (Sset A F).card := by rw [h1]
    rw [Nat.succ_mul] at h3
    omega

theorem circ_eval (r k : ℕ) (A F : Fin k → ℕ) (x : List Bool) (hx : x.length = NN r k)
    (hf : x.getD (fW r k) false = false) (ht : x.getD (tW r k) false = true) :
    (theCirc r k A F).eval x = true ↔ R x r k r (bmax A F) := by
  unfold Circuit.eval
  by_cases hr : r = 0
  · subst hr
    have hg : (theCirc 0 k A F).gates = [] := by
      rw [← List.length_eq_zero_iff]; unfold theCirc; rw [layered_len]; simp
    have ho : (theCirc 0 k A F).output = tW 0 k := by simp [theCirc, layered, outW]
    rw [wires_eq, hg, ho, List.foldl_nil, ht]
    simp only [true_iff]
    exact R_zero x 0 k _
  · have ho : (theCirc r k A F).output =
        NN r k + lay k (r - 1) k (3 * k + 2) * (Sset A F).card + enc (Sset A F) (bmax A F) := by
      simp [theCirc, layered, outW, hr]
    rw [ho]
    unfold theCirc
    have hlt : lay k (r - 1) k (3 * k + 2) < r * (k + 1) * (3 * k + 3) := by
      have := lay_last r k hr; omega
    rw [layered_wire (Sset A F) (spec_ok r k A F) x hx (Mf x r k)
      (fun t ht' b _ => consist x r k hf ht (i := dI k t) (dec_bounds ht').2.1
        (dec_bounds ht').2.2 b (specF r k t b).1 (specF r k t b).2.1 (specF r k t b).2.2 rfl)
      hlt (bmax_mem A F)]
    rw [Mf_lay le_rfl (by omega), decide_eq_true_iff, MD_acc]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, R_step]


/-! ## Reading the inputs -/

theorem ofFn_getD {n : ℕ} (g : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (List.ofFn g).getD i false = g ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

theorem flat_length (r : ℕ) : ∀ (k : ℕ) (g : Fin k → Fin r → Bool),
    ((List.ofFn fun j => List.ofFn (g j)).flatten).length = k * r
  | 0, g => by simp
  | k + 1, g => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      flat_length r k (fun j => g j.succ), Nat.succ_mul]
    omega

theorem flat_getD (r : ℕ) : ∀ (k : ℕ) (g : Fin k → Fin r → Bool) (j i : ℕ) (hj : j < k)
    (hi : i < r),
    ((List.ofFn fun j => List.ofFn (g j)).flatten).getD (j * r + i) false = g ⟨j, hj⟩ ⟨i, hi⟩
  | 0, g, j, i, hj, hi => absurd hj (Nat.not_lt_zero _)
  | k + 1, g, j, i, hj, hi => by
    rw [List.ofFn_succ, List.flatten_cons]
    rcases j with _ | j
    · rw [List.getD_append _ _ _ _ (by simp; omega), Nat.zero_mul, Nat.zero_add, ofFn_getD _ hi]
      exact congrArg (fun z => g z ⟨i, hi⟩) (Fin.ext (by simp))
    · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn, Nat.succ_mul]; omega),
        List.length_ofFn, show (j + 1) * r + i - r = j * r + i by rw [Nat.succ_mul]; omega,
        flat_getD r k (fun j => g j.succ) j i (by omega) hi]
      rfl

def inList (r k : ℕ) (zf qf : Fin k → Fin r → Bool) (lf uf : Fin r → Bool) : List Bool :=
  (List.ofFn fun j => List.ofFn (zf j)).flatten ++ (List.ofFn fun j => List.ofFn (qf j)).flatten ++
    List.ofFn lf ++ List.ofFn uf ++ [false, true]

theorem input_facts (r k : ℕ) (zf qf : Fin k → Fin r → Bool) (lf uf : Fin r → Bool) :
    (inList r k zf qf lf uf).length = NN r k ∧
    (inList r k zf qf lf uf).getD (fW r k) false = false ∧
    (inList r k zf qf lf uf).getD (tW r k) false = true ∧
    (∀ (j : Fin k) (i : Fin r), Zb (inList r k zf qf lf uf) r j i = zf j i) ∧
    (∀ (j : Fin k) (i : Fin r), Ob (inList r k zf qf lf uf) r k j i = qf j i) ∧
    (∀ i : Fin r, Lb (inList r k zf qf lf uf) r k i = lf i) ∧
    (∀ i : Fin r, Ub (inList r k zf qf lf uf) r k i = uf i) := by
  have l1 := flat_length r k zf
  have l2 := flat_length r k qf
  have hkr : ∀ (j : Fin k) (i : Fin r), j.val * r + i.val < k * r := by
    intro j i
    have : (j.val + 1) * r ≤ k * r := Nat.mul_le_mul_right _ j.isLt
    rw [Nat.succ_mul] at this; have := i.isLt; omega
  unfold inList Zb Ob Lb Ub fW tW NN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil, l1, l2]
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega)]
    simp only [List.length_append, List.length_ofFn, l1, l2, Nat.sub_self]
    rfl
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega)]
    simp only [List.length_append, List.length_ofFn, l1, l2]
    rw [show k * r + k * r + r + r + 1 - (k * r + k * r + r + r) = 1 by omega]
    rfl
  · intro j i
    have := hkr j i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      flat_getD r k zf j i j.isLt i.isLt]
  · intro j i
    have := hkr j i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      l1, show k * r + j.val * r + i.val - k * r = j.val * r + i.val by omega,
      flat_getD r k qf j i j.isLt i.isLt]
  · intro i
    have := i.isLt
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega)]
    simp only [List.length_append, l1, l2]
    rw [show k * r + k * r + i.val - (k * r + k * r) = i.val by omega, ofFn_getD _ i.isLt]
  · intro i
    have := i.isLt
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn, l1, l2]; omega)]
    simp only [List.length_append, List.length_ofFn, l1, l2]
    rw [show k * r + k * r + r + i.val - (k * r + k * r + r) = i.val by omega, ofFn_getD _ i.isLt]

/-! ## From columns to sets -/

theorem bridge (r k : ℕ) (a f : Fin k → ℕ) (x : List Bool) (inst : DecidableEq (Fin r))
    (Z O : Fin k → Finset (Fin r)) (L U : Finset (Fin r))
    (hZ : ∀ (j : Fin k) (i : Fin r), Zb x r j i = true ↔ i ∈ Z j)
    (hO : ∀ (j : Fin k) (i : Fin r), Ob x r k j i = true ↔ i ∈ O j)
    (hL : ∀ i : Fin r, Lb x r k i = true ↔ i ∈ L)
    (hU : ∀ i : Fin r, Ub x r k i = true ↔ i ∈ U) :
    R x r k r (bmax (fun j => min r (a j)) (fun j => min r (f j))) ↔
    ∃ (C Y : Fin k → Finset (Fin r)), Monotone Y ∧ ∀ j,
      (Finset.univ \ C j) ⊆ Z j ∧ C j ⊆ O j ∧ (Finset.univ \ L) ⊆ Y j ∧ Y j ⊆ U ∧
        ((C j \ Y j).card ≤ a j ∧ (Y j \ C j).card ≤ f j) := by
  constructor
  · rintro ⟨col, hv, hc⟩
    refine ⟨fun j => Finset.univ.filter (fun i : Fin r => (col i).1 j = true),
      fun j => Finset.univ.filter (fun i : Fin r => (col i).2 j = true), ?_, fun j => ?_⟩
    · intro j j' hjj' i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (hv i i.isLt).1 j j' hjj' hi
    · have e1 : ((Finset.univ.filter (fun i : Fin r => (col i).1 j = true)) \
          (Finset.univ.filter (fun i : Fin r => (col i).2 j = true))).card = cA col r j := by
        have : (Finset.univ.filter (fun i : Fin r => (col i).1 j = true)) \
            (Finset.univ.filter (fun i : Fin r => (col i).2 j = true)) =
            Finset.univ.filter (fun i : Fin r => (col i.val).1 j = true ∧ (col i.val).2 j = false) := by
          ext i; simp
        rw [this, Finset.card_filter]
        exact Fin.sum_univ_eq_sum_range
          (fun i => if (col i).1 j = true ∧ (col i).2 j = false then 1 else 0) r
      have e2 : ((Finset.univ.filter (fun i : Fin r => (col i).2 j = true)) \
          (Finset.univ.filter (fun i : Fin r => (col i).1 j = true))).card = cF col r j := by
        have : (Finset.univ.filter (fun i : Fin r => (col i).2 j = true)) \
            (Finset.univ.filter (fun i : Fin r => (col i).1 j = true)) =
            Finset.univ.filter (fun i : Fin r => (col i.val).1 j = false ∧ (col i.val).2 j = true) := by
          ext i; simp [and_comm]
        rw [this, Finset.card_filter]
        exact Fin.sum_univ_eq_sum_range
          (fun i => if (col i).1 j = false ∧ (col i).2 j = true then 1 else 0) r
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hi
        exact (hZ j i).1 (((hv i i.isLt).2.2.2 j).1 (by simpa using hi))
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact (hO j i).1 (((hv i i.isLt).2.2.2 j).2 hi)
      · intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hl : Lb x r k i = false := by
          cases h : Lb x r k i
          · rfl
          · exact absurd ((hL i).1 h) hi
        exact (hv i i.isLt).2.1 hl j
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hn
        have hu : Ub x r k i = false := by
          cases h : Ub x r k i
          · rfl
          · exact absurd ((hU i).1 h) hn
        rw [(hv i i.isLt).2.2.1 hu j] at hi
        exact absurd hi (by simp)
      · rw [e1]; exact le_trans (hc j).1 (by simp [bmax])
      · rw [e2]; exact le_trans (hc j).2 (by simp [bmax])
  · rintro ⟨C, Y, hY, hCY⟩
    let col : ℕ → Col k := fun i => if h : i < r then
      (fun j => decide (⟨i, h⟩ ∈ C j), fun j => decide (⟨i, h⟩ ∈ Y j))
      else (fun _ => false, fun _ => false)
    refine ⟨col, fun i hi => ?_, fun j => ?_⟩
    · have hc : col i = (fun j => decide (⟨i, hi⟩ ∈ C j), fun j => decide (⟨i, hi⟩ ∈ Y j)) := by
        simp only [col, dif_pos hi]
      rw [hc]
      refine ⟨?_, ?_, ?_, fun j => ⟨?_, ?_⟩⟩
      · intro j j' hjj' h
        simp only [decide_eq_true_eq] at h ⊢
        exact hY hjj' h
      · intro hl j
        simp only [decide_eq_true_eq]
        apply (hCY j).2.2.1
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hm
        have h' : Lb x r k i = true := (hL ⟨i, hi⟩).2 hm
        rw [h'] at hl; exact absurd hl (by simp)
      · intro hu j
        simp only [decide_eq_false_iff_not]
        intro hm
        have h' : Ub x r k i = true := (hU ⟨i, hi⟩).2 ((hCY j).2.2.2.1 hm)
        rw [h'] at hu; exact absurd hu (by simp)
      · intro h
        simp only [decide_eq_false_iff_not] at h
        exact (hZ j ⟨i, hi⟩).2 ((hCY j).1 (by simp [h]))
      · intro h
        simp only [decide_eq_true_eq] at h
        exact (hO j ⟨i, hi⟩).2 ((hCY j).2.1 h)
    · have e1 : cA col r j = (C j \ Y j).card := by
        have : C j \ Y j = Finset.univ.filter
            (fun i : Fin r => (col i.val).1 j = true ∧ (col i.val).2 j = false) := by
          ext i; simp [col, i.isLt]
        rw [this, Finset.card_filter]
        exact (Fin.sum_univ_eq_sum_range
          (fun i => if (col i).1 j = true ∧ (col i).2 j = false then 1 else 0) r).symm
      have e2 : cF col r j = (Y j \ C j).card := by
        have : Y j \ C j = Finset.univ.filter
            (fun i : Fin r => (col i.val).1 j = false ∧ (col i.val).2 j = true) := by
          ext i; simp [col, i.isLt, and_comm]
        rw [this, Finset.card_filter]
        exact (Fin.sum_univ_eq_sum_range
          (fun i => if (col i).1 j = false ∧ (col i).2 j = true then 1 else 0) r).symm
      have c1 : (C j \ Y j).card ≤ r := by
        have := Finset.card_le_univ (C j \ Y j); simpa using this
      have c2 : (Y j \ C j).card ≤ r := by
        have := Finset.card_le_univ (Y j \ C j); simpa using this
      simp only [bmax]
      rw [e1, e2]
      exact ⟨le_min c1 (hCY j).2.2.2.2.1, le_min c2 (hCY j).2.2.2.2.2⟩

theorem circ_valid (r k : ℕ) (A F : Fin k → ℕ) :
    FanInTwo (theCirc r k A F) ∧ ReadsBack (2 * k * r + 2 * r + 2) (theCirc r k A F) ∧
      (theCirc r k A F).output < 2 * k * r + 2 * r + 2 + (theCirc r k A F).size := by
  have hN : 2 * k * r + 2 * r + 2 = NN r k := by unfold NN; ring
  rw [hN]
  exact ⟨layered_fan _ (spec_ok r k A F), layered_reads _ (spec_ok r k A F), circ_output r k A F⟩

theorem circ_notCount (r k : ℕ) (A F : Fin k → ℕ) :
    PEqualNP.NotBracket.notCount (theCirc r k A F) = 0 :=
  layered_notCount _ (spec_ok r k A F)

theorem circ_size (r k : ℕ) (a f : Fin k → ℕ) :
    (theCirc r k (fun j => min r (a j)) (fun j => min r (f j))).size ≤
      12 * (r + 1) * (k + 1) ^ 2 *
        (Finset.univ.prod (fun j : Fin k => (min r (a j) + 1) * (min r (f j) + 1)) + 1) := by
  unfold theCirc
  rw [layered_size, card_Sset]
  generalize Finset.univ.prod (fun j : Fin k => (min r (a j) + 1) * (min r (f j) + 1)) = Q
  calc r * (k + 1) * (3 * k + 3) * Q = 3 * (r * (k + 1) ^ 2 * Q) := by ring
    _ ≤ 12 * ((r + 1) * (k + 1) ^ 2 * (Q + 1)) := by
        apply Nat.mul_le_mul (by norm_num)
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) (by omega)
    _ = 12 * (r + 1) * (k + 1) ^ 2 * (Q + 1) := by ring

end

end PEqualNP.Outside.L_lib_1423_aux

theorem PEqualNP.Outside.L_lib_1423 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
let bits := fun {n : Nat} (X : Finset (Fin n)) => List.ofFn (fun j : Fin n => decide (j ∈ X))
let near := fun {r : Nat} (a f : Nat) (C Y : Finset (Fin r)) => (C \ Y).card ≤ a ∧ (Y \ C).card ≤ f
let rows := fun {k r : Nat} (W : Fin k → Finset (Fin r)) => (List.ofFn (fun j => bits (W j))).flatten
∀ (r k : Nat) (a f : Fin k → Nat),
  let Q := Finset.univ.prod (fun j : Fin k => (min r (a j)+1)*(min r (f j)+1))
  let n := 2*k*r+2*r
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, valid n D ∧ PEqualNP.NotBracket.notCount D=0 ∧
    D.size ≤ 12*(r+1)*(k+1)^2*(Q+1) ∧
    ∀ (Z O : Fin k → Finset (Fin r)) (L U : Finset (Fin r)),
      (D.eval (rows Z ++ rows O ++ bits L ++ bits U ++ [false,true]) = true ↔
       ∃ (C Y : Fin k → Finset (Fin r)), Monotone Y ∧ ∀ j,
         (Finset.univ \ C j) ⊆ Z j ∧ C j ⊆ O j ∧ (Finset.univ \ L) ⊆ Y j ∧ Y j ⊆ U ∧ near (a j) (f j) (C j) (Y j)) := by
  intro valid bits near rows r k a f Q n
  refine ⟨PEqualNP.Outside.L_lib_1423_aux.theCirc r k (fun j => min r (a j)) (fun j => min r (f j)), ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_lib_1423_aux.circ_valid r k _ _
  · exact PEqualNP.Outside.L_lib_1423_aux.circ_notCount r k _ _
  · exact PEqualNP.Outside.L_lib_1423_aux.circ_size r k a f
  · intro Z O L U
    refine (PEqualNP.Outside.L_lib_1423_aux.circ_eval r k _ _ (PEqualNP.Outside.L_lib_1423_aux.inList r k _ _ _ _) ?_ ?_ ?_).trans ?_
    · exact (PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).1
    · exact (PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).2.1
    · exact (PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).2.2.1
    · refine PEqualNP.Outside.L_lib_1423_aux.bridge r k a f _ _ Z O L U ?_ ?_ ?_ ?_
      · intro j i
        rw [(PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).2.2.2.1 j i]
        exact @decide_eq_true_iff _ (Classical.propDecidable _)
      · intro j i
        rw [(PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).2.2.2.2.1 j i]
        exact @decide_eq_true_iff _ (Classical.propDecidable _)
      · intro i
        rw [(PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).2.2.2.2.2.1 i]
        exact @decide_eq_true_iff _ (Classical.propDecidable _)
      · intro i
        rw [(PEqualNP.Outside.L_lib_1423_aux.input_facts r k _ _ _ _).2.2.2.2.2.2 i]
        exact @decide_eq_true_iff _ (Classical.propDecidable _)
