import Mathlib
import PEqualNP.Defs

-- Splicing four switches into a circuit on the ordered inputs, and the odd family built by repeating it.
--
-- First part. The old inputs keep their order but skip two new inputs placed after the first h old ones
-- and two more placed after all of them: old wire w moves to w, w + 2 or w + 4. Every old gate is kept
-- with its reads moved the same way. On level l of the new inputs every moved wire has the value the old
-- wire had on the retimed level (induction over the gate list, last gate removed). With U, V the two
-- inserted inputs and P, Q the two appended ones, eight gates are added: NOT P, NOT Q, NOT U,
-- A = U AND NOT P, B = V AND NOT Q, R OR P, NOT U OR B and their AND, where R is the moved first tap.
-- Their values are read off a table, gate by gate. A and B are the two new pulse taps, and the last gate
-- follows R except that it is false on level h + 1 and true on level n + 3; on level n + 4 it is false,
-- which is the value the old first tap has on its last level. Three NOT gates and five others are added.
--
-- Second part. For h = 0 the circuit x_0 AND NOT x_1 serves both taps. For the step the first part is
-- applied at the middle level 2h + 1; the old pulses, the two new pulses and the changed first tap are
-- exactly the taps of the next member, compared level by level on the retimed levels.

namespace PEqualNP.Outside.L_lib_1385

open PEqualNP.CircuitLowerBounds

theorem ifT {α : Type} (c : Prop) [Decidable c] (x y : α) (h : c) : (if c then x else y) = x := by
  simp [h]

theorem ifF {α : Type} (c : Prop) [Decidable c] (x y : α) (h : ¬ c) : (if c then x else y) = y := by
  simp [h]

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def Run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem Run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    Run (gs ++ [g]) w = Run gs w ++ [g.op.eval (g.inputs.map fun i => (Run gs w).getD i false)] := by
  simp [Run, List.foldl_append]

theorem Run_append (l1 l2 : List Gate) (w : List Bool) : Run (l1 ++ l2) w = Run l2 (Run l1 w) := by
  simp [Run, List.foldl_append]

theorem Run_len (gs : List Gate) (w : List Bool) : (Run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Run]
  | append_singleton gs g ih => rw [Run_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (Run (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (Run gs w).getD t false) := by
  rw [Run_snoc, getD_snoc]; simp [Run_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (Run (gs ++ [g]) w).getD i false = (Run gs w).getD i false := by
  rw [Run_snoc, getD_snoc]; simp [Run_len, hi]

theorem Run_init (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (Run gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [old_wire gs g w i (by omega)]; exact ih

/-- A list of gates given by a rule computes a table of values if every gate does. -/
theorem Run_spec (Ev : ℕ → Bool) (f : ℕ → Gate) (xs : List Bool)
    (hxs : ∀ w < xs.length, xs.getD w false = Ev w) :
    ∀ m : ℕ, (∀ j < m, (f j).op.eval ((f j).inputs.map Ev) = Ev (xs.length + j)) →
      (∀ j < m, ∀ a ∈ (f j).inputs, a < xs.length + j) →
      ∀ w < xs.length + m, (Run ((List.range m).map f) xs).getD w false = Ev w := by
  intro m
  induction m with
  | zero =>
    intro _ _ w hw
    simpa [Run] using hxs w (by omega)
  | succ m ih =>
    intro hev hin w hw
    have ih' := ih (fun j hj => hev j (by omega)) (fun j hj => hin j (by omega))
    rw [List.range_succ, List.map_append, List.map_singleton]
    have hlen : ((List.range m).map f).length = m := by simp
    by_cases hwm : w = xs.length + m
    · rw [hwm]
      have hnw := new_wire ((List.range m).map f) (f m) xs
      rw [hlen] at hnw
      rw [hnw, ← hev m (by omega)]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih' a (hin m (by omega) a ha)
    · have how := old_wire ((List.range m).map f) (f m) xs w (by rw [hlen]; exact hwm)
      rw [how]
      exact ih' w (by omega)

/-- The ordered input at level `t`. -/
def inpN (N t : ℕ) : List Bool := List.ofFn (fun k : Fin N => decide (k.val < t)) ++ [false, true]

theorem inpN_len (N t : ℕ) : (inpN N t).length = N + 2 := by simp [inpN]

theorem inpN_getD (N t u : ℕ) :
    (inpN N t).getD u false = if u < N then decide (u < t) else decide (u = N + 1) := by
  unfold inpN
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · obtain ⟨d, rfl⟩ : ∃ d, u = N + d := ⟨u - N, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rcases d with _ | _ | d
    · simp
    · simp
    · simp

theorem rb_of (N : ℕ) (C : Circuit)
    (h : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ x ∈ g.inputs, x < N + j) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N C := by
  intro j hj i hi
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hi
  exact h j _ (List.getElem?_eq_getElem hj) i hi

theorem rb_to (N : ℕ) (C : Circuit) (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C) :
    ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ x ∈ g.inputs, x < N + j := by
  intro j g hj a ha
  have hjl : j < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    simp at hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, hj]
    rfl
  exact hR j hjl a (by rw [e]; exact ha)

/-! ### Moving the old circuit -/

/-- Where an old wire goes. -/
def rho (n h w : ℕ) : ℕ := if w < h then w else if w < n then w + 2 else w + 4

theorem rho_le (n h w : ℕ) : rho n h w ≤ w + 4 := by
  unfold rho; split_ifs <;> omega

theorem rho_ge (n h w : ℕ) (hh : h ≤ n) (hw : n ≤ w) : rho n h w = w + 4 := by
  unfold rho; split_ifs <;> omega

/-- An old gate with its reads moved. -/
def remap (n h : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n h)⟩

/-- The old level seen on a new level. -/
def retime (n h l : ℕ) : ℕ := if l ≤ h then l else min n (max h (l - 2))

theorem retime_low (n h l : ℕ) (hl : l ≤ h) : retime n h l = l := by
  unfold retime; rw [ifT _ _ _ hl]

theorem retime_mid (n h l : ℕ) (hh : h ≤ n) (h1 : h < l) (h2 : l ≤ h + 2) : retime n h l = h := by
  simp only [retime, Nat.min_def, Nat.max_def]; split_ifs <;> omega

theorem retime_shift (n h l : ℕ) (h1 : h + 2 ≤ l) (h2 : l ≤ n + 2) : retime n h l = l - 2 := by
  simp only [retime, Nat.min_def, Nat.max_def]; split_ifs <;> omega

theorem retime_top (n h l : ℕ) (hh : h < n) (h1 : n + 2 ≤ l) : retime n h l = n := by
  simp only [retime, Nat.min_def, Nat.max_def]; split_ifs <;> omega

theorem retime_le (n h l : ℕ) (hh : h ≤ n) : retime n h l ≤ n := by
  simp only [retime, Nat.min_def, Nat.max_def]; split_ifs <;> omega

theorem inp_sim (n h l w : ℕ) (hh : h < n) (hw : w < n + 2) :
    (inpN (n + 4) l).getD (rho n h w) false = (inpN n (retime n h l)).getD w false := by
  rw [inpN_getD, inpN_getD]
  by_cases h1 : w < n
  · have hr : rho n h w < n + 4 := by unfold rho; split_ifs <;> omega
    rw [ifT _ _ _ hr, ifT _ _ _ h1, decide_eq_decide]
    by_cases c1 : l ≤ h
    · rw [retime_low n h l c1]; unfold rho; split_ifs <;> omega
    · by_cases c2 : l ≤ h + 2
      · rw [retime_mid n h l (by omega) (by omega) c2]; unfold rho; split_ifs <;> omega
      · by_cases c3 : l ≤ n + 2
        · rw [retime_shift n h l (by omega) c3]; unfold rho; split_ifs <;> omega
        · rw [retime_top n h l hh (by omega)]; unfold rho; split_ifs <;> omega
  · rw [rho_ge n h w (by omega) (by omega), ifF _ _ _ (by omega), ifF _ _ _ h1, decide_eq_decide]
    omega

theorem sim (n h l : ℕ) (hh : h < n) :
    ∀ gs : List Gate, (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 2 + j) →
      ∀ w < n + 2 + gs.length,
        (Run (gs.map (remap n h)) (inpN (n + 4) l)).getD (rho n h w) false =
          (Run gs (inpN n (retime n h l))).getD w false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w hw
    exact inp_sim n h l w hh (by simpa using hw)
  | append_singleton gs g ih =>
    intro hR w hw
    have ih' := ih (fun j g' hj a ha => hR j g' (by
        have hjl : j < gs.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hj
          simp at hj
        rw [List.getElem?_append_left hjl]
        exact hj) a ha)
    have hin : ∀ a ∈ g.inputs, a < n + 2 + gs.length := hR gs.length g (by simp)
    rw [List.map_append, List.map_singleton]
    have hlen : (gs.map (remap n h)).length = gs.length := by simp
    by_cases hw2 : w = n + 2 + gs.length
    · rw [hw2, rho_ge n h _ (by omega) (by omega)]
      have h1 := new_wire (gs.map (remap n h)) (remap n h g) (inpN (n + 4) l)
      rw [inpN_len, hlen] at h1
      have h2 := new_wire gs g (inpN n (retime n h l))
      rw [inpN_len] at h2
      rw [show n + 2 + gs.length + 4 = n + 4 + 2 + gs.length by omega, h1, h2]
      show g.op.eval ((g.inputs.map (rho n h)).map fun t =>
        (Run (gs.map (remap n h)) (inpN (n + 4) l)).getD t false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih' a (hin a ha)
    · have hw3 : w < n + 2 + gs.length := by
        simp only [List.length_append, List.length_singleton] at hw
        omega
      have hrl := rho_le n h w
      rw [old_wire (gs.map (remap n h)) (remap n h g) (inpN (n + 4) l) _
          (by rw [inpN_len, hlen]; omega),
        old_wire gs g (inpN n (retime n h l)) w (by rw [inpN_len]; exact hw2)]
      exact ih' w hw3

/-! ### The eight new gates -/

/-- The new gates; `M` is the first new wire and `r` the moved first tap. -/
def extra (n h M r : ℕ) : ℕ → Gate
  | 0 => ⟨GateOp.not, [n + 2]⟩
  | 1 => ⟨GateOp.not, [n + 3]⟩
  | 2 => ⟨GateOp.not, [h]⟩
  | 3 => ⟨GateOp.and, [h, M]⟩
  | 4 => ⟨GateOp.and, [h + 1, M + 1]⟩
  | 5 => ⟨GateOp.or, [r, n + 2]⟩
  | 6 => ⟨GateOp.or, [M + 2, M + 4]⟩
  | _ => ⟨GateOp.and, [M + 5, M + 6]⟩

/-- The values of the new gates. -/
def tbl (U V P Q R : Bool) : ℕ → Bool
  | 0 => !P
  | 1 => !Q
  | 2 => !U
  | 3 => (U && !P)
  | 4 => (V && !Q)
  | 5 => (R || P)
  | 6 => (!U || (V && !Q))
  | _ => ((R || P) && (!U || (V && !Q)))

/-- The values of all wires once the new gates are added to a wire list `Y`. -/
def EvY (n h r : ℕ) (Y : List Bool) (w : ℕ) : Bool :=
  if w < Y.length then Y.getD w false
  else tbl (Y.getD h false) (Y.getD (h + 1) false) (Y.getD (n + 2) false) (Y.getD (n + 3) false)
    (Y.getD r false) (w - Y.length)

theorem EvY_old (n h r : ℕ) (Y : List Bool) (w : ℕ) (hw : w < Y.length) :
    EvY n h r Y w = Y.getD w false := by
  unfold EvY; rw [ifT _ _ _ hw]

theorem EvY_new (n h r : ℕ) (Y : List Bool) (j : ℕ) :
    EvY n h r Y (Y.length + j) = tbl (Y.getD h false) (Y.getD (h + 1) false) (Y.getD (n + 2) false)
      (Y.getD (n + 3) false) (Y.getD r false) j := by
  unfold EvY; rw [ifF _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem extra_val (n h r : ℕ) (Y : List Bool) (hY1 : n + 3 < Y.length) (hY2 : h + 1 < Y.length)
    (hY3 : r < Y.length) :
    ∀ w < Y.length + 8,
      (Run ((List.range 8).map (extra n h Y.length r)) Y).getD w false = EvY n h r Y w := by
  have n0 : EvY n h r Y Y.length = !(Y.getD (n + 2) false) := EvY_new n h r Y 0
  refine Run_spec (EvY n h r Y) (extra n h Y.length r) Y
    (fun w hw => (EvY_old n h r Y w hw).symm) 8 ?_ ?_
  · intro j hj
    rw [EvY_new]
    interval_cases j
    · simp [extra, tbl, GateOp.eval, EvY_old n h r Y (n + 2) (by omega)]
    · simp [extra, tbl, GateOp.eval, EvY_old n h r Y (n + 3) (by omega)]
    · simp [extra, tbl, GateOp.eval, EvY_old n h r Y h (by omega)]
    · simp [extra, tbl, GateOp.eval, EvY_old n h r Y h (by omega), n0]
    · simp [extra, tbl, GateOp.eval, EvY_old n h r Y (h + 1) (by omega), EvY_new n h r Y 1]
    · simp [extra, tbl, GateOp.eval, EvY_old n h r Y r hY3, EvY_old n h r Y (n + 2) (by omega)]
    · simp [extra, tbl, GateOp.eval, EvY_new n h r Y 2, EvY_new n h r Y 4]
    · simp [extra, tbl, GateOp.eval, EvY_new n h r Y 5, EvY_new n h r Y 6]
  · intro j hj a ha
    interval_cases j <;> simp [extra] at ha <;> omega

/-- The new circuit. -/
def newC (n h : ℕ) (C : Circuit) (r : ℕ) : Circuit :=
  ⟨C.gates.map (remap n h) ++ (List.range 8).map (extra n h (n + 6 + C.gates.length) r), 0⟩

theorem newC_val (n h : ℕ) (C : Circuit) (r l : ℕ) (hh : h < n)
    (hr : r < n + 6 + C.gates.length) :
    (∀ w < n + 6 + C.gates.length,
      (Run (newC n h C r).gates (inpN (n + 4) l)).getD w false =
        (Run (C.gates.map (remap n h)) (inpN (n + 4) l)).getD w false) ∧
    (∀ j < 8, (Run (newC n h C r).gates (inpN (n + 4) l)).getD (n + 6 + C.gates.length + j) false =
        tbl (decide (h < l)) (decide (h + 1 < l)) (decide (n + 2 < l)) (decide (n + 3 < l))
          ((Run (C.gates.map (remap n h)) (inpN (n + 4) l)).getD r false) j) := by
  have hYlen : (Run (C.gates.map (remap n h)) (inpN (n + 4) l)).length = n + 6 + C.gates.length := by
    rw [Run_len, inpN_len, List.length_map]
  have hrun : Run (newC n h C r).gates (inpN (n + 4) l) =
      Run ((List.range 8).map (extra n h (Run (C.gates.map (remap n h)) (inpN (n + 4) l)).length r))
        (Run (C.gates.map (remap n h)) (inpN (n + 4) l)) := by
    rw [hYlen]; exact Run_append _ _ _
  have hin : ∀ k < n + 4,
      (Run (C.gates.map (remap n h)) (inpN (n + 4) l)).getD k false = decide (k < l) := by
    intro k hk
    rw [Run_init _ _ k (by rw [inpN_len]; omega), inpN_getD, ifT _ _ _ hk]
  have hv := extra_val n h r (Run (C.gates.map (remap n h)) (inpN (n + 4) l))
    (by rw [hYlen]; omega) (by rw [hYlen]; omega) (by rw [hYlen]; exact hr)
  rw [hrun]
  constructor
  · intro w hw
    rw [hv w (by rw [hYlen]; omega)]
    exact EvY_old _ _ _ _ w (by rw [hYlen]; exact hw)
  · intro j hj
    rw [← hYlen, hv _ (by omega), EvY_new, hin h (by omega), hin (h + 1) (by omega),
      hin (n + 2) (by omega), hin (n + 3) (by omega)]

/-! ### The statement about taps -/

/-- Some circuit within the three budgets has taps carrying the table `W` on every level. -/
def Fit (n a p b s : Nat) (W : Nat → Fin a → Bool) : Prop :=
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
    ∀ (l : Fin (n+1)) i, (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < l.val)) ++ [false,true])).getD (tap i) false = W l.val i

theorem Fit.retap {n a p b s : ℕ} {Wf : ℕ → Fin a → Bool} (hf : Fit n a p b s Wf)
    {p' b' s' a' : ℕ} (hp : p ≤ p') (hb : b ≤ b') (hs : s ≤ s') (σ : Fin a' → Fin a)
    (W' : ℕ → Fin a' → Bool) (hW : ∀ l, l ≤ n → ∀ i, W' l i = Wf l (σ i)) :
    Fit n a' p' b' s' W' := by
  obtain ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  refine ⟨C, fun i => tap (σ i), h1, h2, h3, fun i => h4 (σ i), le_trans h5 hp, le_trans h6 hb,
    le_trans h7 hs, fun l i => ?_⟩
  rw [hW l.val (Nat.lt_succ_iff.1 l.isLt) i]
  exact h8 l (σ i)

theorem Fit.cast {n n' a p b s : ℕ} {Wf : ℕ → Fin a → Bool} (e : n = n') (hf : Fit n a p b s Wf) :
    Fit n' a p b s Wf := by
  subst e; exact hf

/-- The table after the splice. -/
def Vsp (n a h : ℕ) (Wf : Nat → Fin (a+1) → Bool) (l : Nat) (i : Fin (a+4)) : Bool :=
  if i.val < a+1 then Wf (retime n h l) (Fin.ofNat (a+1) i.val)
  else if i.val = a+1 then decide (h+1 ≤ l ∧ l < n+3)
  else if i.val = a+2 then decide (h+2 ≤ l ∧ l < n+4)
  else if l = h+1 then false else if l = n+3 then true else Wf (retime n h l) 0

theorem Vsp_old (n a h : ℕ) (Wf : Nat → Fin (a+1) → Bool) (l : ℕ) (i : Fin (a+4))
    (hi : i.val < a + 1) : Vsp n a h Wf l i = Wf (retime n h l) (Fin.ofNat (a+1) i.val) := by
  unfold Vsp; rw [ifT _ _ _ hi]

theorem Vsp_A (n a h : ℕ) (Wf : Nat → Fin (a+1) → Bool) (l : ℕ) (i : Fin (a+4))
    (hi : i.val = a + 1) : Vsp n a h Wf l i = decide (h+1 ≤ l ∧ l < n+3) := by
  unfold Vsp; rw [ifF _ _ _ (by omega), ifT _ _ _ hi]

theorem Vsp_B (n a h : ℕ) (Wf : Nat → Fin (a+1) → Bool) (l : ℕ) (i : Fin (a+4))
    (hi : i.val = a + 2) : Vsp n a h Wf l i = decide (h+2 ≤ l ∧ l < n+4) := by
  unfold Vsp; rw [ifF _ _ _ (by omega), ifF _ _ _ (by omega), ifT _ _ _ hi]

theorem Vsp_root (n a h : ℕ) (Wf : Nat → Fin (a+1) → Bool) (l : ℕ) (i : Fin (a+4))
    (hi : i.val = a + 3) : Vsp n a h Wf l i =
      if l = h+1 then false else if l = n+3 then true else Wf (retime n h l) 0 := by
  unfold Vsp; rw [ifF _ _ _ (by omega), ifF _ _ _ (by omega), ifF _ _ _ (by omega)]

/-- The taps of the new circuit. -/
def newTap (n a h : ℕ) (C : Circuit) (tap : Fin (a + 1) → ℕ) (i : Fin (a + 4)) : ℕ :=
  if i.val < a + 1 then rho n h (tap (Fin.ofNat (a + 1) i.val))
  else if i.val = a + 1 then n + 6 + C.gates.length + 3
  else if i.val = a + 2 then n + 6 + C.gates.length + 4
  else n + 6 + C.gates.length + 7

theorem splice (n a p b s h : ℕ) (Wf : ℕ → Fin (a + 1) → Bool) (hh : h < n)
    (hWn : Wf n 0 = false) (hfit : Fit n (a + 1) p b s Wf) :
    Fit (n + 4) (a + 4) (p + 5) (b + 3) (s + 8) (Vsp n a h Wf) := by
  obtain ⟨C, tap, hF, hR, -, htap, hP, hB, hS, hval⟩ := hfit
  have hRB := rb_to (n + 2) C hR
  have htap' : ∀ i, tap i < n + 2 + C.gates.length := htap
  have hr : rho n h (tap 0) < n + 6 + C.gates.length := by
    have h1 := rho_le n h (tap 0)
    have h2 := htap' 0
    omega
  have hlenM : (C.gates.map (remap n h)).length = C.gates.length := by simp
  obtain ⟨isNot, hisNot, e1, e2⟩ : ∃ isNot : Gate → Bool,
      (∀ g, isNot g = true ↔ g.op = GateOp.not) ∧
        PEqualNP.NotBracket.notCount C = (C.gates.filter isNot).length ∧
        PEqualNP.NotBracket.notCount (newC n h C (rho n h (tap 0))) =
          ((newC n h C (rho n h (tap 0))).gates.filter isNot).length := by
    refine ⟨_, ?_, rfl, rfl⟩
    intro g
    simp only [decide_eq_true_eq]
  have hN : ∀ ins, isNot ⟨GateOp.not, ins⟩ = true := fun ins => (hisNot _).2 rfl
  have hA : ∀ ins, isNot ⟨GateOp.and, ins⟩ = false := by
    intro ins
    cases hc : isNot ⟨GateOp.and, ins⟩ with
    | false => rfl
    | true => exact absurd ((hisNot _).1 hc) (by simp)
  have hO : ∀ ins, isNot ⟨GateOp.or, ins⟩ = false := by
    intro ins
    cases hc : isNot ⟨GateOp.or, ins⟩ with
    | false => rfl
    | true => exact absurd ((hisNot _).1 hc) (by simp)
  have hmap : ((C.gates.map (remap n h)).filter isNot).length = (C.gates.filter isNot).length := by
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro g _
    apply Bool.eq_iff_iff.2
    show isNot (remap n h g) = true ↔ isNot g = true
    rw [hisNot, hisNot]
    exact Iff.rfl
  have hext : (((List.range 8).map (extra n h (n + 6 + C.gates.length) (rho n h (tap 0)))).filter
      isNot).length = 3 := by
    simp [List.range_succ, extra, hN, hA, hO]
  have hnc : PEqualNP.NotBracket.notCount (newC n h C (rho n h (tap 0))) =
      PEqualNP.NotBracket.notCount C + 3 := by
    rw [e2, e1]
    show ((C.gates.map (remap n h) ++
      (List.range 8).map (extra n h (n + 6 + C.gates.length) (rho n h (tap 0)))).filter isNot).length = _
    rw [List.filter_append, List.length_append, hmap, hext]
  have hsz : (newC n h C (rho n h (tap 0))).size = C.size + 8 := by
    show (C.gates.map (remap n h) ++
      (List.range 8).map (extra n h (n + 6 + C.gates.length) (rho n h (tap 0)))).length = _
    rw [List.length_append, hlenM]
    simp [Circuit.size]
  have hle : PEqualNP.NotBracket.notCount C ≤ C.size := by
    rw [e1]; exact List.length_filter_le _ _
  have hCs : C.size = C.gates.length := rfl
  refine ⟨newC n h C (rho n h (tap 0)), newTap n a h C tap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fan-in two
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      obtain ⟨h1, h2⟩ := hF g0 hg0
      exact ⟨h1, by simpa [remap] using h2⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
      have hk' := List.mem_range.1 hk
      interval_cases k <;> exact ⟨by simp [extra], by simp [extra]⟩
  · -- reads back
    apply rb_of
    intro j g hg x hx
    have hg' : (C.gates.map (remap n h) ++
        (List.range 8).map (extra n h (n + 6 + C.gates.length) (rho n h (tap 0))))[j]? = some g := hg
    rw [List.getElem?_append] at hg'
    split_ifs at hg' with c
    · rw [List.getElem?_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have h1 := hRB j g0 hg0 y hy
      have h2 := rho_le n h y
      omega
    · obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg'
      simp only [List.getElem_map, List.getElem_range] at hx
      have hk8 : j - (C.gates.map (remap n h)).length < 8 := by simpa using hk
      rw [hlenM] at hk8 hx c
      generalize hkk : j - C.gates.length = k at hx hk8
      interval_cases k <;> simp [extra] at hx <;> omega
  · show 0 < _
    omega
  · intro i
    rw [hsz, hCs]
    unfold newTap
    have h1 := rho_le n h (tap (Fin.ofNat (a + 1) i.val))
    have h2 := htap' (Fin.ofNat (a + 1) i.val)
    split_ifs <;> omega
  · rw [hsz, hnc]; omega
  · rw [hnc]; omega
  · rw [hsz]; omega
  · intro l i
    have hl : l.val ≤ n + 4 := Nat.lt_succ_iff.1 l.isLt
    obtain ⟨hold, hnew⟩ := newC_val n h C (rho n h (tap 0)) l.val hh hr
    have hsim := sim n h l.val hh C.gates hRB
    have hlev : ∀ i', (Run C.gates (inpN n (retime n h l.val))).getD (tap i') false =
        Wf (retime n h l.val) i' := fun i' =>
      hval ⟨retime n h l.val, Nat.lt_succ_of_le (retime_le n h l.val (by omega))⟩ i'
    show (Run (newC n h C (rho n h (tap 0))).gates (inpN (n + 4) l.val)).getD (newTap n a h C tap i)
      false = Vsp n a h Wf l.val i
    by_cases c1 : i.val < a + 1
    · rw [Vsp_old n a h Wf l.val i c1]
      have e : newTap n a h C tap i = rho n h (tap (Fin.ofNat (a + 1) i.val)) := by
        unfold newTap; rw [ifT _ _ _ c1]
      have h1 := rho_le n h (tap (Fin.ofNat (a + 1) i.val))
      have h2 := htap' (Fin.ofNat (a + 1) i.val)
      rw [e, hold _ (by omega), hsim _ h2]
      exact hlev _
    · by_cases c2 : i.val = a + 1
      · rw [Vsp_A n a h Wf l.val i c2]
        have e : newTap n a h C tap i = n + 6 + C.gates.length + 3 := by
          unfold newTap; rw [ifF _ _ _ c1, ifT _ _ _ c2]
        rw [e, hnew 3 (by omega)]
        show (decide (h < l.val) && !decide (n + 2 < l.val)) = _
        rw [← decide_not, ← Bool.decide_and, decide_eq_decide]
        omega
      · by_cases c3 : i.val = a + 2
        · rw [Vsp_B n a h Wf l.val i c3]
          have e : newTap n a h C tap i = n + 6 + C.gates.length + 4 := by
            unfold newTap; rw [ifF _ _ _ c1, ifF _ _ _ c2, ifT _ _ _ c3]
          rw [e, hnew 4 (by omega)]
          show (decide (h + 1 < l.val) && !decide (n + 3 < l.val)) = _
          rw [← decide_not, ← Bool.decide_and, decide_eq_decide]
          omega
        · have c4 : i.val = a + 3 := by have := i.isLt; omega
          rw [Vsp_root n a h Wf l.val i c4]
          have e : newTap n a h C tap i = n + 6 + C.gates.length + 7 := by
            unfold newTap; rw [ifF _ _ _ c1, ifF _ _ _ c2, ifF _ _ _ c3]
          have hR0 : (Run (C.gates.map (remap n h)) (inpN (n + 4) l.val)).getD (rho n h (tap 0)) false =
              Wf (retime n h l.val) 0 := by
            rw [hsim _ (htap' 0)]; exact hlev 0
          rw [e, hnew 7 (by omega), hR0]
          show ((Wf (retime n h l.val) 0 || decide (n + 2 < l.val)) &&
            (!decide (h < l.val) || (decide (h + 1 < l.val) && !decide (n + 3 < l.val)))) = _
          by_cases d1 : l.val = h + 1
          · rw [ifT _ _ _ d1]
            have hU : decide (h < l.val) = true := decide_eq_true (by omega)
            have hV : decide (h + 1 < l.val) = false := decide_eq_false (by omega)
            rw [hU, hV]
            simp
          · rw [ifF _ _ _ d1]
            by_cases d2 : l.val = n + 3
            · rw [ifT _ _ _ d2]
              have hPp : decide (n + 2 < l.val) = true := decide_eq_true (by omega)
              have hV : decide (h + 1 < l.val) = true := decide_eq_true (by omega)
              have hQ : decide (n + 3 < l.val) = false := decide_eq_false (by omega)
              rw [hPp, hV, hQ]
              simp
            · rw [ifF _ _ _ d2]
              by_cases d3 : l.val ≤ h
              · have hU : decide (h < l.val) = false := decide_eq_false (by omega)
                have hPp : decide (n + 2 < l.val) = false := decide_eq_false (by omega)
                rw [hU, hPp]
                simp
              · by_cases d4 : l.val ≤ n + 2
                · have hPp : decide (n + 2 < l.val) = false := decide_eq_false (by omega)
                  have hV : decide (h + 1 < l.val) = true := decide_eq_true (by omega)
                  have hQ : decide (n + 3 < l.val) = false := decide_eq_false (by omega)
                  rw [hPp, hV, hQ]
                  simp
                · have hl4 : l.val = n + 4 := by omega
                  have hU : decide (h < l.val) = true := decide_eq_true (by omega)
                  have hQ : decide (n + 3 < l.val) = true := decide_eq_true (by omega)
                  rw [retime_top n h l.val hh (by omega), hWn, hU, hQ]
                  simp

/-! ### The odd family -/

/-- The table of the odd family. -/
def Vodd (h : ℕ) (l : Nat) (i : Fin (2*h+1+1)) : Bool :=
  if i.val = 0 then decide (l % 2 = 1) else decide (i.val ≤ l ∧ l < 2*h+1+i.val)

theorem Vodd_zero (h l : ℕ) (i : Fin (2*h+1+1)) (hi : i.val = 0) :
    Vodd h l i = decide (l % 2 = 1) := by
  unfold Vodd; rw [ifT _ _ _ hi]

theorem Vodd_pos (h l : ℕ) (i : Fin (2*h+1+1)) (hi : ¬ i.val = 0) :
    Vodd h l i = decide (i.val ≤ l ∧ l < 2*h+1+i.val) := by
  unfold Vodd; rw [ifF _ _ _ hi]

theorem base_fit : Fit 2 2 1 1 2 (Vodd 0) := by
  refine ⟨⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 4]⟩], 5⟩, fun _ => 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact ⟨by simp, by simp⟩
  · apply rb_of
    intro j g hg x hx
    rcases j with _ | _ | j
    · simp at hg; subst hg; simp at hx; omega
    · simp at hg; subst hg; simp at hx; omega
    · simp at hg
  · decide
  · intro _
    show (5 : ℕ) < 2 + 2 + 2
    omega
  · simp [PEqualNP.NotBracket.notCount, Circuit.size]
  · simp [PEqualNP.NotBracket.notCount]
  · simp [Circuit.size]
  · decide

/-- Which tap of the spliced circuit is tap `i` of the next member. -/
def sig (h : ℕ) (i : Fin (2 * (h + 1) + 1 + 1)) : Fin (2 * h + 1 + 4) :=
  if i.val = 0 then ⟨2 * h + 1 + 3, by omega⟩ else ⟨i.val, by have := i.isLt; omega⟩

theorem sig_zero (h : ℕ) (i : Fin (2 * (h + 1) + 1 + 1)) (hi : i.val = 0) :
    (sig h i).val = 2 * h + 1 + 3 := by
  simp [sig, hi]

theorem sig_pos (h : ℕ) (i : Fin (2 * (h + 1) + 1 + 1)) (hi : ¬ i.val = 0) :
    (sig h i).val = i.val := by
  simp [sig, hi]

theorem table_step (h l : ℕ) (hl : l ≤ 2 * (2 * h + 1) + 4) (i : Fin (2 * (h + 1) + 1 + 1)) :
    Vodd (h + 1) l i = Vsp (2 * (2 * h + 1)) (2 * h + 1) (2 * h + 1) (Vodd h) l (sig h i) := by
  have hi := i.isLt
  by_cases c0 : i.val = 0
  · rw [Vsp_root _ _ _ _ _ _ (sig_zero h i c0), Vodd_zero (h + 1) l i c0,
      Vodd_zero h _ 0 (Fin.val_zero _)]
    by_cases d1 : l = 2 * h + 1 + 1
    · rw [ifT _ _ _ d1]
      exact decide_eq_false (by omega)
    · rw [ifF _ _ _ d1]
      by_cases d2 : l = 2 * (2 * h + 1) + 3
      · rw [ifT _ _ _ d2]
        exact decide_eq_true (by omega)
      · rw [ifF _ _ _ d2, decide_eq_decide]
        by_cases e1 : l ≤ 2 * h + 1
        · rw [retime_low _ _ _ e1]
        · by_cases e2 : l ≤ 2 * h + 1 + 2
          · rw [retime_mid _ _ _ (by omega) (by omega) e2]; omega
          · by_cases e3 : l ≤ 2 * (2 * h + 1) + 2
            · rw [retime_shift _ _ _ (by omega) e3]; omega
            · rw [retime_top _ _ _ (by omega) (by omega)]; omega
  · have hs := sig_pos h i c0
    by_cases c1 : i.val < 2 * h + 1 + 1
    · rw [Vsp_old _ _ _ _ _ _ (by rw [hs]; exact c1)]
      have hv : (Fin.ofNat (2 * h + 1 + 1) (sig h i).val).val = i.val := by
        rw [hs]
        show i.val % (2 * h + 1 + 1) = i.val
        exact Nat.mod_eq_of_lt c1
      rw [Vodd_pos (h + 1) l i c0, Vodd_pos h _ _ (by rw [hv]; exact c0), hv, decide_eq_decide]
      by_cases e1 : l ≤ 2 * h + 1
      · rw [retime_low _ _ _ e1]; omega
      · by_cases e2 : l ≤ 2 * h + 1 + 2
        · rw [retime_mid _ _ _ (by omega) (by omega) e2]; omega
        · by_cases e3 : l ≤ 2 * (2 * h + 1) + 2
          · rw [retime_shift _ _ _ (by omega) e3]; omega
          · rw [retime_top _ _ _ (by omega) (by omega)]; omega
    · by_cases c2 : i.val = 2 * h + 1 + 1
      · rw [Vsp_A _ _ _ _ _ _ (by rw [hs]; exact c2)]
        rw [Vodd_pos (h + 1) l i c0, decide_eq_decide]
        omega
      · rw [Vsp_B _ _ _ _ _ _ (by rw [hs]; omega)]
        rw [Vodd_pos (h + 1) l i c0, decide_eq_decide]
        omega

theorem odd_family : ∀ h : ℕ,
    Fit (2 * (2 * h + 1)) (2 * h + 1 + 1) (5 * h + 1) (3 * h + 1) (8 * h + 2) (Vodd h) := by
  intro h
  induction h with
  | zero => exact base_fit
  | succ h ih =>
    have hWn : Vodd h (2 * (2 * h + 1)) 0 = false := by
      rw [Vodd_zero h _ 0 (Fin.val_zero _)]
      exact decide_eq_false (by omega)
    have F1 := splice (2 * (2 * h + 1)) (2 * h + 1) (5 * h + 1) (3 * h + 1) (8 * h + 2) (2 * h + 1)
      (Vodd h) (by omega) hWn ih
    exact Fit.cast (by omega) (F1.retap (by omega) (by omega) (by omega) (sig h) (Vodd (h + 1))
      (fun l hl i => table_step h l hl i))

end PEqualNP.Outside.L_lib_1385

theorem PEqualNP.Outside.L_lib_1385 :
let fit := fun (n a p b s : Nat) (W : Nat → Fin a → Bool) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
    ∀ (l : Fin (n+1)) i, (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < l.val)) ++ [false,true])).getD (tap i) false = W l.val i
(∀ (n a p b s h : Nat) (W : Nat → Fin (a+1) → Bool),
  h < n → W h 0 = true → W n 0 = false → fit n (a+1) p b s W →
  let retime := fun l : Nat => if l ≤ h then l else min n (max h (l-2))
  let V := fun (l : Nat) (i : Fin (a+4)) =>
    if i.val < a+1 then W (retime l) (Fin.ofNat (a+1) i.val)
    else if i.val = a+1 then decide (h+1 ≤ l ∧ l < n+3)
    else if i.val = a+2 then decide (h+2 ≤ l ∧ l < n+4)
    else if l = h+1 then false else if l = n+3 then true else W (retime l) 0
  fit (n+4) (a+4) (p+5) (b+3) (s+8) V) ∧
∀ h : Nat,
  let d := 2*h+1
  let V := fun (l : Nat) (i : Fin (d+1)) =>
    if i.val = 0 then decide (l % 2 = 1) else decide (i.val ≤ l ∧ l < d+i.val)
  fit (2*d) (d+1) (5*h+1) (3*h+1) (8*h+2) V := by
  intro fit
  refine ⟨?_, ?_⟩
  · intro n a p b s h W hh _ hWn hfit retime V
    exact PEqualNP.Outside.L_lib_1385.splice n a p b s h W hh hWn hfit
  · intro h d V
    exact PEqualNP.Outside.L_lib_1385.odd_family h
