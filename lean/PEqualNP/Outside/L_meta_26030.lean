import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26030_aux

open PEqualNP.CircuitLowerBounds

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

def fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

/-! ## list helpers -/

theorem getD_app_left {α : Type} (l l' : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getElem?_append_left h]

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) (i : ℕ) (h : i = l.length) :
    (l ++ [a]).getD i d = a := by
  subst h; simp

theorem getD_ge {α : Type} (l : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getElem?_eq_none h]

/-! ## generic folds -/

def gfold {α : Type} (step : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun acc g => acc ++ [step acc g]) init

theorem gfold_nil {α : Type} (step : List α → Gate → α) (init : List α) :
    gfold step [] init = init := rfl

theorem gfold_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    gfold step (gs ++ [g]) init = gfold step gs init ++ [step (gfold step gs init) g] := by
  simp [gfold, List.foldl_append]

theorem gfold_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (init : List α) :
    (gfold step gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [gfold]
  | append_singleton gs g ih => rw [gfold_snoc]; simp [ih]; omega

theorem gfold_prefix {α : Type} (step : List α → Gate → α) (gs1 gs2 : List Gate)
    (init : List α) : ∃ suf, gfold step (gs1 ++ gs2) init = gfold step gs1 init ++ suf := by
  induction gs2 using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton gs g ih =>
    obtain ⟨suf, h⟩ := ih
    refine ⟨suf ++ [step (gfold step (gs1 ++ gs) init) g], ?_⟩
    rw [← List.append_assoc, gfold_snoc, h]; simp

theorem gfold_getD_prefix {α : Type} (step : List α → Gate → α) (gs1 gs2 : List Gate)
    (init : List α) (i : ℕ) (d : α) (hi : i < init.length + gs1.length) :
    (gfold step (gs1 ++ gs2) init).getD i d = (gfold step gs1 init).getD i d := by
  obtain ⟨suf, h⟩ := gfold_prefix step gs1 gs2 init
  rw [h, getD_app_left _ _ _ _ (by rw [gfold_length]; exact hi)]

theorem gfold_getD_init {α : Type} (step : List α → Gate → α) (gs : List Gate)
    (init : List α) (i : ℕ) (d : α) (hi : i < init.length) :
    (gfold step gs init).getD i d = init.getD i d := by
  have := gfold_getD_prefix step [] gs init i d (by simpa using hi)
  simpa [gfold_nil] using this

def stepW (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def stepD (ds : List ℕ) (g : Gate) : ℕ :=
  (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = gfold stepW C.gates x := rfl

theorem depths_eq (w : ℕ) (C : Circuit) :
    depths w C = gfold stepD C.gates (List.replicate w 0) := rfl

/-! ## ZMod 2 -/

def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem toZ_true : toZ true = 1 := rfl
@[simp] theorem toZ_false : toZ false = 0 := rfl

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_inj {a b : Bool} (h : toZ a = toZ b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem toZ_decide_one (z : ZMod 2) : toZ (decide (z = 1)) = z := by
  revert z; decide

theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

theorem eval1 (op : GateOp) (x : Bool) :
    toZ (op.eval [x]) = toZ (op.eval [false]) +
      (toZ (op.eval [false]) + toZ (op.eval [true])) * toZ x := by
  have key : ∀ a b : ZMod 2, b = a + (a + b) * 1 := by decide
  cases x
  · simp
  · simpa using key (toZ (op.eval [false])) (toZ (op.eval [true]))

theorem eval2 (op : GateOp) (x y : Bool) :
    toZ (op.eval [x, y]) = toZ (op.eval [false, false]) +
      (toZ (op.eval [false, false]) + toZ (op.eval [true, false])) * toZ x +
      (toZ (op.eval [false, false]) + toZ (op.eval [false, true])) * toZ y +
      toZ (xor (xor (op.eval [false, false]) (op.eval [false, true]))
        (xor (op.eval [true, false]) (op.eval [true, true]))) * (toZ x * toZ y) := by
  rw [toZ_xor, toZ_xor, toZ_xor]
  generalize h00 : op.eval [false, false] = e00
  generalize h01 : op.eval [false, true] = e01
  generalize h10 : op.eval [true, false] = e10
  generalize h11 : op.eval [true, true] = e11
  cases x <;> cases y <;> simp only [h00, h01, h10, h11] <;>
    cases e00 <;> cases e01 <;> cases e10 <;> cases e11 <;> decide

/-! ## affine functions on the one-hot domain -/

abbrev Fn (n : ℕ) := Fin n → Fin n → ZMod 2

def Aff (n : ℕ) : Submodule (ZMod 2) (Fn n) :=
  { carrier := {f | ∃ α β : Fin n → ZMod 2, ∀ u v, f u v = α u + β v}
    zero_mem' := ⟨0, 0, fun u v => by simp⟩, add_mem' := by
      rintro f g ⟨α, β, hf⟩ ⟨α', β', hg⟩
      exact ⟨α + α', β + β', fun u v => by simp only [Pi.add_apply, hf, hg]; ring⟩
    smul_mem' := by
      rintro c f ⟨α, β, hf⟩
      exact ⟨c • α, c • β, fun u v => by simp only [Pi.smul_apply, smul_eq_mul, hf]; ring⟩ }

theorem mem_Aff {n : ℕ} {f : Fn n} :
    f ∈ Aff n ↔ ∃ α β : Fin n → ZMod 2, ∀ u v, f u v = α u + β v := Iff.rfl

abbrev Pr (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

def tens {n : ℕ} (p : Pr n) : Fn n := fun u v => p.1 u * p.2 v

def W {n : ℕ} (Ls : List (Pr n)) : Submodule (ZMod 2) (Fn n) :=
  Aff n ⊔ Submodule.span (ZMod 2) {f | ∃ p ∈ Ls, f = tens p}

theorem W_mono {n : ℕ} {Ls Ls' : List (Pr n)} (h : ∀ p ∈ Ls, p ∈ Ls') : W Ls ≤ W Ls' :=
  sup_le_sup_left (Submodule.span_mono (by rintro f ⟨p, hp, rfl⟩; exact ⟨p, h p hp, rfl⟩)) _

theorem Aff_le_W {n : ℕ} (Ls : List (Pr n)) : Aff n ≤ W Ls := le_sup_left

theorem const_mem_Aff {n : ℕ} (c : ZMod 2) : (fun _ _ => c : Fn n) ∈ Aff n :=
  ⟨fun _ => c, 0, fun _ _ => by simp⟩

theorem tens_mem_W {n : ℕ} {Ls : List (Pr n)} {p : Pr n} (hp : p ∈ Ls) : tens p ∈ W Ls :=
  (le_sup_right : Submodule.span (ZMod 2) {f | ∃ p ∈ Ls, f = tens p} ≤ W Ls)
    (Submodule.subset_span ⟨p, hp, rfl⟩)

theorem mul_mem_W {n : ℕ} {f g : Fn n} (hf : f ∈ Aff n) (hg : g ∈ Aff n) :
    ∃ p q : Pr n, ∀ Ls : List (Pr n), p ∈ Ls → q ∈ Ls → f * g ∈ W Ls := by
  obtain ⟨α, β, hf⟩ := hf
  obtain ⟨α', β', hg⟩ := hg
  refine ⟨(α, β'), (α', β), fun Ls hp hq => ?_⟩
  have h1 : (fun u v => α u * α' u + β v * β' v : Fn n) ∈ W Ls :=
    Aff_le_W Ls ⟨fun u => α u * α' u, fun v => β v * β' v, fun _ _ => rfl⟩
  have : f * g = (fun u v => α u * α' u + β v * β' v) + tens (α, β') + tens (α', β) := by
    funext u v; simp only [Pi.mul_apply, Pi.add_apply, hf, hg, tens]; ring
  rw [this]; exact add_mem (add_mem h1 (tens_mem_W hp)) (tens_mem_W hq)

/-! ## the one-hot input -/

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false =
      (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold PEqualNP.Represents.oneEach
  rcases Nat.lt_or_ge i n with h | h
  · rw [getD_app_left _ _ _ _ (by simpa using h)]
    have h2 : ¬ i = n + v.val := by omega
    simp [List.getElem?_ofFn, h, h2, Fin.ext_iff]
  · have h1 : ¬ i = u.val := by omega
    have hlen : (List.ofFn fun i : Fin n => decide (i = u)).length ≤ i := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hlen, List.length_ofFn]
    by_cases h3 : i - n < m
    · have : (i = n + v.val) ↔ (⟨i - n, h3⟩ : Fin m) = v := by
        rw [Fin.ext_iff]; simp; omega
      simp [List.getElem?_ofFn, h3, h1, this]
    · have h4 : ¬ i = n + v.val := by omega
      simp [List.getElem?_ofFn, h3, h1, h4]

theorem toZ_onehot {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    toZ ((PEqualNP.Represents.oneEach u v).getD i false) =
      toZ (decide (i = u.val)) + toZ (decide (i = n + v.val)) := by
  rw [oneEach_getD]
  by_cases h1 : i = u.val
  · have h2 : ¬ i = n + v.val := by omega
    rw [decide_eq_true h1, decide_eq_false h2]; decide
  · by_cases h2 : i = n + v.val
    · rw [decide_eq_false h1, decide_eq_true h2]; decide
    · rw [decide_eq_false h1, decide_eq_false h2]; decide

/-! ## the lower bound invariant -/

def vf (n : ℕ) (gs : List Gate) (i : ℕ) : Fn n :=
  fun u v => toZ ((gfold stepW gs (PEqualNP.Represents.oneEach u v)).getD i false)

def RB (N : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < N + j

theorem RB_snoc {N : ℕ} {gs : List Gate} {g : Gate} :
    RB N (gs ++ [g]) ↔ RB N gs ∧ ∀ i ∈ g.inputs, i < N + gs.length := by
  constructor
  · intro h
    refine ⟨fun j hj i hi => ?_, fun i hi => ?_⟩
    · have := h j (by simp; omega) i (by rw [getD_app_left _ _ _ _ hj]; exact hi)
      exact this
    · exact h gs.length (by simp) i (by rw [getD_snoc_eq _ _ _ _ rfl]; exact hi)
  · rintro ⟨h1, h2⟩ j hj i hi
    simp at hj
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [getD_app_left _ _ _ _ h] at hi; exact h1 j h i hi
    · have : j = gs.length := by omega
      subst this
      rw [getD_snoc_eq _ _ _ _ rfl] at hi; exact h2 i hi

theorem nonlinear_len {g : Gate} (h : g.inputs.length ≠ 2) : nonlinear g = false := by
  simp [nonlinear, h]

theorem vf_old (n : ℕ) (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < n + n + gs.length) :
    vf n (gs ++ [g]) i = vf n gs i := by
  funext u v
  simp only [vf]
  rw [gfold_getD_prefix _ _ _ _ _ _ (by rw [oneEach_length]; exact hi)]

theorem vf_new (n : ℕ) (gs : List Gate) (g : Gate) :
    vf n (gs ++ [g]) (n + n + gs.length) = fun u v =>
      toZ (g.op.eval (g.inputs.map fun a =>
        (gfold stepW gs (PEqualNP.Represents.oneEach u v)).getD a false)) := by
  funext u v
  simp only [vf]
  rw [gfold_snoc, getD_snoc_eq _ _ _ _ (by rw [gfold_length, oneEach_length])]
  rfl

theorem vf_beyond (n : ℕ) (gs : List Gate) (i : ℕ) (hi : n + n + gs.length ≤ i) :
    vf n gs i = 0 := by
  funext u v
  simp only [vf]
  rw [getD_ge _ _ _ (by rw [gfold_length, oneEach_length]; exact hi)]
  rfl

theorem lower_inv (n : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    RB (n + n) gs →
    ∃ Ls : List (Pr n), Ls.length ≤ 2 * gs.countP nonlinear ∧
      ∀ i, ((gfold stepD gs (List.replicate (n+n) 0)).getD i 0 = 0 → vf n gs i ∈ Aff n) ∧
           ((gfold stepD gs (List.replicate (n+n) 0)).getD i 0 ≤ 1 → vf n gs i ∈ W Ls) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨[], by simp, fun i => ?_⟩
    have hA : vf n [] i ∈ Aff n := by
      refine ⟨fun u => toZ (decide (i = u.val)), fun v => toZ (decide (i = n + v.val)),
        fun u v => ?_⟩
      simp only [vf, gfold_nil]
      exact toZ_onehot u v i
    exact ⟨fun _ => hA, fun _ => Aff_le_W _ hA⟩
  | append_singleton gs g ih =>
    intro hfan hrb
    rw [RB_snoc] at hrb
    obtain ⟨Ls, hlen, hinv⟩ := ih (fun g' hg' => hfan g' (by simp [hg'])) hrb.1
    have hg2 : g.inputs.length ≤ 2 := hfan g (by simp)
    set D := gfold stepD gs (List.replicate (n+n) 0) with hD
    have hDlen : D.length = n + n + gs.length := by rw [hD, gfold_length]; simp
    have hD' : gfold stepD (gs ++ [g]) (List.replicate (n+n) 0) = D ++ [stepD D g] := by
      rw [gfold_snoc]
    -- value of the new wire
    have hval : ∀ a ∈ g.inputs, ∀ u v,
        toZ ((gfold stepW gs (PEqualNP.Represents.oneEach u v)).getD a false) =
          vf n gs a u v := fun _ _ _ _ => rfl
    -- generic step: given a submodule description of the new wire, conclude
    suffices hnew : ∃ Ls' : List (Pr n), (∀ p ∈ Ls, p ∈ Ls') ∧
        Ls'.length ≤ 2 * (gs ++ [g]).countP nonlinear ∧
        (stepD D g = 0 → vf n (gs ++ [g]) (n + n + gs.length) ∈ Aff n) ∧
        (stepD D g ≤ 1 → vf n (gs ++ [g]) (n + n + gs.length) ∈ W Ls') by
      obtain ⟨Ls', hsub, hlen', h0, h1⟩ := hnew
      refine ⟨Ls', hlen', fun i => ?_⟩
      rw [hD']
      rcases lt_trichotomy i (n + n + gs.length) with h | h | h
      · rw [getD_app_left _ _ _ _ (by omega), vf_old n gs g i h]
        exact ⟨(hinv i).1, fun hd => W_mono hsub ((hinv i).2 hd)⟩
      · subst h
        rw [getD_snoc_eq _ _ _ _ hDlen.symm]
        exact ⟨h0, h1⟩
      · rw [getD_ge _ _ _ (by simp; omega), vf_beyond n _ i (by simp; omega)]
        exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    have hcount : (gs ++ [g]).countP nonlinear =
        gs.countP nonlinear + (if nonlinear g then 1 else 0) := by
      simp [List.countP_append]
    rw [vf_new]
    match hin : g.inputs, hg2 with
    | [], _ =>
      refine ⟨Ls, fun p hp => hp, by rw [hcount]; split_ifs <;> omega, fun _ => ?_, fun _ => ?_⟩
      · simp only [List.map_nil]; exact const_mem_Aff _
      · simp only [List.map_nil]; exact Aff_le_W _ (const_mem_Aff _)
    | [a], _ =>
      have hnl : nonlinear g = false := nonlinear_len (by rw [hin]; simp)
      have hdep : stepD D g = D.getD a 0 := by
        simp [stepD, hin, hnl]
      have heq : (fun u v => toZ (g.op.eval ([a].map fun a =>
          (gfold stepW gs (PEqualNP.Represents.oneEach u v)).getD a false))) =
          (fun _ _ => toZ (g.op.eval [false])) +
            (toZ (g.op.eval [false]) + toZ (g.op.eval [true])) • vf n gs a := by
        funext u v
        simp only [List.map_cons, List.map_nil, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [eval1]; rfl
      refine ⟨Ls, fun p hp => hp, by rw [hcount, hnl]; simpa using hlen, fun h => ?_, fun h => ?_⟩
      · rw [heq]; exact add_mem (const_mem_Aff _) (Submodule.smul_mem _ _ ((hinv a).1 (by omega)))
      · rw [heq]
        exact add_mem (Aff_le_W _ (const_mem_Aff _)) (Submodule.smul_mem _ _ ((hinv a).2 (by omega)))
    | [a, b], _ =>
      have heq : (fun u v => toZ (g.op.eval ([a, b].map fun a =>
          (gfold stepW gs (PEqualNP.Represents.oneEach u v)).getD a false))) =
          (fun _ _ => toZ (g.op.eval [false, false])) +
            (toZ (g.op.eval [false, false]) + toZ (g.op.eval [true, false])) • vf n gs a +
            (toZ (g.op.eval [false, false]) + toZ (g.op.eval [false, true])) • vf n gs b +
            toZ (xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
              (xor (g.op.eval [true, false]) (g.op.eval [true, true]))) •
              (vf n gs a * vf n gs b) := by
        funext u v
        simp only [List.map_cons, List.map_nil, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.mul_apply]
        rw [eval2]; rfl
      have hnlv : nonlinear g = xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) := by
        simp [nonlinear, hin]
      have hdep : stepD D g = max (D.getD a 0) (max (D.getD b 0) 0) + (nonlinear g).toNat := by
        simp [stepD, hin]
      rw [heq]
      cases hc : nonlinear g with
      | false =>
        rw [hc] at hnlv
        rw [← hnlv]
        rw [hc] at hdep
        have hd2 : stepD D g = max (D.getD a 0) (D.getD b 0) := by
          rw [hdep]; simp only [Bool.toNat_false, add_zero, Nat.max_zero]
        have hma := le_max_left (D.getD a 0) (D.getD b 0)
        have hmb := le_max_right (D.getD a 0) (D.getD b 0)
        simp only [toZ_false, zero_smul, add_zero]
        refine ⟨Ls, fun p hp => hp, by rw [hcount, hc]; simpa using hlen, fun h => ?_, fun h => ?_⟩
        · rw [hd2] at h
          exact add_mem (add_mem (const_mem_Aff _) (Submodule.smul_mem _ _
            ((hinv a).1 (by omega)))) (Submodule.smul_mem _ _ ((hinv b).1 (by omega)))
        · rw [hd2] at h
          exact add_mem (add_mem (Aff_le_W _ (const_mem_Aff _)) (Submodule.smul_mem _ _
            ((hinv a).2 (by omega)))) (Submodule.smul_mem _ _ ((hinv b).2 (by omega)))
      | true =>
        rw [hc] at hdep
        have hd2 : stepD D g = max (D.getD a 0) (D.getD b 0) + 1 := by
          rw [hdep]; simp only [Bool.toNat_true, Nat.max_zero]
        have hma := le_max_left (D.getD a 0) (D.getD b 0)
        have hmb := le_max_right (D.getD a 0) (D.getD b 0)
        rw [hd2]
        by_cases hab : D.getD a 0 = 0 ∧ D.getD b 0 = 0
        · obtain ⟨p, q, hpq⟩ := mul_mem_W ((hinv a).1 hab.1) ((hinv b).1 hab.2)
          refine ⟨Ls ++ [p, q], fun p hp => by simp [hp], ?_, fun h => by omega, fun h => ?_⟩
          · rw [hcount, hc]; simp; omega
          · have hW := W_mono (Ls := Ls) (Ls' := Ls ++ [p, q]) (fun p hp => by simp [hp])
            exact add_mem (add_mem (add_mem (Aff_le_W _ (const_mem_Aff _))
              (Submodule.smul_mem _ _ (hW ((hinv a).2 (by omega)))))
              (Submodule.smul_mem _ _ (hW ((hinv b).2 (by omega)))))
              (Submodule.smul_mem _ _ (hpq _ (by simp) (by simp)))
        · refine ⟨Ls, fun p hp => hp, by rw [hcount, hc]; simp; omega, fun h => by omega,
            fun h => by omega⟩
    | _ :: _ :: _ :: _, h => simp at h


theorem lower {n q t : ℕ} {G : Fin q → Fin n → Fin n → Bool} (h : fits n n q G t) :
    ∃ Ls : List (Pr n), Ls.length ≤ 2 * t ∧ ∀ j, (fun u v => toZ (G j u v)) ∈ W Ls := by
  obtain ⟨C, tap, hrb, hfan, hcnt, htap⟩ := h
  obtain ⟨Ls, hlen, hinv⟩ := lower_inv n C.gates hfan hrb
  refine ⟨Ls, by omega, fun j => ?_⟩
  have h1 := (hinv (tap j)).2 (by rw [← depths_eq]; exact (htap j).1)
  have h2 : (fun u v => toZ (G j u v)) = vf n C.gates (tap j) := by
    funext u v
    rw [← (htap j).2 u v]
    rfl
  rw [h2]; exact h1

/-! ## chains of linear gates -/

def chainG (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (base : ℕ) : ℕ → List Gate
  | 0 => [⟨if c then GateOp.and else GateOp.or, []⟩]
  | m+1 => chainG c wf cf base m ++
      (if cf m then [⟨GateOp.mod 2, [base + 2*m, wf m]⟩, ⟨GateOp.not, [base + 2*m + 1]⟩]
       else [⟨GateOp.and, [base + 2*m]⟩, ⟨GateOp.and, [base + 2*m + 1]⟩])

theorem chainG_length (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (base : ℕ) :
    ∀ m, (chainG c wf cf base m).length = 2*m+1
  | 0 => rfl
  | m+1 => by
    rw [chainG, List.length_append, chainG_length c wf cf base m]
    split_ifs <;> simp <;> omega

theorem app2 (P : List Gate) (g1 g2 : Gate) : P ++ [g1, g2] = P ++ [g1] ++ [g2] := by simp

theorem xor_gate (p w : Bool) :
    toZ (GateOp.eval GateOp.not [GateOp.eval (GateOp.mod 2) [p, w]]) = toZ p + toZ w := by
  cases p <;> cases w <;> decide

theorem chain_val (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (gs : List Gate) (x : List Bool)
    (base : ℕ) (hb : x.length + gs.length = base) :
    ∀ m, (∀ i < m, cf i = true → wf i < base) →
    toZ ((gfold stepW (gs ++ chainG c wf cf base m) x).getD (base + 2*m) false) =
      toZ c + ∑ i ∈ Finset.range m,
        if cf i then toZ ((gfold stepW gs x).getD (wf i) false) else 0
  | 0, _ => by
    simp only [chainG, gfold_snoc]
    rw [getD_snoc_eq _ _ _ _ (by rw [gfold_length]; omega)]
    cases c <;> rfl
  | m+1, hw => by
    have ih := chain_val c wf cf gs x base hb m (fun i hi => hw i (by omega))
    have hlen : (gfold stepW (gs ++ chainG c wf cf base m) x).length = base + 2*m + 1 := by
      rw [gfold_length, List.length_append, chainG_length]; omega
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    simp only [chainG]
    split_ifs with hc
    · rw [app2, ← List.append_assoc, ← List.append_assoc, gfold_snoc, gfold_snoc,
        getD_snoc_eq _ _ _ _ (by simp [hlen]; omega)]
      simp only [stepW, List.map_cons, List.map_nil]
      rw [getD_snoc_eq _ _ _ _ (by rw [hlen])]
      rw [gfold_getD_prefix stepW gs (chainG c wf cf base m) x (wf m) false
        (by have := hw m (by omega) hc; omega)]
      have := xor_gate ((gfold stepW (gs ++ chainG c wf cf base m) x).getD (base + 2 * m) false)
        ((gfold stepW gs x).getD (wf m) false)
      rw [← this]
    · rw [app2, ← List.append_assoc, ← List.append_assoc, gfold_snoc, gfold_snoc,
        getD_snoc_eq _ _ _ _ (by simp [hlen]; omega)]
      simp only [stepW, List.map_cons, List.map_nil]
      rw [getD_snoc_eq _ _ _ _ (by rw [hlen])]
      simp [GateOp.eval]

theorem nl_mod2 (a b : ℕ) : nonlinear ⟨GateOp.mod 2, [a, b]⟩ = false := rfl
theorem nl_and2 (a b : ℕ) : nonlinear ⟨GateOp.and, [a, b]⟩ = true := rfl

theorem chain_depth (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (gs : List Gate) (init : List ℕ)
    (base : ℕ) (hb : init.length + gs.length = base) (D : ℕ) :
    ∀ m, (∀ i < m, cf i = true → wf i < base ∧ (gfold stepD gs init).getD (wf i) 0 ≤ D) →
    (gfold stepD (gs ++ chainG c wf cf base m) init).getD (base + 2*m) 0 ≤ D
  | 0, _ => by
    simp only [chainG, gfold_snoc]
    rw [getD_snoc_eq _ _ _ _ (by rw [gfold_length]; omega)]
    simp [stepD, nonlinear]
  | m+1, hw => by
    have ih := chain_depth c wf cf gs init base hb D m (fun i hi => hw i (by omega))
    have hlen : (gfold stepD (gs ++ chainG c wf cf base m) init).length = base + 2*m + 1 := by
      rw [gfold_length, List.length_append, chainG_length]; omega
    simp only [chainG]
    split_ifs with hc
    · rw [app2, ← List.append_assoc, ← List.append_assoc, gfold_snoc, gfold_snoc,
        getD_snoc_eq _ _ _ _ (by simp [hlen]; omega)]
      have hw' := hw m (by omega) hc
      simp only [stepD, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      rw [getD_snoc_eq _ _ _ _ (by rw [hlen])]
      rw [gfold_getD_prefix stepD gs (chainG c wf cf base m) init (wf m) 0 (by omega)]
      rw [nl_mod2, nonlinear_len (by simp)]
      simp only [Bool.toNat_false, add_zero, Nat.max_zero]
      exact max_le ih hw'.2
    · rw [app2, ← List.append_assoc, ← List.append_assoc, gfold_snoc, gfold_snoc,
        getD_snoc_eq _ _ _ _ (by simp [hlen]; omega)]
      simp only [stepD, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      rw [getD_snoc_eq _ _ _ _ (by rw [hlen])]
      rw [nonlinear_len (by simp), nonlinear_len (by simp)]
      simp only [Bool.toNat_false, add_zero, Nat.max_zero]
      exact ih

theorem chain_count (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (base : ℕ) :
    ∀ m, (chainG c wf cf base m).countP nonlinear = 0
  | 0 => by simp [chainG, nonlinear]
  | m+1 => by
    simp only [chainG]
    rw [List.countP_append, chain_count c wf cf base m]
    split_ifs
    · rfl
    · rfl

theorem chain_fan (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (base : ℕ) :
    ∀ m, ∀ g ∈ chainG c wf cf base m, g.inputs.length ≤ 2
  | 0 => by simp [chainG]
  | m+1 => by
    intro g hg
    simp only [chainG, List.mem_append] at hg
    rcases hg with hg | hg
    · exact chain_fan c wf cf base m g hg
    · split_ifs at hg <;> simp at hg <;> rcases hg with rfl | rfl <;> simp

theorem chain_RB (c : Bool) (wf : ℕ → ℕ) (cf : ℕ → Bool) (N : ℕ) (gs : List Gate)
    (h : RB N gs) (base : ℕ) (hb : N + gs.length = base) :
    ∀ m, (∀ i < m, cf i = true → wf i < base) → RB N (gs ++ chainG c wf cf base m)
  | 0, _ => by
    simp only [chainG]
    rw [RB_snoc]; exact ⟨h, by simp⟩
  | m+1, hw => by
    have ih := chain_RB c wf cf N gs h base hb m (fun i hi => hw i (by omega))
    have hlen : (gs ++ chainG c wf cf base m).length = gs.length + 2*m + 1 := by
      rw [List.length_append, chainG_length]; omega
    simp only [chainG]
    split_ifs with hc
    · rw [app2, ← List.append_assoc, ← List.append_assoc, RB_snoc, RB_snoc]
      have := hw m (by omega) hc
      refine ⟨⟨ih, ?_⟩, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        simp only [List.length_append, List.length_singleton, chainG_length]
        omega
      · intro i hi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        simp only [List.length_append, List.length_singleton, chainG_length]
        omega
    · rw [app2, ← List.append_assoc, ← List.append_assoc, RB_snoc, RB_snoc]
      refine ⟨⟨ih, ?_⟩, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        simp only [List.length_append, List.length_singleton, chainG_length]
        omega
      · intro i hi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        simp only [List.length_append, List.length_singleton, chainG_length]
        omega


/-! ## blocks of products -/

def blk (N : ℕ) (ca cb : ℕ → ℕ → Bool) : ℕ → List Gate
  | 0 => []
  | j+1 => blk N ca cb j ++ chainG false id (ca j) (N + (blk N ca cb j).length) N ++
      chainG false id (cb j) (N + (blk N ca cb j).length + (2*N+1)) N ++
      [⟨GateOp.and, [N + (blk N ca cb j).length + 2*N,
        N + (blk N ca cb j).length + (2*N+1) + 2*N]⟩]

theorem blk_length (N : ℕ) (ca cb : ℕ → ℕ → Bool) :
    ∀ j, (blk N ca cb j).length = j * (4*N+3)
  | 0 => by simp [blk]
  | j+1 => by
    simp only [blk, List.length_append, chainG_length, blk_length N ca cb j,
      List.length_singleton]
    ring

def lin (cf : ℕ → Bool) (N : ℕ) (x : List Bool) : ZMod 2 :=
  ∑ i ∈ Finset.range N, if cf i then toZ (x.getD i false) else 0

theorem lin_eq (cf : ℕ → Bool) (N : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = N) :
    (∑ i ∈ Finset.range N, if cf i then toZ ((gfold stepW gs x).getD (id i) false) else 0) =
      lin cf N x := by
  unfold lin
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [id, gfold_getD_init _ _ _ _ _ (by omega)]

theorem blk_val (N : ℕ) (ca cb : ℕ → ℕ → Bool) (x : List Bool) (hx : x.length = N) :
    ∀ j, ∀ j' < j,
      toZ ((gfold stepW (blk N ca cb j) x).getD (N + j'*(4*N+3) + 4*N+2) false) =
        lin (ca j') N x * lin (cb j') N x
  | 0 => fun j' h => absurd h (Nat.not_lt_zero _)
  | j+1 => by
    intro j' hj'
    have ih := blk_val N ca cb x hx j
    have hB := blk_length N ca cb j
    simp only [blk]
    generalize blk N ca cb j = B at ih hB ⊢
    rcases Nat.lt_or_ge j' j with h | h
    · rw [List.append_assoc, List.append_assoc,
        gfold_getD_prefix _ B _ _ _ _ (by rw [hx, hB]; nlinarith)]
      exact ih j' h
    · have hj : j' = j := by omega
      subst hj
      have hl1 : (B ++ chainG false id (ca j') (N + B.length) N).length = B.length + (2*N+1) := by
        rw [List.length_append, chainG_length]
      rw [gfold_snoc, getD_snoc_eq _ _ _ _ (by
        rw [gfold_length, List.length_append, hl1, chainG_length, hx, hB]; ring)]
      simp only [stepW, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id]
      rw [toZ_and]
      congr 1
      · rw [gfold_getD_prefix _ _ _ _ _ _ (by rw [hl1, hx]; omega)]
        rw [chain_val false id (ca j') B x (N + B.length) (by rw [hx]) N
          (fun i hi _ => by simp; omega)]
        rw [lin_eq _ _ _ _ hx]; simp
      · rw [chain_val false id (cb j') _ x (N + B.length + (2*N+1)) (by rw [hx, hl1]; ring) N
          (fun i hi _ => by simp; omega)]
        rw [lin_eq _ _ _ _ hx]; simp

theorem blk_depth (N : ℕ) (ca cb : ℕ → ℕ → Bool) :
    ∀ j, ∀ j' < j,
      (gfold stepD (blk N ca cb j) (List.replicate N 0)).getD (N + j'*(4*N+3) + 4*N+2) 0 ≤ 1
  | 0 => fun j' h => absurd h (Nat.not_lt_zero _)
  | j+1 => by
    intro j' hj'
    have ih := blk_depth N ca cb j
    have hB := blk_length N ca cb j
    simp only [blk]
    generalize blk N ca cb j = B at ih hB ⊢
    have hinit : (List.replicate N 0).length = N := by simp
    rcases Nat.lt_or_ge j' j with h | h
    · rw [List.append_assoc, List.append_assoc,
        gfold_getD_prefix _ B _ _ _ _ (by rw [hinit, hB]; nlinarith)]
      exact ih j' h
    · have hj : j' = j := by omega
      subst hj
      have hl1 : (B ++ chainG false id (ca j') (N + B.length) N).length = B.length + (2*N+1) := by
        rw [List.length_append, chainG_length]
      rw [gfold_snoc, getD_snoc_eq _ _ _ _ (by
        rw [gfold_length, List.length_append, hl1, chainG_length, hinit, hB]; ring)]
      simp only [stepD, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nl_and2,
        Bool.toNat_true, Nat.max_zero]
      have hz : ∀ (gs : List Gate) (i : ℕ), i < N →
          (gfold stepD gs (List.replicate N 0)).getD i 0 ≤ 0 := by
        intro gs i hi
        rw [gfold_getD_init _ _ _ _ _ (by simpa using hi)]
        simp [List.getElem?_replicate, hi]
      have h1 : (gfold stepD (B ++ chainG false id (ca j') (N + B.length) N ++
          chainG false id (cb j') (N + B.length + (2 * N + 1)) N) (List.replicate N 0)).getD
          (N + B.length + 2 * N) 0 ≤ 0 := by
        rw [gfold_getD_prefix _ _ _ _ _ _ (by rw [hl1, hinit]; omega)]
        exact chain_depth false id (ca j') B _ (N + B.length) (by rw [hinit]) 0 N
          (fun i hi _ => ⟨by simp; omega, hz B i hi⟩)
      have h2 : (gfold stepD (B ++ chainG false id (ca j') (N + B.length) N ++
          chainG false id (cb j') (N + B.length + (2 * N + 1)) N) (List.replicate N 0)).getD
          (N + B.length + (2 * N + 1) + 2 * N) 0 ≤ 0 :=
        chain_depth false id (cb j') _ _ (N + B.length + (2*N+1)) (by rw [hinit, hl1]; ring) 0 N
          (fun i hi _ => ⟨by simp; omega, hz _ i hi⟩)
      omega

theorem blk_count (N : ℕ) (ca cb : ℕ → ℕ → Bool) :
    ∀ j, (blk N ca cb j).countP nonlinear = j
  | 0 => rfl
  | j+1 => by
    simp only [blk, List.countP_append, chain_count, blk_count N ca cb j]
    simp [nl_and2]

theorem blk_fan (N : ℕ) (ca cb : ℕ → ℕ → Bool) :
    ∀ j, ∀ g ∈ blk N ca cb j, g.inputs.length ≤ 2
  | 0 => by simp [blk]
  | j+1 => by
    intro g hg
    simp only [blk, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | hg) | rfl
    · exact blk_fan N ca cb j g hg
    · exact chain_fan _ _ _ _ _ g hg
    · exact chain_fan _ _ _ _ _ g hg
    · simp

theorem blk_RB (N : ℕ) (ca cb : ℕ → ℕ → Bool) : ∀ j, RB N (blk N ca cb j)
  | 0 => by intro j hj; simp [blk] at hj
  | j+1 => by
    have ih := blk_RB N ca cb j
    simp only [blk]
    generalize blk N ca cb j = B at ih ⊢
    have h1 := chain_RB false id (ca j) N B ih (N + B.length) rfl N (fun i hi _ => by simp; omega)
    have hl1 : (B ++ chainG false id (ca j) (N + B.length) N).length = B.length + (2*N+1) := by
      rw [List.length_append, chainG_length]
    have h2 := chain_RB false id (cb j) N _ h1 (N + B.length + (2*N+1)) (by rw [hl1]; ring) N
      (fun i hi _ => by simp; omega)
    rw [RB_snoc]
    refine ⟨h2, fun i hi => ?_⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    simp only [List.length_append, chainG_length]
    omega

/-! ## the full circuit -/

def wfF (N t : ℕ) (i : ℕ) : ℕ := if i < t then N + i*(4*N+3) + 4*N+2 else i - t
def cfF (t : ℕ) (cg : ℕ → Bool) (i : ℕ) : Bool := if i < t then true else cg (i - t)

def fullC (N t : ℕ) (ca cb : ℕ → ℕ → Bool) (cg : ℕ → Bool) : List Gate :=
  blk N ca cb t ++ chainG false (wfF N t) (cfF t cg) (N + t*(4*N+3)) (t + N)

def tapF (N t : ℕ) : ℕ := N + t*(4*N+3) + 2*(t+N)

theorem wfF_lt (N t : ℕ) (cg : ℕ → Bool) : ∀ i < t + N, cfF t cg i = true →
    wfF N t i < N + t*(4*N+3) := by
  intro i hi _
  unfold wfF
  split_ifs with h
  · nlinarith
  · have : i - t < N := by omega
    nlinarith

theorem full_val (N t : ℕ) (ca cb : ℕ → ℕ → Bool) (cg : ℕ → Bool) (x : List Bool)
    (hx : x.length = N) :
    toZ ((gfold stepW (fullC N t ca cb cg) x).getD (tapF N t) false) =
      (∑ j ∈ Finset.range t, lin (ca j) N x * lin (cb j) N x) + lin cg N x := by
  unfold fullC tapF
  rw [chain_val false (wfF N t) (cfF t cg) _ x (N + t*(4*N+3)) (by rw [hx, blk_length]) (t + N)
    (wfF_lt N t cg)]
  rw [Finset.sum_range_add, toZ_false, zero_add]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    simp only [cfF, wfF, if_pos hj]
    exact blk_val N ca cb x hx t j hj
  · unfold lin
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have h1 : ¬ t + i < t := by omega
    simp only [cfF, wfF, if_neg h1, Nat.add_sub_cancel_left]
    rw [gfold_getD_init _ _ _ _ _ (by omega)]

theorem full_depth (N t : ℕ) (ca cb : ℕ → ℕ → Bool) (cg : ℕ → Bool) :
    (gfold stepD (fullC N t ca cb cg) (List.replicate N 0)).getD (tapF N t) 0 ≤ 1 := by
  unfold fullC tapF
  refine chain_depth false (wfF N t) (cfF t cg) _ _ (N + t*(4*N+3))
    (by rw [blk_length]; simp) 1 (t + N) (fun i hi hc => ⟨wfF_lt N t cg i hi hc, ?_⟩)
  unfold wfF
  split_ifs with h
  · exact blk_depth N ca cb t i h
  · rw [gfold_getD_init _ _ _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp

theorem full_count (N t : ℕ) (ca cb : ℕ → ℕ → Bool) (cg : ℕ → Bool) :
    (fullC N t ca cb cg).countP nonlinear = t := by
  unfold fullC
  rw [List.countP_append, blk_count, chain_count, Nat.add_zero]

theorem full_fan (N t : ℕ) (ca cb : ℕ → ℕ → Bool) (cg : ℕ → Bool) :
    ∀ g ∈ fullC N t ca cb cg, g.inputs.length ≤ 2 := by
  intro g hg
  unfold fullC at hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · exact blk_fan N ca cb t g hg
  · exact chain_fan _ _ _ _ _ g hg

theorem full_RB (N t : ℕ) (ca cb : ℕ → ℕ → Bool) (cg : ℕ → Bool) :
    RB N (fullC N t ca cb cg) := by
  unfold fullC
  exact chain_RB false (wfF N t) (cfF t cg) N _ (blk_RB N ca cb t) _ (by rw [blk_length])
    (t + N) (wfF_lt N t cg)

/-! ## evaluation on one-hot inputs and the decomposition -/

theorem lin_onehot (n : ℕ) (cf : ℕ → Bool) (u v : Fin n) :
    lin cf (n+n) (PEqualNP.Represents.oneEach u v) = toZ (cf u.val) + toZ (cf (n + v.val)) := by
  unfold lin
  have : ∀ i, (if cf i then toZ ((PEqualNP.Represents.oneEach u v).getD i false) else 0) =
      (if u.val = i then toZ (cf i) else 0) + (if n + v.val = i then toZ (cf i) else 0) := by
    intro i
    rw [toZ_onehot]
    by_cases h1 : u.val = i
    · have h2 : ¬ n + v.val = i := by omega
      rw [if_pos h1, if_neg h2, decide_eq_true h1.symm, decide_eq_false (Ne.symm h2)]
      cases cf i <;> simp
    · by_cases h2 : n + v.val = i
      · rw [if_neg h1, if_pos h2, decide_eq_false (Ne.symm h1), decide_eq_true h2.symm]
        cases cf i <;> simp
      · rw [if_neg h1, if_neg h2, decide_eq_false (Ne.symm h1), decide_eq_false (Ne.symm h2)]
        cases cf i <;> simp
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  rw [if_pos (by simp only [Finset.mem_range]; omega),
    if_pos (by simp only [Finset.mem_range]; omega)]

def fN (n : ℕ) (f : Fin n → Fin n → Bool) (i v : ℕ) : ZMod 2 :=
  if h : i < n ∧ v < n then toZ (f ⟨i, h.1⟩ ⟨v, h.2⟩) else 0

def R2 (n : ℕ) (f : Fin n → Fin n → Bool) (i v : ℕ) : ZMod 2 :=
  fN n f i v + fN n f i 0 + fN n f 0 v + fN n f 0 0

def caF (n : ℕ) (f : Fin n → Fin n → Bool) (j w : ℕ) : Bool :=
  if w < n then decide (w = 2*j+1) else decide (R2 n f (2*j+2) (w - n) = 1)

def cbF (n : ℕ) (f : Fin n → Fin n → Bool) (j w : ℕ) : Bool :=
  if w < n then decide (w = 2*j+2) else decide (R2 n f (2*j+1) (w - n) = 1)

def dF (n t : ℕ) (f : Fin n → Fin n → Bool) (v : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range t, R2 n f (2*j+2) v * R2 n f (2*j+1) v

def cgF (n t : ℕ) (f : Fin n → Fin n → Bool) (w : ℕ) : Bool :=
  if w < n then decide (fN n f w 0 = 1)
  else decide (dF n t f (w - n) + fN n f 0 (w - n) + fN n f 0 0 = 1)

theorem key_sum (t u : ℕ) (hu : u ≤ 2*t) (R : ℕ → ℕ → ZMod 2) (v : ℕ) (hR0 : R 0 v = 0) :
    ∑ j ∈ Finset.range t, (toZ (decide (u = 2*j+1)) + R (2*j+2) v) *
      (toZ (decide (u = 2*j+2)) + R (2*j+1) v)
      = R u v + ∑ j ∈ Finset.range t, R (2*j+2) v * R (2*j+1) v := by
  have hterm : ∀ j, (toZ (decide (u = 2*j+1)) + R (2*j+2) v) *
      (toZ (decide (u = 2*j+2)) + R (2*j+1) v) =
      (toZ (decide (u = 2*j+1)) + toZ (decide (u = 2*j+2))) * R u v +
        R (2*j+2) v * R (2*j+1) v := by
    intro j
    by_cases h1 : u = 2*j+1
    · have h2 : ¬ u = 2*j+2 := by omega
      rw [decide_eq_true h1, decide_eq_false h2, h1]; simp only [toZ_true, toZ_false]; ring
    · by_cases h2 : u = 2*j+2
      · rw [decide_eq_false h1, decide_eq_true h2, h2]; simp only [toZ_true, toZ_false]; ring
      · rw [decide_eq_false h1, decide_eq_false h2]; simp only [toZ_false]; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  rcases Nat.eq_zero_or_pos u with h0 | h0
  · subst h0; rw [hR0]; simp
  · rw [Finset.sum_eq_single ((u-1)/2)]
    · by_cases h1 : u = 2*((u-1)/2)+1
      · rw [decide_eq_true h1, decide_eq_false (by omega)]; simp
      · rw [decide_eq_false h1, decide_eq_true (by omega)]; simp
    · intro j _ hj
      rw [decide_eq_false (by omega), decide_eq_false (by omega)]; simp
    · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

theorem upper (k t : ℕ) (f : Fin (k+1) → Fin (k+1) → Bool) (hk : k ≤ 2*t) :
    fits (k+1) (k+1) 1 (fun _ => f) t := by
  refine ⟨⟨fullC ((k+1)+(k+1)) t (caF (k+1) f) (cbF (k+1) f) (cgF (k+1) t f), 0⟩,
    fun _ => tapF ((k+1)+(k+1)) t, full_RB _ _ _ _ _, full_fan _ _ _ _ _,
    by rw [full_count], fun _ => ⟨full_depth _ _ _ _ _, ?_⟩⟩
  intro u v
  apply toZ_inj
  show toZ ((gfold stepW _ (PEqualNP.Represents.oneEach u v)).getD _ false) = _
  rw [full_val _ _ _ _ _ _ (oneEach_length u v)]
  rw [Finset.sum_congr rfl (fun j _ => by rw [lin_onehot, lin_onehot]), lin_onehot]
  have hu : u.val < k + 1 := u.isLt
  have hv : v.val < k + 1 := v.isLt
  have hca1 : ∀ j, toZ (caF (k+1) f j u.val) = toZ (decide (u.val = 2*j+1)) := by
    intro j; unfold caF; rw [if_pos hu]
  have hca2 : ∀ j, toZ (caF (k+1) f j (k + 1 + v.val)) = R2 (k+1) f (2*j+2) v.val := by
    intro j; unfold caF; rw [if_neg (by omega), Nat.add_sub_cancel_left, toZ_decide_one]
  have hcb1 : ∀ j, toZ (cbF (k+1) f j u.val) = toZ (decide (u.val = 2*j+2)) := by
    intro j; unfold cbF; rw [if_pos hu]
  have hcb2 : ∀ j, toZ (cbF (k+1) f j (k + 1 + v.val)) = R2 (k+1) f (2*j+1) v.val := by
    intro j; unfold cbF; rw [if_neg (by omega), Nat.add_sub_cancel_left, toZ_decide_one]
  have hcg1 : toZ (cgF (k+1) t f u.val) = fN (k+1) f u.val 0 := by
    unfold cgF; rw [if_pos hu, toZ_decide_one]
  have hcg2 : toZ (cgF (k+1) t f (k + 1 + v.val)) =
      dF (k+1) t f v.val + fN (k+1) f 0 v.val + fN (k+1) f 0 0 := by
    unfold cgF; rw [if_neg (by omega), Nat.add_sub_cancel_left, toZ_decide_one]
  simp only [hca1, hca2, hcb1, hcb2, hcg1, hcg2]
  have hR0 : R2 (k+1) f 0 v.val = 0 := by
    have h : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
    exact h _ _
  rw [key_sum t u.val (by omega) (R2 (k+1) f) v.val hR0]
  have hf : toZ (f u v) = fN (k+1) f u.val v.val := by
    unfold fN; rw [dif_pos ⟨hu, hv⟩]
  rw [hf]
  have hdF : dF (k+1) t f v.val =
      ∑ j ∈ Finset.range t, R2 (k+1) f (2*j+2) v.val * R2 (k+1) f (2*j+1) v.val := rfl
  rw [hdF]
  generalize (∑ j ∈ Finset.range t, R2 (k+1) f (2*j+2) v.val * R2 (k+1) f (2*j+1) v.val) = Z
  simp only [R2]
  linear_combination (fN (k+1) f u.val 0 + fN (k+1) f 0 v.val + fN (k+1) f 0 0 + Z) *
    two_eq_zero'


/-! ## the field part -/

theorem W_explicit {n : ℕ} {Ls : List (Pr n)} {x : Fn n} (h : x ∈ W Ls) :
    ∃ a ∈ Aff n, ∃ c : Fin Ls.length → ZMod 2,
      x = a + ∑ q, c q • tens (Ls.get q) := by
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp h
  have hset : {f | ∃ p ∈ Ls, f = tens p} = Set.range (fun q : Fin Ls.length => tens (Ls.get q)) := by
    ext f
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨q, rfl⟩ := List.get_of_mem hp
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨_, List.get_mem _ _, rfl⟩
  rw [hset, Submodule.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, hc⟩ := hz
  exact ⟨a, ha, c, by rw [hc]⟩

def Elin (k : ℕ) : Fn (k+1) →ₗ[ZMod 2] (Fin k → Fin k → ZMod 2) where
  toFun f := fun i j => f i.succ j.succ - f i.succ 0 - f 0 j.succ + f 0 0
  map_add' f g := by funext i j; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Elin_apply (k : ℕ) (f : Fn (k+1)) (i j : Fin k) :
    Elin k f i j = f i.succ j.succ - f i.succ 0 - f 0 j.succ + f 0 0 := rfl

theorem Elin_aff {k : ℕ} {a : Fn (k+1)} (ha : a ∈ Aff (k+1)) : Elin k a = 0 := by
  obtain ⟨α, β, h⟩ := ha
  funext i j
  rw [Elin_apply, h, h, h, h]
  simp only [Pi.zero_apply]; ring

theorem Elin_decomp {k : ℕ} {Ls : List (Pr (k+1))} (a : Fn (k+1)) (ha : a ∈ Aff (k+1))
    (c : Fin Ls.length → ZMod 2) (i j : Fin k) :
    Elin k (a + ∑ q, c q • tens (Ls.get q)) i j =
      ∑ q, c q * (((Ls.get q).1 i.succ - (Ls.get q).1 0) *
        ((Ls.get q).2 j.succ - (Ls.get q).2 0)) := by
  rw [map_add, Elin_aff ha, zero_add, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Elin_apply]; simp only [tens]; ring

section field

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]

def pairing (bit : K →ₗ[ZMod 2] ZMod 2) : K →ₗ[ZMod 2] Module.Dual (ZMod 2) K :=
  (LinearMap.mul (ZMod 2) K).compr₂ bit

theorem pairing_apply (bit : K →ₗ[ZMod 2] ZMod 2) (c b : K) :
    pairing bit c b = bit (c * b) := rfl

theorem pairing_inj (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    Function.Injective (pairing bit) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hne
  apply hbit
  ext y
  have := LinearMap.congr_fun hc (c⁻¹ * y)
  rw [pairing_apply, ← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
  simpa using this

theorem pairing_surj (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    Function.Surjective (pairing bit) := by
  have H : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) (Module.Dual (ZMod 2) K) :=
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := K)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mp (pairing_inj bit hbit)

theorem eq_zero_of_basis {k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) (x : K) (h : ∀ j, bit (x * basis j) = 0) :
    x = 0 := by
  apply pairing_inj bit hbit
  rw [map_zero]
  exact basis.ext (fun j => by rw [pairing_apply, h j, LinearMap.zero_apply])

theorem sum_tri (L : ℕ) : 2 * ∑ q : Fin L, (q.val + 1) = L * (L + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => q + 1)]
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem toZ_decide_ne (b : ZMod 2) : toZ (decide (b ≠ 0)) = b := by
  revert b; decide

theorem toZ_parity {α : Type} (S : Finset α) (p : α → Bool) :
    toZ (((S.filter (fun i => p i)).card % 2) == 1) = ∑ i ∈ S, toZ (p i) := by
  have h1 : ∑ i ∈ S, toZ (p i) = ((S.filter (fun i => p i)).card : ZMod 2) := by
    rw [← Finset.sum_boole]; rfl
  rw [h1]
  generalize (S.filter (fun i => p i)).card = c
  rw [← ZMod.natCast_mod c 2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> rfl

theorem core (k : ℕ) (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (point : Fin (k+1) → K) (hp0 : point 0 = 0)
    (hps : ∀ i : Fin k, point i.succ = basis i)
    (g s : ℕ) (T : Fin g → Fin (k+1) → Fin (k+1) → Bool) (hT : fits (k+1) (k+1) g T s) :
    ∃ V : Submodule (ZMod 2) K, k ≤ Module.finrank (ZMod 2) V + s*(2*s+1) ∧
      ∀ w ∈ V, w ≠ 0 → ∀ (S : Finset (Fin g)) (t : ℕ),
        (fits (k+1) (k+1) 1 (fun _ x y => xor (decide (bit (w⁻¹ * point x * point y) ≠ 0))
          (((S.filter (fun i => T i x y)).card % 2) == 1)) t ↔ k ≤ 2*t) := by
  obtain ⟨Ls, hlen, hmem⟩ := lower hT
  let lam : Fin Ls.length → (K →ₗ[ZMod 2] ZMod 2) := fun q =>
    basis.constr (ZMod 2) (fun i => (Ls.get q).1 i.succ - (Ls.get q).1 0)
  let mu : Fin Ls.length → (K →ₗ[ZMod 2] ZMod 2) := fun q =>
    basis.constr (ZMod 2) (fun j => (Ls.get q).2 j.succ - (Ls.get q).2 0)
  have hlam : ∀ q i, lam q (basis i) = (Ls.get q).1 i.succ - (Ls.get q).1 0 := fun q i =>
    Module.Basis.constr_basis _ _ _ _
  have hmu : ∀ q j, mu q (basis j) = (Ls.get q).2 j.succ - (Ls.get q).2 0 := fun q j =>
    Module.Basis.constr_basis _ _ _ _
  choose ρ hρ using fun q => pairing_surj bit hbit (mu q)
  have hρbit : ∀ q j, bit (ρ q * basis j) = (Ls.get q).2 j.succ - (Ls.get q).2 0 := by
    intro q j
    rw [← pairing_apply, hρ q, hmu]
  let Φ : K →ₗ[ZMod 2] ((Σ q : Fin Ls.length, Fin (q.val + 1)) → ZMod 2) :=
    LinearMap.pi (fun qp => (lam qp.1).comp
      (LinearMap.mulRight (ZMod 2) (ρ ⟨qp.2.val, lt_of_lt_of_le qp.2.isLt qp.1.isLt⟩)))
  have hΦ : ∀ w ∈ LinearMap.ker Φ, ∀ q p : Fin Ls.length, p ≤ q → lam q (w * ρ p) = 0 := by
    intro w hw q p hpq
    have := congrFun (LinearMap.mem_ker.mp hw) ⟨q, ⟨p.val, by have := hpq; omega⟩⟩
    simpa [Φ] using this
  refine ⟨LinearMap.ker Φ, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 : Module.finrank (ZMod 2) (LinearMap.range Φ) ≤
        Fintype.card (Σ q : Fin Ls.length, Fin (q.val + 1)) := by
      have := Submodule.finrank_le (LinearMap.range Φ)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    have h3 : Module.finrank (ZMod 2) K = k := by
      rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]
    have h4 : Fintype.card (Σ q : Fin Ls.length, Fin (q.val + 1)) =
        ∑ q : Fin Ls.length, (q.val + 1) := by
      simp [Fintype.card_sigma]
    have h5 := sum_tri Ls.length
    have h6 : Ls.length * (Ls.length + 1) ≤ (2*s) * (2*s+1) := Nat.mul_le_mul hlen (by omega)
    have h7 : (2*s) * (2*s+1) = 2 * (s * (2*s+1)) := by ring
    rw [h4] at h2
    rw [h3] at h1
    linarith
  · intro w hw hw0 S t
    constructor
    · intro hfit
      by_contra hlt
      push_neg at hlt
      obtain ⟨Ls', hlen', hmem'⟩ := lower hfit
      have hres := hmem' 0
      have hTsum : (fun x y => ∑ i ∈ S, toZ (T i x y) : Fn (k+1)) ∈ W Ls := by
        have : (fun x y => ∑ i ∈ S, toZ (T i x y) : Fn (k+1)) =
            ∑ i ∈ S, (fun x y => toZ (T i x y)) := by
          funext x y; simp [Finset.sum_apply]
        rw [this]; exact Submodule.sum_mem _ (fun i _ => hmem i)
      obtain ⟨a1, ha1, c1, he1⟩ := W_explicit hTsum
      obtain ⟨a2, ha2, c2, he2⟩ := W_explicit hres
      -- the matrix of the field product
      have hM : ∀ i j : Fin k, bit (w⁻¹ * basis i * basis j) =
          ∑ q, c2 q * (((Ls'.get q).1 i.succ - (Ls'.get q).1 0) *
            ((Ls'.get q).2 j.succ - (Ls'.get q).2 0)) -
          ∑ p, c1 p * (((Ls.get p).1 i.succ - (Ls.get p).1 0) *
            ((Ls.get p).2 j.succ - (Ls.get p).2 0)) := by
        intro i j
        rw [← Elin_decomp a2 ha2 c2 i j, ← Elin_decomp a1 ha1 c1 i j, ← he1, ← he2]
        simp only [Elin_apply]
        simp only [toZ_xor, toZ_decide_ne, toZ_parity, hp0, hps, mul_zero, zero_mul, map_zero]
        ring
      -- extend to all of K in the first variable
      have hext : ∀ (a : K) (j : Fin k), bit (w⁻¹ * a * basis j) =
          ∑ q, (c2 q * ((Ls'.get q).2 j.succ - (Ls'.get q).2 0)) *
            basis.constr (ZMod 2) (fun i => (Ls'.get q).1 i.succ - (Ls'.get q).1 0) a -
          ∑ p, (c1 p * ((Ls.get p).2 j.succ - (Ls.get p).2 0)) * lam p a := by
        intro a j
        let F1 : K →ₗ[ZMod 2] ZMod 2 :=
          bit.comp ((LinearMap.mulRight (ZMod 2) (basis j)).comp (LinearMap.mulLeft (ZMod 2) w⁻¹))
        let F2 : K →ₗ[ZMod 2] ZMod 2 :=
          ∑ q, (c2 q * ((Ls'.get q).2 j.succ - (Ls'.get q).2 0)) •
            basis.constr (ZMod 2) (fun i => (Ls'.get q).1 i.succ - (Ls'.get q).1 0) -
          ∑ p, (c1 p * ((Ls.get p).2 j.succ - (Ls.get p).2 0)) • lam p
        have hF : F1 = F2 := by
          refine basis.ext (fun i => ?_)
          simp only [F1, F2, LinearMap.comp_apply, LinearMap.mulLeft_apply,
            LinearMap.mulRight_apply, LinearMap.sub_apply, LinearMap.coe_sum, LinearMap.sum_apply, Finset.sum_apply,
            LinearMap.smul_apply, smul_eq_mul, Module.Basis.constr_basis, hlam]
          rw [hM i j]
          congr 1
          · refine Finset.sum_congr rfl (fun q _ => ?_); ring
          · refine Finset.sum_congr rfl (fun q _ => ?_); ring
        have := LinearMap.congr_fun hF a
        simpa [F1, F2, LinearMap.sub_apply, LinearMap.coe_sum, LinearMap.sum_apply, Finset.sum_apply,
          LinearMap.smul_apply, smul_eq_mul] using this
      -- a nonzero vector killed by all the residual functionals
      let Λ : K →ₗ[ZMod 2] (Fin Ls'.length → ZMod 2) := LinearMap.pi (fun q =>
        basis.constr (ZMod 2) (fun i => (Ls'.get q).1 i.succ - (Ls'.get q).1 0))
      have hker : LinearMap.ker Λ ≠ ⊥ := by
        apply LinearMap.ker_ne_bot_of_finrank_lt
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
          Module.finrank_eq_card_basis basis, Fintype.card_fin]
        omega
      obtain ⟨a, haK, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
      have hΛ : ∀ q, basis.constr (ZMod 2) (fun i => (Ls'.get q).1 i.succ - (Ls'.get q).1 0) a
          = 0 := by
        intro q
        have := congrFun (LinearMap.mem_ker.mp haK) q
        simpa [Λ] using this
      set d : Fin Ls.length → ZMod 2 := fun p => c1 p * lam p a with hd
      have hkey : ∀ j, bit (w⁻¹ * a * basis j) =
          -∑ p, d p * ((Ls.get p).2 j.succ - (Ls.get p).2 0) := by
        intro j
        rw [hext a j]
        simp only [hΛ, mul_zero, Finset.sum_const_zero, zero_sub, hd]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_); ring
      have hz : w⁻¹ * a + ∑ p, d p • ρ p = 0 := by
        apply eq_zero_of_basis basis bit hbit
        intro j
        rw [add_mul, Finset.sum_mul, map_add, map_sum]
        simp only [smul_mul_assoc, map_smul, smul_eq_mul, hρbit, hkey]
        ring
      have ha : a = -∑ p, d p • (w * ρ p) := by
        have h2 : a = w * (w⁻¹ * a) := by rw [← mul_assoc, mul_inv_cancel₀ hw0, one_mul]
        rw [h2, eq_neg_of_add_eq_zero_left hz, mul_neg, Finset.mul_sum]
        simp only [mul_smul_comm]
      have hlamq : ∀ q, lam q a = -∑ p, d p * lam q (w * ρ p) := by
        intro q
        conv_lhs => rw [ha]
        rw [map_neg, map_sum]
        simp only [map_smul, smul_eq_mul]
      have hd0 : ∀ p, d p = 0 := by
        by_contra hne
        push_neg at hne
        have hS : (Finset.univ.filter (fun p => d p ≠ 0)).Nonempty := by
          obtain ⟨p, hp⟩ := hne
          exact ⟨p, by simp [hp]⟩
        set q := (Finset.univ.filter (fun p => d p ≠ 0)).max' hS with hq
        have hqmem : d q ≠ 0 := by
          have := Finset.max'_mem _ hS
          rw [← hq] at this
          simpa using this
        have hl : lam q a = 0 := by
          rw [hlamq q]
          rw [neg_eq_zero]
          refine Finset.sum_eq_zero (fun p _ => ?_)
          rcases le_or_gt p q with hpq | hpq
          · rw [hΦ w hw q p hpq, mul_zero]
          · have : d p = 0 := by
              by_contra hp
              have hmem : p ∈ Finset.univ.filter (fun p => d p ≠ 0) := by simp [hp]
              have := Finset.le_max' _ p hmem
              rw [← hq] at this
              exact absurd hpq (not_lt.mpr this)
            rw [this, zero_mul]
        apply hqmem
        simp [hd, hl]
      apply ha0
      rw [ha]
      simp [hd0]
    · intro hk
      exact upper k t _ hk

end field

end PEqualNP.Outside.L_meta_26030_aux

theorem PEqualNP.Outside.L_meta_26030 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
  let n := k+1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)

  ∀ (g s : ℕ) (T : Fin g → Fin n → Fin n → Bool), fits n n g T s →
    ∃ V : Submodule F K, k ≤ Module.finrank F V + s*(2*s+1) ∧
      ∀ w ∈ V, w ≠ 0 → ∀ (S : Finset (Fin g)) (t : ℕ),
        (fits n n 1 (fun _ => residual T S w⁻¹) t ↔ k ≤ 2*t) := by
  intro nonlinear depths fits F K _ _ _ k basis bit hbit n point mult residual g s T hT
  exact PEqualNP.Outside.L_meta_26030_aux.core k basis bit hbit point rfl (fun _ => rfl) g s T hT
