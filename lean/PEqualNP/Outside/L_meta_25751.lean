import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25751_aux

open PEqualNP.CircuitLowerBounds

private abbrev F2 := ZMod 2

private def b2f (b : Bool) : F2 := if b then 1 else 0

private lemma b2f_injective : Function.Injective b2f := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private lemma b2f_false : b2f false = 0 := rfl
private lemma b2f_true : b2f true = 1 := rfl

private lemma b2f_not (b : Bool) : b2f (!b) = 1 + b2f b := by
  cases b <;> decide

private lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

private lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

private lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma z2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_ne_zero_iff (a : F2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

private lemma b2f_xnor (a b : Bool) :
    b2f (GateOp.eval (GateOp.mod 2) [a, b]) = 1 + b2f a + b2f b := by
  cases a <;> cases b <;> decide

private def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

private def fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n + m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

private lemma nonlinear_const_false : nonlinear ⟨GateOp.or, []⟩ = false := rfl
private lemma nonlinear_const_true : nonlinear ⟨GateOp.and, []⟩ = false := rfl
private lemma nonlinear_not (w : ℕ) : nonlinear ⟨GateOp.not, [w]⟩ = false := rfl
private lemma nonlinear_xnor (w1 w2 : ℕ) : nonlinear ⟨GateOp.mod 2, [w1, w2]⟩ = false := rfl
private lemma nonlinear_and (w1 w2 : ℕ) : nonlinear ⟨GateOp.and, [w1, w2]⟩ = true := rfl

private lemma gate_eval_unary (op : GateOp) (a : Bool) :
    b2f (op.eval [a]) = b2f (op.eval [false]) + (b2f (op.eval [false]) + b2f (op.eval [true])) * b2f a := by
  cases a
  · simp [b2f_false]
  · simp only [b2f_true, mul_one]
    have h := z2_add_self (b2f (op.eval [false]))
    linear_combination -h

private lemma gate_eval_binary (op : GateOp) (a b : Bool) :
    let c0 := b2f (op.eval [false, false])
    let c1 := b2f (op.eval [false, false]) + b2f (op.eval [true, false])
    let c2 := b2f (op.eval [false, false]) + b2f (op.eval [false, true])
    let c3 := b2f (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                       (xor (op.eval [true, false]) (op.eval [true, true])))
    b2f (op.eval [a, b]) = c0 + c1 * b2f a + c2 * b2f b + c3 * (b2f a * b2f b) := by
  intro c0 c1 c2 c3
  have hc3 : c3 = b2f (op.eval [false, false]) + b2f (op.eval [false, true]) +
      b2f (op.eval [true, false]) + b2f (op.eval [true, true]) := by
    simp only [c3, b2f_xor]; ring
  cases a <;> cases b
  · simp [c0, b2f_false]
  · simp only [c0, c2, b2f_false, b2f_true, mul_zero, add_zero, mul_one]
    have h := z2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [c0, c1, b2f_false, b2f_true, mul_zero, add_zero, mul_one]
    have h := z2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [c0, c1, c2, hc3, b2f_true, mul_one]
    have h0 := z2_add_self (b2f (op.eval [false, false]))
    have h1 := z2_add_self (b2f (op.eval [true, false]))
    have h2 := z2_add_self (b2f (op.eval [false, true]))
    linear_combination -2 * h0 - h1 - h2

private lemma getD_append_singleton {α : Type*} (l : List α) (v d : α) (i : ℕ) :
    (l ++ [v]).getD i d = if i < l.length then l.getD i d else if i = l.length then v else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < l.length
  · simp only [hi, ↓reduceIte, List.getElem?_append_left hi]
  · by_cases heq : i = l.length
    · subst heq
      simp only [lt_irrefl, ↓reduceIte, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    · have hlen : (l ++ [v]).length ≤ i := by simp; omega
      simp only [hi, heq, ↓reduceIte, List.getElem?_eq_none hlen, Option.getD_none]

private def wiresL (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private def depthsL (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

private lemma wiresL_length (gs : List Gate) (x : List Bool) :
    (wiresL gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresL]
  | append_singleton gs g ih =>
    simp only [wiresL, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton] at ih ⊢
    omega

private lemma depthsL_length (width : ℕ) (gs : List Gate) :
    (depthsL width gs).length = width + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depthsL]
  | append_singleton gs g ih =>
    simp only [depthsL, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton] at ih ⊢
    omega

private lemma wiresL_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresL (gs ++ [g]) x =
      wiresL gs x ++ [g.op.eval (g.inputs.map fun i => (wiresL gs x).getD i false)] := by
  simp [wiresL, List.foldl_append]

private lemma depthsL_append_singleton (width : ℕ) (gs : List Gate) (g : Gate) :
    depthsL width (gs ++ [g]) =
      depthsL width gs ++ [(g.inputs.map (fun a => (depthsL width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat] := by
  simp [depthsL, List.foldl_append]

private lemma wiresL_getD_append_lt (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs.length) :
    (wiresL (gs ++ [g]) x).getD w false = (wiresL gs x).getD w false := by
  rw [wiresL_append_singleton, getD_append_singleton, wiresL_length]
  simp only [hw, ↓reduceIte]

private lemma wiresL_getD_append_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresL (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresL gs x).getD i false) := by
  rw [wiresL_append_singleton, getD_append_singleton, wiresL_length]
  simp

private lemma depthsL_getD_append_lt (width : ℕ) (gs : List Gate) (g : Gate) (w : ℕ)
    (hw : w < width + gs.length) :
    (depthsL width (gs ++ [g])).getD w 0 = (depthsL width gs).getD w 0 := by
  rw [depthsL_append_singleton, getD_append_singleton, depthsL_length]
  simp only [hw, ↓reduceIte]

private lemma depthsL_getD_append_last (width : ℕ) (gs : List Gate) (g : Gate) :
    (depthsL width (gs ++ [g])).getD (width + gs.length) 0 =
      (g.inputs.map (fun a => (depthsL width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat := by
  rw [depthsL_append_singleton, getD_append_singleton, depthsL_length]
  simp

private lemma wiresL_getD_take (gs : List Gate) (x : List Bool) (k w : ℕ)
    (hw : w < x.length + k) (hk : k ≤ gs.length) :
    (wiresL gs x).getD w false = (wiresL (gs.take k) x).getD w false := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsplit]
  generalize gs.drop k = rest
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest g ih =>
    rw [← List.append_assoc, wiresL_getD_append_lt]
    · exact ih
    · rw [List.length_append, List.length_take_of_le hk]; omega

private lemma depthsL_getD_take (width : ℕ) (gs : List Gate) (k w : ℕ)
    (hw : w < width + k) (hk : k ≤ gs.length) :
    (depthsL width gs).getD w 0 = (depthsL width (gs.take k)).getD w 0 := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsplit]
  generalize gs.drop k = rest
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest g ih =>
    rw [← List.append_assoc, depthsL_getD_append_lt]
    · exact ih
    · rw [List.length_append, List.length_take_of_le hk]; omega

private lemma wiresL_getD_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length)
    (hrb : ∀ i ∈ gs[k].inputs, i < x.length + k) :
    (wiresL gs x).getD (x.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (wiresL gs x).getD i false) := by
  have h1 : (wiresL gs x).getD (x.length + k) false = (wiresL (gs.take (k + 1)) x).getD (x.length + k) false :=
    wiresL_getD_take gs x (k + 1) (x.length + k) (by omega) (by omega)
  rw [h1, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have hlen : (gs.take k).length = k := List.length_take_of_le (by omega)
  have h2 := wiresL_getD_append_last (gs.take k) gs[k] x
  rw [hlen] at h2
  rw [h2]
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  exact (wiresL_getD_take gs x k i (hrb i hi) (by omega)).symm

private lemma depthsL_getD_gate (width : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hrb : ∀ i ∈ gs[k].inputs, i < width + k) :
    (depthsL width gs).getD (width + k) 0 =
      (gs[k].inputs.map (fun a => (depthsL width gs).getD a 0)).foldr max 0 + (nonlinear gs[k]).toNat := by
  have h1 : (depthsL width gs).getD (width + k) 0 = (depthsL width (gs.take (k + 1))).getD (width + k) 0 :=
    depthsL_getD_take width gs (k + 1) (width + k) (by omega) (by omega)
  rw [h1, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have hlen : (gs.take k).length = k := List.length_take_of_le (by omega)
  have h2 := depthsL_getD_append_last width (gs.take k) gs[k]
  rw [hlen] at h2
  rw [h2]
  congr 2
  refine List.map_congr_left ?_
  intro i hi
  exact (depthsL_getD_take width gs k i (hrb i hi) (by omega)).symm

private lemma wiresL_getD_input (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wiresL gs x).getD w false = x.getD w false := by
  have := wiresL_getD_take gs x 0 w (by omega) (Nat.zero_le _)
  simpa [wiresL] using this

private lemma depthsL_getD_input (width : ℕ) (gs : List Gate) (w : ℕ) (hw : w < width) :
    (depthsL width gs).getD w 0 = 0 := by
  have h := depthsL_getD_take width gs 0 w (by omega) (Nat.zero_le _)
  rw [h]
  simp [depthsL, List.getD_eq_getElem?_getD, hw]

private lemma wiresL_getD_ge (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    (wiresL gs x).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wiresL_length]; exact hw

private lemma depthsL_getD_ge (width : ℕ) (gs : List Gate) (w : ℕ) (hw : width + gs.length ≤ w) :
    (depthsL width gs).getD w 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [depthsL_length]; exact hw

private lemma oneEach_length {n m : ℕ} (x : Fin n) (y : Fin m) :
    (PEqualNP.Represents.oneEach x y).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

private lemma oneEach_getD_left {n m : ℕ} (x : Fin n) (y : Fin m) (w : ℕ) (hw : w < n) :
    (PEqualNP.Represents.oneEach x y).getD w false = decide (x.val = w) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw])]
  simp [hw, Fin.ext_iff, eq_comm]

private lemma oneEach_getD_right {n m : ℕ} (x : Fin n) (y : Fin m) (w : ℕ) (hw1 : n ≤ w) (hw2 : w < n + m) :
    (PEqualNP.Represents.oneEach x y).getD w false = decide (y.val = w - n) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hw1])]
  simp only [List.length_ofFn]
  have hlt : w - n < m := by omega
  simp [hlt, Fin.ext_iff, eq_comm]

private lemma foldr_max_le_iff (l : List ℕ) (d : ℕ) :
    l.foldr max 0 ≤ d ↔ ∀ x ∈ l, x ≤ d := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldr_cons, max_le_iff, ih, List.mem_cons, forall_eq_or_imp]

private lemma card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin l.length => p l[i] = true)).card = l.countP p := by
  rw [Finset.card_filter]
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.countP_cons]
    change (∑ i : Fin (tl.length + 1), if p (a :: tl)[i.val] = true then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]
    have hih : (∑ x : Fin tl.length, if p tl[x.val] = true then 1 else 0) = tl.countP p := ih
    rw [hih]
    exact Nat.add_comm _ _

private lemma sum_fin_list_map {α : Type*} (l : List α) (f : α → F2) :
    (∑ idx : Fin l.length, f l[idx]) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    change (∑ idx : Fin (tl.length + 1), f (a :: tl)[idx.val]) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
      List.map_cons, List.sum_cons]
    exact congrArg (f a + ·) ih

private lemma list_map_sum_eq_finset_sum {α : Type*} [DecidableEq α] (s : Finset α) (g : α → F2) :
    (s.toList.map g).sum = ∑ x ∈ s, g x := by
  simp

private def IsAff {n m : ℕ} (f : Fin n → Fin m → F2) : Prop :=
  ∃ (r : Fin n → F2) (c : Fin m → F2) (d : F2), ∀ x y, f x y = r x + c y + d

private lemma isAff_const {n m : ℕ} (d : F2) : IsAff (fun (_ : Fin n) (_ : Fin m) => d) :=
  ⟨0, 0, d, fun _ _ => by simp⟩

private lemma isAff_add {n m : ℕ} {f g : Fin n → Fin m → F2} (hf : IsAff f) (hg : IsAff g) :
    IsAff (fun x y => f x y + g x y) := by
  rcases hf with ⟨r1, c1, d1, h1⟩
  rcases hg with ⟨r2, c2, d2, h2⟩
  refine ⟨fun x => r1 x + r2 x, fun y => c1 y + c2 y, d1 + d2, fun x y => ?_⟩
  dsimp only; rw [h1 x y, h2 x y]; ring

private lemma isAff_smul {n m : ℕ} (a : F2) {f : Fin n → Fin m → F2} (hf : IsAff f) :
    IsAff (fun x y => a * f x y) := by
  rcases hf with ⟨r, c, d, h⟩
  refine ⟨fun x => a * r x, fun y => a * c y, a * d, fun x y => ?_⟩
  dsimp only; rw [h x y]; ring

private lemma delta_isAff {n m : ℕ} (u : Fin n) (v : Fin m) {f : Fin n → Fin m → F2} (hf : IsAff f) :
    ∀ x y, f x y + f x v + f u y + f u v = 0 := by
  rcases hf with ⟨r, c, d, h⟩
  intro x y
  rw [h x y, h x v, h u y, h u v]
  have h1 := z2_add_self (r x)
  have h2 := z2_add_self (r u)
  have h3 := z2_add_self (c y)
  have h4 := z2_add_self (c v)
  have h5 := z2_add_self d
  linear_combination h1 + h2 + h3 + h4 + 2 * h5

private lemma elim_columns : ∀ (p K : ℕ) (R : Fin p → Fin K → F2),
    LinearIndependent F2 R →
    ∃ S : Finset (Fin K), S.card + p = K ∧
      ∀ v : Fin K → F2, ∃ γ : Fin p → F2,
        ∀ k : Fin K, k ∉ S → (v + ∑ i : Fin p, γ i • R i) k = 0 := by
  intro p
  induction p with
  | zero =>
    intro K R _
    refine ⟨Finset.univ, by simp, fun v => ⟨Fin.elim0, fun k hk => absurd (Finset.mem_univ k) hk⟩⟩
  | succ p ih =>
    intro K R hLI
    have hR0 : R 0 ≠ 0 := hLI.ne_zero 0
    have hexk : ∃ k0 : Fin K, R 0 k0 ≠ 0 := by
      by_contra hnot
      push Not at hnot
      exact hR0 (funext hnot)
    obtain ⟨k0, hk0_ne⟩ := hexk
    have hk0 : R 0 k0 = 1 := (z2_ne_zero_iff _).mp hk0_ne
    have hKpos : 0 < K := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 k0)
    have hcard_other : Fintype.card {k : Fin K // k ≠ k0} = K - 1 := by
      have : Fintype.card {k : Fin K // k ≠ k0} = ((Finset.univ : Finset (Fin K)).erase k0).card := by
        rw [Fintype.card_subtype]; congr 1; ext k; simp
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ k0), Finset.card_univ, Fintype.card_fin]
    let eK : Fin (K - 1) ≃ {k : Fin K // k ≠ k0} :=
      (Fintype.equivFinOfCardEq hcard_other).symm
    let R' : Fin p → Fin K → F2 := fun i => R i.succ + R i.succ k0 • R 0
    have hR'k0 : ∀ i : Fin p, R' i k0 = 0 := by
      intro i
      simp only [R', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk0, mul_one]
      exact z2_add_self _
    let R'' : Fin p → Fin (K - 1) → F2 := fun i j => R' i (eK j).val
    have hLI'' : LinearIndependent F2 R'' := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hfull : ∑ i : Fin p, c i • R' i = 0 := by
        funext k
        by_cases hk : k = k0
        · subst hk
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR'k0, mul_zero, Finset.sum_const_zero, Pi.zero_apply]
        · let j := eK.symm ⟨k, hk⟩
          have hj : (eK j).val = k := by simp [j]
          have hcj := congrFun hc j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, R'', hj] at hcj ⊢
          exact hcj
      let c0 : F2 := ∑ i : Fin p, c i * R i.succ k0
      let cfull : Fin (p + 1) → F2 := Fin.cons c0 c
      have hsum : ∑ i : Fin (p + 1), cfull i • R i = 0 := by
        rw [Fin.sum_univ_succ]
        simp only [cfull, Fin.cons_zero, Fin.cons_succ]
        funext k
        have hfk := congrFun hfull k
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, R'] at hfk ⊢
        calc c0 * R 0 k + ∑ x : Fin p, c x * R x.succ k
            = (∑ x : Fin p, c x * R x.succ k0) * R 0 k + ∑ x : Fin p, c x * R x.succ k := rfl
          _ = (∑ x : Fin p, c x * (R x.succ k0 * R 0 k)) + ∑ x : Fin p, c x * R x.succ k := by
              rw [Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun x _ => by ring
          _ = ∑ x : Fin p, c x * (R x.succ k + R x.succ k0 * R 0 k) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun x _ => by ring
          _ = 0 := hfk
      have hcz := (Fintype.linearIndependent_iff.mp hLI) cfull hsum
      intro i
      exact hcz i.succ
    obtain ⟨S', hScard', hSelim'⟩ := ih (K - 1) R'' hLI''
    let S : Finset (Fin K) := S'.image (fun j => (eK j).val)
    have hScard : S.card = S'.card := by
      rw [Finset.card_image_of_injective]
      intro j1 j2 heq
      exact eK.injective (Subtype.ext heq)
    refine ⟨S, by omega, ?_⟩
    intro v
    let v' : Fin K → F2 := v + v k0 • R 0
    have hv'k0 : v' k0 = 0 := by
      simp only [v', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk0, mul_one]
      exact z2_add_self _
    let v'' : Fin (K - 1) → F2 := fun j => v' (eK j).val
    obtain ⟨γ', hγ'⟩ := hSelim' v''
    let γ0 : F2 := v k0 + ∑ i : Fin p, γ' i * R i.succ k0
    let γ : Fin (p + 1) → F2 := Fin.cons γ0 γ'
    refine ⟨γ, ?_⟩
    intro k hkS
    have hexpand : (v + ∑ i : Fin (p + 1), γ i • R i) k =
        (v' + ∑ i : Fin p, γ' i • R' i) k := by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
        γ, Fin.cons_zero, Fin.cons_succ, γ0, v', R']
      have h1 : (∑ i : Fin p, γ' i * R i.succ k0) * R 0 k = ∑ i : Fin p, γ' i * (R i.succ k0 * R 0 k) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
      have h2 : ∑ i : Fin p, γ' i * (R i.succ k + R i.succ k0 * R 0 k) =
          (∑ i : Fin p, γ' i * R i.succ k) + ∑ i : Fin p, γ' i * (R i.succ k0 * R 0 k) := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [h2]; linear_combination h1
    rw [hexpand]
    by_cases hk : k = k0
    · subst hk
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv'k0, hR'k0,
        mul_zero, Finset.sum_const_zero, add_zero]
    · let j := eK.symm ⟨k, hk⟩
      have hj : (eK j).val = k := by simp [j]
      have hjS : j ∉ S' := by
        intro hmem
        exact hkS (Finset.mem_image.mpr ⟨j, hmem, hj⟩)
      have h0 := hγ' j hjS
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v'', R'', hj] at h0 ⊢
      exact h0

private def buildXorAux (width : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws =>
    let w1 := width + gs.length
    let g1 : Gate := ⟨GateOp.mod 2, [acc, w]⟩
    let g2 : Gate := ⟨GateOp.not, [w1]⟩
    buildXorAux width (gs ++ [g1, g2]) (w1 + 1) ws

private def buildXor (width : ℕ) (gs : List Gate) (ws : List ℕ) : List Gate × ℕ :=
  let w0 := width + gs.length
  let g0 : Gate := ⟨GateOp.or, []⟩
  buildXorAux width (gs ++ [g0]) w0 ws

private lemma readsBack_append_singleton (width : ℕ) (gs : List Gate) (g : Gate)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs, 0⟩)
    (hg : ∀ i ∈ g.inputs, i < width + gs.length) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  dsimp only at hi
  by_cases hlt : j < gs.length
  · rw [getD_append_singleton] at hi
    simp only [hlt, ↓reduceIte] at hi
    exact hrb j hlt i hi
  · have heq : j = gs.length := by omega
    subst heq
    rw [getD_append_singleton] at hi
    simp only [lt_irrefl, ↓reduceIte] at hi
    exact hg i hi

private lemma buildXorAux_spec (width : ℕ) (d : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate) (acc : ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs, 0⟩ →
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      acc < width + gs.length →
      (depthsL width gs).getD acc 0 ≤ d →
      (∀ w ∈ ws, w < width + gs.length ∧ (depthsL width gs).getD w 0 ≤ d) →
      let res := buildXorAux width gs acc ws
      gs.length ≤ res.1.length ∧
      (∀ x : List Bool, x.length = width → ∀ w < width + gs.length,
        (wiresL res.1 x).getD w false = (wiresL gs x).getD w false) ∧
      (∀ w < width + gs.length, (depthsL width res.1).getD w 0 = (depthsL width gs).getD w 0) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, g.inputs.length ≤ 2) ∧
      res.1.countP nonlinear = gs.countP nonlinear ∧
      res.2 < width + res.1.length ∧
      (depthsL width res.1).getD res.2 0 ≤ d ∧
      ∀ x : List Bool, x.length = width →
        b2f ((wiresL res.1 x).getD res.2 false) =
          b2f ((wiresL gs x).getD acc false) + (ws.map (fun w => b2f ((wiresL gs x).getD w false))).sum := by
  intro ws
  induction ws with
  | nil =>
    intro gs acc hrb hlen hacc hdacc _
    dsimp only [buildXorAux]
    refine ⟨le_refl _, fun _ _ _ _ => rfl, fun _ _ => rfl, hrb, hlen, rfl, hacc, hdacc, ?_⟩
    intro x _; simp
  | cons w ws ih =>
    intro gs acc hrb hlen hacc hdacc hws
    have hw_spec := hws w (List.mem_cons_self ..)
    let w1 := width + gs.length
    let g1 : Gate := ⟨GateOp.mod 2, [acc, w]⟩
    let g2 : Gate := ⟨GateOp.not, [w1]⟩
    let gs1 := gs ++ [g1]
    let gs2 := gs1 ++ [g2]
    have hgs2_eq : gs ++ [g1, g2] = gs2 := by simp [gs2, gs1]
    have hrb1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs1, 0⟩ :=
      readsBack_append_singleton width gs g1 hrb (by
        intro i hi; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hacc
        · exact hw_spec.1)
    have hrb2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs2, 0⟩ :=
      readsBack_append_singleton width gs1 g2 hrb1 (by
        intro i hi; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi; simp [gs1, w1])
    have hlen2 : ∀ g ∈ gs2, g.inputs.length ≤ 2 := by
      intro g hg
      simp only [gs2, gs1, List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | rfl) | rfl
      · exact hlen g hg
      · simp [g1]
      · simp [g2]
    have hcnt2 : gs2.countP nonlinear = gs.countP nonlinear := by
      simp [gs2, gs1, g1, g2, List.countP_append, nonlinear_xnor, nonlinear_not]
    have hdep_pres : ∀ u < width + gs.length, (depthsL width gs2).getD u 0 = (depthsL width gs).getD u 0 := by
      intro u hu
      have h1 : (depthsL width gs2).getD u 0 = (depthsL width gs1).getD u 0 :=
        depthsL_getD_append_lt width gs1 g2 u (by simp [gs1]; omega)
      have h2 : (depthsL width gs1).getD u 0 = (depthsL width gs).getD u 0 :=
        depthsL_getD_append_lt width gs g1 u hu
      exact h1.trans h2
    have hdep_w1 : (depthsL width gs1).getD w1 0 ≤ d := by
      dsimp only [gs1, w1]
      rw [depthsL_getD_append_last, nonlinear_xnor]
      simp only [g1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
      exact max_le hdacc (max_le hw_spec.2 (Nat.zero_le _))
    have hdep_acc2 : (depthsL width gs2).getD (w1 + 1) 0 ≤ d := by
      have hlen1 : width + gs1.length = w1 + 1 := by simp [gs1, w1]; omega
      rw [← hlen1]
      dsimp only [gs2]
      rw [depthsL_getD_append_last, nonlinear_not]
      simp only [g2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
      exact max_le hdep_w1 (Nat.zero_le _)
    have hwire_pres : ∀ x : List Bool, x.length = width → ∀ u < width + gs.length,
        (wiresL gs2 x).getD u false = (wiresL gs x).getD u false := by
      intro x hx u hu
      have h1 : (wiresL gs2 x).getD u false = (wiresL gs1 x).getD u false :=
        wiresL_getD_append_lt gs1 g2 x u (by simp [gs1, hx]; omega)
      have h2 : (wiresL gs1 x).getD u false = (wiresL gs x).getD u false :=
        wiresL_getD_append_lt gs g1 x u (by omega)
      exact h1.trans h2
    have hwire_acc2 : ∀ x : List Bool, x.length = width →
        b2f ((wiresL gs2 x).getD (w1 + 1) false) =
          b2f ((wiresL gs x).getD acc false) + b2f ((wiresL gs x).getD w false) := by
      intro x hx
      have hlen1 : x.length + gs1.length = w1 + 1 := by simp [gs1, w1, hx]; omega
      rw [← hlen1]
      dsimp only [gs2]
      rw [wiresL_getD_append_last]
      simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      have hw1_val : (wiresL gs1 x).getD w1 false =
          GateOp.eval (GateOp.mod 2) [(wiresL gs x).getD acc false, (wiresL gs x).getD w false] := by
        have hlen0 : x.length + gs.length = w1 := by omega
        rw [← hlen0]
        dsimp only [gs1]
        rw [wiresL_getD_append_last]
        rfl
      rw [hw1_val, b2f_not, b2f_xnor]
      have h11 := z2_add_self (1 : F2)
      linear_combination h11
    have hacc2_lt : w1 + 1 < width + gs2.length := by simp [gs2, gs1, w1]; omega
    have hws2 : ∀ u ∈ ws, u < width + gs2.length ∧ (depthsL width gs2).getD u 0 ≤ d := by
      intro u hu
      have h0 := hws u (List.mem_cons_of_mem w hu)
      refine ⟨by simp [gs2, gs1]; omega, ?_⟩
      rw [hdep_pres u h0.1]
      exact h0.2
    have hrec := ih gs2 (w1 + 1) hrb2 hlen2 hacc2_lt hdep_acc2 hws2
    dsimp only [buildXorAux]
    change gs.length ≤ (buildXorAux width (gs ++ [g1, g2]) (w1 + 1) ws).1.length ∧ _
    rw [hgs2_eq]
    rcases hrec with ⟨hL, hW, hD, hRB, hLen, hCnt, hOutLt, hOutDep, hVal⟩
    have hgs2_le : gs.length ≤ gs2.length := by simp [gs2, gs1]
    refine ⟨le_trans hgs2_le hL, ?_, ?_, hRB, hLen, hCnt.trans hcnt2, hOutLt, hOutDep, ?_⟩
    · intro x hx u hu
      have h1 := hW x hx u (by simp [gs2, gs1]; omega)
      exact h1.trans (hwire_pres x hx u hu)
    · intro u hu
      have h1 := hD u (by simp [gs2, gs1]; omega)
      exact h1.trans (hdep_pres u hu)
    · intro x hx
      rw [hVal x hx, hwire_acc2 x hx]
      simp only [List.map_cons, List.sum_cons]
      have hmap : ws.map (fun u => b2f ((wiresL gs2 x).getD u false)) =
          ws.map (fun u => b2f ((wiresL gs x).getD u false)) := by
        refine List.map_congr_left ?_
        intro u hu
        rw [hwire_pres x hx u (hws u (List.mem_cons_of_mem w hu)).1]
      rw [hmap]; ring

private lemma buildXor_spec (width d : ℕ) (gs : List Gate) (ws : List ℕ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs, 0⟩)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hws : ∀ w ∈ ws, w < width + gs.length ∧ (depthsL width gs).getD w 0 ≤ d) :
    let res := buildXor width gs ws
    gs.length ≤ res.1.length ∧
    (∀ x : List Bool, x.length = width → ∀ w < width + gs.length,
      (wiresL res.1 x).getD w false = (wiresL gs x).getD w false) ∧
    (∀ w < width + gs.length, (depthsL width res.1).getD w 0 = (depthsL width gs).getD w 0) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, g.inputs.length ≤ 2) ∧
    res.1.countP nonlinear = gs.countP nonlinear ∧
    res.2 < width + res.1.length ∧
    (depthsL width res.1).getD res.2 0 ≤ d ∧
    ∀ x : List Bool, x.length = width →
      b2f ((wiresL res.1 x).getD res.2 false) =
        (ws.map (fun w => b2f ((wiresL gs x).getD w false))).sum := by
  let g0 : Gate := ⟨GateOp.or, []⟩
  let gs0 := gs ++ [g0]
  have hrb0 : PEqualNP.MetaComplexity.NestedCover.ReadsBack width ⟨gs0, 0⟩ :=
    readsBack_append_singleton width gs g0 hrb (by simp [g0])
  have hlen0 : ∀ g ∈ gs0, g.inputs.length ≤ 2 := by
    intro g hg; simp only [gs0, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hlen g hg
    · simp [g0]
  have hcnt0 : gs0.countP nonlinear = gs.countP nonlinear := by
    simp [gs0, g0, List.countP_append, nonlinear_const_false]
  have hw0_lt : width + gs.length < width + gs0.length := by simp [gs0]
  have hd0 : (depthsL width gs0).getD (width + gs.length) 0 ≤ d := by
    dsimp only [gs0]; rw [depthsL_getD_append_last, nonlinear_const_false]; simp [g0]
  have hws0 : ∀ w ∈ ws, w < width + gs0.length ∧ (depthsL width gs0).getD w 0 ≤ d := by
    intro w hw
    have h0 := hws w hw
    refine ⟨by simp [gs0]; omega, ?_⟩
    rw [depthsL_getD_append_lt width gs g0 w h0.1]
    exact h0.2
  have hrec := buildXorAux_spec width d ws gs0 (width + gs.length) hrb0 hlen0 hw0_lt hd0 hws0
  dsimp only [buildXor]
  change gs.length ≤ (buildXorAux width gs0 (width + gs.length) ws).1.length ∧ _
  rcases hrec with ⟨hL, hW, hD, hRB, hLen, hCnt, hOutLt, hOutDep, hVal⟩
  have hgs0_le : gs.length ≤ gs0.length := by simp [gs0]
  refine ⟨le_trans hgs0_le hL, ?_, ?_, hRB, hLen, hCnt.trans hcnt0, hOutLt, hOutDep, ?_⟩
  · intro x hx w hw
    have h1 := hW x hx w (by simp [gs0]; omega)
    exact h1.trans (wiresL_getD_append_lt gs g0 x w (by omega))
  · intro w hw
    have h1 := hD w (by simp [gs0]; omega)
    exact h1.trans (depthsL_getD_append_lt width gs g0 w hw)
  · intro x hx
    rw [hVal x hx]
    have hzero : (wiresL gs0 x).getD (width + gs.length) false = false := by
      have hlenx : x.length + gs.length = width + gs.length := by omega
      rw [← hlenx]; dsimp only [gs0]; rw [wiresL_getD_append_last]; rfl
    rw [hzero, b2f_false, zero_add]
    have hmap : ws.map (fun w => b2f ((wiresL gs0 x).getD w false)) =
        ws.map (fun w => b2f ((wiresL gs x).getD w false)) := by
      refine List.map_congr_left ?_
      intro w hw
      rw [wiresL_getD_append_lt gs g0 x w (by have := (hws w hw).1; omega)]
    rw [hmap]

private lemma sum_filter_fin_list {k : ℕ} (f : Fin k → F2) (g : Fin k → F2) :
    (((List.finRange k).filter (fun i => decide (f i = 1))).map g).sum =
      ∑ i : Fin k, f i * g i := by
  have h1 : (((List.finRange k).filter (fun i => decide (f i = 1))).map g).sum =
      ∑ i ∈ (Finset.univ : Finset (Fin k)).filter (fun i => f i = 1), g i := by
    rw [← list_map_sum_eq_finset_sum]
    have hnd : ((List.finRange k).filter (fun i => decide (f i = 1))).Nodup :=
      (List.nodup_finRange k).filter _
    have hperm : ((List.finRange k).filter (fun i => decide (f i = 1))).Perm
        ((Finset.univ : Finset (Fin k)).filter (fun i => f i = 1)).toList := by
      refine (List.perm_ext_iff_of_nodup hnd (Finset.nodup_toList _)).mpr ?_
      intro i
      simp [List.mem_finRange]
    exact (hperm.map g).sum_eq
  rw [h1, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases z2_eq_zero_or_one (f i) with h0 | h1'
  · simp [h0]
  · simp [h1']

private def buildProducts (n m : ℕ) (gs : List Gate)
    (a1 a2 : ℕ → Fin n → F2) (b1 b2 : ℕ → Fin m → F2) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | k :: ks =>
    let ws1 : List ℕ :=
      ((List.finRange n).filter (fun i => decide (a1 k i = 1))).map Fin.val ++
      ((List.finRange m).filter (fun j => decide (b1 k j = 1))).map (fun j => n + j.val)
    let r1 := buildXor (n + m) gs ws1
    let ws2 : List ℕ :=
      ((List.finRange n).filter (fun i => decide (a2 k i = 1))).map Fin.val ++
      ((List.finRange m).filter (fun j => decide (b2 k j = 1))).map (fun j => n + j.val)
    let r2 := buildXor (n + m) r1.1 ws2
    let wAnd := n + m + r2.1.length
    let gAnd : Gate := ⟨GateOp.and, [r1.2, r2.2]⟩
    let gs3 := r2.1 ++ [gAnd]
    let resSub := buildProducts n m gs3 a1 a2 b1 b2 ks
    (resSub.1, wAnd :: resSub.2)

private lemma buildProducts_spec (n m : ℕ)
    (a1 a2 : ℕ → Fin n → F2) (b1 b2 : ℕ → Fin m → F2) :
    ∀ (ks : List ℕ) (gs : List Gate),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨gs, 0⟩ →
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      let res := buildProducts n m gs a1 a2 b1 b2 ks
      gs.length ≤ res.1.length ∧
      (∀ x : List Bool, x.length = n + m → ∀ w < n + m + gs.length,
        (wiresL res.1 x).getD w false = (wiresL gs x).getD w false) ∧
      (∀ w < n + m + gs.length, (depthsL (n + m) res.1).getD w 0 = (depthsL (n + m) gs).getD w 0) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, g.inputs.length ≤ 2) ∧
      res.1.countP nonlinear = gs.countP nonlinear + ks.length ∧
      res.2.length = ks.length ∧
      ∀ idx : Fin ks.length,
        let w := res.2.getD idx.val 0
        w < n + m + res.1.length ∧
        (depthsL (n + m) res.1).getD w 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2f ((wiresL res.1 (PEqualNP.Represents.oneEach x y)).getD w false) =
            (a1 ks[idx] x + b1 ks[idx] y) * (a2 ks[idx] x + b2 ks[idx] y) := by
  intro ks
  induction ks with
  | nil =>
    intro gs hrb hlen
    dsimp only [buildProducts]
    refine ⟨le_refl _, fun _ _ _ _ => rfl, fun _ _ => rfl, hrb, hlen, by simp, rfl, fun idx => Fin.elim0 idx⟩
  | cons k ks ih =>
    intro gs hrb hlen
    let ws1 : List ℕ :=
      ((List.finRange n).filter (fun i => decide (a1 k i = 1))).map Fin.val ++
      ((List.finRange m).filter (fun j => decide (b1 k j = 1))).map (fun j => n + j.val)
    have hws1 : ∀ w ∈ ws1, w < n + m + gs.length ∧ (depthsL (n + m) gs).getD w 0 ≤ 0 := by
      intro w hw
      simp only [ws1, List.mem_append, List.mem_map, List.mem_filter] at hw
      rcases hw with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩
      · refine ⟨by omega, ?_⟩
        rw [depthsL_getD_input (n + m) gs i.val (by omega)]
      · refine ⟨by omega, ?_⟩
        rw [depthsL_getD_input (n + m) gs (n + j.val) (by omega)]
    rcases buildXor_spec (n + m) 0 gs ws1 hrb hlen hws1 with
      ⟨hL1, hW1, hD1, hRB1, hLen1, hCnt1, hOut1Lt, hOut1Dep, hVal1⟩
    set r1 := buildXor (n + m) gs ws1
    let ws2 : List ℕ :=
      ((List.finRange n).filter (fun i => decide (a2 k i = 1))).map Fin.val ++
      ((List.finRange m).filter (fun j => decide (b2 k j = 1))).map (fun j => n + j.val)
    have hws2 : ∀ w ∈ ws2, w < n + m + r1.1.length ∧ (depthsL (n + m) r1.1).getD w 0 ≤ 0 := by
      intro w hw
      simp only [ws2, List.mem_append, List.mem_map, List.mem_filter] at hw
      rcases hw with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩
      · refine ⟨by omega, ?_⟩
        rw [depthsL_getD_input (n + m) r1.1 i.val (by omega)]
      · refine ⟨by omega, ?_⟩
        rw [depthsL_getD_input (n + m) r1.1 (n + j.val) (by omega)]
    rcases buildXor_spec (n + m) 0 r1.1 ws2 hRB1 hLen1 hws2 with
      ⟨hL2, hW2, hD2, hRB2, hLen2, hCnt2, hOut2Lt, hOut2Dep, hVal2⟩
    set r2 := buildXor (n + m) r1.1 ws2
    let wAnd := n + m + r2.1.length
    let gAnd : Gate := ⟨GateOp.and, [r1.2, r2.2]⟩
    let gs3 := r2.1 ++ [gAnd]
    have hOut1Lt2 : r1.2 < n + m + r2.1.length := by omega
    have hRB3 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨gs3, 0⟩ :=
      readsBack_append_singleton (n + m) r2.1 gAnd hRB2 (by
        intro i hi; simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hOut1Lt2
        · exact hOut2Lt)
    have hLen3 : ∀ g ∈ gs3, g.inputs.length ≤ 2 := by
      intro g hg; simp only [gs3, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hLen2 g hg
      · simp [gAnd]
    have hCnt3 : gs3.countP nonlinear = gs.countP nonlinear + 1 := by
      simp only [gs3, gAnd, List.countP_append, List.countP_cons, List.countP_nil, nonlinear_and,
        ↓reduceIte, zero_add]
      rw [hCnt2, hCnt1]
    have hDepAnd : (depthsL (n + m) gs3).getD wAnd 0 ≤ 1 := by
      dsimp only [gs3, wAnd]
      rw [depthsL_getD_append_last, nonlinear_and]
      simp only [gAnd, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true]
      have hd1 : (depthsL (n + m) r2.1).getD r1.2 0 ≤ 0 := by rw [hD2 r1.2 hOut1Lt]; exact hOut1Dep
      have hmax : max ((depthsL (n + m) r2.1).getD r1.2 0) (max ((depthsL (n + m) r2.1).getD r2.2 0) 0) ≤ 0 :=
        max_le hd1 (max_le hOut2Dep (Nat.zero_le _))
      omega
    have hEvalWs : ∀ (f : Fin n → F2) (g : Fin m → F2) (gs' : List Gate) (x : Fin n) (y : Fin m),
        let ws := ((List.finRange n).filter (fun i => decide (f i = 1))).map Fin.val ++
                  ((List.finRange m).filter (fun j => decide (g j = 1))).map (fun j => n + j.val)
        (ws.map (fun w => b2f ((wiresL gs' (PEqualNP.Represents.oneEach x y)).getD w false))).sum =
          f x + g y := by
      intro f g gs' x y ws
      dsimp only [ws]
      rw [List.map_append, List.sum_append, List.map_map, List.map_map]
      have hLpart : (((List.finRange n).filter (fun i => decide (f i = 1))).map
          ((fun w => b2f ((wiresL gs' (PEqualNP.Represents.oneEach x y)).getD w false)) ∘ Fin.val)).sum = f x := by
        rw [sum_filter_fin_list]
        have hterm : ∀ i : Fin n,
            f i * b2f ((wiresL gs' (PEqualNP.Represents.oneEach x y)).getD i.val false) =
              if i = x then f x else 0 := by
          intro i
          rw [wiresL_getD_input gs' _ i.val (by rw [oneEach_length]; omega),
              oneEach_getD_left x y i.val i.isLt]
          by_cases hix : i = x
          · subst hix; simp [b2f_true]
          · have hne : x.val ≠ i.val := fun heq => hix (Fin.ext heq.symm)
            simp [hix, hne, b2f_false]
        simp_rw [Function.comp_apply, hterm]
        simp
      have hRpart : (((List.finRange m).filter (fun j => decide (g j = 1))).map
          ((fun w => b2f ((wiresL gs' (PEqualNP.Represents.oneEach x y)).getD w false)) ∘ fun j => n + j.val)).sum = g y := by
        rw [sum_filter_fin_list]
        have hterm : ∀ j : Fin m,
            g j * b2f ((wiresL gs' (PEqualNP.Represents.oneEach x y)).getD (n + j.val) false) =
              if j = y then g y else 0 := by
          intro j
          rw [wiresL_getD_input gs' _ (n + j.val) (by rw [oneEach_length]; omega),
              oneEach_getD_right x y (n + j.val) (by omega) (by omega)]
          have hsub : n + j.val - n = j.val := by omega
          rw [hsub]
          by_cases hjy : j = y
          · subst hjy; simp [b2f_true]
          · have hne : y.val ≠ j.val := fun heq => hjy (Fin.ext heq.symm)
            simp [hjy, hne, b2f_false]
        simp_rw [Function.comp_apply, hterm]
        simp
      rw [hLpart, hRpart]
    have hValAnd : ∀ (x : Fin n) (y : Fin m),
        b2f ((wiresL gs3 (PEqualNP.Represents.oneEach x y)).getD wAnd false) =
          (a1 k x + b1 k y) * (a2 k x + b2 k y) := by
      intro x y
      have hlenx : (PEqualNP.Represents.oneEach x y).length + r2.1.length = wAnd := by
        rw [oneEach_length]
      rw [← hlenx]
      dsimp only [gs3]
      rw [wiresL_getD_append_last]
      simp only [gAnd, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      rw [b2f_and]
      have h1 : b2f ((wiresL r2.1 (PEqualNP.Represents.oneEach x y)).getD r1.2 false) = a1 k x + b1 k y := by
        rw [hW2 _ (oneEach_length x y) r1.2 hOut1Lt, hVal1 _ (oneEach_length x y)]
        exact hEvalWs (a1 k) (b1 k) gs x y
      have h2 : b2f ((wiresL r2.1 (PEqualNP.Represents.oneEach x y)).getD r2.2 false) = a2 k x + b2 k y := by
        rw [hVal2 _ (oneEach_length x y)]
        exact hEvalWs (a2 k) (b2 k) r1.1 x y
      rw [h1, h2]
    rcases ih gs3 hRB3 hLen3 with ⟨hLr, hWr, hDr, hRBr, hLenr, hCntr, hResLen, hIdx⟩
    set resSub := buildProducts n m gs3 a1 a2 b1 b2 ks
    have hres_eq : buildProducts n m gs a1 a2 b1 b2 (k :: ks) = (resSub.1, wAnd :: resSub.2) := rfl
    change gs.length ≤ (buildProducts n m gs a1 a2 b1 b2 (k :: ks)).1.length ∧ _
    rw [hres_eq]
    have hgs3_len : gs.length ≤ gs3.length := by simp [gs3]; omega
    refine ⟨le_trans hgs3_len hLr, ?_, ?_, hRBr, hLenr, ?_, by simp only [List.length_cons, hResLen], ?_⟩
    · intro x hx w hw
      have h0 := hWr x hx w (by simp [gs3]; omega)
      have h1 := wiresL_getD_append_lt r2.1 gAnd x w (by omega)
      have h2 := hW2 x hx w (by omega)
      have h3 := hW1 x hx w hw
      exact h0.trans (h1.trans (h2.trans h3))
    · intro w hw
      have h0 := hDr w (by simp [gs3]; omega)
      have h1 := depthsL_getD_append_lt (n + m) r2.1 gAnd w (by omega)
      have h2 := hD2 w (by omega)
      have h3 := hD1 w hw
      exact h0.trans (h1.trans (h2.trans h3))
    · rw [hCntr, hCnt3]; simp; omega
    · intro idx
      refine Fin.cases ?_ ?_ idx
      · simp only [Fin.val_zero, List.getD_cons_zero]
        have hwAnd_lt3 : wAnd < n + m + gs3.length := by simp [gs3, wAnd]
        refine ⟨by omega, ?_, ?_⟩
        · rw [hDr wAnd hwAnd_lt3]; exact hDepAnd
        · intro x y
          rw [hWr _ (oneEach_length x y) wAnd hwAnd_lt3, hValAnd x y]
          rfl
      · intro idx'
        simp only [Fin.val_succ, List.getD_cons_succ]
        exact hIdx idx'

private def buildOutputs (n m : ℕ) (gs : List Gate) (cTrue : ℕ)
    (prodWires : List ℕ) (prodKs : List ℕ)
    (mask' : ℕ → ℕ → F2) (rj : ℕ → Fin n → F2) (cj : ℕ → Fin m → F2) (dj : ℕ → F2) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | j :: js =>
    let wsProd : List ℕ :=
      ((List.finRange prodKs.length).filter (fun idx =>
        decide (mask' j (prodKs[idx]) = 1))).map (fun idx => prodWires.getD idx.val 0)
    let wsX : List ℕ :=
      ((List.finRange n).filter (fun i => decide (rj j i = 1))).map Fin.val
    let wsY : List ℕ :=
      ((List.finRange m).filter (fun i => decide (cj j i = 1))).map (fun i => n + i.val)
    let wsD : List ℕ := if dj j = 1 then [cTrue] else []
    let r := buildXor (n + m) gs (wsProd ++ wsX ++ wsY ++ wsD)
    let resSub := buildOutputs n m r.1 cTrue prodWires prodKs mask' rj cj dj js
    (resSub.1, r.2 :: resSub.2)

private lemma buildOutputs_spec (n m : ℕ) (cTrue : ℕ)
    (prodWires : List ℕ) (prodKs : List ℕ)
    (Q : ℕ → Fin n → Fin m → F2)
    (mask' : ℕ → ℕ → F2) (rj : ℕ → Fin n → F2) (cj : ℕ → Fin m → F2) (dj : ℕ → F2) :
    ∀ (js : List ℕ) (gs : List Gate),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨gs, 0⟩ →
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      cTrue < n + m + gs.length →
      (depthsL (n + m) gs).getD cTrue 0 ≤ 1 →
      (∀ (x : Fin n) (y : Fin m), (wiresL gs (PEqualNP.Represents.oneEach x y)).getD cTrue false = true) →
      (∀ idx : Fin prodKs.length,
        let w := prodWires.getD idx.val 0
        w < n + m + gs.length ∧
        (depthsL (n + m) gs).getD w 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false) = Q prodKs[idx] x y) →
      let res := buildOutputs n m gs cTrue prodWires prodKs mask' rj cj dj js
      gs.length ≤ res.1.length ∧
      (∀ x : List Bool, x.length = n + m → ∀ w < n + m + gs.length,
        (wiresL res.1 x).getD w false = (wiresL gs x).getD w false) ∧
      (∀ w < n + m + gs.length, (depthsL (n + m) res.1).getD w 0 = (depthsL (n + m) gs).getD w 0) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, g.inputs.length ≤ 2) ∧
      res.1.countP nonlinear = gs.countP nonlinear ∧
      res.2.length = js.length ∧
      ∀ idx : Fin js.length,
        let w := res.2.getD idx.val 0
        (depthsL (n + m) res.1).getD w 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2f ((wiresL res.1 (PEqualNP.Represents.oneEach x y)).getD w false) =
            (∑ p : Fin prodKs.length, mask' js[idx] prodKs[p] * Q prodKs[p] x y) +
              rj js[idx] x + cj js[idx] y + dj js[idx] := by
  intro js
  induction js with
  | nil =>
    intro gs hrb hlen _ _ _ _
    dsimp only [buildOutputs]
    refine ⟨le_refl _, fun _ _ _ _ => rfl, fun _ _ => rfl, hrb, hlen, rfl, rfl, fun idx => Fin.elim0 idx⟩
  | cons j js ih =>
    intro gs hrb hlen hcLt hcDep hcVal hprod
    let wsProd : List ℕ :=
      ((List.finRange prodKs.length).filter (fun idx =>
        decide (mask' j (prodKs[idx]) = 1))).map (fun idx => prodWires.getD idx.val 0)
    let wsX : List ℕ :=
      ((List.finRange n).filter (fun i => decide (rj j i = 1))).map Fin.val
    let wsY : List ℕ :=
      ((List.finRange m).filter (fun i => decide (cj j i = 1))).map (fun i => n + i.val)
    let wsD : List ℕ := if dj j = 1 then [cTrue] else []
    have hws : ∀ w ∈ wsProd ++ wsX ++ wsY ++ wsD, w < n + m + gs.length ∧ (depthsL (n + m) gs).getD w 0 ≤ 1 := by
      intro w hw
      simp only [List.mem_append] at hw
      rcases hw with ((hw | hw) | hw) | hw
      · simp only [wsProd, List.mem_map, List.mem_filter] at hw
        rcases hw with ⟨idx, _, rfl⟩
        exact ⟨(hprod idx).1, (hprod idx).2.1⟩
      · simp only [wsX, List.mem_map, List.mem_filter] at hw
        rcases hw with ⟨i, _, rfl⟩
        refine ⟨by omega, ?_⟩
        rw [depthsL_getD_input (n + m) gs i.val (by omega)]; exact Nat.zero_le _
      · simp only [wsY, List.mem_map, List.mem_filter] at hw
        rcases hw with ⟨i, _, rfl⟩
        refine ⟨by omega, ?_⟩
        rw [depthsL_getD_input (n + m) gs (n + i.val) (by omega)]; exact Nat.zero_le _
      · dsimp only [wsD] at hw
        split_ifs at hw with hd1
        · simp only [List.mem_singleton] at hw; subst hw; exact ⟨hcLt, hcDep⟩
        · simp at hw
    rcases buildXor_spec (n + m) 1 gs (wsProd ++ wsX ++ wsY ++ wsD) hrb hlen hws with
      ⟨hL1, hW1, hD1, hRB1, hLen1, hCnt1, hOut1Lt, hOut1Dep, hVal1⟩
    set r := buildXor (n + m) gs (wsProd ++ wsX ++ wsY ++ wsD)
    have hValJ : ∀ (x : Fin n) (y : Fin m),
        b2f ((wiresL r.1 (PEqualNP.Represents.oneEach x y)).getD r.2 false) =
          (∑ p : Fin prodKs.length, mask' j prodKs[p] * Q prodKs[p] x y) +
            rj j x + cj j y + dj j := by
      intro x y
      rw [hVal1 _ (oneEach_length x y)]
      simp only [List.map_append, List.sum_append]
      have hP : (wsProd.map (fun w => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false))).sum =
          ∑ p : Fin prodKs.length, mask' j prodKs[p] * Q prodKs[p] x y := by
        dsimp only [wsProd]
        rw [List.map_map, sum_filter_fin_list]
        refine Finset.sum_congr rfl ?_
        intro p _
        dsimp only [Function.comp_apply]
        rw [(hprod p).2.2 x y]
      have hX : (wsX.map (fun w => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false))).sum = rj j x := by
        dsimp only [wsX]
        rw [List.map_map, sum_filter_fin_list]
        have hterm : ∀ i : Fin n,
            rj j i * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD i.val false) =
              if i = x then rj j x else 0 := by
          intro i
          rw [wiresL_getD_input gs _ i.val (by rw [oneEach_length]; omega),
              oneEach_getD_left x y i.val i.isLt]
          by_cases hix : i = x
          · subst hix; simp [b2f_true]
          · have hne : x.val ≠ i.val := fun heq => hix (Fin.ext heq.symm)
            simp [hix, hne, b2f_false]
        simp_rw [Function.comp_apply, hterm]; simp
      have hY : (wsY.map (fun w => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false))).sum = cj j y := by
        dsimp only [wsY]
        rw [List.map_map, sum_filter_fin_list]
        have hterm : ∀ i : Fin m,
            cj j i * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + i.val) false) =
              if i = y then cj j y else 0 := by
          intro i
          rw [wiresL_getD_input gs _ (n + i.val) (by rw [oneEach_length]; omega),
              oneEach_getD_right x y (n + i.val) (by omega) (by omega)]
          have hsub : n + i.val - n = i.val := by omega
          rw [hsub]
          by_cases hiy : i = y
          · subst hiy; simp [b2f_true]
          · have hne : y.val ≠ i.val := fun heq => hiy (Fin.ext heq.symm)
            simp [hiy, hne, b2f_false]
        simp_rw [Function.comp_apply, hterm]; simp
      have hD : (wsD.map (fun w => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false))).sum = dj j := by
        dsimp only [wsD]
        rcases z2_eq_zero_or_one (dj j) with h0 | h1
        · simp [h0]
        · simp only [h1, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [hcVal x y]; rfl
      rw [hP, hX, hY, hD]
    have hprod1 : ∀ idx : Fin prodKs.length,
        let w := prodWires.getD idx.val 0
        w < n + m + r.1.length ∧
        (depthsL (n + m) r.1).getD w 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2f ((wiresL r.1 (PEqualNP.Represents.oneEach x y)).getD w false) = Q prodKs[idx] x y := by
      intro idx
      have hp := hprod idx
      refine ⟨by omega, ?_, ?_⟩
      · rw [hD1 _ hp.1]; exact hp.2.1
      · intro x y; rw [hW1 _ (oneEach_length x y) _ hp.1]; exact hp.2.2 x y
    rcases ih r.1 hRB1 hLen1 (by omega) (by rw [hD1 cTrue hcLt]; exact hcDep)
      (fun x y => by rw [hW1 _ (oneEach_length x y) cTrue hcLt]; exact hcVal x y) hprod1 with
      ⟨hLr, hWr, hDr, hRBr, hLenr, hCntr, hResLen, hIdx⟩
    set resSub := buildOutputs n m r.1 cTrue prodWires prodKs mask' rj cj dj js
    have hres_eq : buildOutputs n m gs cTrue prodWires prodKs mask' rj cj dj (j :: js) = (resSub.1, r.2 :: resSub.2) := rfl
    change gs.length ≤ (buildOutputs n m gs cTrue prodWires prodKs mask' rj cj dj (j :: js)).1.length ∧ _
    rw [hres_eq]
    refine ⟨le_trans hL1 hLr, ?_, ?_, hRBr, hLenr, hCntr.trans hCnt1, by simp only [List.length_cons, hResLen], ?_⟩
    · intro x hx w hw
      exact (hWr x hx w (by omega)).trans (hW1 x hx w hw)
    · intro w hw
      exact (hDr w (by omega)).trans (hD1 w hw)
    · intro idx
      refine Fin.cases ?_ ?_ idx
      · simp only [Fin.val_zero, List.getD_cons_zero]
        refine ⟨?_, ?_⟩
        · rw [hDr r.2 hOut1Lt]; exact hOut1Dep
        · intro x y; rw [hWr _ (oneEach_length x y) r.2 hOut1Lt, hValJ x y]; rfl
      · intro idx'
        simp only [Fin.val_succ, List.getD_cons_succ]
        exact hIdx idx'

private lemma dep0_isAff {n m : ℕ} (gs : List Gate)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨gs, 0⟩)
    (hLen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ w : ℕ, (depthsL (n + m) gs).getD w 0 = 0 →
      IsAff (fun (x : Fin n) (y : Fin m) => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false)) := by
  have hrb_idx : ∀ k : Fin gs.length, ∀ a ∈ gs[k].inputs, a < n + m + k.val := by
    intro k a ha
    have h1 := hRB k.val k.isLt a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
    rw [List.getD_eq_getElem _ _ k.isLt] at h1
    exact h1 ha
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hdw
    by_cases hltW : w < n + m
    · by_cases hltn : w < n
      · refine ⟨fun x => if x.val = w then 1 else 0, 0, 0, fun x y => ?_⟩
        have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false = decide (x.val = w) := by
          rw [wiresL_getD_input gs _ w (by rw [oneEach_length]; exact hltW)]
          exact oneEach_getD_left x y w hltn
        dsimp only; rw [hv]; by_cases hx : x.val = w <;> simp [hx, b2f_true, b2f_false]
      · refine ⟨0, fun y => if y.val = w - n then 1 else 0, 0, fun x y => ?_⟩
        have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false = decide (y.val = w - n) := by
          rw [wiresL_getD_input gs _ w (by rw [oneEach_length]; exact hltW)]
          exact oneEach_getD_right x y w (by omega) hltW
        dsimp only; rw [hv]; by_cases hy : y.val = w - n <;> simp [hy, b2f_true, b2f_false]
    · by_cases hge : n + m + gs.length ≤ w
      · have hfun : (fun (x : Fin n) (y : Fin m) =>
            b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false)) = (fun _ _ => (0 : F2)) := by
          funext x y
          rw [wiresL_getD_ge gs _ w (by rw [oneEach_length]; exact hge)]; rfl
        rw [hfun]; exact isAff_const 0
      · let k : Fin gs.length := ⟨w - (n + m), by omega⟩
        have hw_eq : w = n + m + k.val := by dsimp only [k]; omega
        rw [hw_eq] at hdw ⊢
        rw [depthsL_getD_gate (n + m) gs k.val k.isLt (hrb_idx k)] at hdw
        change (gs[k].inputs.map (fun a => (depthsL (n + m) gs).getD a 0)).foldr max 0 + (nonlinear gs[k]).toNat = 0 at hdw
        have hnl_false : nonlinear gs[k] = false := by
          cases hnl : nonlinear gs[k]
          · rfl
          · rw [hnl] at hdw; simp at hdw
        have hmax0 : (gs[k].inputs.map (fun a => (depthsL (n + m) gs).getD a 0)).foldr max 0 ≤ 0 := by omega
        have hda0 : ∀ a ∈ gs[k].inputs, (depthsL (n + m) gs).getD a 0 = 0 := by
          intro a ha
          have hle := (foldr_max_le_iff _ 0).mp hmax0 _ (List.mem_map_of_mem ha)
          omega
        have haff_in : ∀ a ∈ gs[k].inputs,
            IsAff (fun (x : Fin n) (y : Fin m) => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false)) :=
          fun a ha => ih a (by have := hrb_idx k a ha; omega) (hda0 a ha)
        have hlen_k : gs[k].inputs.length ≤ 2 := hLen gs[k] (List.getElem_mem k.isLt)
        have hval_k : ∀ (x : Fin n) (y : Fin m),
            (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
              gs[k].op.eval (gs[k].inputs.map fun a => (wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false) := by
          intro x y
          have h1 := wiresL_getD_gate gs (PEqualNP.Represents.oneEach x y) k.val k.isLt
            (by rw [oneEach_length]; exact hrb_idx k)
          rw [oneEach_length] at h1
          exact h1
        rcases hlist : gs[k].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · have hfun : (fun (x : Fin n) (y : Fin m) =>
              b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false)) =
              (fun _ _ => b2f (gs[k].op.eval [])) := by
            funext x y; rw [hval_k x y, hlist]; rfl
          rw [hfun]; exact isAff_const _
        · have hfun : (fun (x : Fin n) (y : Fin m) =>
              b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false)) =
              (fun x y => b2f (gs[k].op.eval [false]) +
                (b2f (gs[k].op.eval [false]) + b2f (gs[k].op.eval [true])) *
                  b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false)) := by
            funext x y
            have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
                gs[k].op.eval [(wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false] := by
              rw [hval_k x y, hlist]; rfl
            rw [hv, gate_eval_unary]
          rw [hfun]
          exact isAff_add (isAff_const _) (isAff_smul _ (haff_in a (by rw [hlist]; simp)))
        · have hc3 : xor (xor (gs[k].op.eval [false, false]) (gs[k].op.eval [false, true]))
              (xor (gs[k].op.eval [true, false]) (gs[k].op.eval [true, true])) = false := by
            unfold nonlinear at hnl_false; rw [hlist] at hnl_false; simpa using hnl_false
          have hfun : (fun (x : Fin n) (y : Fin m) =>
              b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false)) =
              (fun x y => (b2f (gs[k].op.eval [false, false]) +
                (b2f (gs[k].op.eval [false, false]) + b2f (gs[k].op.eval [true, false])) *
                  b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false)) +
                (b2f (gs[k].op.eval [false, false]) + b2f (gs[k].op.eval [false, true])) *
                  b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD b false)) := by
            funext x y
            have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
                gs[k].op.eval [(wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false,
                               (wiresL gs (PEqualNP.Represents.oneEach x y)).getD b false] := by
              rw [hval_k x y, hlist]; rfl
            rw [hv, gate_eval_binary, hc3, b2f_false, zero_mul, add_zero]
          rw [hfun]
          exact isAff_add
            (isAff_add (isAff_const _) (isAff_smul _ (haff_in a (by rw [hlist]; simp))))
            (isAff_smul _ (haff_in b (by rw [hlist]; simp)))
        · rw [hlist] at hlen_k; simp at hlen_k

private lemma dep1_rep {n m K : ℕ} (gs : List Gate)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨gs, 0⟩)
    (hLen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (nlIdx : Fin K → Fin gs.length)
    (hnl_surj : ∀ k : Fin gs.length, nonlinear gs[k] = true → (depthsL (n + m) gs).getD (n + m + k.val) 0 ≤ 1 →
      ∃ idx : Fin K, nlIdx idx = k) :
    ∀ w : ℕ, (depthsL (n + m) gs).getD w 0 ≤ 1 →
      ∃ (coeff : Fin K → F2) (aff : Fin n → Fin m → F2), IsAff aff ∧
        ∀ (x : Fin n) (y : Fin m),
          b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false) =
            (∑ idx : Fin K, coeff idx * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx idx).val) false)) + aff x y := by
  have hrb_idx : ∀ k : Fin gs.length, ∀ a ∈ gs[k].inputs, a < n + m + k.val := by
    intro k a ha
    have h1 := hRB k.val k.isLt a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
    rw [List.getD_eq_getElem _ _ k.isLt] at h1
    exact h1 ha
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hdw
    by_cases h0 : (depthsL (n + m) gs).getD w 0 = 0
    · exact ⟨0, fun x y => b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD w false),
        dep0_isAff gs hRB hLen w h0,
        fun x y => by simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]⟩
    · have hgeW : n + m ≤ w := by
        by_contra hlt; push Not at hlt
        exact h0 (depthsL_getD_input (n + m) gs w hlt)
      have hltWN : w < n + m + gs.length := by
        by_contra hge; push Not at hge
        exact h0 (depthsL_getD_ge (n + m) gs w hge)
      let k : Fin gs.length := ⟨w - (n + m), by omega⟩
      have hw_eq : w = n + m + k.val := by dsimp only [k]; omega
      have hdwk : (depthsL (n + m) gs).getD (n + m + k.val) 0 ≤ 1 := hw_eq ▸ hdw
      rw [hw_eq]
      by_cases hnl : nonlinear gs[k] = true
      · obtain ⟨idx, hidx⟩ := hnl_surj k hnl hdwk
        refine ⟨fun j => if j = idx then 1 else 0, 0, isAff_const 0, fun x y => ?_⟩
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Pi.zero_apply, add_zero, hidx]
      · have hnl_false : nonlinear gs[k] = false := by cases h : nonlinear gs[k] <;> simp_all
        have hdg : (depthsL (n + m) gs).getD (n + m + k.val) 0 =
            (gs[k].inputs.map (fun a => (depthsL (n + m) gs).getD a 0)).foldr max 0 + (nonlinear gs[k]).toNat :=
          depthsL_getD_gate (n + m) gs k.val k.isLt (hrb_idx k)
        rw [hnl_false, Bool.toNat_false, add_zero] at hdg
        have hmax1 : (gs[k].inputs.map (fun a => (depthsL (n + m) gs).getD a 0)).foldr max 0 ≤ 1 := by omega
        have hda1 : ∀ a ∈ gs[k].inputs, (depthsL (n + m) gs).getD a 0 ≤ 1 := fun a ha =>
          (foldr_max_le_iff _ 1).mp hmax1 _ (List.mem_map_of_mem ha)
        have hlen_k : gs[k].inputs.length ≤ 2 := hLen gs[k] (List.getElem_mem k.isLt)
        have hval_k : ∀ (x : Fin n) (y : Fin m),
            (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
              gs[k].op.eval (gs[k].inputs.map fun a => (wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false) := by
          intro x y
          have h1 := wiresL_getD_gate gs (PEqualNP.Represents.oneEach x y) k.val k.isLt
            (by rw [oneEach_length]; exact hrb_idx k)
          rw [oneEach_length] at h1
          exact h1
        have hih_in : ∀ a ∈ gs[k].inputs,
            ∃ (coeff : Fin K → F2) (aff : Fin n → Fin m → F2), IsAff aff ∧
              ∀ (x : Fin n) (y : Fin m),
                b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false) =
                  (∑ idx : Fin K, coeff idx * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx idx).val) false)) + aff x y :=
          fun a ha => ih a (by have := hrb_idx k a ha; omega) (hda1 a ha)
        cases hlist : gs[k].inputs with
        | nil =>
          refine ⟨0, fun _ _ => b2f (gs[k].op.eval []), isAff_const _, fun x y => ?_⟩
          have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false = gs[k].op.eval [] := by
            rw [hval_k x y, hlist]; rfl
          simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, hv]
        | cons a rest =>
          cases rest with
          | nil =>
            obtain ⟨ca, affa, haffa, hrep_a⟩ := hih_in a (by rw [hlist]; simp)
            let c0 := b2f (gs[k].op.eval [false])
            let c1 := b2f (gs[k].op.eval [false]) + b2f (gs[k].op.eval [true])
            refine ⟨fun j => c1 * ca j, fun x y => c0 + c1 * affa x y,
              isAff_add (isAff_const _) (isAff_smul _ haffa), fun x y => ?_⟩
            have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
                gs[k].op.eval [(wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false] := by
              rw [hval_k x y, hlist]; rfl
            rw [hv, gate_eval_unary, hrep_a x y, mul_add, Finset.mul_sum]
            have hsum : ∑ j : Fin K, c1 * (ca j * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx j).val) false)) =
                ∑ j : Fin K, c1 * ca j * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx j).val) false) := by
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [hsum]; ring
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              obtain ⟨ca, affa, haffa, hrep_a⟩ := hih_in a (by rw [hlist]; simp)
              obtain ⟨cb, affb, haffb, hrep_b⟩ := hih_in b (by rw [hlist]; simp)
              let c0 := b2f (gs[k].op.eval [false, false])
              let c1 := b2f (gs[k].op.eval [false, false]) + b2f (gs[k].op.eval [true, false])
              let c2 := b2f (gs[k].op.eval [false, false]) + b2f (gs[k].op.eval [false, true])
              have hc3 : xor (xor (gs[k].op.eval [false, false]) (gs[k].op.eval [false, true]))
                  (xor (gs[k].op.eval [true, false]) (gs[k].op.eval [true, true])) = false := by
                unfold nonlinear at hnl_false; rw [hlist] at hnl_false; simpa using hnl_false
              refine ⟨fun j => c1 * ca j + c2 * cb j, fun x y => c0 + c1 * affa x y + c2 * affb x y,
                isAff_add (isAff_add (isAff_const _) (isAff_smul _ haffa)) (isAff_smul _ haffb), fun x y => ?_⟩
              have hv : (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
                  gs[k].op.eval [(wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false,
                                 (wiresL gs (PEqualNP.Represents.oneEach x y)).getD b false] := by
                rw [hval_k x y, hlist]; rfl
              rw [hv, gate_eval_binary, hc3, b2f_false, zero_mul, add_zero, hrep_a x y, hrep_b x y]
              have hsum : ∑ j : Fin K, (c1 * ca j + c2 * cb j) * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx j).val) false) =
                  c1 * (∑ j : Fin K, ca j * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx j).val) false)) +
                  c2 * (∑ j : Fin K, cb j * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx j).val) false)) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => by ring
              rw [hsum]; ring
            | cons c tl =>
              rw [hlist] at hlen_k; simp at hlen_k

private lemma extract_rank2_rep {n m r t : ℕ} (G : Fin r → Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (hfits : fits n m r G t) :
    let entry := fun j x y => if G j x y then (1 : F2) else 0
    let A : Fin r → Matrix (Fin n) (Fin m) F2 := fun j x y =>
      entry j x y + entry j x v + entry j u y + entry j u v
    ∃ (K : ℕ) (α1 α2 : Fin K → Fin n → F2) (β1 β2 : Fin K → Fin m → F2) (mask : Fin r → Fin K → F2),
      K ≤ t ∧ ∀ j : Fin r,
        A j = ∑ idx : Fin K, mask j idx • (fun x y => α1 idx x * β2 idx y + α2 idx x * β1 idx y) := by
  classical
  intro entry A
  rcases hfits with ⟨C, tap, hRB, hLen, hCnt, hTap⟩
  let gs := C.gates
  have hRB' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) ⟨gs, 0⟩ := hRB
  let NL : Finset (Fin gs.length) :=
    Finset.univ.filter (fun k : Fin gs.length => nonlinear gs[k] = true ∧ (depthsL (n + m) gs).getD (n + m + k.val) 0 ≤ 1)
  have hNL_le_t : NL.card ≤ t := by
    have hsub : NL ⊆ Finset.univ.filter (fun k : Fin gs.length => nonlinear gs[k] = true) := by
      intro k hk; simp only [NL, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; exact hk.1
    have h1 := Finset.card_le_card hsub
    rw [card_filter_fin_eq_countP gs nonlinear] at h1
    exact le_trans h1 hCnt
  obtain ⟨K, hK_eq⟩ : ∃ K : ℕ, K = NL.card := ⟨NL.card, rfl⟩
  have hK_le_t : K ≤ t := hK_eq.symm ▸ hNL_le_t
  let eNL : Fin K ≃ {k : Fin gs.length // k ∈ NL} := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, ← hK_eq])).symm
  let nlIdx : Fin K → Fin gs.length := fun idx => (eNL idx).val
  have hnl_surj : ∀ k : Fin gs.length, nonlinear gs[k] = true → (depthsL (n + m) gs).getD (n + m + k.val) 0 ≤ 1 →
      ∃ idx : Fin K, nlIdx idx = k := by
    intro k hnl hdk
    have hkNL : k ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hnl, hdk⟩
    exact ⟨eNL.symm ⟨k, hkNL⟩, by simp [nlIdx]⟩
  have hrb_idx : ∀ k : Fin gs.length, ∀ a ∈ gs[k].inputs, a < n + m + k.val := by
    intro k a ha
    have h1 := hRB' k.val k.isLt a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
    rw [List.getD_eq_getElem _ _ k.isLt] at h1
    exact h1 ha
  have hNL_rank2 : ∀ idx : Fin K,
      ∃ (α1 α2 : Fin n → F2) (β1 β2 : Fin m → F2),
        ∀ x y,
          b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx idx).val) false) +
          b2f ((wiresL gs (PEqualNP.Represents.oneEach x v)).getD (n + m + (nlIdx idx).val) false) +
          b2f ((wiresL gs (PEqualNP.Represents.oneEach u y)).getD (n + m + (nlIdx idx).val) false) +
          b2f ((wiresL gs (PEqualNP.Represents.oneEach u v)).getD (n + m + (nlIdx idx).val) false) =
            α1 x * β2 y + α2 x * β1 y := by
    intro idx
    let k := nlIdx idx
    have hkNL : k ∈ NL := (eNL idx).property
    rcases (Finset.mem_filter.mp hkNL).2 with ⟨hnl, hdk1⟩
    have hlen2 : gs[k].inputs.length = 2 := by
      unfold nonlinear at hnl
      exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hnl).1
    have hc3_true : xor (xor (gs[k].op.eval [false, false]) (gs[k].op.eval [false, true]))
        (xor (gs[k].op.eval [true, false]) (gs[k].op.eval [true, true])) = true := by
      unfold nonlinear at hnl
      exact ((Bool.and_eq_true _ _).mp hnl).2
    have hdg : (depthsL (n + m) gs).getD (n + m + k.val) 0 =
        (gs[k].inputs.map (fun a => (depthsL (n + m) gs).getD a 0)).foldr max 0 + (nonlinear gs[k]).toNat :=
      depthsL_getD_gate (n + m) gs k.val k.isLt (hrb_idx k)
    rw [hnl, Bool.toNat_true] at hdg
    have hmax0 : (gs[k].inputs.map (fun a => (depthsL (n + m) gs).getD a 0)).foldr max 0 ≤ 0 := by omega
    have hval_k : ∀ (x : Fin n) (y : Fin m),
        (wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + k.val) false =
          gs[k].op.eval (gs[k].inputs.map fun a => (wiresL gs (PEqualNP.Represents.oneEach x y)).getD a false) := by
      intro x y
      have h1 := wiresL_getD_gate gs (PEqualNP.Represents.oneEach x y) k.val k.isLt
        (by rw [oneEach_length]; exact hrb_idx k)
      rw [oneEach_length] at h1
      exact h1
    rcases hlist : gs[k].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · rw [hlist] at hlen2; simp at hlen2
    · rw [hlist] at hlen2; simp at hlen2
    · have hda0 : (depthsL (n + m) gs).getD a 0 = 0 := by
        have := (foldr_max_le_iff _ 0).mp hmax0 ((depthsL (n + m) gs).getD a 0) (List.mem_map_of_mem (by rw [hlist]; simp))
        omega
      have hdb0 : (depthsL (n + m) gs).getD b 0 = 0 := by
        have := (foldr_max_le_iff _ 0).mp hmax0 ((depthsL (n + m) gs).getD b 0) (List.mem_map_of_mem (by rw [hlist]; simp))
        omega
      obtain ⟨r1, c1, d1, hfa⟩ := dep0_isAff gs hRB' hLen a hda0
      obtain ⟨r2, c2, d2, hfb⟩ := dep0_isAff gs hRB' hLen b hdb0
      dsimp only at hfa hfb
      refine ⟨fun x => r1 x + r1 u, fun x => r2 x + r2 u, fun y => c1 y + c1 v, fun y => c2 y + c2 v, ?_⟩
      intro x y
      let c0 := b2f (gs[k].op.eval [false, false])
      let k1 := b2f (gs[k].op.eval [false, false]) + b2f (gs[k].op.eval [true, false])
      let k2 := b2f (gs[k].op.eval [false, false]) + b2f (gs[k].op.eval [false, true])
      have hv : ∀ x' y', b2f ((wiresL gs (PEqualNP.Represents.oneEach x' y')).getD (n + m + k.val) false) =
          (r1 x' * c2 y' + r2 x' * c1 y') +
          ((r1 x' * r2 x' + (d2 + k1) * r1 x' + (d1 + k2) * r2 x') +
           (c1 y' * c2 y' + (d2 + k1) * c1 y' + (d1 + k2) * c2 y') +
           (c0 + k1 * d1 + k2 * d2 + d1 * d2)) := by
        intro x' y'
        have hvg : (wiresL gs (PEqualNP.Represents.oneEach x' y')).getD (n + m + k.val) false =
            gs[k].op.eval [(wiresL gs (PEqualNP.Represents.oneEach x' y')).getD a false,
                           (wiresL gs (PEqualNP.Represents.oneEach x' y')).getD b false] := by
          rw [hval_k x' y', hlist]; rfl
        rw [hvg, gate_eval_binary, hc3_true, b2f_true, one_mul, hfa x' y', hfb x' y']
        ring
      have haff_rest : IsAff (fun x' y' =>
          (r1 x' * r2 x' + (d2 + k1) * r1 x' + (d1 + k2) * r2 x') +
          (c1 y' * c2 y' + (d2 + k1) * c1 y' + (d1 + k2) * c2 y') +
          (c0 + k1 * d1 + k2 * d2 + d1 * d2)) :=
        ⟨_, _, _, fun _ _ => rfl⟩
      have hdel_rest := delta_isAff u v haff_rest x y
      rw [hv x y, hv x v, hv u y, hv u v]
      linear_combination hdel_rest
    · rw [hlist] at hlen2; simp at hlen2
  choose α1 α2 β1 β2 hM_eq using hNL_rank2
  have hTap_rep : ∀ j : Fin r, ∃ mask_j : Fin K → F2,
      A j = ∑ idx : Fin K, mask_j idx • (fun x y => α1 idx x * β2 idx y + α2 idx x * β1 idx y) := by
    intro j
    obtain ⟨hdep_j, hrep_j⟩ := hTap j
    obtain ⟨coeff, aff, haff, hval_j⟩ := dep1_rep gs hRB' hLen nlIdx hnl_surj (tap j) hdep_j
    refine ⟨coeff, ?_⟩
    ext x y
    have hgj : ∀ x' y', entry j x' y' = b2f ((wiresL gs (PEqualNP.Represents.oneEach x' y')).getD (tap j) false) := by
      intro x' y'
      have hre := hrep_j x' y'
      change (wiresL gs (PEqualNP.Represents.oneEach x' y')).getD (tap j) false = G j x' y' at hre
      dsimp only [entry, b2f]
      rw [hre]
    simp only [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hgj x y, hgj x v, hgj u y, hgj u v, hval_j x y, hval_j x v, hval_j u y, hval_j u v]
    have hdel_aff := delta_isAff u v haff x y
    have hsum :
        (∑ k : Fin K, coeff k * b2f ((wiresL gs (PEqualNP.Represents.oneEach x y)).getD (n + m + (nlIdx k).val) false)) +
        (∑ k : Fin K, coeff k * b2f ((wiresL gs (PEqualNP.Represents.oneEach x v)).getD (n + m + (nlIdx k).val) false)) +
        (∑ k : Fin K, coeff k * b2f ((wiresL gs (PEqualNP.Represents.oneEach u y)).getD (n + m + (nlIdx k).val) false)) +
        (∑ k : Fin K, coeff k * b2f ((wiresL gs (PEqualNP.Represents.oneEach u v)).getD (n + m + (nlIdx k).val) false)) =
        ∑ k : Fin K, coeff k * (α1 k x * β2 k y + α2 k x * β1 k y) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hM_eq k x y]; ring
    linear_combination hsum + hdel_aff
  choose mask hA_eq using hTap_rep
  exact ⟨K, α1, α2, β1, β2, mask, hK_le_t, hA_eq⟩

private lemma build_reduced_circuit {n m q K : ℕ}
    (G' : Fin q → Fin n → Fin m → Bool)
    (S : Finset (Fin K))
    (a1 a2 : Fin K → Fin n → F2) (b1 b2 : Fin K → Fin m → F2)
    (mask' : Fin q → Fin K → F2) (rj : Fin q → Fin n → F2) (cj : Fin q → Fin m → F2) (dj : Fin q → F2)
    (hdecomp : ∀ (j : Fin q) (x : Fin n) (y : Fin m),
      b2f (G' j x y) =
        (∑ k ∈ S, mask' j k * ((a1 k x + b1 k y) * (a2 k x + b2 k y))) + rj j x + cj j y + dj j) :
    fits n m q G' S.card := by
  let W := n + m
  let gs0 : List Gate := [⟨GateOp.and, []⟩]
  let cTrue : ℕ := W
  have hRB0 : PEqualNP.MetaComplexity.NestedCover.ReadsBack W ⟨gs0, 0⟩ := by
    intro j hj i hi
    have hj0 : j = 0 := by simp [gs0] at hj; omega
    subst hj0
    simp [gs0, PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
  have hLen0 : ∀ g ∈ gs0, g.inputs.length ≤ 2 := by
    intro g hg; simp only [gs0, List.mem_singleton] at hg; subst hg; decide
  have hCnt0 : gs0.countP nonlinear = 0 := by simp [gs0, nonlinear_const_true]
  have hcTrue_lt : cTrue < W + gs0.length := by simp [gs0, cTrue]
  have hcTrue_dep : (depthsL W gs0).getD cTrue 0 ≤ 1 := by
    have h1 := depthsL_getD_append_last W [] ⟨GateOp.and, []⟩
    simp only [List.nil_append, List.length_nil, add_zero, nonlinear_const_true] at h1
    change (depthsL W [⟨GateOp.and, []⟩]).getD W 0 ≤ 1
    rw [h1]; simp
  have hcTrue_val : ∀ (x : Fin n) (y : Fin m),
      (wiresL gs0 (PEqualNP.Represents.oneEach x y)).getD cTrue false = true := by
    intro x y
    have h1 := wiresL_getD_append_last [] ⟨GateOp.and, []⟩ (PEqualNP.Represents.oneEach x y)
    simp only [List.nil_append, List.length_nil, add_zero, oneEach_length] at h1
    change (wiresL [⟨GateOp.and, []⟩] (PEqualNP.Represents.oneEach x y)).getD W false = true
    rw [h1]; rfl
  let Slist : List (Fin K) := S.toList
  let ksNat : List ℕ := Slist.map Fin.val
  let a1N : ℕ → Fin n → F2 := fun k x => if hk : k < K then a1 ⟨k, hk⟩ x else 0
  let a2N : ℕ → Fin n → F2 := fun k x => if hk : k < K then a2 ⟨k, hk⟩ x else 0
  let b1N : ℕ → Fin m → F2 := fun k y => if hk : k < K then b1 ⟨k, hk⟩ y else 0
  let b2N : ℕ → Fin m → F2 := fun k y => if hk : k < K then b2 ⟨k, hk⟩ y else 0
  let QN : ℕ → Fin n → Fin m → F2 := fun k x y => (a1N k x + b1N k y) * (a2N k x + b2N k y)
  let mask'N : ℕ → ℕ → F2 := fun j k =>
    if hj : j < q then if hk : k < K then mask' ⟨j, hj⟩ ⟨k, hk⟩ else 0 else 0
  let rjN : ℕ → Fin n → F2 := fun j x => if hj : j < q then rj ⟨j, hj⟩ x else 0
  let cjN : ℕ → Fin m → F2 := fun j y => if hj : j < q then cj ⟨j, hj⟩ y else 0
  let djN : ℕ → F2 := fun j => if hj : j < q then dj ⟨j, hj⟩ else 0
  rcases buildProducts_spec n m a1N a2N b1N b2N ksNat gs0 hRB0 hLen0 with
    ⟨hLp, hWp, hDp, hRBp, hLenp, hCntp, _, hPidx⟩
  set resP := buildProducts n m gs0 a1N a2N b1N b2N ksNat
  let jsNat : List ℕ := (List.finRange q).map Fin.val
  rcases buildOutputs_spec n m cTrue resP.2 ksNat QN mask'N rjN cjN djN jsNat resP.1
    hRBp hLenp (by omega) (by rw [hDp cTrue hcTrue_lt]; exact hcTrue_dep)
    (fun x y => by rw [hWp _ (oneEach_length x y) cTrue hcTrue_lt]; exact hcTrue_val x y) hPidx with
    ⟨_, _, _, hRBo, hLeno, hCnto, _, hOidx⟩
  set resO := buildOutputs n m resP.1 cTrue resP.2 ksNat mask'N rjN cjN djN jsNat
  let C' : Circuit := ⟨resO.1, 0⟩
  let tap' : Fin q → ℕ := fun j => resO.2.getD j.val 0
  refine ⟨C', tap', hRBo, hLeno, ?_, ?_⟩
  · have hSlen : ksNat.length = S.card := by simp [ksNat, Slist]
    change resO.1.countP nonlinear ≤ S.card
    rw [hCnto, hCntp, hCnt0, zero_add, hSlen]
  · intro j
    have hj_lt : j.val < jsNat.length := by simp [jsNat]
    have ho := hOidx ⟨j.val, hj_lt⟩
    have hjs_val : jsNat[(⟨j.val, hj_lt⟩ : Fin jsNat.length)] = j.val := by simp [jsNat]
    refine ⟨ho.1, ?_⟩
    intro x y
    apply b2f_injective
    have h1 := ho.2 x y
    rw [hjs_val] at h1
    change b2f ((wiresL resO.1 (PEqualNP.Represents.oneEach x y)).getD (tap' j) false) = b2f (G' j x y)
    rw [h1]
    have hsumS : (∑ idx : Fin ksNat.length, mask'N j.val ksNat[idx] * QN ksNat[idx] x y) =
        ∑ k ∈ S, mask' j k * ((a1 k x + b1 k y) * (a2 k x + b2 k y)) := by
      have hSlen : ksNat.length = Slist.length := by simp [ksNat]
      have h1' : (∑ idx : Fin ksNat.length, mask'N j.val ksNat[idx] * QN ksNat[idx] x y) =
          ∑ idx : Fin Slist.length, mask' j Slist[idx] * ((a1 Slist[idx] x + b1 Slist[idx] y) * (a2 Slist[idx] x + b2 Slist[idx] y)) := by
        refine Finset.sum_bij (fun idx _ => ⟨idx.val, by omega⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro i1 _ i2 _ heq; exact Fin.ext (congrArg (Fin.val : Fin Slist.length → ℕ) heq)
        · intro idx _; exact ⟨⟨idx.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro idx _
          have hkget : ksNat[idx] = Slist[idx.val].val := by simp [ksNat]
          rw [hkget]
          have hltK : (Slist[idx.val]'(by omega)).val < K := (Slist[idx.val]'(by omega)).isLt
          simp only [mask'N, QN, a1N, a2N, b1N, b2N, j.isLt, hltK, ↓reduceDIte, Fin.eta]
          rfl
      rw [h1', sum_fin_list_map Slist (fun k => mask' j k * ((a1 k x + b1 k y) * (a2 k x + b2 k y)))]
      exact list_map_sum_eq_finset_sum S (fun k => mask' j k * ((a1 k x + b1 k y) * (a2 k x + b2 k y)))
    rw [hsumS]
    simp only [rjN, cjN, djN, j.isLt, ↓reduceDIte, Fin.eta]
    rw [← hdecomp j x y]

private lemma main_25751 (n m p q : ℕ) (G : Fin (p + q) → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) :
    let entry := fun j x y => if G j x y then (1 : F2) else 0
    let A : Fin (p + q) → Matrix (Fin n) (Fin m) F2 := fun j x y =>
      entry j x y + entry j x v + entry j u y + entry j u v
    LinearIndependent F2 (fun i : Fin p => A (Fin.castAdd q i)) →
    (∃ L : Matrix (Fin n) (Fin n) F2,
      (∀ i : Fin p, L * A (Fin.castAdd q i) = 0) ∧
      (∀ j : Fin q, L * A (Fin.natAdd p j) = A (Fin.natAdd p j))) →
    ∀ t : ℕ, fits n m (p + q) G t →
      ∃ s : ℕ, s + p ≤ t ∧ fits n m q (fun j => G (Fin.natAdd p j)) s := by
  classical
  intro entry A hLI hLex t hfits
  rcases hLex with ⟨L, hL1, hL2⟩
  obtain ⟨K, α1, α2, β1, β2, mask, hK_le_t, hA_eq_raw⟩ := extract_rank2_rep G u v hfits
  let M : Fin K → Matrix (Fin n) (Fin m) F2 := fun idx x y => α1 idx x * β2 idx y + α2 idx x * β1 idx y
  have hA_eq : ∀ j : Fin (p + q), A j = ∑ idx : Fin K, mask j idx • M idx := hA_eq_raw
  let R : Fin p → Fin K → F2 := fun i => mask (Fin.castAdd q i)
  have hLI_R : LinearIndependent F2 R := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsumA : ∑ i : Fin p, c i • A (Fin.castAdd q i) = 0 := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      have h1 : ∑ i : Fin p, c i * A (Fin.castAdd q i) x y =
          ∑ idx : Fin K, (∑ i : Fin p, c i * R i idx) * M idx x y := by
        calc ∑ i : Fin p, c i * A (Fin.castAdd q i) x y
            = ∑ i : Fin p, c i * (∑ idx : Fin K, R i idx * M idx x y) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [hA_eq (Fin.castAdd q i)]; simp [R]
          _ = ∑ i : Fin p, ∑ idx : Fin K, c i * (R i idx * M idx x y) := by
                refine Finset.sum_congr rfl fun i _ => Finset.mul_sum ..
          _ = ∑ idx : Fin K, ∑ i : Fin p, c i * (R i idx * M idx x y) := Finset.sum_comm
          _ = ∑ idx : Fin K, (∑ i : Fin p, c i * R i idx) * M idx x y := by
                refine Finset.sum_congr rfl fun idx _ => ?_
                rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [h1]
      refine Finset.sum_eq_zero fun idx _ => ?_
      have hci := congrFun hc idx
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hci
      rw [hci, zero_mul]
    exact (Fintype.linearIndependent_iff.mp hLI) c hsumA
  obtain ⟨S, hScard, hSelim⟩ := elim_columns p K R hLI_R
  choose γ hγ using fun j : Fin q => hSelim (mask (Fin.natAdd p j))
  let mask' : Fin q → Fin K → F2 := fun j => mask (Fin.natAdd p j) + ∑ i : Fin p, γ j i • R i
  have hmask'_zero : ∀ j : Fin q, ∀ k : Fin K, k ∉ S → mask' j k = 0 := hγ
  have hA_L : ∀ j : Fin q, A (Fin.natAdd p j) = ∑ k ∈ S, mask' j k • (L * M k) := by
    intro j
    have hcomb : A (Fin.natAdd p j) + ∑ i : Fin p, γ j i • A (Fin.castAdd q i) =
        ∑ k ∈ S, mask' j k • M k := by
      have h1 : A (Fin.natAdd p j) + ∑ i : Fin p, γ j i • A (Fin.castAdd q i) =
          ∑ k : Fin K, mask' j k • M k := by
        ext x y
        simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mask', Pi.add_apply,
          Finset.sum_apply, Pi.smul_apply]
        rw [hA_eq (Fin.natAdd p j)]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        have h2 : ∑ i : Fin p, γ j i * A (Fin.castAdd q i) x y =
            ∑ k : Fin K, (∑ i : Fin p, γ j i * R i k) * M k x y := by
          calc ∑ i : Fin p, γ j i * A (Fin.castAdd q i) x y
              = ∑ i : Fin p, γ j i * (∑ k : Fin K, R i k * M k x y) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [hA_eq (Fin.castAdd q i)]; simp [R]
            _ = ∑ i : Fin p, ∑ k : Fin K, γ j i * (R i k * M k x y) := by
                  refine Finset.sum_congr rfl fun i _ => Finset.mul_sum ..
            _ = ∑ k : Fin K, ∑ i : Fin p, γ j i * (R i k * M k x y) := Finset.sum_comm
            _ = ∑ k : Fin K, (∑ i : Fin p, γ j i * R i k) * M k x y := by
                  refine Finset.sum_congr rfl fun k _ => ?_
                  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
        rw [h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [h1]
      symm
      refine Finset.sum_subset (Finset.subset_univ S) ?_
      intro k _ hkS
      rw [hmask'_zero j k hkS, zero_smul]
    calc A (Fin.natAdd p j)
        = L * A (Fin.natAdd p j) := (hL2 j).symm
      _ = L * A (Fin.natAdd p j) + ∑ i : Fin p, γ j i • (L * A (Fin.castAdd q i)) := by
          simp [hL1]
      _ = L * (A (Fin.natAdd p j) + ∑ i : Fin p, γ j i • A (Fin.castAdd q i)) := by
          rw [Matrix.mul_add, Matrix.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_smul]
      _ = L * (∑ k ∈ S, mask' j k • M k) := by rw [hcomb]
      _ = ∑ k ∈ S, mask' j k • (L * M k) := by
          rw [Matrix.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_smul]
  let a1 : Fin K → Fin n → F2 := fun k x => ∑ z : Fin n, L x z * α1 k z
  let a2 : Fin K → Fin n → F2 := fun k x => ∑ z : Fin n, L x z * α2 k z
  have hLM : ∀ (k : Fin K) (x : Fin n) (y : Fin m),
      (L * M k) x y = a1 k x * β2 k y + a2 k x * β1 k y := by
    intro k x y
    rw [Matrix.mul_apply]
    simp only [M, a1, a2, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => by ring
  let Q : Fin K → Fin n → Fin m → F2 := fun k x y => (a1 k x + β1 k y) * (a2 k x + β2 k y)
  have hQ_LM : ∀ (k : Fin K) (x : Fin n) (y : Fin m),
      (L * M k) x y = Q k x y + a1 k x * a2 k x + β1 k y * β2 k y := by
    intro k x y
    rw [hLM k x y]
    dsimp only [Q]
    have h1 := z2_add_self (a1 k x * a2 k x)
    have h2 := z2_add_self (β1 k y * β2 k y)
    linear_combination -h1 - h2
  let rj : Fin q → Fin n → F2 := fun j x =>
    entry (Fin.natAdd p j) x v + ∑ k ∈ S, mask' j k * (a1 k x * a2 k x)
  let cj : Fin q → Fin m → F2 := fun j y =>
    entry (Fin.natAdd p j) u y + ∑ k ∈ S, mask' j k * (β1 k y * β2 k y)
  let dj : Fin q → F2 := fun j => entry (Fin.natAdd p j) u v
  have hG_decomp : ∀ (j : Fin q) (x : Fin n) (y : Fin m),
      b2f (G (Fin.natAdd p j) x y) =
        (∑ k ∈ S, mask' j k * ((a1 k x + β1 k y) * (a2 k x + β2 k y))) + rj j x + cj j y + dj j := by
    intro j x y
    have hAj := congrFun (congrFun (hA_L j) x) y
    simp only [A, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hAj
    have hsumQ : ∑ k ∈ S, mask' j k * (L * M k) x y =
        (∑ k ∈ S, mask' j k * Q k x y) +
        (∑ k ∈ S, mask' j k * (a1 k x * a2 k x)) +
        (∑ k ∈ S, mask' j k * (β1 k y * β2 k y)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hQ_LM k x y]; ring
    change entry (Fin.natAdd p j) x y = _
    dsimp only [rj, cj, dj, Q] at hsumQ ⊢
    have h1 := z2_add_self (entry (Fin.natAdd p j) x v)
    have h2 := z2_add_self (entry (Fin.natAdd p j) u y)
    have h3 := z2_add_self (entry (Fin.natAdd p j) u v)
    linear_combination hAj + hsumQ - h1 - h2 - h3
  exact ⟨S.card, by omega, build_reduced_circuit (fun j => G (Fin.natAdd p j)) S a1 a2 β1 β2 mask' rj cj dj hG_decomp⟩

end PEqualNP.Outside.L_meta_25751_aux

theorem PEqualNP.Outside.L_meta_25751 :
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
∀ (n m p q : ℕ) (G : Fin (p+q) → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let F := ZMod 2
  let entry := fun j x y => if G j x y then (1 : F) else 0
  let A : Fin (p+q) → Matrix (Fin n) (Fin m) F := fun j x y =>
    entry j x y + entry j x v + entry j u y + entry j u v
  LinearIndependent F (fun i : Fin p => A (Fin.castAdd q i)) →
  (∃ L : Matrix (Fin n) (Fin n) F,
    (∀ i : Fin p, L * A (Fin.castAdd q i) = 0) ∧
    (∀ j : Fin q, L * A (Fin.natAdd p j) = A (Fin.natAdd p j))) →
  ∀ t : ℕ, fits n m (p+q) G t →
    ∃ s : ℕ, s+p ≤ t ∧ fits n m q (fun j => G (Fin.natAdd p j)) s := by
  intro nonlinear depths fits n m p q G u v F entry A
  exact PEqualNP.Outside.L_meta_25751_aux.main_25751 n m p q G u v
