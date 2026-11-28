import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1390

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq_W (C : Circuit) (w : List Bool) : C.wires w = W C.gates w := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_append (gs hs : List Gate) (w : List Bool) :
    W (gs ++ hs) w = W hs (W gs w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = W gs w ++ [g.op.eval (g.inputs.map fun i => (W gs w).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (w : List Bool) : (W gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (W (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (W gs w).getD t false) := by
  rw [W_snoc, getD_snoc]; simp [W_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (W (gs ++ [g]) w).getD i false = (W gs w).getD i false := by
  rw [W_snoc, getD_snoc]; simp [W_len, hi]

theorem W_append_old (gs hs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs.length) :
    (W (gs ++ hs) w).getD i false = (W gs w).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_wire (gs ++ hs) g w i (by simp; omega)]
    exact ih

def prefixInput (n : ℕ) (l : Fin (n + 1)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]

theorem prefixInput_len (n : ℕ) (l : Fin (n + 1)) : (prefixInput n l).length = n + 2 := by
  simp [prefixInput]

theorem prefixInput_lt (n : ℕ) (l : Fin (n + 1)) (i : ℕ) (hi : i < n) :
    (prefixInput n l).getD i false = decide (i < l.val) := by
  unfold prefixInput
  rw [List.getD_append _ _ _ _ (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

theorem prefixInput_n (n : ℕ) (l : Fin (n + 1)) :
    (prefixInput n l).getD n false = false := by
  unfold prefixInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem prefixInput_n1 (n : ℕ) (l : Fin (n + 1)) :
    (prefixInput n l).getD (n + 1) false = true := by
  unfold prefixInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

def vl (n : ℕ) (gs : List Gate) (u : ℕ) (l : Fin (n + 1)) : Bool :=
  (W gs (prefixInput n l)).getD u false

def isNotGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

theorem isNotGate_eq_true (g : Gate) : isNotGate g = true ↔ g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

theorem isNotGate_eq_false (g : Gate) : isNotGate g = false ↔ g.op ≠ GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

def nonNotCount (gs : List Gate) : ℕ := (gs.filter fun g => !isNotGate g).length

theorem filter_split (p : Gate → Bool) (l : List Gate) :
    (l.filter p).length + (l.filter fun g => !p g).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h] <;> omega

theorem notCount_eq_filter (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter isNotGate).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

theorem notCount_add_nonNotCount (C : Circuit) :
    PEqualNP.NotBracket.notCount C + nonNotCount C.gates = C.size := by
  rw [notCount_eq_filter]
  exact filter_split isNotGate C.gates

theorem nonNotCount_append (gs hs : List Gate) :
    nonNotCount (gs ++ hs) = nonNotCount gs + nonNotCount hs := by
  simp [nonNotCount, List.filter_append]

theorem notCount_append (gs hs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs ++ hs, o⟩ =
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + PEqualNP.NotBracket.notCount ⟨hs, 0⟩ := by
  rw [notCount_eq_filter, notCount_eq_filter, notCount_eq_filter]
  simp [List.filter_append]

theorem readsBack_of_append {m : ℕ} {gs hs : List Gate}
    (h1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs, 0⟩)
    (h2 : ∀ k < hs.length, ∀ i ∈ (hs.getD k ⟨GateOp.or, []⟩).inputs, i < m + gs.length + k) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs ++ hs, 0⟩ := by
  intro j hj i hi
  simp only [List.length_append] at hj
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  by_cases hlt : j < gs.length
  · have hget : (gs ++ hs).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
      List.getD_append _ _ _ _ hlt
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs.length ≤ j := Nat.le_of_not_lt hlt
    have hk : j - gs.length < hs.length := by omega
    have hget : (gs ++ hs).getD j ⟨GateOp.or, []⟩ = hs.getD (j - gs.length) ⟨GateOp.or, []⟩ :=
      List.getD_append_right _ _ _ _ hge
    rw [hget] at hi
    have := h2 (j - gs.length) hk i hi
    omega

theorem readsBack_snoc {m : ℕ} {gs : List Gate} {g : Gate}
    (h1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs, 0⟩)
    (h2 : ∀ i ∈ g.inputs, i < m + gs.length) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs ++ [g], 0⟩ := by
  apply readsBack_of_append h1
  intro k hk i hi
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  simp at hi
  exact Nat.lt_of_lt_of_le (h2 i hi) (by omega)

theorem fanInTwo_append {gs hs : List Gate}
    (h1 : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (h2 : PEqualNP.MetaComplexity.FanInTwo ⟨hs, 0⟩) :
    PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ hs, 0⟩ := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact h1 g hg
  · exact h2 g hg

def chg {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc ≠ f i.succ

def falls {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc = true ∧ f i.succ = false

def rises {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc = false ∧ f i.succ = true

theorem mem_chg {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ chg f ↔ f i.castSucc ≠ f i.succ := by simp [chg]

theorem mem_falls {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ falls f ↔ f i.castSucc = true ∧ f i.succ = false := by simp [falls]

theorem mem_rises {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ rises f ↔ f i.castSucc = false ∧ f i.succ = true := by simp [rises]

theorem chg_const {n : ℕ} {f : Fin (n + 1) → Bool} (h : ∀ t t', f t = f t') : chg f = ∅ := by
  ext i; rw [mem_chg]; simp [h i.castSucc i.succ]

theorem chg_congr {n : ℕ} {f g : Fin (n + 1) → Bool}
    (h : (∀ t, g t = f t) ∨ (∀ t, g t = !f t)) : chg g = chg f := by
  ext i; rw [mem_chg, mem_chg]
  rcases h with h | h
  · rw [h, h]
  · rw [h, h]; cases f i.castSucc <;> cases f i.succ <;> simp

theorem falls_not_eq_rises {n : ℕ} (f : Fin (n + 1) → Bool) :
    falls (fun t => !f t) = rises f := by
  ext i; rw [mem_falls, mem_rises]
  cases f i.castSucc <;> cases f i.succ <;> simp

theorem falls_congr {n : ℕ} {f g : Fin (n + 1) → Bool} (h : ∀ t, g t = f t) :
    falls g = falls f := by
  ext i; rw [mem_falls, mem_falls, h, h]

theorem falls_subset_chg {n : ℕ} (f : Fin (n + 1) → Bool) : falls f ⊆ chg f := by
  intro i hi; rw [mem_falls] at hi; rw [mem_chg]; rw [hi.1, hi.2]; decide

theorem rises_le_falls_succ {n : ℕ} (f : Fin (n + 1) → Bool) :
    (rises f).card ≤ (falls f).card + 1 := by
  have key : ∀ (k : ℕ) (hk : k ≤ n),
      ((falls f).filter fun i => i.val < k).card + (f ⟨k, by omega⟩).toNat =
      ((rises f).filter fun i => i.val < k).card + (f ⟨0, by omega⟩).toNat := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h1 : (falls f).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      have h2 : (rises f).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      rw [h1, h2]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      let idx : Fin n := ⟨k, by omega⟩
      have hcs : idx.castSucc = ⟨k, by omega⟩ := rfl
      have hsc : idx.succ = ⟨k + 1, by omega⟩ := rfl
      have hfsplit : (falls f).filter (fun i => i.val < k + 1) =
          if idx ∈ falls f then insert idx ((falls f).filter (fun i => i.val < k))
          else (falls f).filter (fun i => i.val < k) := by
        split_ifs with hm
        · ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact Or.inr ⟨hi, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hm, Nat.lt_succ_self k⟩
            · exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
        · ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact ⟨hi, hlt⟩
            · exfalso; exact hm ((Fin.ext heq : i = idx) ▸ hi)
          · rintro ⟨hi, hlt⟩; exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
      have hrsplit : (rises f).filter (fun i => i.val < k + 1) =
          if idx ∈ rises f then insert idx ((rises f).filter (fun i => i.val < k))
          else (rises f).filter (fun i => i.val < k) := by
        split_ifs with hm
        · ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact Or.inr ⟨hi, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hm, Nat.lt_succ_self k⟩
            · exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
        · ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact ⟨hi, hlt⟩
            · exfalso; exact hm ((Fin.ext heq : i = idx) ▸ hi)
          · rintro ⟨hi, hlt⟩; exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
      have hnf : idx ∉ (falls f).filter (fun i => i.val < k) := by simp [idx]
      have hnr : idx ∉ (rises f).filter (fun i => i.val < k) := by simp [idx]
      rw [hfsplit, hrsplit]
      have hmf : idx ∈ falls f ↔ f ⟨k, by omega⟩ = true ∧ f ⟨k + 1, by omega⟩ = false := by
        rw [mem_falls, hcs, hsc]
      have hmr : idx ∈ rises f ↔ f ⟨k, by omega⟩ = false ∧ f ⟨k + 1, by omega⟩ = true := by
        rw [mem_rises, hcs, hsc]
      cases h1 : f ⟨k, by omega⟩ <;> cases h2 : f ⟨k + 1, by omega⟩ <;>
        simp [hmf, hmr, h1, h2, Finset.card_insert_of_notMem hnf,
          Finset.card_insert_of_notMem hnr] at hprev ⊢ <;> omega
  have htop := key n (le_refl n)
  have hf : (falls f).filter (fun i => i.val < n) = falls f := by
    ext i; simp [i.isLt]
  have hr : (rises f).filter (fun i => i.val < n) = rises f := by
    ext i; simp [i.isLt]
  rw [hf, hr] at htop
  cases hlast : f ⟨n, by omega⟩ <;> cases hzero : f ⟨0, by omega⟩ <;>
    simp [hlast, hzero] at htop <;> omega

theorem eq_or_not_of_chg_eq {n : ℕ} {f g : Fin (n + 1) → Bool} (h : chg f = chg g) :
    (∀ l, f l = g l) ∨ (∀ l, f l = !g l) := by
  have step : ∀ (k : ℕ) (hk : k < n + 1),
      (f ⟨0, by omega⟩ = g ⟨0, by omega⟩ → f ⟨k, hk⟩ = g ⟨k, hk⟩) ∧
      (f ⟨0, by omega⟩ ≠ g ⟨0, by omega⟩ → f ⟨k, hk⟩ = !g ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun h0 => h0, fun h0 => ?_⟩
      cases hf : f ⟨0, by omega⟩ <;> cases hg : g ⟨0, by omega⟩ <;> simp_all
    | succ k ih =>
      intro hk
      have ⟨ih1, ih2⟩ := ih (by omega)
      let i : Fin n := ⟨k, by omega⟩
      have hch : (f i.castSucc ≠ f i.succ) ↔ (g i.castSucc ≠ g i.succ) := by
        have := Finset.ext_iff.1 h i
        simpa [mem_chg] using this
      have hcs : i.castSucc = ⟨k, by omega⟩ := rfl
      have hsc : i.succ = ⟨k + 1, hk⟩ := rfl
      rw [hcs, hsc] at hch
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · have hprev := ih1 h0
        cases hf1 : f ⟨k, by omega⟩ <;> cases hf2 : f ⟨k + 1, hk⟩ <;>
          cases hg2 : g ⟨k + 1, hk⟩ <;> simp_all
      · have hprev := ih2 h0
        cases hf1 : f ⟨k, by omega⟩ <;> cases hf2 : f ⟨k + 1, hk⟩ <;>
          cases hg1 : g ⟨k, by omega⟩ <;> cases hg2 : g ⟨k + 1, hk⟩ <;> simp_all
  by_cases h0 : f ⟨0, by omega⟩ = g ⟨0, by omega⟩
  · exact Or.inl fun l => (step l.val l.isLt).1 h0
  · exact Or.inr fun l => (step l.val l.isLt).2 h0

theorem const_of_chg_empty {n : ℕ} {f : Fin (n + 1) → Bool} (h : chg f = ∅) :
    ∀ t t', f t = f t' := by
  have h0 : ∀ (k : ℕ) (hk : k < n + 1), f ⟨k, hk⟩ = f ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hnc : (⟨k, by omega⟩ : Fin n) ∉ chg f := by rw [h]; exact Finset.notMem_empty _
      rw [mem_chg] at hnc
      have heq : f ⟨k, by omega⟩ = f ⟨k + 1, hk⟩ := not_not.1 hnc
      rw [← heq, ih (by omega)]
  intro t t'
  rw [h0 t.val t.isLt, h0 t'.val t'.isLt]

theorem const_after_max {n : ℕ} {f : Fin (n + 1) → Bool} {m : Fin n}
    (hm : ∀ i ∈ chg f, i ≤ m) :
    ∀ l : Fin (n + 1), m.val < l.val → f l = f m.succ := by
  have step : ∀ (d : ℕ) (hd : m.val + 1 + d < n + 1),
      f ⟨m.val + 1 + d, hd⟩ = f m.succ := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      let idx : Fin n := ⟨m.val + 1 + d, by omega⟩
      have hnc : idx ∉ chg f := by
        intro hmem
        have := hm idx hmem
        change idx.val ≤ m.val at this
        simp [idx] at this
        omega
      rw [mem_chg] at hnc
      have heq : f idx.castSucc = f idx.succ := not_not.1 hnc
      have h1 : idx.castSucc = ⟨m.val + 1 + d, by omega⟩ := rfl
      have h2 : idx.succ = ⟨m.val + 1 + (d + 1), hd⟩ := by ext; simp [idx]; omega
      rw [h1, h2] at heq
      rw [← heq, ih (by omega)]
  intro l hl
  have hval : l = ⟨m.val + 1 + (l.val - (m.val + 1)), by omega⟩ := by ext; simp; omega
  rw [hval]
  exact step (l.val - (m.val + 1)) (by omega)

theorem const_before_min {n : ℕ} {f : Fin (n + 1) → Bool} {m : Fin n}
    (hm : ∀ i ∈ chg f, m ≤ i) :
    ∀ l : Fin (n + 1), l.val ≤ m.val → f l = f m.castSucc := by
  have step : ∀ (d : ℕ) (hd : d ≤ m.val),
      f ⟨m.val - d, by omega⟩ = f m.castSucc := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      let idx : Fin n := ⟨m.val - (d + 1), by omega⟩
      have hnc : idx ∉ chg f := by
        intro hmem
        have := hm idx hmem
        change m.val ≤ idx.val at this
        simp [idx] at this
        omega
      rw [mem_chg] at hnc
      have heq : f idx.castSucc = f idx.succ := not_not.1 hnc
      have h1 : idx.castSucc = ⟨m.val - (d + 1), by omega⟩ := rfl
      have h2 : idx.succ = ⟨m.val - d, by omega⟩ := by ext; simp [idx]; omega
      rw [h1, h2] at heq
      rw [heq, ih (by omega)]
  intro l hl
  have hval : l = ⟨m.val - (m.val - l.val), by omega⟩ := by ext; simp; omega
  rw [hval]
  exact step (m.val - l.val) (by omega)

theorem bool_and_sub (x y c d : Bool) : (x && c) ≠ (y && d) → x ≠ y ∨ c ≠ d := by
  revert x y c d; decide

theorem bool_or_sub (x y c d : Bool) : (x || c) ≠ (y || d) → x ≠ y ∨ c ≠ d := by
  revert x y c d; decide

theorem bool_and_l (x y c : Bool) : (x && c) ≠ (y && c) → (x && c) = x := by
  revert x y c; decide

theorem bool_or_l (x y c : Bool) : (x || c) ≠ (y || c) → (x || c) = x := by
  revert x y c; decide

theorem bool_and_r (x c d : Bool) : (x && c) ≠ (x && d) → (x && c) = c := by
  revert x c d; decide

theorem bool_or_r (x c d : Bool) : (x || c) ≠ (x || d) → (x || c) = c := by
  revert x c d; decide

theorem bin_sub {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) : chg f ⊆ chg a ∪ chg b := by
  intro i hi
  rw [Finset.mem_union, mem_chg, mem_chg]
  rw [mem_chg] at hi
  rcases hop with h | h
  · rw [h, h] at hi; exact bool_and_sub _ _ _ _ hi
  · rw [h, h] at hi; exact bool_or_sub _ _ _ _ hi

theorem bin_left {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (hb : i ∉ chg b) : f i.castSucc = a i.castSucc ∧ f i.succ = a i.succ := by
  rw [mem_chg] at hi hb
  have hb' : b i.castSucc = b i.succ := not_not.1 hb
  have h1 : f i.castSucc = a i.castSucc := by
    rcases hop with h | h
    · rw [h, h, ← hb'] at hi; rw [h]; exact bool_and_l _ _ _ hi
    · rw [h, h, ← hb'] at hi; rw [h]; exact bool_or_l _ _ _ hi
  have h2 : f i.succ = a i.succ := by
    rcases hop with h | h
    · rw [h, h, hb'] at hi; rw [h]; exact bool_and_l _ _ _ hi.symm
    · rw [h, h, hb'] at hi; rw [h]; exact bool_or_l _ _ _ hi.symm
  exact ⟨h1, h2⟩

theorem bin_right {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (ha : i ∉ chg a) : f i.castSucc = b i.castSucc ∧ f i.succ = b i.succ := by
  rw [mem_chg] at hi ha
  have ha' : a i.castSucc = a i.succ := not_not.1 ha
  have h1 : f i.castSucc = b i.castSucc := by
    rcases hop with h | h
    · rw [h, h, ← ha'] at hi; rw [h]; exact bool_and_r _ _ _ hi
    · rw [h, h, ← ha'] at hi; rw [h]; exact bool_or_r _ _ _ hi
  have h2 : f i.succ = b i.succ := by
    rcases hop with h | h
    · rw [h, h, ha'] at hi; rw [h]; exact bool_and_r _ _ _ hi.symm
    · rw [h, h, ha'] at hi; rw [h]; exact bool_or_r _ _ _ hi.symm
  exact ⟨h1, h2⟩

theorem bin_falls_union {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t)))
    (hdisj : Disjoint (chg a) (chg b)) (hunion : chg f = chg a ∪ chg b) :
    falls f = falls a ∪ falls b ∧ Disjoint (falls a) (falls b) := by
  have hd : Disjoint (falls a) (falls b) :=
    hdisj.mono (falls_subset_chg a) (falls_subset_chg b)
  refine ⟨?_, hd⟩
  ext i
  rw [Finset.mem_union, mem_falls, mem_falls, mem_falls]
  by_cases ha : i ∈ chg a
  · have hb : i ∉ chg b := Finset.disjoint_left.1 hdisj ha
    have hf : i ∈ chg f := by rw [hunion]; exact Finset.mem_union_left _ ha
    have ⟨h1, h2⟩ := bin_left hop i hf hb
    have hnb : ¬(b i.castSucc = true ∧ b i.succ = false) := by
      rintro ⟨hb1, hb2⟩; exact hb (by rw [mem_chg, hb1, hb2]; decide)
    rw [h1, h2]; simp [hnb]
  · by_cases hb : i ∈ chg b
    · have hf : i ∈ chg f := by rw [hunion]; exact Finset.mem_union_right _ hb
      have ⟨h1, h2⟩ := bin_right hop i hf ha
      have hna : ¬(a i.castSucc = true ∧ a i.succ = false) := by
        rintro ⟨ha1, ha2⟩; exact ha (by rw [mem_chg, ha1, ha2]; decide)
      rw [h1, h2]; simp [hna]
    · have hnf : i ∉ chg f := by rw [hunion, Finset.mem_union]; tauto
      have h1 : ¬(f i.castSucc = true ∧ f i.succ = false) := by
        rintro ⟨e1, e2⟩; exact hnf (by rw [mem_chg, e1, e2]; decide)
      have h2 : ¬(a i.castSucc = true ∧ a i.succ = false) := by
        rintro ⟨e1, e2⟩; exact ha (by rw [mem_chg, e1, e2]; decide)
      have h3 : ¬(b i.castSucc = true ∧ b i.succ = false) := by
        rintro ⟨e1, e2⟩; exact hb (by rw [mem_chg, e1, e2]; decide)
      simp [h1, h2, h3]

def Lam {n : ℕ} (A B : Finset (Fin n)) : Prop := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => cls j = c

theorem mem_blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) (j : Fin n) :
    j ∈ blk cls c ↔ cls j = c := by simp [blk]

def maxFalls {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n)) : ℕ :=
  ((Finset.range K).filter fun u => chg (F u) = S).sup fun u => (falls (F u)).card

theorem falls_le_maxFalls {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K u : ℕ) (S : Finset (Fin n))
    (hu : u < K) (hS : chg (F u) = S) :
    (falls (F u)).card ≤ maxFalls F K S := by
  apply Finset.le_sup (f := fun v => (falls (F v)).card)
  simp [Finset.mem_filter, Finset.mem_range, hu, hS]

theorem maxFalls_succ_of_ne {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n))
    (hne : chg (F K) ≠ S) :
    maxFalls F (K + 1) S = maxFalls F K S := by
  unfold maxFalls
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨hu | rfl, hS⟩
    · exact ⟨hu, hS⟩
    · exact absurd hS hne
  · rintro ⟨hu, hS⟩
    exact ⟨Or.inl hu, hS⟩

theorem maxFalls_succ_le {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n))
    (m : ℕ) (h1 : maxFalls F K S ≤ m) (h2 : chg (F K) = S → (falls (F K)).card ≤ m) :
    maxFalls F (K + 1) S ≤ m := by
  apply Finset.sup_le
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff_lt_or_eq] at hu
  rcases hu.1 with hlt | rfl
  · exact le_trans (falls_le_maxFalls F K u S hlt hu.2) h1
  · exact h2 hu.2

theorem maxFalls_succ_eq_of_unique {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n))
    (hnone : ∀ u < K, chg (F u) ≠ S) (hK : chg (F K) = S) :
    maxFalls F (K + 1) S = (falls (F K)).card := by
  have hset : (Finset.range (K + 1)).filter (fun u => chg (F u) = S) = {K} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨hlt | rfl, hS⟩
      · exact absurd hS (hnone u hlt)
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, hK⟩
  unfold maxFalls
  rw [hset]
  simp

def GoodWire {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (u : ℕ) : Prop :=
  (∀ t t', F u t = F u t') ∨
  (∃ a < u, (∀ t, F u t = F a t) ∨ (∀ t, F u t = !F a t)) ∨
  (∃ a < u, ∃ b < u, (chg (F a)).Nonempty ∧ (chg (F b)).Nonempty ∧
    Disjoint (chg (F a)) (chg (F b)) ∧ chg (F u) = chg (F a) ∪ chg (F b) ∧
    ((∀ t, F u t = (F a t && F b t)) ∨ (∀ t, F u t = (F a t || F b t))))

def Str {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (cls : Fin n → ℕ) (Q : ℕ) : Prop :=
  (∀ u < K, ∀ v < K, Lam (chg (F u)) (chg (F v))) ∧
  (∀ u, n + 2 ≤ u → u < K → GoodWire F u) ∧
  (∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) ≤ Q)

def Inv {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K P Q : ℕ) : Prop :=
  ∃ cls : Fin n → ℕ,
    (∀ u < K, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls i = cls j) ∧
    n ≤ (Finset.univ.image cls).card + P ∧
    ((n = (Finset.univ.image cls).card + P ∧
        ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i)) → Str F K cls Q)

theorem Inv.congr {n : ℕ} {F F' : ℕ → Fin (n + 1) → Bool} {K P Q : ℕ}
    (h : ∀ u < K, F' u = F u) (hI : Inv F K P Q) : Inv F' K P Q := by
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu; rw [h u hu]; exact hW u hu
  · rintro ⟨heq, hfull⟩
    obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, fun i => by
      obtain ⟨u, hu, hue⟩ := hfull i
      exact ⟨u, hu, by rw [← h u hu]; exact hue⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv; rw [h u hu, h v hv]; exact hlam u hu v hv
    · intro u hlo hhi
      have hg := hgood u hlo hhi
      rcases hg with hc | ⟨a, ha, hs⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, hop⟩
      · exact Or.inl fun t t' => by rw [h u hhi]; exact hc t t'
      · refine Or.inr (Or.inl ⟨a, ha, ?_⟩)
        rcases hs with hs | hs
        · exact Or.inl fun t => by rw [h u hhi, h a (lt_trans ha hhi)]; exact hs t
        · exact Or.inr fun t => by rw [h u hhi, h a (lt_trans ha hhi)]; exact hs t
      · refine Or.inr (Or.inr ⟨a, ha, b, hb, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [h a (lt_trans ha hhi)]; exact hna
        · rw [h b (lt_trans hb hhi)]; exact hnb
        · rw [h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hdj
        · rw [h u hhi, h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hun
        · rcases hop with hop | hop
          · exact Or.inl fun t => by rw [h u hhi, h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hop t
          · exact Or.inr fun t => by rw [h u hhi, h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hop t
    · have hmf : ∀ S, maxFalls F' K S = maxFalls F K S := by
        intro S
        unfold maxFalls
        have hfilt : (Finset.range K).filter (fun u => chg (F' u) = S) =
            (Finset.range K).filter (fun u => chg (F u) = S) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_range]
          constructor <;> rintro ⟨hu, hS⟩ <;> refine ⟨hu, ?_⟩
          · rwa [← h u hu]
          · rwa [h u hu]
        rw [hfilt]
        apply Finset.sup_congr rfl
        intro u hu
        have hlt : u < K := Finset.mem_range.1 (Finset.mem_filter.1 hu).1
        rw [h u hlt]
      simpa [hmf] using hfalls

theorem Inv.const_slack {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q : ℕ}
    (hc : chg (F K) = ∅) (h : Inv F K P Q) : Inv F (K + 1) (P + 1) Q := by
  obtain ⟨cls, hW, hN, -⟩ := h
  refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
  intro u hu i hi j hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
  · exact hW u hu i hi j hj
  · rw [hc] at hi; exact absurd hi (Finset.notMem_empty i)

theorem Inv.copy_slack {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q a : ℕ}
    (ha : a < K) (h : ∀ t, F K t = F a t) (hI : Inv F K P Q) : Inv F (K + 1) (P + 1) Q := by
  have hc : chg (F K) = chg (F a) := chg_congr (Or.inl h)
  obtain ⟨cls, hW, hN, -⟩ := hI
  refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
  intro u hu i hi j hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
  · exact hW u hu i hi j hj
  · rw [hc] at hi hj; exact hW a ha i hi j hj

theorem Inv.const_not {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q : ℕ}
    (hc : chg (F K) = ∅) (h : Inv F K P Q) : Inv F (K + 1) P (Q + 1) := by
  obtain ⟨cls, hW, hN, hS⟩ := h
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact hW u hu i hi j hj
    · rw [hc] at hi; exact absurd hi (Finset.notMem_empty i)
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact ⟨u, hu, hue⟩
      · exfalso
        have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
        rw [← hue, hc] at hi
        exact Finset.notMem_empty i hi
    obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, hfullK⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · exact hlam u hu v hv
        · exact Or.inr (Or.inl (by rw [hc]; exact Finset.empty_subset _))
      · exact Or.inl (by rw [hc]; exact Finset.empty_subset _)
    · intro u hlo hhi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhi with hlt | rfl
      · exact hgood u hlo hlt
      · exact Or.inl (const_of_chg_empty hc)
    · have hsum : ∑ c ∈ Finset.univ.image cls, maxFalls F (K + 1) (blk cls c) =
          ∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) := by
        apply Finset.sum_congr rfl
        intro c hc_mem
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc_mem
        apply maxFalls_succ_of_ne
        intro he
        have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
        rw [← he, hc] at hi
        exact Finset.notMem_empty i hi
      rw [hsum]; omega

theorem Inv.notGate {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q a : ℕ}
    (ha : a < K) (h : ∀ t, F K t = !F a t) (hI : Inv F K P Q) : Inv F (K + 1) P (Q + 1) := by
  have hc : chg (F K) = chg (F a) := chg_congr (Or.inr h)
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact hW u hu i hi j hj
    · rw [hc] at hi hj; exact hW a ha i hi j hj
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact ⟨u, hu, hue⟩
      · rw [hc] at hue; exact ⟨a, ha, hue⟩
    obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, hfullK⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · exact hlam u hu v hv
        · rw [hc]; exact hlam u hu a ha
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [hc]; exact hlam a ha v hv
        · exact Or.inl (Finset.Subset.refl _)
    · intro u hlo hhi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhi with hlt | rfl
      · exact hgood u hlo hlt
      · exact Or.inr (Or.inl ⟨a, ha, Or.inr h⟩)
    · by_cases hex : ∃ c ∈ Finset.univ.image cls, chg (F K) = blk cls c
      · obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hex
        have hother : ∀ c ∈ (Finset.univ.image cls).erase c₀,
            maxFalls F (K + 1) (blk cls c) = maxFalls F K (blk cls c) := by
          intro c hc_mem
          have hne : c ≠ c₀ := (Finset.mem_erase.1 hc_mem).1
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_erase.1 hc_mem).2
          apply maxFalls_succ_of_ne
          intro he
          have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
          rw [← he, hc₀_eq, mem_blk] at hi
          exact hne hi
        have hc₀_le : maxFalls F (K + 1) (blk cls c₀) ≤ maxFalls F K (blk cls c₀) + 1 := by
          apply maxFalls_succ_le
          · omega
          · intro _
            have hfa : falls (F K) = rises (F a) := by
              rw [falls_congr h, falls_not_eq_rises]
            have h1 := rises_le_falls_succ (F a)
            have h2 := falls_le_maxFalls F K a (blk cls c₀) ha (hc.symm.trans hc₀_eq)
            rw [hfa]; omega
        rw [← Finset.add_sum_erase _ _ hc₀_mem]
        rw [← Finset.add_sum_erase _ _ hc₀_mem] at hfalls
        have hsum_eq : ∑ c ∈ (Finset.univ.image cls).erase c₀, maxFalls F (K + 1) (blk cls c) =
            ∑ c ∈ (Finset.univ.image cls).erase c₀, maxFalls F K (blk cls c) :=
          Finset.sum_congr rfl hother
        rw [hsum_eq]; omega
      · push_neg at hex
        have hsum : ∑ c ∈ Finset.univ.image cls, maxFalls F (K + 1) (blk cls c) =
            ∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) := by
          apply Finset.sum_congr rfl
          intro c hc_mem
          exact maxFalls_succ_of_ne F K (blk cls c) (hex c hc_mem)
        rw [hsum]; omega

theorem Inv.bin {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q a b : ℕ}
    (ha : a < K) (hb : b < K)
    (hop : (∀ t, F K t = (F a t && F b t)) ∨ (∀ t, F K t = (F a t || F b t)))
    (hI : Inv F K P Q) : Inv F (K + 1) (P + 1) Q := by
  have hsub : chg (F K) ⊆ chg (F a) ∪ chg (F b) := bin_sub hop
  obtain ⟨cls, hW, hN, hS⟩ := hI
  by_cases hea : (chg (F a)).Nonempty
  · by_cases heb : (chg (F b)).Nonempty
    · obtain ⟨ia, hia⟩ := hea
      obtain ⟨ib, hib⟩ := heb
      set ca := cls ia
      set cb := cls ib
      by_cases hcab : ca = cb
      · refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
        intro u hu i hi j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | heq
        · exact hW u hu i hi j hj
        · rw [heq] at hi hj
          have hmem : ∀ x ∈ chg (F K), cls x = ca := by
            intro x hx
            rcases Finset.mem_union.1 (hsub hx) with hxa | hxb
            · exact hW a ha x hxa ia hia
            · exact (hW b hb x hxb ib hib).trans hcab.symm
          rw [hmem i hi, hmem j hj]
      · let cls' : Fin n → ℕ := fun j => if cls j = cb then ca else cls j
        have himg : Finset.univ.image cls' = (Finset.univ.image cls).erase cb := by
          ext c
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro ⟨j, rfl⟩
            dsimp only [cls']
            split_ifs with hj
            · exact ⟨hcab, ia, rfl⟩
            · exact ⟨hj, j, rfl⟩
          · rintro ⟨hne, j, rfl⟩
            exact ⟨j, by simp [cls', hne]⟩
        have hcb_mem : cb ∈ Finset.univ.image cls :=
          Finset.mem_image.2 ⟨ib, Finset.mem_univ _, rfl⟩
        have hca_mem : ca ∈ Finset.univ.image cls :=
          Finset.mem_image.2 ⟨ia, Finset.mem_univ _, rfl⟩
        have hca_mem' : ca ∈ Finset.univ.image cls' := by
          rw [himg]; exact Finset.mem_erase.2 ⟨hcab, hca_mem⟩
        have hcard' : (Finset.univ.image cls').card + 1 = (Finset.univ.image cls).card := by
          rw [himg, Finset.card_erase_add_one hcb_mem]
        have hblk_ca : blk cls' ca = blk cls ca ∪ blk cls cb := by
          ext j
          simp only [mem_blk, Finset.mem_union, cls']
          split_ifs with hj
          · simp [hj]
          · simp [hj]
        have hblk_other : ∀ c, c ≠ ca → c ≠ cb → blk cls' c = blk cls c := by
          intro c h1 h2
          ext j
          simp only [mem_blk, cls']
          split_ifs with hj
          · simp [h1.symm, hj, h2.symm]
          · rfl
        have hsub_a : chg (F a) ⊆ blk cls ca := fun x hx =>
          (mem_blk cls ca x).2 (hW a ha x hx ia hia)
        have hsub_b : chg (F b) ⊆ blk cls cb := fun x hx =>
          (mem_blk cls cb x).2 (hW b hb x hx ib hib)
        have hdisj_ab : Disjoint (blk cls ca) (blk cls cb) := by
          rw [Finset.disjoint_left]
          intro x hxa hxb
          rw [mem_blk] at hxa hxb
          exact hcab (hxa.symm.trans hxb)
        refine ⟨cls', ?_, by omega, ?_⟩
        · intro u hu i hi j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | heq
          · have e := hW u hu i hi j hj
            simp [cls', e]
          · rw [heq] at hi hj
            have hmem : ∀ x ∈ chg (F K), cls' x = ca := by
              intro x hx
              rcases Finset.mem_union.1 (hsub hx) with hxa | hxb
              · have := hW a ha x hxa ia hia
                dsimp only [cls']; rw [this, if_neg hcab]
              · have := hW b hb x hxb ib hib
                dsimp only [cls']; rw [this, if_pos rfl]
            rw [hmem i hi, hmem j hj]
        · rintro ⟨heq', hfull'⟩
          have hno_old : ∀ u < K, chg (F u) ≠ blk cls' ca := by
            intro u hu he
            have hi1 : ia ∈ chg (F u) := by
              rw [he, hblk_ca]; exact Finset.mem_union_left _ ((mem_blk cls ca ia).2 rfl)
            have hi2 : ib ∈ chg (F u) := by
              rw [he, hblk_ca]; exact Finset.mem_union_right _ ((mem_blk cls cb ib).2 rfl)
            exact hcab (hW u hu ia hi1 ib hi2)
          have hchgK : chg (F K) = blk cls ca ∪ blk cls cb := by
            have hcls'_ia : cls' ia = ca := by dsimp only [cls']; exact if_neg hcab
            obtain ⟨u, hu, hue⟩ := hfull' ia
            rw [hcls'_ia] at hue
            rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | heq
            · exact absurd hue (hno_old u hlt)
            · rw [heq, hblk_ca] at hue; exact hue
          have hchg_a : chg (F a) = blk cls ca := by
            apply Finset.Subset.antisymm hsub_a
            intro x hx
            have hxK : x ∈ chg (F K) := by rw [hchgK]; exact Finset.mem_union_left _ hx
            rcases Finset.mem_union.1 (hsub hxK) with hxa | hxb
            · exact hxa
            · exact absurd (hsub_b hxb) (Finset.disjoint_left.1 hdisj_ab hx)
          have hchg_b : chg (F b) = blk cls cb := by
            apply Finset.Subset.antisymm hsub_b
            intro x hx
            have hxK : x ∈ chg (F K) := by rw [hchgK]; exact Finset.mem_union_right _ hx
            rcases Finset.mem_union.1 (hsub hxK) with hxa | hxb
            · exact absurd (hsub_a hxa) (Finset.disjoint_right.1 hdisj_ab hx)
            · exact hxb
          have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
            intro i
            by_cases h1 : cls i = ca
            · rw [h1]; exact ⟨a, ha, hchg_a⟩
            · by_cases h2 : cls i = cb
              · rw [h2]; exact ⟨b, hb, hchg_b⟩
              · have hcls'_i : cls' i = cls i := by simp [cls', h2]
                obtain ⟨u, hu, hue⟩ := hfull' i
                rw [hcls'_i, hblk_other (cls i) h1 h2] at hue
                rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | heq
                · exact ⟨u, hlt, hue⟩
                · exfalso
                  rw [heq] at hue
                  have hiaK : ia ∈ chg (F K) := by
                    rw [hchgK]; exact Finset.mem_union_left _ ((mem_blk cls ca ia).2 rfl)
                  rw [hue, mem_blk] at hiaK
                  exact h1 hiaK.symm
          obtain ⟨hlamK, hgoodK, hfallsK⟩ := hS ⟨by omega, hfullK⟩
          have hlam_old_K : ∀ u < K, Lam (chg (F u)) (chg (F K)) := by
            intro u hu
            by_cases heu : (chg (F u)).Nonempty
            · obtain ⟨x, hx⟩ := heu
              have hsub_u : chg (F u) ⊆ blk cls (cls x) := fun y hy =>
                (mem_blk cls (cls x) y).2 (hW u hu y hy x hx)
              by_cases hc1 : cls x = ca
              · exact Or.inl (by rw [hchgK]; exact Finset.Subset.trans hsub_u (by rw [hc1]; exact Finset.subset_union_left))
              · by_cases hc2 : cls x = cb
                · exact Or.inl (by rw [hchgK]; exact Finset.Subset.trans hsub_u (by rw [hc2]; exact Finset.subset_union_right))
                · refine Or.inr (Or.inr ?_)
                  rw [Finset.disjoint_left]
                  intro y hyu hyK
                  have hy1 : cls y = cls x := (mem_blk cls (cls x) y).1 (hsub_u hyu)
                  rw [hchgK, Finset.mem_union, mem_blk, mem_blk] at hyK
                  rcases hyK with hyK | hyK
                  · exact hc1 (hy1.symm.trans hyK)
                  · exact hc2 (hy1.symm.trans hyK)
            · rw [Finset.not_nonempty_iff_eq_empty] at heu
              exact Or.inl (by rw [heu]; exact Finset.empty_subset _)
          refine ⟨?_, ?_, ?_⟩
          · intro u hu v hv
            rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hult | rfl
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hvlt | rfl
              · exact hlamK u hult v hvlt
              · exact hlam_old_K u hult
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hvlt | rfl
              · rcases hlam_old_K v hvlt with h1 | h2 | h3
                · exact Or.inr (Or.inl h1)
                · exact Or.inl h2
                · exact Or.inr (Or.inr h3.symm)
              · exact Or.inl (Finset.Subset.refl _)
          · intro u hlo hhi
            rcases Nat.lt_succ_iff_lt_or_eq.1 hhi with hlt | rfl
            · exact hgoodK u hlo hlt
            · refine Or.inr (Or.inr ⟨a, ha, b, hb, ⟨ia, hia⟩, ⟨ib, hib⟩, ?_, ?_, hop⟩)
              · rw [hchg_a, hchg_b]; exact hdisj_ab
              · rw [hchg_a, hchg_b, hchgK]
          · have hdisj_chg : Disjoint (chg (F a)) (chg (F b)) := by
              rw [hchg_a, hchg_b]; exact hdisj_ab
            have hunion_chg : chg (F K) = chg (F a) ∪ chg (F b) := by
              rw [hchg_a, hchg_b, hchgK]
            have ⟨hfu, hfd⟩ := bin_falls_union hop hdisj_chg hunion_chg
            have hmf_ca : maxFalls F (K + 1) (blk cls' ca) ≤
                maxFalls F K (blk cls ca) + maxFalls F K (blk cls cb) := by
              rw [maxFalls_succ_eq_of_unique F K (blk cls' ca) hno_old (by rw [hblk_ca, hchgK])]
              rw [hfu, Finset.card_union_of_disjoint hfd]
              exact Nat.add_le_add
                (falls_le_maxFalls F K a (blk cls ca) ha hchg_a)
                (falls_le_maxFalls F K b (blk cls cb) hb hchg_b)
            have hmf_rest : ∑ c ∈ (Finset.univ.image cls').erase ca, maxFalls F (K + 1) (blk cls' c) =
                ∑ c ∈ ((Finset.univ.image cls).erase cb).erase ca, maxFalls F K (blk cls c) := by
              rw [himg]
              apply Finset.sum_congr rfl
              intro c hc
              have hne_a : c ≠ ca := (Finset.mem_erase.1 hc).1
              have hne_b : c ≠ cb := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
              rw [hblk_other c hne_a hne_b]
              apply maxFalls_succ_of_ne
              intro he
              have hiaK : ia ∈ chg (F K) := by
                rw [hchgK]; exact Finset.mem_union_left _ ((mem_blk cls ca ia).2 rfl)
              rw [he, mem_blk] at hiaK
              exact hne_a hiaK.symm
            rw [← Finset.add_sum_erase _ _ hca_mem', hmf_rest]
            have hca_in_erase : ca ∈ (Finset.univ.image cls).erase cb :=
              Finset.mem_erase.2 ⟨hcab, hca_mem⟩
            have hsplit_old : ∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) =
                maxFalls F K (blk cls cb) +
                  (maxFalls F K (blk cls ca) +
                    ∑ c ∈ ((Finset.univ.image cls).erase cb).erase ca, maxFalls F K (blk cls c)) := by
              rw [← Finset.add_sum_erase _ _ hcb_mem]
              congr 1
              rw [← Finset.add_sum_erase _ _ hca_in_erase]
            omega
    · rw [Finset.not_nonempty_iff_eq_empty] at heb
      refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
      intro u hu i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact hW u hu i hi j hj
      · rw [heb, Finset.union_empty] at hsub
        exact hW a ha i (hsub hi) j (hsub hj)
  · rw [Finset.not_nonempty_iff_eq_empty] at hea
    refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
    intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact hW u hu i hi j hj
    · rw [hea, Finset.empty_union] at hsub
      exact hW b hb i (hsub hi) j (hsub hj)

theorem chg_input_lt (n : ℕ) (u : ℕ) (hu : u < n) :
    chg (vl n [] u) = {⟨u, hu⟩} := by
  ext i
  rw [mem_chg, Finset.mem_singleton]
  simp only [vl, W_nil, prefixInput_lt n _ u hu, Fin.val_castSucc, Fin.val_succ]
  constructor
  · intro hne
    ext
    by_cases h1 : u < i.val
    · exfalso; apply hne
      have h2 : u < i.val + 1 := by omega
      simp [h1, h2]
    · by_cases h2 : u < i.val + 1
      · simp; omega
      · exfalso; apply hne; simp [h1, h2]
  · rintro rfl
    have h1 : ¬(u < u) := lt_irrefl u
    have h2 : u < u + 1 := Nat.lt_succ_self u
    simp [h1, h2]

theorem chg_input_const (n : ℕ) (u : ℕ) (hu : n ≤ u) :
    chg (vl n [] u) = ∅ := by
  apply chg_const
  intro t t'
  simp only [vl, W_nil]
  by_cases h1 : u = n
  · subst h1; rw [prefixInput_n, prefixInput_n]
  · by_cases h2 : u = n + 1
    · subst h2; rw [prefixInput_n1, prefixInput_n1]
    · rw [List.getD_eq_default _ _ (by rw [prefixInput_len]; omega),
          List.getD_eq_default _ _ (by rw [prefixInput_len]; omega)]

theorem falls_input (n : ℕ) (u : ℕ) : falls (vl n [] u) = ∅ := by
  ext i
  rw [mem_falls]
  simp only [Finset.notMem_empty, iff_false, not_and]
  by_cases hu : u < n
  · simp only [vl, W_nil, prefixInput_lt n _ u hu, Fin.val_castSucc, Fin.val_succ,
      decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · have hc := const_of_chg_empty (chg_input_const n u (Nat.le_of_not_lt hu)) i.castSucc i.succ
    rw [hc]; intro h; rw [h]; decide

theorem inv_base (n : ℕ) : Inv (vl n []) (n + 2) 0 0 := by
  let cls : Fin n → ℕ := fun i => i.val
  have hcard : (Finset.univ.image cls).card = n := by
    rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext h)]
    simp
  refine ⟨cls, ?_, by omega, ?_⟩
  · intro u _ i hi j hj
    by_cases hlt : u < n
    · rw [chg_input_lt n u hlt, Finset.mem_singleton] at hi hj
      rw [hi, hj]
    · rw [chg_input_const n u (Nat.le_of_not_lt hlt)] at hi
      exact absurd hi (Finset.notMem_empty i)
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · intro u _ v _
      by_cases hu : u < n
      · by_cases hv : v < n
        · rw [chg_input_lt n u hu, chg_input_lt n v hv]
          by_cases huv : u = v
          · subst huv; exact Or.inl (Finset.Subset.refl _)
          · refine Or.inr (Or.inr ?_)
            rw [Finset.disjoint_singleton]
            intro h; exact huv (congrArg Fin.val h)
        · rw [chg_input_const n v (Nat.le_of_not_lt hv)]
          exact Or.inr (Or.inl (Finset.empty_subset _))
      · rw [chg_input_const n u (Nat.le_of_not_lt hu)]
        exact Or.inl (Finset.empty_subset _)
    · intro u hlo hhi; omega
    · apply Finset.sum_eq_zero _ |>.le
      intro c _
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro u _
      rw [falls_input n u]; simp

theorem inv_all (n : ℕ) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩) :
    Inv (vl n gs) (n + 2 + gs.length) (nonNotCount gs) (PEqualNP.NotBracket.notCount ⟨gs, 0⟩) := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [notCount_eq_filter]
    simpa [nonNotCount] using inv_base n
  | append_singleton gs g ih =>
    have hF_pre : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ :=
      fun x hx => hF x (List.mem_append_left _ hx)
    have hR_pre : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ := by
      intro j hj i hi
      have hj' : j < (gs ++ [g]).length := by
        simp only [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt hj
      have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        List.getD_append _ _ _ _ hj
      exact hR j hj' i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rwa [hget])
    have hI0 := ih hF_pre hR_pre
    have hcongr : ∀ u < n + 2 + gs.length, vl n (gs ++ [g]) u = vl n gs u := by
      intro u hu
      funext l
      exact old_wire gs g (prefixInput n l) u (by rw [prefixInput_len]; omega)
    have hI := Inv.congr hcongr hI0
    have hnew : ∀ l, vl n (gs ++ [g]) (n + 2 + gs.length) l =
        g.op.eval (g.inputs.map fun t => vl n gs t l) := by
      intro l
      simpa [vl, prefixInput_len] using new_wire gs g (prefixInput n l)
    have hin : ∀ a ∈ g.inputs, a < n + 2 + gs.length := by
      intro a ha
      have hj' : gs.length < (gs ++ [g]).length := by simp
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
      exact hR gs.length hj' a (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rwa [hget])
    have ⟨hgop, hglen⟩ := hF g (List.mem_append_right _ (by simp))
    have hlen : n + 2 + (gs ++ [g]).length = (n + 2 + gs.length) + 1 := by simp; omega
    rw [hlen, nonNotCount_append, notCount_append]
    by_cases hnot : g.op = GateOp.not
    · have hnn : nonNotCount [g] = 0 := by simp [nonNotCount, (isNotGate_eq_true g).2 hnot]
      have hnc : PEqualNP.NotBracket.notCount ⟨[g], 0⟩ = 1 := by
        rw [notCount_eq_filter]; simp [(isNotGate_eq_true g).2 hnot]
      rw [hnn, hnc, Nat.add_zero]
      rcases hgi : g.inputs with _ | ⟨a, rest⟩
      · apply Inv.const_not _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi, hnot]; rfl
      · have ha : a < n + 2 + gs.length := hin a (by rw [hgi]; simp)
        apply Inv.notGate ha _ hI
        intro l
        rw [hnew, hgi, hnot, hcongr a ha]
        simp [GateOp.eval]
    · have hnn : nonNotCount [g] = 1 := by simp [nonNotCount, (isNotGate_eq_false g).2 hnot]
      have hnc : PEqualNP.NotBracket.notCount ⟨[g], 0⟩ = 0 := by
        rw [notCount_eq_filter]; simp [(isNotGate_eq_false g).2 hnot]
      rw [hnn, hnc, Nat.add_zero]
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
        tauto
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · apply Inv.const_slack _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi]; rfl
      · have ha : a < n + 2 + gs.length := hin a (by rw [hgi]; simp)
        apply Inv.copy_slack ha _ hI
        intro l
        rw [hnew, hgi, hcongr a ha]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
      · have ha : a < n + 2 + gs.length := hin a (by rw [hgi]; simp)
        have hb : b < n + 2 + gs.length := hin b (by rw [hgi]; simp)
        apply Inv.bin ha hb _ hI
        rcases hop with h | h
        · refine Or.inl fun l => ?_
          rw [hnew, hgi, h, hcongr a ha, hcongr b hb]
          simp [GateOp.eval]
        · refine Or.inr fun l => ?_
          rw [hnew, hgi, h, hcongr a ha, hcongr b hb]
          simp [GateOp.eval]
      · rw [hgi] at hglen; simp at hglen

theorem tight_structure (n : ℕ) (hn : 0 < n) (C : Circuit) (root : ℕ)
    (hroot_lt : root < n + 2 + C.size)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hP : C.size - PEqualNP.NotBracket.notCount C ≤ n - 1)
    (hroot : chg (vl n C.gates root) = Finset.univ) :
    (∀ u < n + 2 + C.size, ∀ v < n + 2 + C.size, Lam (chg (vl n C.gates u)) (chg (vl n C.gates v))) ∧
    (∀ u, n + 2 ≤ u → u < n + 2 + C.size → GoodWire (vl n C.gates) u) ∧
    (falls (vl n C.gates root)).card ≤ PEqualNP.NotBracket.notCount C := by
  have hInv := inv_all n C.gates hF hR
  obtain ⟨cls, hW, hN, hS⟩ := hInv
  have hsplit := notCount_add_nonNotCount C
  have hall : ∀ i j : Fin n, cls i = cls j := fun i j =>
    hW root hroot_lt i (by rw [hroot]; exact Finset.mem_univ _) j
      (by rw [hroot]; exact Finset.mem_univ _)
  have hc1 : (Finset.univ.image cls).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro c hc d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hd
    exact hall i j
  have hi0 : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hc_pos : 1 ≤ (Finset.univ.image cls).card :=
    Finset.card_pos.2 ⟨cls ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, hi0, rfl⟩⟩
  have hnn_le : nonNotCount C.gates ≤ n - 1 := by omega
  have heq : n = (Finset.univ.image cls).card + nonNotCount C.gates := by omega
  have hfull : ∀ i : Fin n, ∃ u < n + 2 + C.gates.length, chg (vl n C.gates u) = blk cls (cls i) := by
    intro i
    refine ⟨root, hroot_lt, ?_⟩
    rw [hroot]
    ext j; rw [mem_blk]; simp [hall j i]
  obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, hfull⟩
  refine ⟨hlam, hgood, ?_⟩
  have hblk0 : blk cls (cls ⟨0, hn⟩) = Finset.univ := by
    ext j; rw [mem_blk]; simp [hall j ⟨0, hn⟩]
  have hle1 : (falls (vl n C.gates root)).card ≤ maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls (cls ⟨0, hn⟩)) :=
    falls_le_maxFalls _ _ root _ hroot_lt (by rw [hroot, hblk0])
  have hmem0 : cls ⟨0, hn⟩ ∈ Finset.univ.image cls :=
    Finset.mem_image.2 ⟨⟨0, hn⟩, hi0, rfl⟩
  have hle2 : maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls (cls ⟨0, hn⟩)) ≤
      ∑ c ∈ Finset.univ.image cls, maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls c) :=
    Finset.single_le_sum (f := fun c => maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls c))
      (fun _ _ => Nat.zero_le _) hmem0
  exact le_trans hle1 (le_trans hle2 hfalls)

theorem build_prefix_fn {n : ℕ} (f : Fin (n + 1) → Bool) (hne : (chg f).Nonempty)
    (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩) :
    ∃ (extra : List Gate) (w : ℕ),
      w < n + 2 + (gs ++ extra).length ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ extra, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
      nonNotCount extra = (chg f).card - 1 ∧
      PEqualNP.NotBracket.notCount ⟨extra, 0⟩ = (falls f).card ∧
      ∀ l, vl n (gs ++ extra) w l = f l := by
  have key : ∀ (c : ℕ) (f : Fin (n + 1) → Bool), (chg f).card = c → (chg f).Nonempty →
      ∀ (gs : List Gate),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ →
        ∃ (extra : List Gate) (w : ℕ),
          w < n + 2 + (gs ++ extra).length ∧
          PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ extra, 0⟩ ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
          nonNotCount extra = (chg f).card - 1 ∧
          PEqualNP.NotBracket.notCount ⟨extra, 0⟩ = (falls f).card ∧
          ∀ l, vl n (gs ++ extra) w l = f l := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ih =>
      intro f hc hne gs hF hR
      let m : Fin n := (chg f).max' hne
      have hm_mem : m ∈ chg f := Finset.max'_mem (chg f) hne
      have hm_max : ∀ i ∈ chg f, i ≤ m := fun i hi => Finset.le_max' (chg f) i hi
      by_cases hc1 : c = 1
      · have hsing : chg f = {m} := by
          obtain ⟨m', hm'⟩ := Finset.card_eq_one.1 (hc.trans hc1)
          have : m = m' := Finset.mem_singleton.1 (hm' ▸ hm_mem)
          rw [this, hm']
        have hbefore : ∀ l : Fin (n + 1), l.val ≤ m.val → f l = f m.castSucc :=
          const_before_min fun i hi => by rw [hsing, Finset.mem_singleton] at hi; rw [hi]
        have hafter : ∀ l : Fin (n + 1), m.val < l.val → f l = f m.succ :=
          const_after_max hm_max
        have hm_chg : f m.castSucc ≠ f m.succ := (mem_chg f m).1 hm_mem
        cases hf1 : f m.castSucc
        · have hf2 : f m.succ = true := by
            cases h : f m.succ
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
            · rfl
          have hfalls0 : falls f = ∅ := by
            ext i; simp only [Finset.notMem_empty, iff_false]
            intro hi
            have : i = m := Finset.mem_singleton.1 (hsing ▸ falls_subset_chg f hi)
            subst this
            rw [mem_falls, hf1] at hi; exact Bool.false_ne_true hi.1
          refine ⟨[], m.val, by simp; omega, by simpa using hF, by simpa using hR,
            by rw [hc, hc1]; rfl, by rw [hfalls0]; rfl, fun l => ?_⟩
          simp only [List.append_nil]
          have h0 := W_append_old [] gs (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
          have hv : vl n gs m.val l = decide (m.val < l.val) :=
            h0.trans (prefixInput_lt n l m.val m.isLt)
          rw [hv]
          by_cases hlt : m.val < l.val
          · rw [hafter l hlt, hf2]; simp [hlt]
          · rw [hbefore l (Nat.le_of_not_lt hlt), hf1]; simp [hlt]
        · have hf2 : f m.succ = false := by
            cases h : f m.succ
            · rfl
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
          have hfalls1 : falls f = {m} := by
            ext i; rw [Finset.mem_singleton]
            constructor
            · intro hi; exact Finset.mem_singleton.1 (hsing ▸ falls_subset_chg f hi)
            · rintro rfl; rw [mem_falls]; exact ⟨hf1, hf2⟩
          let gnot : Gate := ⟨GateOp.not, [m.val]⟩
          refine ⟨[gnot], n + 2 + gs.length, by simp, ?_, ?_,
            by rw [hc, hc1]; rfl,
            by rw [hfalls1, notCount_eq_filter]; rfl, fun l => ?_⟩
          · apply fanInTwo_append hF
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gnot]
          · apply readsBack_snoc hR
            intro i hi; simp only [gnot, List.mem_singleton] at hi; subst hi; omega
          · have hnw := new_wire gs gnot (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W (gs ++ [gnot]) (prefixInput n l)).getD (n + 2 + gs.length) false = f l
            rw [hnw]
            have h0 := W_append_old [] gs (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
            have hv : (W gs (prefixInput n l)).getD m.val false = decide (m.val < l.val) :=
              h0.trans (prefixInput_lt n l m.val m.isLt)
            simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hv]
            by_cases hlt : m.val < l.val
            · rw [hafter l hlt, hf2]; simp [hlt]
            · rw [hbefore l (Nat.le_of_not_lt hlt), hf1]; simp [hlt]
      · have hc2 : 2 ≤ c := by
          have := Finset.card_pos.2 hne; omega
        let f' : Fin (n + 1) → Bool := fun l => if l.val ≤ m.val then f l else f m.castSucc
        have hchg_f' : chg f' = (chg f).erase m := by
          ext i
          rw [mem_chg, Finset.mem_erase, mem_chg]
          by_cases hlt : i.val < m.val
          · have h1 : i.castSucc.val ≤ m.val := by simp [Fin.val_castSucc]; omega
            have h2 : i.succ.val ≤ m.val := by simp [Fin.val_succ]; omega
            have hne_im : i ≠ m := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
            simp only [f', h1, h2, ↓reduceIte]; exact ⟨fun h => ⟨hne_im, h⟩, fun h => h.2⟩
          · by_cases heq : i = m
            · subst heq
              have h1 : m.castSucc.val ≤ m.val := le_refl _
              have h2 : ¬(m.succ.val ≤ m.val) := by simp
              simp only [f', h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_and]
            · have hgt : m.val < i.val := by
                have : i.val ≠ m.val := fun h => heq (Fin.ext h)
                omega
              have h1 : ¬(i.castSucc.val ≤ m.val) := by simp [Fin.val_castSucc]; omega
              have h2 : ¬(i.succ.val ≤ m.val) := by simp [Fin.val_succ]; omega
              have hnf : f i.castSucc = f i.succ := by
                by_contra h
                have := hm_max i ((mem_chg f i).2 h)
                change i.val ≤ m.val at this
                omega
              simp only [f', h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, hnf, and_false]
        have hfalls_f' : falls f' = (falls f).erase m := by
          ext i
          rw [mem_falls, Finset.mem_erase, mem_falls]
          by_cases hlt : i.val < m.val
          · have h1 : i.castSucc.val ≤ m.val := by simp [Fin.val_castSucc]; omega
            have h2 : i.succ.val ≤ m.val := by simp [Fin.val_succ]; omega
            have hne_im : i ≠ m := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
            simp only [f', h1, h2, ↓reduceIte]; exact ⟨fun h => ⟨hne_im, h⟩, fun h => h.2⟩
          · by_cases heq : i = m
            · subst heq
              have h1 : m.castSucc.val ≤ m.val := le_refl _
              have h2 : ¬(m.succ.val ≤ m.val) := by simp
              simp only [f', h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_and, iff_false, not_and]
              intro h; rw [h]; decide
            · have hgt : m.val < i.val := by
                have : i.val ≠ m.val := fun h => heq (Fin.ext h)
                omega
              have h1 : ¬(i.castSucc.val ≤ m.val) := by simp [Fin.val_castSucc]; omega
              have h2 : ¬(i.succ.val ≤ m.val) := by simp [Fin.val_succ]; omega
              have hnf : f i.castSucc = f i.succ := by
                by_contra h
                have := hm_max i ((mem_chg f i).2 h)
                change i.val ≤ m.val at this
                omega
              simp only [f', h1, h2, ↓reduceIte, ne_eq, heq, not_false_eq_true, true_and, hnf]
              constructor <;> rintro ⟨e1, e2⟩ <;> rw [e1] at e2 <;> exact absurd e2 (by decide)
        have hcard_f' : (chg f').card = c - 1 := by
          rw [hchg_f', Finset.card_erase_of_mem hm_mem, hc]
        have hne_f' : (chg f').Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨e1, w1, hw1_lt, hF1, hR1, hnn1, hnc1, hval1⟩ :=
          ih (c - 1) (by omega) f' hcard_f' hne_f' gs hF hR
        have hafter : ∀ l : Fin (n + 1), m.val < l.val → f l = f m.succ :=
          const_after_max hm_max
        have hm_chg : f m.castSucc ≠ f m.succ := (mem_chg f m).1 hm_mem
        cases hf1 : f m.castSucc
        · have hf2 : f m.succ = true := by
            cases h : f m.succ
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
            · rfl
          have hm_nf : m ∉ falls f := by rw [mem_falls, hf1]; simp
          let gor : Gate := ⟨GateOp.or, [w1, m.val]⟩
          refine ⟨e1 ++ [gor], n + 2 + (gs ++ e1).length, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [← List.append_assoc]; simp
          · rw [← List.append_assoc]
            apply fanInTwo_append hF1
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gor]
          · rw [← List.append_assoc]
            apply readsBack_snoc hR1
            intro i hi
            simp only [gor, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact hw1_lt
            · omega
          · rw [nonNotCount_append, hnn1, hcard_f', hc]
            have h1 : nonNotCount [gor] = 1 := by simp [nonNotCount, isNotGate, gor]
            omega
          · rw [notCount_append, hnc1, hfalls_f', Finset.erase_eq_of_notMem hm_nf, notCount_eq_filter]
            simp [isNotGate, gor]
          · intro l
            rw [← List.append_assoc]
            have hnw := new_wire (gs ++ e1) gor (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W ((gs ++ e1) ++ [gor]) (prefixInput n l)).getD (n + 2 + (gs ++ e1).length) false = f l
            rw [hnw]
            have hm_val : (W (gs ++ e1) (prefixInput n l)).getD m.val false = decide (m.val < l.val) := by
              have h0 := W_append_old [] (gs ++ e1) (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
              exact h0.trans (prefixInput_lt n l m.val m.isLt)
            have hw1_val : (W (gs ++ e1) (prefixInput n l)).getD w1 false = f' l := hval1 l
            simp only [gor, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hw1_val, hm_val]
            by_cases hlt : m.val < l.val
            · rw [hafter l hlt, hf2]; simp [hlt]
            · have hle : l.val ≤ m.val := Nat.le_of_not_lt hlt
              simp [f', hle, hlt]
        · have hf2 : f m.succ = false := by
            cases h : f m.succ
            · rfl
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
          have hm_fl : m ∈ falls f := (mem_falls f m).2 ⟨hf1, hf2⟩
          let wnot := n + 2 + (gs ++ e1).length
          let gnot : Gate := ⟨GateOp.not, [m.val]⟩
          let gand : Gate := ⟨GateOp.and, [w1, wnot]⟩
          have hF2 : PEqualNP.MetaComplexity.FanInTwo ⟨(gs ++ e1) ++ [gnot], 0⟩ := by
            apply fanInTwo_append hF1
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gnot]
          have hR2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨(gs ++ e1) ++ [gnot], 0⟩ := by
            apply readsBack_snoc hR1
            intro i hi; simp only [gnot, List.mem_singleton] at hi; subst hi; omega
          refine ⟨e1 ++ [gnot, gand], n + 2 + ((gs ++ e1) ++ [gnot]).length, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]; simp
          · have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]
            apply fanInTwo_append hF2
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gand]
          · have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]
            apply readsBack_snoc hR2
            intro i hi
            simp only [gand, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · simp only [List.length_append, List.length_singleton] at hw1_lt ⊢; omega
            · simp [wnot]
          · rw [nonNotCount_append, hnn1, hcard_f', hc]
            have h1 : nonNotCount [gnot, gand] = 1 := rfl
            omega
          · rw [notCount_append, hnc1, hfalls_f']
            have h1 : PEqualNP.NotBracket.notCount ⟨[gnot, gand], 0⟩ = 1 := by
              rw [notCount_eq_filter]; rfl
            rw [h1, Finset.card_erase_add_one hm_fl]
          · intro l
            have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]
            have hnw := new_wire ((gs ++ e1) ++ [gnot]) gand (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W (((gs ++ e1) ++ [gnot]) ++ [gand]) (prefixInput n l)).getD (n + 2 + ((gs ++ e1) ++ [gnot]).length) false = f l
            rw [hnw]
            have hw1_val : (W ((gs ++ e1) ++ [gnot]) (prefixInput n l)).getD w1 false = f' l := by
              rw [old_wire (gs ++ e1) gnot (prefixInput n l) w1 (by rw [prefixInput_len]; omega)]
              exact hval1 l
            have hwnot_val : (W ((gs ++ e1) ++ [gnot]) (prefixInput n l)).getD wnot false = !decide (m.val < l.val) := by
              have hnw' := new_wire (gs ++ e1) gnot (prefixInput n l)
              rw [prefixInput_len] at hnw'
              change (W ((gs ++ e1) ++ [gnot]) (prefixInput n l)).getD (n + 2 + (gs ++ e1).length) false = _
              rw [hnw']
              have h0 := W_append_old [] (gs ++ e1) (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
              have hv : (W (gs ++ e1) (prefixInput n l)).getD m.val false = decide (m.val < l.val) :=
                h0.trans (prefixInput_lt n l m.val m.isLt)
              simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hv]
            simp only [gand, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, hw1_val, hwnot_val]
            by_cases hlt : m.val < l.val
            · rw [hafter l hlt, hf2]; simp [hlt]
            · have hle : l.val ≤ m.val := Nat.le_of_not_lt hlt
              simp [f', hle, hlt]
  exact key (chg f).card f rfl hne gs hF hR

def coord {n d : ℕ} (X : Fin (n + 1) → Finset (Fin d)) (j : Fin d) : Fin (n + 1) → Bool :=
  fun l => decide (j ∈ X l)

def colorClass {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) : Finset (Fin n) :=
  Finset.univ.filter fun i => color i = j

theorem chg_coord_eq_colorClass {n d : ℕ} (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (j : Fin d) :
    chg (coord X j) = colorClass color j := by
  ext i
  rw [mem_chg, colorClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, coord]
  exact hX i j

theorem colorClass_nonempty {n d : ℕ} (color : Fin n → Fin d) (hsurj : Function.Surjective color)
    (j : Fin d) : (colorClass color j).Nonempty := by
  obtain ⟨i, hi⟩ := hsurj j
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩

theorem sum_card_colorClass {n d : ℕ} (color : Fin n → Fin d) :
    ∑ j : Fin d, (colorClass color j).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin d))) (f := color) (fun _ _ => Finset.mem_univ _)
  simpa [colorClass] using h.symm

theorem two_mul_falls_coord {n : ℕ} (f : Fin (n + 1) → Bool) :
    2 * (falls f).card + (if f (Fin.last n) then 1 else 0) =
      (chg f).card + (if f 0 then 1 else 0) := by
  induction n with
  | zero =>
    have h1 : (falls f).card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_isEmpty _)
    have h2 : (chg f).card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_isEmpty _)
    rw [h1, h2]
    have : Fin.last 0 = (0 : Fin 1) := rfl
    rw [this]
  | succ n ih =>
    let f' : Fin (n + 1) → Bool := fun l => f l.castSucc
    have ih' := ih f'
    have h0 : f' 0 = f 0 := rfl
    have hlast : f' (Fin.last n) = f (Fin.last n).castSucc := rfl
    let emb : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩
    have hcs_eq : ∀ k : Fin n, (k.castSucc : Fin (n + 1)).castSucc = (k.castSucc : Fin (n + 1)).castSucc := fun _ => rfl
    have hsc_eq : ∀ k : Fin n, (k.castSucc : Fin (n + 1)).succ = k.succ.castSucc := fun k => by ext; simp
    have hchg_split : (chg f).card = (chg f').card +
        if f (Fin.last n).castSucc ≠ f (Fin.last n).succ then 1 else 0 := by
      have hsub : chg f = (chg f').map emb ∪
          (if f (Fin.last n).castSucc ≠ f (Fin.last n).succ then {Fin.last n} else ∅) := by
        ext i
        simp only [mem_chg, Finset.mem_union, Finset.mem_map]
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simp only [emb, Function.Embedding.coeFn_mk]
          constructor
          · intro h; right; rw [if_pos h]; exact Finset.mem_singleton_self _
          · rintro (⟨k, -, hk⟩ | h)
            · exact absurd hk (Fin.castSucc_ne_last k)
            · split_ifs at h with hc
              · exact hc
              · simp at h
        · simp only [emb, Function.Embedding.coeFn_mk]
          constructor
          · intro h
            left; refine ⟨k, ?_, rfl⟩
            rw [hsc_eq k] at h; exact h
          · rintro (⟨k', hk', heq⟩ | h)
            · have hk_eq : k' = k := Fin.castSucc_injective n heq
              rw [← hk_eq, hsc_eq k']; exact hk'
            · split_ifs at h with hc
              · rw [Finset.mem_singleton] at h
                exact absurd h (Fin.castSucc_ne_last k)
              · simp at h
      have hdisj : Disjoint ((chg f').map emb)
          (if f (Fin.last n).castSucc ≠ f (Fin.last n).succ then {Fin.last n} else ∅) := by
        split_ifs
        · rw [Finset.disjoint_singleton_right, Finset.mem_map]
          rintro ⟨k, -, hk⟩; exact Fin.castSucc_ne_last k hk
        · exact Finset.disjoint_empty_right _
      rw [hsub, Finset.card_union_of_disjoint hdisj, Finset.card_map]
      split_ifs <;> simp
    have hfalls_split : (falls f).card = (falls f').card +
        if f (Fin.last n).castSucc = true ∧ f (Fin.last n).succ = false then 1 else 0 := by
      have hsub : falls f = (falls f').map emb ∪
          (if f (Fin.last n).castSucc = true ∧ f (Fin.last n).succ = false then {Fin.last n} else ∅) := by
        ext i
        simp only [mem_falls, Finset.mem_union, Finset.mem_map]
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simp only [emb, Function.Embedding.coeFn_mk]
          constructor
          · intro h; right; rw [if_pos h]; exact Finset.mem_singleton_self _
          · rintro (⟨k, -, hk⟩ | h)
            · exact absurd hk (Fin.castSucc_ne_last k)
            · split_ifs at h with hc
              · exact hc
              · simp at h
        · simp only [emb, Function.Embedding.coeFn_mk]
          constructor
          · intro h
            left; refine ⟨k, ?_, rfl⟩
            rw [hsc_eq k] at h; exact h
          · rintro (⟨k', hk', heq⟩ | h)
            · have hk_eq : k' = k := Fin.castSucc_injective n heq
              rw [← hk_eq, hsc_eq k']; exact hk'
            · split_ifs at h with hc
              · rw [Finset.mem_singleton] at h
                exact absurd h (Fin.castSucc_ne_last k)
              · simp at h
      have hdisj : Disjoint ((falls f').map emb)
          (if f (Fin.last n).castSucc = true ∧ f (Fin.last n).succ = false then {Fin.last n} else ∅) := by
        split_ifs
        · rw [Finset.disjoint_singleton_right, Finset.mem_map]
          rintro ⟨k, -, hk⟩; exact Fin.castSucc_ne_last k hk
        · exact Finset.disjoint_empty_right _
      rw [hsub, Finset.card_union_of_disjoint hdisj, Finset.card_map]
      split_ifs <;> simp
    have hlast_eq : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    rw [hchg_split, hfalls_split, ← hlast_eq]
    rw [h0, hlast] at ih'
    cases ha : f (Fin.last n).castSucc <;> cases hb : f (Fin.last n).succ <;>
      simp [ha, hb] at ih' ⊢ <;> omega

theorem falls_not_vs_falls {n : ℕ} (f : Fin (n + 1) → Bool) :
    (f 0 = true ∧ f (Fin.last n) = false → (falls (fun l => !f l)).card + 1 = (falls f).card) ∧
    (¬(f 0 = true ∧ f (Fin.last n) = false) → (falls f).card ≤ (falls (fun l => !f l)).card) := by
  have h1 := two_mul_falls_coord f
  have h2 := two_mul_falls_coord (fun l => !f l)
  have hc : chg (fun l => !f l) = chg f := chg_congr (Or.inr fun _ => rfl)
  rw [hc] at h2
  cases ha : f 0 <;> cases hb : f (Fin.last n) <;> simp [ha, hb] at h1 h2 ⊢ <;> omega

def walkFalls {n d : ℕ} (X : Fin (n + 1) → Finset (Fin d)) : ℕ :=
  ∑ j : Fin d, (falls (coord X j)).card

theorem two_mul_walkFalls {n d : ℕ} (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    2 * walkFalls X + (X (Fin.last n)).card = n + (X 0).card := by
  have hsum : ∑ j : Fin d, (2 * (falls (coord X j)).card + if coord X j (Fin.last n) then 1 else 0) =
      ∑ j : Fin d, ((chg (coord X j)).card + if coord X j 0 then 1 else 0) :=
    Finset.sum_congr rfl fun j _ => two_mul_falls_coord (coord X j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hchg_sum : ∑ j : Fin d, (chg (coord X j)).card = n := by
    calc ∑ j : Fin d, (chg (coord X j)).card
        = ∑ j : Fin d, (colorClass color j).card :=
            Finset.sum_congr rfl fun j _ => by rw [chg_coord_eq_colorClass color X hX j]
      _ = n := sum_card_colorClass color
  have hcard : ∀ l : Fin (n + 1), (∑ j : Fin d, if coord X j l then 1 else 0) = (X l).card := by
    intro l
    simp only [coord, decide_eq_true_eq, Finset.sum_boole, Nat.cast_id]
    congr 1; ext j; simp
  rw [hchg_sum, hcard (Fin.last n), hcard 0] at hsum
  exact hsum

theorem walk_parity_and_discount {n m d : ℕ}
    (cX : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ cX i = j)
    (cY : Fin m → Fin d) (Y : Fin (m + 1) → Finset (Fin d))
    (hY : ∀ i j, (decide (j ∈ Y i.castSucc) ≠ decide (j ∈ Y i.succ)) ↔ cY i = j)
    (hle : m ≤ n) (h0 : X 0 = Y 0) (hlast : X (Fin.last n) = Y (Fin.last m)) :
    (n - m) % 2 = 0 ∧ walkFalls X = walkFalls Y + (n - m) / 2 := by
  have h1 := two_mul_walkFalls cX X hX
  have h2 := two_mul_walkFalls cY Y hY
  rw [h0, hlast] at h1
  omega

def stepAdj {d : ℕ} (A B : Finset (Fin d)) : Prop :=
  ∃ j : Fin d, ∀ k : Fin d, (decide (k ∈ A) ≠ decide (k ∈ B)) ↔ k = j

theorem stepAdj_symm {d : ℕ} {A B : Finset (Fin d)} (h : stepAdj A B) : stepAdj B A := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun k => by rw [ne_comm]; exact hj k⟩

theorem symmDiff_card_le_one_of_stepAdj {d : ℕ} {A B : Finset (Fin d)} (h : stepAdj A B) :
    ((A \ B) ∪ (B \ A)).card ≤ 1 := by
  obtain ⟨j, hj⟩ := h
  have hsub : (A \ B) ∪ (B \ A) ⊆ {j} := by
    intro k hk
    rw [Finset.mem_singleton]
    apply (hj k).1
    simp only [Finset.mem_union, Finset.mem_sdiff] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  exact le_trans (Finset.card_le_card hsub) (by simp)

theorem symmDiff_triangle {d : ℕ} (A B C : Finset (Fin d)) :
    ((A \ C) ∪ (C \ A)).card ≤ ((A \ B) ∪ (B \ A)).card + ((B \ C) ∪ (C \ B)).card := by
  have hsub : (A \ C) ∪ (C \ A) ⊆ ((A \ B) ∪ (B \ A)) ∪ ((B \ C) ∪ (C \ B)) := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_sdiff] at hk ⊢
    by_cases hB : k ∈ B
    · rcases hk with ⟨hA, hC⟩ | ⟨hC, hA⟩
      · exact Or.inr (Or.inl ⟨hB, hC⟩)
      · exact Or.inl (Or.inr ⟨hB, hA⟩)
    · rcases hk with ⟨hA, hC⟩ | ⟨hC, hA⟩
      · exact Or.inl (Or.inl ⟨hA, hB⟩)
      · exact Or.inr (Or.inr ⟨hC, hB⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

def ValidPath {d : ℕ} : List (Finset (Fin d)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => stepAdj a b ∧ ValidPath (b :: rest)

theorem validPath_append {d : ℕ} {l1 l2 : List (Finset (Fin d))}
    (h1 : ValidPath l1) (h2 : ValidPath l2)
    (hjoin : ∀ a b, l1.getLast? = some a → l2.head? = some b → stepAdj a b) :
    ValidPath (l1 ++ l2) := by
  induction l1 with
  | nil => simpa using h2
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases l2 with
      | nil => trivial
      | cons y ys =>
        exact ⟨hjoin x y rfl rfl, h2⟩
    | cons y ys =>
      refine ⟨h1.1, ih h1.2 ?_⟩
      intro a b hla hlb
      exact hjoin a b (by simpa using hla) hlb

inductive STree (d : ℕ) where
  | node : Finset (Fin d) → List (STree d) → STree d

def STree.root {d : ℕ} : STree d → Finset (Fin d)
  | .node r _ => r

def STree.size {d : ℕ} : STree d → ℕ
  | .node _ cs => 1 + (cs.map STree.size).sum

def STree.verts {d : ℕ} : STree d → Finset (Finset (Fin d))
  | .node r cs => insert r (cs.foldr (fun c acc => c.verts ∪ acc) ∅)

theorem STree.root_mem_verts {d : ℕ} (T : STree d) : T.root ∈ T.verts := by
  cases T with | node r cs => simp only [STree.root, STree.verts]; exact Finset.mem_insert_self r _

theorem STree.mem_foldr_verts {d : ℕ} (cs : List (STree d)) (v : Finset (Fin d)) :
    v ∈ cs.foldr (fun c acc => c.verts ∪ acc) ∅ ↔ ∃ c ∈ cs, v ∈ c.verts := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp, ih]

def STree.WF {d : ℕ} : STree d → Prop
  | .node r cs =>
      (∀ c ∈ cs, stepAdj r c.root ∧ c.WF ∧ r ∉ c.verts) ∧
      cs.Pairwise (fun c1 c2 => Disjoint c1.verts c2.verts)

theorem STree.verts_card_eq_size {d : ℕ} (T : STree d) (h : T.WF) :
    T.verts.card = T.size := by
  match T with
  | .node r cs =>
    simp only [STree.WF] at h
    obtain ⟨hch, hpw⟩ := h
    have hfold : ∀ (ls : List (STree d)),
        (∀ c ∈ ls, c.verts.card = c.size) →
        ls.Pairwise (fun c1 c2 => Disjoint c1.verts c2.verts) →
        (ls.foldr (fun (c : STree d) (acc : Finset (Finset (Fin d))) => c.verts ∪ acc) ∅).card = (ls.map STree.size).sum := by
      intro ls hsz hp
      induction ls with
      | nil => simp
      | cons c rest ih =>
        rw [List.pairwise_cons] at hp
        have hdisj : Disjoint c.verts (rest.foldr (fun c acc => c.verts ∪ acc) ∅) := by
          rw [Finset.disjoint_left]
          intro v hv hvr
          rw [STree.mem_foldr_verts] at hvr
          obtain ⟨c', hc', hvc'⟩ := hvr
          exact Finset.disjoint_left.1 (hp.1 c' hc') hv hvc'
        simp only [List.foldr_cons, List.map_cons, List.sum_cons]
        rw [Finset.card_union_of_disjoint hdisj, hsz c (by simp),
          ih (fun x hx => hsz x (by simp [hx])) hp.2]
    have hnot : r ∉ cs.foldr (fun c acc => c.verts ∪ acc) ∅ := by
      rw [STree.mem_foldr_verts]
      rintro ⟨c, hc, hrc⟩; exact (hch c hc).2.2 hrc
    simp only [STree.verts, STree.size]
    rw [Finset.card_insert_of_notMem hnot,
      hfold cs (fun c hc => STree.verts_card_eq_size c (hch c hc).2.1) hpw]
    omega

def STree.insertAt {d : ℕ} (p v : Finset (Fin d)) : STree d → STree d
  | .node r cs =>
      if r = p then .node r (.node v [] :: cs)
      else .node r (cs.map (STree.insertAt p v))

theorem STree.insertAt_root {d : ℕ} (p v : Finset (Fin d)) (T : STree d) :
    (T.insertAt p v).root = T.root := by
  cases T with | node r cs => simp [STree.insertAt]; split_ifs <;> rfl

theorem STree.size_lt_of_mem {d : ℕ} {r : Finset (Fin d)} {cs : List (STree d)} {c : STree d}
    (hc : c ∈ cs) : c.size < (STree.node r cs).size := by
  simp only [STree.size]
  have hle : c.size ≤ (cs.map STree.size).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem (f := STree.size) hc)
  omega

theorem STree.insertAt_notMem {d : ℕ} {p v : Finset (Fin d)} (T : STree d)
    (hp : p ∉ T.verts) : T.insertAt p v = T := by
  match T with
  | .node r cs =>
    simp only [STree.verts, Finset.mem_insert, STree.mem_foldr_verts, not_or, not_exists, not_and] at hp
    simp only [STree.insertAt, Ne.symm hp.1, ↓reduceIte]
    congr 1
    have hmap : ∀ (ls : List (STree d)), (∀ c ∈ ls, c.size < (STree.node r cs).size) →
        (∀ c ∈ ls, p ∉ c.verts) → ls.map (STree.insertAt p v) = ls := by
      intro ls hlt hls
      induction ls with
      | nil => rfl
      | cons c rest ih =>
        have _ : c.size < (STree.node r cs).size := hlt c (by simp)
        simp only [List.map_cons, STree.insertAt_notMem c (hls c (by simp)),
          ih (fun x hx => hlt x (by simp [hx])) (fun x hx => hls x (by simp [hx]))]
    exact hmap cs (fun c hc => STree.size_lt_of_mem hc) hp.2
termination_by T.size

theorem STree.insertAt_spec {d : ℕ} {p v : Finset (Fin d)} (T : STree d)
    (hWF : T.WF) (hp : p ∈ T.verts) (hv : v ∉ T.verts) (hadj : stepAdj p v) :
    (T.insertAt p v).WF ∧ (T.insertAt p v).verts = insert v T.verts := by
  match T with
  | .node r cs =>
    simp only [STree.WF] at hWF
    obtain ⟨hch, hpw⟩ := hWF
    by_cases hrp : r = p
    · subst hrp
      simp only [STree.insertAt, ↓reduceIte]
      have hleafWF : (STree.node v ([] : List (STree d))).WF := by simp [STree.WF]
      have hleafV : (STree.node v ([] : List (STree d))).verts = {v} := by simp [STree.verts]
      have hv_ne : r ≠ v := fun h => hv (h ▸ STree.root_mem_verts (.node r cs))
      have hv_nch : ∀ c ∈ cs, v ∉ c.verts := fun c hc hvc =>
        hv (by simp only [STree.verts, Finset.mem_insert]; exact Or.inr ((STree.mem_foldr_verts cs v).2 ⟨c, hc, hvc⟩))
      refine ⟨?_, ?_⟩
      · simp only [STree.WF]
        refine ⟨?_, ?_⟩
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨hadj, hleafWF, by rw [hleafV]; simp [hv_ne]⟩
          · exact hch c hc
        · rw [List.pairwise_cons]
          refine ⟨fun c hc => ?_, hpw⟩
          rw [hleafV, Finset.disjoint_singleton_left]
          exact hv_nch c hc
      · simp only [STree.verts, List.foldr_cons, hleafV]
        ext x; simp [Finset.mem_insert]; tauto
    · simp only [STree.insertAt, hrp, ↓reduceIte]
      have hp_fold : p ∈ cs.foldr (fun c acc => c.verts ∪ acc) ∅ := by
        simp only [STree.verts, Finset.mem_insert] at hp
        exact hp.resolve_left (Ne.symm hrp)
      obtain ⟨c0, hc0, hpc0⟩ := (STree.mem_foldr_verts cs p).1 hp_fold
      have hv_nch : ∀ c ∈ cs, v ∉ c.verts := fun c hc hvc =>
        hv (by simp only [STree.verts, Finset.mem_insert]; exact Or.inr ((STree.mem_foldr_verts cs v).2 ⟨c, hc, hvc⟩))
      have hne_rv : r ≠ v := fun h => hv (h ▸ STree.root_mem_verts (.node r cs))
      have hmap_spec : ∀ c ∈ cs, (c.insertAt p v).WF ∧
          (c.insertAt p v).verts = if p ∈ c.verts then insert v c.verts else c.verts := by
        intro c hc
        by_cases hpc : p ∈ c.verts
        · have hrec := STree.insertAt_spec c (hch c hc).2.1 hpc (hv_nch c hc) hadj
          exact ⟨hrec.1, by simp [hpc, hrec.2]⟩
        · rw [STree.insertAt_notMem c hpc]
          exact ⟨(hch c hc).2.1, by simp [hpc]⟩
      refine ⟨?_, ?_⟩
      · simp only [STree.WF]
        refine ⟨?_, ?_⟩
        · intro c' hc'
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
          have hs := hmap_spec c hc
          refine ⟨by rw [STree.insertAt_root]; exact (hch c hc).1, hs.1, ?_⟩
          rw [hs.2]; split_ifs
          · simp [hne_rv, (hch c hc).2.2]
          · exact (hch c hc).2.2
        · rw [List.pairwise_map]
          refine hpw.imp_of_mem ?_
          intro c1 c2 hc1 hc2 hdisj
          have hs1 := (hmap_spec c1 hc1).2
          have hs2 := (hmap_spec c2 hc2).2
          rw [hs1, hs2]
          by_cases h1 : p ∈ c1.verts
          · have h2 : p ∉ c2.verts := Finset.disjoint_left.1 hdisj h1
            simp only [h1, h2, ↓reduceIte, Finset.disjoint_insert_left]
            exact ⟨hv_nch c2 hc2, hdisj⟩
          · by_cases h2 : p ∈ c2.verts
            · simp only [h1, h2, ↓reduceIte, Finset.disjoint_insert_right]
              exact ⟨hv_nch c1 hc1, hdisj⟩
            · simp only [h1, h2, ↓reduceIte]; exact hdisj
      · ext x
        simp only [STree.verts, Finset.mem_insert, STree.mem_foldr_verts, List.mem_map]
        constructor
        · rintro (rfl | ⟨c', ⟨c, hc, rfl⟩, hx⟩)
          · exact Or.inr (Or.inl rfl)
          · rw [(hmap_spec c hc).2] at hx
            split_ifs at hx
            · rcases Finset.mem_insert.1 hx with rfl | hx
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ⟨c, hc, hx⟩)
            · exact Or.inr (Or.inr ⟨c, hc, hx⟩)
        · rintro (hx | rfl | ⟨c, hc, hx⟩)
          · right; refine ⟨c0.insertAt p v, ⟨c0, hc0, rfl⟩, ?_⟩
            rw [hx, (hmap_spec c0 hc0).2, if_pos hpc0]; exact Finset.mem_insert_self _ _
          · left; rfl
          · right; refine ⟨c.insertAt p v, ⟨c, hc, rfl⟩, ?_⟩
            rw [(hmap_spec c hc).2]; split_ifs
            · exact Finset.mem_insert_of_mem hx
            · exact hx

def STree.loop {d : ℕ} : STree d → List (Finset (Fin d))
  | .node r cs => r :: cs.flatMap fun c => c.loop ++ [r]

theorem STree.loop_spec {d : ℕ} (T : STree d) (hWF : T.WF) :
    ValidPath T.loop ∧ T.loop.head? = some T.root ∧ T.loop.getLast? = some T.root ∧
    T.loop.toFinset = T.verts ∧ T.loop.length = 2 * T.size - 1 := by
  match T with
  | .node r cs =>
    simp only [STree.WF] at hWF
    obtain ⟨hch, -⟩ := hWF
    have haux : ∀ (ls : List (STree d)),
        (∀ c ∈ ls, c.size < (STree.node r cs).size) →
        (∀ c ∈ ls, stepAdj r c.root ∧ c.WF ∧ r ∉ c.verts) →
        let L := r :: ls.flatMap fun c => c.loop ++ [r]
        ValidPath L ∧ L.head? = some r ∧ L.getLast? = some r ∧
        L.toFinset = insert r (ls.foldr (fun c acc => c.verts ∪ acc) ∅) ∧
        L.length = 1 + 2 * (ls.map STree.size).sum := by
      intro ls hlt hls
      induction ls with
      | nil =>
        refine ⟨trivial, rfl, rfl, by simp, by simp⟩
      | cons c rest ih =>
        have hc := hls c (by simp)
        have _ : c.size < (STree.node r cs).size := hlt c (by simp)
        have ih' := ih (fun x hx => hlt x (by simp [hx])) (fun x hx => hls x (by simp [hx]))
        have hcs := STree.loop_spec c hc.2.1
        have hpos : 0 < c.size := by cases c; simp [STree.size]
        have hne_c : c.loop ≠ [] := by
          intro he; rw [he] at hcs; simp at hcs
        have heq_list : (r :: (c :: rest).flatMap fun x => x.loop ++ [r]) =
            ([r] ++ c.loop) ++ (r :: rest.flatMap fun x => x.loop ++ [r]) := by
          simp [List.flatMap_cons, List.append_assoc]
        have hvp1 : ValidPath ([r] ++ c.loop) := by
          apply validPath_append (by simp [ValidPath] : ValidPath [r]) hcs.1
          intro a b ha hb
          simp at ha; subst ha
          rw [hcs.2.1] at hb; cases hb; exact hc.1
        have hlast1 : ([r] ++ c.loop).getLast? = some c.root := by
          rw [List.getLast?_append_of_ne_nil _ hne_c]
          exact hcs.2.2.1
        have hvp : ValidPath (r :: (c :: rest).flatMap fun x => x.loop ++ [r]) := by
          rw [heq_list]
          apply validPath_append hvp1 ih'.1
          intro a b ha hb
          rw [hlast1] at ha; cases ha
          rw [ih'.2.1] at hb; cases hb
          exact stepAdj_symm hc.1
        have hlast : (r :: (c :: rest).flatMap fun x => x.loop ++ [r]).getLast? = some r := by
          rw [heq_list, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
          exact ih'.2.2.1
        have hfin : (r :: (c :: rest).flatMap fun x => x.loop ++ [r]).toFinset =
            insert r ((c :: rest).foldr (fun x acc => x.verts ∪ acc) ∅) := by
          rw [heq_list, List.toFinset_append, List.toFinset_append, List.toFinset_cons,
            List.toFinset_nil, hcs.2.2.2.1, ih'.2.2.2.1]
          simp only [List.foldr_cons]
          ext x; simp [Finset.mem_insert, Finset.mem_union]
        have hlen : (r :: (c :: rest).flatMap fun x => x.loop ++ [r]).length =
            1 + 2 * ((c :: rest).map STree.size).sum := by
          rw [heq_list, List.length_append, List.length_append, List.length_singleton,
            hcs.2.2.2.2, ih'.2.2.2.2]
          simp only [List.map_cons, List.sum_cons]
          omega
        exact ⟨hvp, rfl, hlast, hfin, hlen⟩
    have hres := haux cs (fun c hc => STree.size_lt_of_mem hc) hch
    dsimp only at hres
    simp only [STree.loop, STree.root, STree.verts, STree.size]
    exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1, by omega⟩
termination_by T.size

open Classical in
noncomputable def STree.tour {d : ℕ} (T : STree d) (t : Finset (Fin d)) :
    List (Finset (Fin d)) × ℕ :=
  match T with
  | .node r cs =>
      if t = r then (STree.loop (.node r cs), 0)
      else
        let others := cs.filter fun c => decide (t ∉ c.verts)
        let prefixL := r :: others.flatMap fun c => c.loop ++ [r]
        match hfind : cs.find? fun c => decide (t ∈ c.verts) with
        | none => (STree.loop (.node r cs), 0)
        | some c0 =>
            have _ : c0.size < (STree.node r cs).size := STree.size_lt_of_mem (List.mem_of_find?_eq_some hfind)
            let res := c0.tour t
            (prefixL ++ res.1, res.2 + 1)
termination_by T.size

open Classical in
theorem STree.tour_spec {d : ℕ} (T : STree d) (hWF : T.WF) (t : Finset (Fin d))
    (ht : t ∈ T.verts) :
    let res := T.tour t
    ValidPath res.1 ∧ res.1.head? = some T.root ∧ res.1.getLast? = some t ∧
    res.1.toFinset = T.verts ∧ res.1.length + res.2 = 2 * T.size - 1 ∧
    ((T.root \ t) ∪ (t \ T.root)).card ≤ res.2 := by
  match T with
  | .node r cs =>
    simp only [STree.WF] at hWF
    obtain ⟨hch, hpw⟩ := hWF
    by_cases htr : t = r
    · subst htr
      have hwf' : (STree.node t cs).WF := by simp only [STree.WF]; exact ⟨hch, hpw⟩
      have hlp := STree.loop_spec (.node t cs) hwf'
      dsimp only
      rw [STree.tour]
      simp only [↓reduceIte]
      exact ⟨hlp.1, hlp.2.1, hlp.2.2.1, hlp.2.2.2.1, by simpa using hlp.2.2.2.2, by simp [STree.root]⟩
    · have ht_fold : t ∈ cs.foldr (fun c acc => c.verts ∪ acc) ∅ := by
        simp only [STree.verts, Finset.mem_insert] at ht
        exact ht.resolve_left htr
      obtain ⟨c1, hc1, htc1⟩ := (STree.mem_foldr_verts cs t).1 ht_fold
      have hfind_ne : (cs.find? fun c => decide (t ∈ c.verts)).isSome := by
        rw [List.find?_isSome]; exact ⟨c1, hc1, by simp [htc1]⟩
      obtain ⟨c0, hfind⟩ := Option.isSome_iff_exists.1 hfind_ne
      have hc0_mem : c0 ∈ cs := List.mem_of_find?_eq_some hfind
      have htc0 : t ∈ c0.verts := by
        have := List.find?_some hfind; simpa using this
      have hrec := STree.tour_spec c0 (hch c0 hc0_mem).2.1 t htc0
      dsimp only at hrec
      let others := cs.filter fun c => decide (t ∉ c.verts)
      have hothers_sub : ∀ c ∈ others, c ∈ cs := fun c hc => (List.mem_filter.1 hc).1
      have hothers_disj : ∀ c ∈ others, t ∉ c.verts := fun c hc => by
        simpa using (List.mem_filter.1 hc).2
      have huniq : ∀ c ∈ cs, t ∈ c.verts → c = c0 := by
        intro c hc htc
        by_contra hne
        have hdisj : Disjoint c.verts c0.verts ∨ Disjoint c0.verts c.verts := by
          have := List.pairwise_iff_getElem.1 hpw
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc0_mem
          rcases lt_trichotomy i j with hlt | heq | hgt
          · exact Or.inl (this i j hi hj hlt)
          · subst heq; exact absurd rfl hne
          · exact Or.inr (this j i hj hi hgt)
        rcases hdisj with hd | hd
        · exact Finset.disjoint_left.1 hd htc htc0
        · exact Finset.disjoint_left.1 hd htc0 htc
      have hloop_others :
          let L := r :: others.flatMap fun c => c.loop ++ [r]
          ValidPath L ∧ L.head? = some r ∧ L.getLast? = some r ∧
          L.toFinset = insert r (others.foldr (fun c acc => c.verts ∪ acc) ∅) ∧
          L.length = 1 + 2 * (others.map STree.size).sum := by
        have hwf_o : (STree.node r others).WF := by
          simp only [STree.WF]
          exact ⟨fun c hc => hch c (hothers_sub c hc), List.Pairwise.filter _ hpw⟩
        have hlp := STree.loop_spec (.node r others) hwf_o
        simp only [STree.loop, STree.root, STree.verts, STree.size] at hlp
        dsimp only
        refine ⟨hlp.1, hlp.2.1, hlp.2.2.1, hlp.2.2.2.1, by omega⟩
      dsimp only at hloop_others
      have hsum_split : (cs.map STree.size).sum = (others.map STree.size).sum + c0.size := by
        have hpart : ∀ (ls : List (STree d)),
            ls.Pairwise (fun a b => Disjoint a.verts b.verts) →
            c0 ∈ ls →
            (ls.map STree.size).sum =
              ((ls.filter fun c => decide (t ∉ c.verts)).map STree.size).sum + c0.size := by
          intro ls hls hmem
          induction ls with
          | nil => simp at hmem
          | cons x xs ih =>
            rw [List.pairwise_cons] at hls
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · have hnot : ∀ y ∈ xs, t ∉ y.verts := fun y hy hty =>
                Finset.disjoint_left.1 (hls.1 y hy) htc0 hty
              have hfilt : (xs.filter fun c => decide (t ∉ c.verts)) = xs :=
                List.filter_eq_self.2 fun y hy => by simp [hnot y hy]
              simp only [List.filter_cons, htc0, not_true_eq_false, decide_false, Bool.false_eq_true,
                ↓reduceIte, hfilt, List.map_cons, List.sum_cons]
              omega
            · have htx : t ∉ x.verts := fun htx =>
                Finset.disjoint_left.1 (hls.1 c0 hmem) htx htc0
              simp only [List.filter_cons, htx, not_false_eq_true, decide_true, ↓reduceIte,
                List.map_cons, List.sum_cons]
              rw [ih hls.2 hmem]; omega
        exact hpart cs hpw hc0_mem
      have hne_rec : (c0.tour t).1 ≠ [] := by
        intro he; have hh := hrec.2.1; rw [he] at hh; simp at hh
      have htour_eq : (STree.node r cs).tour t =
          ((r :: others.flatMap fun c => c.loop ++ [r]) ++ (c0.tour t).1, (c0.tour t).2 + 1) := by
        rw [STree.tour]
        dsimp only
        rw [if_neg htr]
        split
        · rename_i hnone; rw [hfind] at hnone; cases hnone
        · rename_i c0' hsome; rw [hfind] at hsome; cases hsome; rfl
      dsimp only
      rw [htour_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply validPath_append hloop_others.1 hrec.1
        intro a b ha hb
        rw [hloop_others.2.2.1] at ha; cases ha
        rw [hrec.2.1] at hb; cases hb
        exact (hch c0 hc0_mem).1
      · simp [STree.root]
      · rw [List.getLast?_append_of_ne_nil _ hne_rec]
        exact hrec.2.2.1
      · rw [List.toFinset_append, hloop_others.2.2.2.1, hrec.2.2.2.1]
        ext x
        simp only [STree.verts, Finset.mem_union, Finset.mem_insert, STree.mem_foldr_verts]
        constructor
        · rintro ((rfl | ⟨c, hc, hxc⟩) | hxc0)
          · exact Or.inl rfl
          · exact Or.inr ⟨c, hothers_sub c hc, hxc⟩
          · exact Or.inr ⟨c0, hc0_mem, hxc0⟩
        · rintro (rfl | ⟨c, hc, hxc⟩)
          · exact Or.inl (Or.inl rfl)
          · by_cases htc : t ∈ c.verts
            · rw [huniq c hc htc] at hxc; exact Or.inr hxc
            · exact Or.inl (Or.inr ⟨c, List.mem_filter.2 ⟨hc, by simp [htc]⟩, hxc⟩)
      · rw [List.length_append, hloop_others.2.2.2.2]
        have hpos0 : 0 < c0.size := by cases c0; simp [STree.size]
        simp only [STree.size]
        omega
      · have htri := symmDiff_triangle r c0.root t
        have hadj1 := symmDiff_card_le_one_of_stepAdj (hch c0 hc0_mem).1
        simp only [STree.root]
        omega

theorem build_spanning_tree {n d : ℕ} (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    ∃ T : STree d, T.WF ∧ T.root = X 0 ∧ T.verts = Finset.univ.image X := by
  let S : Finset (Finset (Fin d)) := Finset.univ.image X
  have hstep : ∀ i : Fin n, stepAdj (X i.castSucc) (X i.succ) :=
    fun i => ⟨color i, fun k => (hX i k).trans eq_comm⟩
  have haux : ∀ k (T : STree d), T.WF → T.root = X 0 → T.verts ⊆ S → (S \ T.verts).card = k →
      ∃ T' : STree d, T'.WF ∧ T'.root = X 0 ∧ T'.verts = S := by
    intro k
    induction k with
    | zero =>
      intro T hWF hroot hsub hcard
      have hempty : S \ T.verts = ∅ := Finset.card_eq_zero.1 hcard
      have heq : T.verts = S := Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.1 hempty)
      exact ⟨T, hWF, hroot, heq⟩
    | succ k ih =>
      intro T hWF hroot hsub hcard
      have hne : (S \ T.verts).Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨v0, hv0⟩ := hne
      rw [Finset.mem_sdiff] at hv0
      obtain ⟨l0, -, rfl⟩ := Finset.mem_image.1 hv0.1
      have hX0 : X 0 ∈ T.verts := hroot ▸ T.root_mem_verts

      have hex : ∃ l : Fin (n + 1), X l ∉ T.verts := ⟨l0, hv0.2⟩
      have hfind : ∃ i : Fin n, X i.castSucc ∈ T.verts ∧ X i.succ ∉ T.verts := by
        let P : ℕ → Prop := fun m => ∃ hm : m < n + 1, X ⟨m, hm⟩ ∉ T.verts
        classical
        have hP : ∃ m, P m := ⟨l0.val, l0.isLt, hv0.2⟩
        let m0 := Nat.find hP
        have hm0 : P m0 := Nat.find_spec hP
        have hm0_pos : 0 < m0 := by
          by_contra h0
          have : m0 = 0 := by omega
          obtain ⟨hlt, hnot⟩ := hm0
          have heq0 : (⟨m0, hlt⟩ : Fin (n + 1)) = 0 := Fin.ext this
          rw [heq0] at hnot; exact hnot hX0
        have hm0_lt : m0 - 1 < n := by obtain ⟨hlt, _⟩ := hm0; omega
        refine ⟨⟨m0 - 1, hm0_lt⟩, ?_, ?_⟩
        · by_contra hnot
          have hlt' : m0 - 1 < m0 := by omega
          exact Nat.find_min hP hlt' ⟨by omega, hnot⟩
        · obtain ⟨hlt, hnot⟩ := hm0
          have heq : (⟨m0 - 1, hm0_lt⟩ : Fin n).succ = ⟨m0, hlt⟩ := by
            ext; simp; omega
          rwa [heq]
      obtain ⟨i, hi_in, hi_out⟩ := hfind
      have hins := STree.insertAt_spec T hWF hi_in hi_out (hstep i)
      have hsub' : (T.insertAt (X i.castSucc) (X i.succ)).verts ⊆ S := by
        rw [hins.2, Finset.insert_subset_iff]
        exact ⟨Finset.mem_image.2 ⟨i.succ, Finset.mem_univ _, rfl⟩, hsub⟩
      have hcard' : (S \ (T.insertAt (X i.castSucc) (X i.succ)).verts).card = k := by
        rw [hins.2]
        have hmem : X i.succ ∈ S \ T.verts :=
          Finset.mem_sdiff.2 ⟨Finset.mem_image.2 ⟨i.succ, Finset.mem_univ _, rfl⟩, hi_out⟩
        have heq_sd : S \ insert (X i.succ) T.verts = (S \ T.verts).erase (X i.succ) := by
          ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
        rw [heq_sd, Finset.card_erase_of_mem hmem, hcard]; omega
      exact ih (T.insertAt (X i.castSucc) (X i.succ)) hins.1
        ((STree.insertAt_root _ _ T).trans hroot) hsub' hcard'
  let T0 : STree d := .node (X 0) []
  have hWF0 : T0.WF := by simp [T0, STree.WF]
  have hsub0 : T0.verts ⊆ S := by
    intro x hx
    simp only [T0, STree.verts, List.foldr_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hx
    subst hx
    exact Finset.mem_image.2 ⟨(0 : Fin (n + 1)), Finset.mem_univ _, rfl⟩
  exact haux (S \ T0.verts).card T0 hWF0 rfl hsub0 rfl

theorem walk_shorten {n d : ℕ} (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    ∃ (m : ℕ) (Y : Fin (m + 1) → Finset (Fin d)), m ≤ n ∧
      (∃ cY : Fin m → Fin d, Function.Surjective cY ∧
        ∀ i j, (decide (j ∈ Y i.castSucc) ≠ decide (j ∈ Y i.succ)) ↔ cY i = j) ∧
      Finset.univ.image X = Finset.univ.image Y ∧ X 0 = Y 0 ∧ X (Fin.last n) = Y (Fin.last m) ∧
      m + ((X 0 \ X (Fin.last n)) ∪ (X (Fin.last n) \ X 0)).card ≤
        2 * ((Finset.univ.image X).card - 1) := by
  obtain ⟨T, hWF, hroot, hverts⟩ := build_spanning_tree color X hX
  have hlast_mem : X (Fin.last n) ∈ T.verts := by
    rw [hverts]; exact Finset.mem_image.2 ⟨Fin.last n, Finset.mem_univ _, rfl⟩
  have htour := STree.tour_spec T hWF (X (Fin.last n)) hlast_mem
  dsimp only at htour
  set L := (T.tour (X (Fin.last n))).1
  set dep := (T.tour (X (Fin.last n))).2
  have hL_ne : L ≠ [] := by
    intro h
    have hh := htour.2.1
    rw [h] at hh; simp at hh
  have hL_pos : 0 < L.length := List.length_pos_iff.2 hL_ne
  let m' := L.length - 1
  have hm'_eq : m' + 1 = L.length := Nat.sub_add_cancel hL_pos
  have hbound : m' + ((X 0 \ X (Fin.last n)) ∪ (X (Fin.last n) \ X 0)).card ≤
      2 * ((Finset.univ.image X).card - 1) := by
    have hcard := T.verts_card_eq_size hWF
    rw [hverts] at hcard
    rw [hroot] at htour
    have hpos_sz : 0 < T.size := by cases T; simp [STree.size]
    have hlen_dep : L.length + dep = 2 * T.size - 1 := htour.2.2.2.2.1
    have hdist_le : ((X 0 \ X (Fin.last n)) ∪ (X (Fin.last n) \ X 0)).card ≤ dep := htour.2.2.2.2.2
    omega
  by_cases hle : m' ≤ n
  · let Y : Fin (m' + 1) → Finset (Fin d) := fun l => L.get (l.cast hm'_eq)
    have hY_step : ∀ i : Fin m', stepAdj (Y i.castSucc) (Y i.succ) := by
      have hvp_get : ∀ (ls : List (Finset (Fin d))), ValidPath ls →
          ∀ (k : ℕ) (hk : k + 1 < ls.length),
            stepAdj (ls.get ⟨k, by omega⟩) (ls.get ⟨k + 1, hk⟩) := by
        intro ls hvp
        induction ls with
        | nil => intro k hk; simp at hk
        | cons a rest ih =>
          cases rest with
          | nil => intro k hk; simp at hk
          | cons b rest' =>
            intro k hk
            cases k with
            | zero => exact hvp.1
            | succ k' => exact ih hvp.2 k' (by simpa using hk)
      intro i
      exact hvp_get L htour.1 i.val (by omega)
    have hY_img : Finset.univ.image Y = Finset.univ.image X := by
      rw [← hverts, ← htour.2.2.2.1]
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨l, rfl⟩; exact List.get_mem L _
      · intro hv
        obtain ⟨idx, rfl⟩ := List.mem_iff_get.1 hv
        exact ⟨idx.cast hm'_eq.symm, by simp [Y, List.get_eq_getElem]⟩
    have hY0 : Y 0 = X 0 := by
      have hh := htour.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hL_pos] at hh
      have h1 : L[0] = T.root := Option.some.inj hh
      simpa [Y, List.get_eq_getElem, hroot] using h1
    have hYlast : Y (Fin.last m') = X (Fin.last n) := by
      have hl := htour.2.2.1
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (Nat.sub_lt hL_pos (by omega))] at hl
      have h1 : L[L.length - 1] = X (Fin.last n) := Option.some.inj hl
      simpa [Y, List.get_eq_getElem, m'] using h1
    classical
    let cY : Fin m' → Fin d := fun i => Classical.choose (hY_step i)
    have hcY : ∀ i j, (decide (j ∈ Y i.castSucc) ≠ decide (j ∈ Y i.succ)) ↔ cY i = j :=
      fun i j => (Classical.choose_spec (hY_step i) j).trans eq_comm
    have hcY_surj : Function.Surjective cY := by
      intro j
      obtain ⟨i0, hi0⟩ := hsurj j
      have hdiff := (hX i0 j).2 hi0
      have hmem1 : X i0.castSucc ∈ Finset.univ.image Y := by
        rw [hY_img]; exact Finset.mem_image.2 ⟨i0.castSucc, Finset.mem_univ _, rfl⟩
      have hmem2 : X i0.succ ∈ Finset.univ.image Y := by
        rw [hY_img]; exact Finset.mem_image.2 ⟨i0.succ, Finset.mem_univ _, rfl⟩
      obtain ⟨l1, -, hl1⟩ := Finset.mem_image.1 hmem1
      obtain ⟨l2, -, hl2⟩ := Finset.mem_image.1 hmem2
      rw [← hl1, ← hl2] at hdiff

      have hne_chg : (chg (coord Y j)).Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        exact hdiff (const_of_chg_empty he l1 l2)
      obtain ⟨i, hi⟩ := hne_chg
      exact ⟨i, (hcY i j).1 ((mem_chg (coord Y j) i).1 hi)⟩
    exact ⟨m', Y, hle, ⟨cY, hcY_surj, hcY⟩, hY_img.symm, hY0.symm, hYlast.symm, hbound⟩
  · exact ⟨n, X, le_refl n, ⟨color, hsurj, hX⟩, rfl, rfl, rfl, by omega⟩

def logInput (d : ℕ) (A : Finset (Fin d)) : List Bool :=
  List.ofFn (fun j : Fin d => decide (j ∈ A)) ++
  List.ofFn (fun j : Fin d => !decide (j ∈ A)) ++ [false, true]

theorem logInput_len (d : ℕ) (A : Finset (Fin d)) : (logInput d A).length = 2 * d + 2 := by
  simp [logInput]; omega

theorem logInput_pos (d : ℕ) (A : Finset (Fin d)) (j : Fin d) :
    (logInput d A).getD j.val false = decide (j ∈ A) := by
  unfold logInput
  rw [List.append_assoc, List.getD_append _ _ _ _ (by simp [j.isLt]),
    List.getD_eq_getElem _ _ (by simp [j.isLt])]
  simp

theorem logInput_neg (d : ℕ) (A : Finset (Fin d)) (j : Fin d) :
    (logInput d A).getD (d + j.val) false = !decide (j ∈ A) := by
  unfold logInput
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
    List.length_ofFn, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simp [j.isLt]),
    List.getD_eq_getElem _ _ (by simp [j.isLt])]
  simp

theorem logInput_false (d : ℕ) (A : Finset (Fin d)) :
    (logInput d A).getD (2 * d) false = false := by
  unfold logInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  have h : 2 * d - (List.ofFn (fun j : Fin d => decide (j ∈ A)) ++
      List.ofFn (fun j : Fin d => !decide (j ∈ A))).length = 0 := by simp; omega
  rw [h]; rfl

theorem logInput_true (d : ℕ) (A : Finset (Fin d)) :
    (logInput d A).getD (2 * d + 1) false = true := by
  unfold logInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  have h : 2 * d + 1 - (List.ofFn (fun j : Fin d => decide (j ∈ A)) ++
      List.ofFn (fun j : Fin d => !decide (j ∈ A))).length = 1 := by simp; omega
  rw [h]; rfl

def AllowedIn (d : ℕ) (s0 s1 : Finset (Fin d)) (w : ℕ) : Prop :=
  w < d ∨ (∃ j : Fin d, w = d + j.val ∧ j ∈ s0 ∧ j ∉ s1) ∨ 2 * d ≤ w

def LogFit (d : ℕ) (S : Finset (Finset (Fin d))) (s0 s1 : Finset (Fin d))
    (a : ℕ) (M : Fin (a + 1) → Finset (Fin d)) (phase : Fin (a + 1) → Bool) (b_log : ℕ) : Prop :=
  ∃ (D : Circuit) (out : Fin (a + 1) → ℕ),
    PEqualNP.MetaComplexity.FanInTwo D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * d + 2) D ∧
    (∀ g ∈ D.gates, ∀ i ∈ g.inputs, AllowedIn d s0 s1 i) ∧
    (∀ t, out t < 2 * d + 2 + D.size ∧ AllowedIn d s0 s1 (out t)) ∧
    nonNotCount D.gates ≤ d - 1 ∧
    PEqualNP.NotBracket.notCount D ≤ b_log ∧
    ∀ A ∈ S, ∀ t,
      (W D.gates (logInput d A)).getD (out t) false =
        Bool.xor (phase t) (decide ((A ∩ M t).card % 2 = 1))

def remapGate (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem isNotGate_remap (φ : ℕ → ℕ) (g : Gate) : isNotGate (remapGate φ g) = isNotGate g := rfl

theorem nonNotCount_remap (φ : ℕ → ℕ) (gs : List Gate) :
    nonNotCount (gs.map (remapGate φ)) = nonNotCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, nonNotCount, List.filter_cons, isNotGate_remap]
    by_cases h : isNotGate g = true
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ih
    · have hf : isNotGate g = false := Bool.eq_false_iff.2 h
      simp only [hf, Bool.not_false, ↓reduceIte, List.length_cons]
      exact congrArg Nat.succ ih

theorem notCount_remap (φ : ℕ → ℕ) (gs : List Gate) :
    PEqualNP.NotBracket.notCount ⟨gs.map (remapGate φ), 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  rw [notCount_eq_filter, notCount_eq_filter]
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.filter_cons, isNotGate_remap]
    by_cases h : isNotGate g = true
    · simp only [h, ↓reduceIte, List.length_cons]; exact congrArg Nat.succ ih
    · have hf : isNotGate g = false := Bool.eq_false_iff.2 h
      simp only [hf, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem build_walk_taps {n d : ℕ} (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    ∃ (gs : List Gate) (tap negTap : Fin d → ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ ∧
      nonNotCount gs = n - d ∧
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = walkFalls X ∧
      (∀ j, tap j < n + 2 + gs.length ∧ ∀ l, vl n gs (tap j) l = decide (j ∈ X l)) ∧
      (∀ j, j ∈ X 0 → j ∉ X (Fin.last n) →
        negTap j < n + 2 + gs.length ∧ ∀ l, vl n gs (negTap j) l = !decide (j ∈ X l)) := by
  have haux : ∀ k (hk : k ≤ d),
      ∃ (gs : List Gate) (tap negTap : Fin d → ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ ∧
        nonNotCount gs = ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), ((colorClass color j).card - 1) ∧
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ =
          ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), (falls (coord X j)).card ∧
        (∀ j : Fin d, j.val < k → tap j < n + 2 + gs.length ∧ ∀ l, vl n gs (tap j) l = decide (j ∈ X l)) ∧
        (∀ j : Fin d, j.val < k → j ∈ X 0 → j ∉ X (Fin.last n) →
          negTap j < n + 2 + gs.length ∧ ∀ l, vl n gs (negTap j) l = !decide (j ∈ X l)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun _ => 0, fun _ => 0, by intro g hg; simp at hg,
        by intro i hi; simp at hi, by simp [nonNotCount], by rw [notCount_eq_filter]; simp,
        fun j hj => by omega, fun j hj => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨gs, tap, negTap, hF, hR, hnn, hnc, htap, hneg⟩ := ih (by omega)
      let j0 : Fin d := ⟨k, hk⟩
      have hne : (chg (coord X j0)).Nonempty := by
        rw [chg_coord_eq_colorClass color X hX j0]; exact colorClass_nonempty color hsurj j0
      have hfilt : Finset.univ.filter (fun j : Fin d => j.val < k + 1) =
          insert j0 (Finset.univ.filter (fun j : Fin d => j.val < k)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, j0]
        omega
      have hj0_not : j0 ∉ Finset.univ.filter (fun j : Fin d => j.val < k) := by
        simp [j0]
      by_cases hspec : j0 ∈ X 0 ∧ j0 ∉ X (Fin.last n)
      · have hne' : (chg (fun l => !coord X j0 l)).Nonempty := by
          rw [chg_congr (Or.inr fun _ => rfl)]; exact hne
        obtain ⟨extra, wneg, hwneg_lt, hF1, hR1, hnn1, hnc1, hval1⟩ :=
          build_prefix_fn (fun l => !coord X j0 l) hne' gs hF hR
        let gnot : Gate := ⟨GateOp.not, [wneg]⟩
        let gs' := (gs ++ extra) ++ [gnot]
        let wpos := n + 2 + (gs ++ extra).length
        have hF2 : PEqualNP.MetaComplexity.FanInTwo ⟨gs', 0⟩ := by
          apply fanInTwo_append hF1
          intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gnot]
        have hR2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs', 0⟩ := by
          apply readsBack_snoc hR1
          intro i hi; simp only [gnot, List.mem_singleton] at hi; subst hi; exact hwneg_lt
        have hfalls_rel : (falls (fun l => !coord X j0 l)).card + 1 = (falls (coord X j0)).card :=
          (falls_not_vs_falls (coord X j0)).1 ⟨by simp [coord, hspec.1], by simp [coord, hspec.2]⟩
        refine ⟨gs', fun j => if j = j0 then wpos else tap j,
          fun j => if j = j0 then wneg else negTap j, hF2, hR2, ?_, ?_, ?_, ?_⟩
        · rw [hfilt, Finset.sum_insert hj0_not]
          simp only [gs', nonNotCount_append, hnn, hnn1]
          have h1 : nonNotCount [gnot] = 0 := by simp [nonNotCount, isNotGate, gnot]
          have h2 : chg (fun l => !coord X j0 l) = colorClass color j0 := by
            rw [chg_congr (Or.inr fun _ => rfl), chg_coord_eq_colorClass color X hX j0]
          rw [h1, h2]; omega
        · rw [hfilt, Finset.sum_insert hj0_not]
          simp only [gs', notCount_append, hnc, hnc1]
          have h1 : PEqualNP.NotBracket.notCount ⟨[gnot], 0⟩ = 1 := by
            rw [notCount_eq_filter]; rfl
          rw [h1]; omega
        · intro j hj
          by_cases heq : j = j0
          · subst heq; simp only [↓reduceIte]
            refine ⟨by simp [gs', wpos], fun l => ?_⟩
            have hnw := new_wire (gs ++ extra) gnot (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W ((gs ++ extra) ++ [gnot]) (prefixInput n l)).getD (n + 2 + (gs ++ extra).length) false = _
            rw [hnw]
            simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            have := hval1 l; unfold vl at this; rw [this]; simp [coord]
          · have hjk : j.val < k := by
              have : j.val ≠ k := fun h => heq (Fin.ext h)
              omega
            simp only [heq, ↓reduceIte]
            have hlt := (htap j hjk).1
            refine ⟨by simp [gs']; omega, fun l => ?_⟩
            have h1 := W_append_old gs (extra ++ [gnot]) (prefixInput n l) (tap j) (by rw [prefixInput_len]; omega)
            rw [← List.append_assoc] at h1
            exact h1.trans ((htap j hjk).2 l)
        · intro j hj hj0 hj1
          by_cases heq : j = j0
          · subst heq; simp only [↓reduceIte]
            refine ⟨by simp only [gs', List.length_append, List.length_singleton] at hwneg_lt ⊢; omega, fun l => ?_⟩
            have h1 := old_wire (gs ++ extra) gnot (prefixInput n l) wneg (by rw [prefixInput_len]; exact ne_of_lt hwneg_lt)
            exact h1.trans (hval1 l)
          · have hjk : j.val < k := by
              have : j.val ≠ k := fun h => heq (Fin.ext h)
              omega
            simp only [heq, ↓reduceIte]
            have hlt := (hneg j hjk hj0 hj1).1
            refine ⟨by simp [gs']; omega, fun l => ?_⟩
            have h1 := W_append_old gs (extra ++ [gnot]) (prefixInput n l) (negTap j) (by rw [prefixInput_len]; omega)
            rw [← List.append_assoc] at h1
            exact h1.trans ((hneg j hjk hj0 hj1).2 l)
      · obtain ⟨extra, wpos, hwpos_lt, hF1, hR1, hnn1, hnc1, hval1⟩ :=
          build_prefix_fn (coord X j0) hne gs hF hR
        refine ⟨gs ++ extra, fun j => if j = j0 then wpos else tap j, negTap, hF1, hR1, ?_, ?_, ?_, ?_⟩
        · rw [hfilt, Finset.sum_insert hj0_not, nonNotCount_append, hnn, hnn1,
            chg_coord_eq_colorClass color X hX j0]
          omega
        · rw [hfilt, Finset.sum_insert hj0_not, notCount_append, hnc, hnc1]; omega
        · intro j hj
          by_cases heq : j = j0
          · subst heq; simp only [↓reduceIte]; exact ⟨hwpos_lt, hval1⟩
          · have hjk : j.val < k := by
              have : j.val ≠ k := fun h => heq (Fin.ext h)
              omega
            simp only [heq, ↓reduceIte]
            have hlt := (htap j hjk).1
            refine ⟨by simp; omega, fun l => ?_⟩
            exact (W_append_old gs extra (prefixInput n l) (tap j) (by rw [prefixInput_len]; omega)).trans
              ((htap j hjk).2 l)
        · intro j hj hj0 hj1
          have hne_j : j ≠ j0 := fun h => hspec (h ▸ ⟨hj0, hj1⟩)
          have hjk : j.val < k := by
            have : j.val ≠ k := fun h => hne_j (Fin.ext h)
            omega
          have hlt := (hneg j hjk hj0 hj1).1
          refine ⟨by simp; omega, fun l => ?_⟩
          exact (W_append_old gs extra (prefixInput n l) (negTap j) (by rw [prefixInput_len]; omega)).trans
            ((hneg j hjk hj0 hj1).2 l)
  obtain ⟨gs, tap, negTap, hF, hR, hnn, hnc, htap, hneg⟩ := haux d (le_refl d)
  have huniv : Finset.univ.filter (fun j : Fin d => j.val < d) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [huniv] at hnn hnc
  have hsum_nn : ∑ j : Fin d, ((colorClass color j).card - 1) = n - d := by
    have hge1 : ∀ j : Fin d, 1 ≤ (colorClass color j).card := fun j =>
      Finset.card_pos.2 (colorClass_nonempty color hsurj j)
    have hadd : (∑ j : Fin d, ((colorClass color j).card - 1)) + d =
        ∑ j : Fin d, (colorClass color j).card := by
      have : (∑ j : Fin d, ((colorClass color j).card - 1)) + ∑ _j : Fin d, 1 =
          ∑ j : Fin d, ((colorClass color j).card - 1 + 1) := by rw [← Finset.sum_add_distrib]
      have h1 : ∑ _j : Fin d, (1 : ℕ) = d := by simp
      rw [h1] at this
      rw [this]
      exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hge1 j)
    rw [sum_card_colorClass color] at hadd
    omega
  exact ⟨gs, tap, negTap, hF, hR, hnn.trans hsum_nn, hnc,
    fun j => htap j j.isLt, fun j hj0 hj1 => hneg j j.isLt hj0 hj1⟩

theorem log_to_physical {n d a : ℕ} (hd : 0 < d) (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (M : Fin (a + 1) → Finset (Fin d)) (phase : Fin (a + 1) → Bool) (b_log : ℕ)
    (hLog : LogFit d (Finset.univ.image X) (X 0) (X (Fin.last n)) a M phase b_log) :
    ∃ (C : Circuit) (tap : Fin d → ℕ) (out : Fin (a + 1) → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ j, tap j < n + 2 + C.size) ∧ (∀ t, out t < n + 2 + C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n - 1 ∧
      PEqualNP.NotBracket.notCount C ≤ b_log + walkFalls X ∧
      ∀ l, let w := C.wires (prefixInput n l)
           (∀ j, w.getD (tap j) false = decide (j ∈ X l)) ∧
           ∀ t, w.getD (out t) false = Bool.xor (phase t) (decide ((X l ∩ M t).card % 2 = 1)) := by
  obtain ⟨D, dout, hFD, hRD, hAllD, hOutD, hnnD, hncD, hEvalD⟩ := hLog
  obtain ⟨gs, tap, negTap, hFg, hRg, hnng, hncg, htap, hneg⟩ := build_walk_taps color X hsurj hX
  let φ : ℕ → ℕ := fun w =>
    if h1 : w < d then tap ⟨w, h1⟩
    else if h2 : w < 2 * d then negTap ⟨w - d, by omega⟩
    else if w = 2 * d then n
    else if w = 2 * d + 1 then n + 1
    else n + 2 + gs.length + (w - (2 * d + 2))
  let hs := D.gates.map (remapGate φ)
  have hφ_lt : ∀ k (w : ℕ), w < 2 * d + 2 + k → AllowedIn d (X 0) (X (Fin.last n)) w →
      φ w < n + 2 + gs.length + k := by
    intro k w hw hall
    simp only [φ]
    split_ifs with h1 h2 h3 h4
    · have := (htap ⟨w, h1⟩).1; omega
    · rcases hall with ha | ⟨j, hj, hb3, hb4⟩ | hc
      · omega
      · have hj_eq : (⟨w - d, by omega⟩ : Fin d) = j := Fin.ext (by change w - d = j.val; rw [hj]; exact Nat.add_sub_cancel_left d j.val)
        rw [hj_eq]
        have := (hneg j hb3 hb4).1; omega
      · omega
    · omega
    · omega
    · omega
  have hF_all : PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ hs, 0⟩ := by
    apply fanInTwo_append hFg
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have h0 := hFD g0 hg0
    simpa [remapGate] using h0
  have hR_all : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs ++ hs, 0⟩ := by
    apply readsBack_of_append hRg
    intro k hk u hu
    have hkD : k < D.gates.length := by simpa [hs] using hk
    have hget : hs.getD k ⟨GateOp.or, []⟩ = remapGate φ (D.gates.getD k ⟨GateOp.or, []⟩) := by
      rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hkD]
      simp [hs]
    rw [hget] at hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    have hrb : w < 2 * d + 2 + k := hRD k hkD w hw
    have hmem : D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates := by
      rw [List.getD_eq_getElem _ _ hkD]; exact List.getElem_mem _
    have hall := hAllD _ hmem w hw
    exact hφ_lt k w hrb hall
  have hEval_map : ∀ (ds : List Gate),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * d + 2) ⟨ds, 0⟩ →
      (∀ g ∈ ds, ∀ i ∈ g.inputs, AllowedIn d (X 0) (X (Fin.last n)) i) →
      ∀ l (w : ℕ), w < 2 * d + 2 + ds.length → AllowedIn d (X 0) (X (Fin.last n)) w →
      (W (gs ++ ds.map (remapGate φ)) (prefixInput n l)).getD (φ w) false =
        (W ds (logInput d (X l))).getD w false := by
    intro ds
    induction ds using List.reverseRecOn with
    | nil =>
      intro _ _ l w hw hall
      simp only [List.map_nil, List.append_nil, W_nil, List.length_nil, Nat.add_zero] at hw ⊢
      simp only [φ]
      split_ifs with h1 h2 h3 h4
      · exact ((htap ⟨w, h1⟩).2 l).trans (logInput_pos d (X l) ⟨w, h1⟩).symm
      · rcases hall with ha | ⟨j, hj, hb3, hb4⟩ | hc
        · omega
        · have hj_eq : (⟨w - d, by omega⟩ : Fin d) = j := Fin.ext (by change w - d = j.val; rw [hj]; exact Nat.add_sub_cancel_left d j.val)
          rw [hj_eq, hj]
          exact ((hneg j hb3 hb4).2 l).trans (logInput_neg d (X l) j).symm
        · omega
      · subst h3
        have h0 := W_append_old [] gs (prefixInput n l) n (by rw [prefixInput_len]; simp)
        exact (h0.trans (prefixInput_n n l)).trans (logInput_false d (X l)).symm
      · subst h4
        have h0 := W_append_old [] gs (prefixInput n l) (n + 1) (by rw [prefixInput_len]; simp)
        exact (h0.trans (prefixInput_n1 n l)).trans (logInput_true d (X l)).symm
      · omega
    | append_singleton ds g ih =>
      intro hRds hAllds l w hw hall
      have hR' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * d + 2) ⟨ds, 0⟩ := by
        intro j hj i hi
        have hj' : j < ds.length := hj
        have hlt : j < (ds ++ [g]).length := by simp only [List.length_append, List.length_singleton]; omega
        have hget : (ds ++ [g]).getD j ⟨GateOp.or, []⟩ = ds.getD j ⟨GateOp.or, []⟩ :=
          List.getD_append _ _ _ _ hj'
        exact hRds j hlt i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rw [hget]; exact hi)
      have hAll' : ∀ g' ∈ ds, ∀ i ∈ g'.inputs, AllowedIn d (X 0) (X (Fin.last n)) i :=
        fun g' hg' => hAllds g' (by simp [hg'])
      have hEq : gs ++ (ds ++ [g]).map (remapGate φ) = (gs ++ ds.map (remapGate φ)) ++ [remapGate φ g] := by
        simp [List.append_assoc]
      rw [hEq]
      simp only [List.length_append, List.length_singleton] at hw
      have hw' : w < 2 * d + 2 + ds.length ∨ w = 2 * d + 2 + ds.length := by omega
      rcases hw' with hlt | rfl
      · have hφne : φ w ≠ n + 2 + (gs ++ ds.map (remapGate φ)).length := by
          have := hφ_lt ds.length w hlt hall
          simp only [List.length_append, List.length_map]; omega
        rw [old_wire _ _ _ _ (by rw [prefixInput_len]; exact hφne),
          old_wire _ _ _ _ (by rw [logInput_len]; omega)]
        exact ih hR' hAll' l w hlt hall
      · have hφeq : φ (2 * d + 2 + ds.length) = n + 2 + (gs ++ ds.map (remapGate φ)).length := by
          simp only [φ, List.length_append, List.length_map]
          split_ifs <;> omega
        rw [hφeq]
        have hnw1 := new_wire (gs ++ ds.map (remapGate φ)) (remapGate φ g) (prefixInput n l)
        have hnw2 := new_wire ds g (logInput d (X l))
        rw [prefixInput_len] at hnw1
        rw [logInput_len] at hnw2
        rw [hnw1, hnw2]
        simp only [remapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hrb_i : i < 2 * d + 2 + ds.length := by
          have hget : (ds ++ [g]).getD ds.length ⟨GateOp.or, []⟩ = g := by
            rw [List.getD_eq_getElem _ _ (by simp)]; simp
          exact hRds ds.length (by simp) i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rw [hget]; exact hi)
        have hall_i := hAllds g (by simp) i hi
        exact ih hR' hAll' l i hrb_i hall_i
  have hn_pos : 0 < n := by
    obtain ⟨i, _⟩ := hsurj ⟨0, hd⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn_ge_d : d ≤ n := by
    rw [← sum_card_colorClass color]
    calc d = ∑ _j : Fin d, 1 := by simp
      _ ≤ ∑ j : Fin d, (colorClass color j).card :=
          Finset.sum_le_sum fun j _ => Finset.card_pos.2 (colorClass_nonempty color hsurj j)
  refine ⟨⟨gs ++ hs, 0⟩, tap, fun t => φ (dout t), hF_all, hR_all, by simp,
    fun j => by simp only [Circuit.size, List.length_append]; have := (htap j).1; omega,
    fun t => by
      simp only [Circuit.size, List.length_append, hs, List.length_map]
      have := hφ_lt D.gates.length (dout t) (hOutD t).1 (hOutD t).2
      omega,
    ?_, ?_, ?_⟩
  · have hsp := notCount_add_nonNotCount ⟨gs ++ hs, 0⟩
    have hnn_all : nonNotCount (gs ++ hs) ≤ n - 1 := by
      rw [nonNotCount_append, hnng, nonNotCount_remap]; omega
    simp only [Circuit.size] at hsp ⊢
    omega
  · rw [notCount_append, hncg, notCount_remap]
    change walkFalls X + PEqualNP.NotBracket.notCount ⟨D.gates, 0⟩ ≤ b_log + walkFalls X
    have hD0 : PEqualNP.NotBracket.notCount ⟨D.gates, 0⟩ = PEqualNP.NotBracket.notCount D := by
      rw [notCount_eq_filter, notCount_eq_filter]
    omega
  · intro l
    refine ⟨fun j => ?_, fun t => ?_⟩
    · have h1 := W_append_old gs hs (prefixInput n l) (tap j) (by rw [prefixInput_len]; exact (htap j).1)
      exact h1.trans ((htap j).2 l)
    · have h1 := hEval_map D.gates hRD hAllD l (dout t) (hOutD t).1 (hOutD t).2
      exact h1.trans (hEvalD (X l) (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩) t)

theorem physical_to_log {n d a : ℕ} (hd : 0 < d) (color : Fin n → Fin d)
    (X : Fin (n + 1) → Finset (Fin d))
    (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (M : Fin (a + 1) → Finset (Fin d)) (phase : Fin (a + 1) → Bool) (b : ℕ)
    (hM0 : M 0 = Finset.univ)
    (hFit : ∃ (C : Circuit) (tap : Fin d → ℕ) (out : Fin (a + 1) → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ j, tap j < n + 2 + C.size) ∧ (∀ t, out t < n + 2 + C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n - 1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ l, let w := C.wires (prefixInput n l)
           (∀ j, w.getD (tap j) false = decide (j ∈ X l)) ∧
           ∀ t, w.getD (out t) false = Bool.xor (phase t) (decide ((X l ∩ M t).card % 2 = 1))) :
    walkFalls X ≤ b ∧
    LogFit d (Finset.univ.image X) (X 0) (X (Fin.last n)) a M phase (b - walkFalls X) := by
  classical
  obtain ⟨C, tap, out, hF, hR, -, htap_lt, hout_lt, hP, hQ, hval⟩ := hFit
  have hn_pos : 0 < n := by
    obtain ⟨i, _⟩ := hsurj ⟨0, hd⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

  have hout0_chg : chg (vl n C.gates (out 0)) = Finset.univ := by
    ext i
    simp only [mem_chg, Finset.mem_univ, iff_true]
    have h1 := (hval i.castSucc).2 0
    have h2 := (hval i.succ).2 0
    change vl n C.gates (out 0) i.castSucc = _ at h1
    change vl n C.gates (out 0) i.succ = _ at h2
    rw [h1, h2, hM0, Finset.inter_univ, Finset.inter_univ]
    have hstep : X i.succ = insert (color i) (X i.castSucc) ∨ X i.castSucc = insert (color i) (X i.succ) := by
      by_cases hm : color i ∈ X i.castSucc
      · right
        have hnot : color i ∉ X i.succ := by
          have := (hX i (color i)).2 rfl; simp [hm] at this; exact this
        ext j
        by_cases hj : j = color i
        · subst hj; simp [hm]
        · have heq : decide (j ∈ X i.castSucc) = decide (j ∈ X i.succ) := by
            by_contra hne; exact hj ((hX i j).1 hne).symm
          simp only [Finset.mem_insert, hj, false_or]
          exact decide_eq_decide.1 heq
      · left
        have hmem : color i ∈ X i.succ := by
          have := (hX i (color i)).2 rfl; simp [hm] at this; exact this
        ext j
        by_cases hj : j = color i
        · subst hj; simp [hmem]
        · have heq : decide (j ∈ X i.castSucc) = decide (j ∈ X i.succ) := by
            by_contra hne; exact hj ((hX i j).1 hne).symm
          simp only [Finset.mem_insert, hj, false_or]
          exact (decide_eq_decide.1 heq).symm
    have hpar : (X i.castSucc).card % 2 ≠ (X i.succ).card % 2 := by
      rcases hstep with hs | hs
      · have hnot : color i ∉ X i.castSucc := by
          have := (hX i (color i)).2 rfl
          by_contra hm; rw [hs] at this; simp [hm] at this
        rw [hs, Finset.card_insert_of_notMem hnot]; omega
      · have hnot : color i ∉ X i.succ := by
          have := (hX i (color i)).2 rfl
          by_contra hm; rw [hs] at this; simp [hm] at this
        rw [hs, Finset.card_insert_of_notMem hnot]; omega
    cases hp : phase 0 with
    | false =>
      intro heq; apply hpar
      have heq' : decide ((X i.castSucc).card % 2 = 1) = decide ((X i.succ).card % 2 = 1) := by
        simpa [hp] using heq
      have := decide_eq_decide.1 heq'; omega
    | true =>
      intro heq; apply hpar
      have heq' : (!decide ((X i.castSucc).card % 2 = 1)) = (!decide ((X i.succ).card % 2 = 1)) := by
        simpa [hp] using heq
      have := decide_eq_decide.1 (Bool.not_inj heq'); omega

  obtain ⟨hlam, hgood, -⟩ := tight_structure n hn_pos C (out 0) (hout_lt 0) hF hR hP hout0_chg
  have htap_chg : ∀ j : Fin d, chg (vl n C.gates (tap j)) = colorClass color j := fun j => by
    have : vl n C.gates (tap j) = coord X j := funext fun l => (hval l).1 j
    rw [this, chg_coord_eq_colorClass color X hX j]

  let isLocal (u : ℕ) : Prop := (chg (vl n C.gates u)).Nonempty ∧ ∃ j : Fin d, chg (vl n C.gates u) ⊆ colorClass color j

  let binIdx : Finset ℕ := (Finset.range C.gates.length).filter fun idx =>
    !isNotGate (C.gates.getD idx ⟨.or, []⟩)
  let notIdx : Finset ℕ := (Finset.range C.gates.length).filter fun idx =>
    isNotGate (C.gates.getD idx ⟨.or, []⟩)
  have hbin_card : binIdx.card = nonNotCount C.gates := by
    have haux : ∀ (gs : List Gate),
        ((Finset.range gs.length).filter fun idx => !isNotGate (gs.getD idx ⟨.or, []⟩)).card =
          nonNotCount gs := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => simp [nonNotCount]
      | append_singleton gs g ih =>
        rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
        have hget : ∀ idx < gs.length, (gs ++ [g]).getD idx ⟨.or, []⟩ = gs.getD idx ⟨.or, []⟩ := by
          intro idx hlt
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hlt,
            List.getElem_append_left hlt]
        have hfilt : (Finset.range gs.length).filter (fun idx => !isNotGate ((gs ++ [g]).getD idx ⟨.or, []⟩)) =
            (Finset.range gs.length).filter (fun idx => !isNotGate (gs.getD idx ⟨.or, []⟩)) := by
          apply Finset.filter_congr; intro idx hi; rw [hget idx (Finset.mem_range.1 hi)]
        have hlast : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        rw [hfilt, hlast, nonNotCount_append]
        have hnotmem : gs.length ∉ (Finset.range gs.length).filter (fun idx => !isNotGate (gs.getD idx ⟨.or, []⟩)) := by
          simp
        cases hb : isNotGate g
        · simp only [Bool.not_false, ↓reduceIte, Finset.card_insert_of_notMem hnotmem, ih]
          have h1 : nonNotCount [g] = 1 := by simp [nonNotCount, hb]
          omega
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih]
          have h1 : nonNotCount [g] = 0 := by simp [nonNotCount, hb]
          omega
    exact haux C.gates
  have hnot_card : notIdx.card = PEqualNP.NotBracket.notCount C := by
    have hsp := notCount_add_nonNotCount C
    have hunion : binIdx ∪ notIdx = Finset.range C.gates.length := by
      ext idx; simp only [binIdx, notIdx, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      cases isNotGate (C.gates.getD idx ⟨.or, []⟩) <;> simp
    have hdisj : Disjoint binIdx notIdx := by
      rw [Finset.disjoint_left]; intro idx h1 h2
      simp only [binIdx, notIdx, Finset.mem_filter] at h1 h2
      rw [h2.2] at h1; simp at h1
    have hsum := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_range, hbin_card] at hsum
    change notIdx.card = PEqualNP.NotBracket.notCount C
    simp only [Circuit.size] at hsp
    omega

  let binSub (S : Finset (Fin n)) : Finset ℕ :=
    binIdx.filter fun idx => (chg (vl n C.gates (n + 2 + idx))).Nonempty ∧ chg (vl n C.gates (n + 2 + idx)) ⊆ S
  let notSub (S : Finset (Fin n)) : Finset ℕ :=
    notIdx.filter fun idx => (chg (vl n C.gates (n + 2 + idx))).Nonempty ∧ chg (vl n C.gates (n + 2 + idx)) ⊆ S
  let notStrict (S : Finset (Fin n)) : Finset ℕ :=
    notIdx.filter fun idx => (chg (vl n C.gates (n + 2 + idx))).Nonempty ∧ chg (vl n C.gates (n + 2 + idx)) ⊂ S
  let notAt (S : Finset (Fin n)) : Finset ℕ :=
    notIdx.filter fun idx => chg (vl n C.gates (n + 2 + idx)) = S

  have hnot_gate_eq : ∀ idx < C.gates.length, idx ∈ notIdx →
      (chg (vl n C.gates (n + 2 + idx)) = ∅) ∨
      ∃ a < n + 2 + idx, ∀ l, vl n C.gates (n + 2 + idx) l = !vl n C.gates a l := by
    intro idx hlt hmem
    have hnot : (C.gates.getD idx ⟨.or, []⟩).op = GateOp.not :=
      (isNotGate_eq_true _).1 (Finset.mem_filter.1 hmem).2
    have hget : C.gates.getD idx ⟨.or, []⟩ = C.gates[idx] := List.getD_eq_getElem _ _ hlt
    rw [hget] at hnot
    have hval_idx : ∀ l, vl n C.gates (n + 2 + idx) l =
        (C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun i => vl n C.gates i l) := by
      intro l
      have hsplit : C.gates = C.gates.take idx ++ [C.gates[idx]] ++ C.gates.drop (idx + 1) := by
        simpa [List.append_assoc] using (List.take_append_getElem_append_drop idx C.gates hlt).symm
      have hlen_t : (C.gates.take idx).length = idx := List.length_take_of_le (by omega)
      have h1 : vl n C.gates (n + 2 + idx) l =
          (W (C.gates.take idx ++ [C.gates[idx]]) (prefixInput n l)).getD (n + 2 + idx) false := by
        unfold vl; conv_lhs => rw [hsplit]
        exact W_append_old _ _ _ _ (by rw [prefixInput_len]; simp [hlen_t]; omega)
      have h2 := new_wire (C.gates.take idx) C.gates[idx] (prefixInput n l)
      rw [prefixInput_len, hlen_t] at h2
      rw [h1, h2]
      congr 1; apply List.map_congr_left
      intro i hi
      have hrb : i < n + 2 + idx := hR idx hlt i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rw [hget]; exact hi)
      unfold vl; conv_rhs => rw [hsplit]
      rw [List.append_assoc]
      exact (W_append_old (C.gates.take idx) ([C.gates[idx]] ++ C.gates.drop (idx + 1))
        (prefixInput n l) i (by rw [prefixInput_len, hlen_t]; exact hrb)).symm
    cases hgi : (C.gates[idx]).inputs with
    | nil =>
      left; apply chg_const; intro t t'
      rw [hval_idx t, hval_idx t', hgi, hnot]; rfl
    | cons a rest =>
      right
      have ha : a < n + 2 + idx := hR idx hlt a (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rw [hget, hgi]; simp)
      refine ⟨a, ha, fun l => ?_⟩
      rw [hval_idx l, hgi, hnot]; simp [GateOp.eval]

  have hchg_input : ∀ u < n + 2, (chg (vl n C.gates u)).card ≤ 1 := by
    intro u hu
    by_cases hlt : u < n
    · have heq : chg (vl n C.gates u) = {⟨u, hlt⟩} := by
        ext i; rw [mem_chg, Finset.mem_singleton]
        have hv : ∀ l, vl n C.gates u l = decide (u < l.val) := fun l =>
          (W_append_old [] C.gates (prefixInput n l) u (by rw [prefixInput_len]; simp; omega)).trans
            (prefixInput_lt n l u hlt)
        rw [hv, hv]; simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
        constructor
        · intro h; by_contra hne
          by_cases h1 : u < i.val
          · have h2 : u < i.val + 1 := by omega
            simp [h1, h2] at h
          · have h2 : ¬(u < i.val + 1) := by omega
            simp [h1, h2] at h
        · rintro rfl; simp
      rw [heq]; simp
    · have hc : chg (vl n C.gates u) = ∅ := by
        apply chg_const; intro t t'
        have hv : ∀ l, vl n C.gates u l = (prefixInput n l).getD u false := fun l =>
          W_append_old [] C.gates (prefixInput n l) u (by rw [prefixInput_len]; simp; omega)
        rw [hv t, hv t']
        have : u = n ∨ u = n + 1 := by omega
        rcases this with rfl | rfl
        · rw [prefixInput_n, prefixInput_n]
        · rw [prefixInput_n1, prefixInput_n1]
      rw [hc]; simp

  have hbin_ge : ∀ k (S : Finset (Fin n)), S.card = k → S.Nonempty →
      (∃ u < n + 2 + C.gates.length, chg (vl n C.gates u) = S) →
      S.card - 1 ≤ (binSub S).card := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro S hcard hne hex
      by_cases hk1 : k ≤ 1
      · omega
      · let P : ℕ → Prop := fun u => u < n + 2 + C.gates.length ∧ chg (vl n C.gates u) = S
        let u0 := Nat.find hex
        have hu0 : u0 < n + 2 + C.gates.length ∧ chg (vl n C.gates u0) = S := Nat.find_spec hex
        have hu0_ge : n + 2 ≤ u0 := by
          by_contra hlt
          have := hchg_input u0 (by omega)
          rw [hu0.2] at this; omega
        have hgu0 := hgood u0 hu0_ge hu0.1
        rcases hgu0 with hc | ⟨a, ha, heq⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, _⟩
        · have : S = ∅ := hu0.2.symm.trans (chg_const hc)
          rw [this] at hne; exact absurd hne (by simp)
        · have hca : chg (vl n C.gates a) = S := (chg_congr heq).symm.trans hu0.2
          exact absurd ⟨lt_trans ha hu0.1, hca⟩ (Nat.find_min hex ha)
        · let idx0 := u0 - (n + 2)
          have hidx0_lt : idx0 < C.gates.length := by omega
          have hu0_eq : n + 2 + idx0 = u0 := by omega
          have hidx0_bin : idx0 ∈ binIdx := by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_range.2 hidx0_lt, ?_⟩
            by_contra hnot
            have hmem_not : idx0 ∈ notIdx := by
              rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidx0_lt, ?_⟩
              cases hb0 : isNotGate (C.gates.getD idx0 ⟨.or, []⟩)
              · rw [hb0] at hnot; simp at hnot
              · rfl
            rcases hnot_gate_eq idx0 hidx0_lt hmem_not with hce | ⟨a', ha', heq'⟩
            · rw [hu0_eq, hu0.2] at hce; rw [hce] at hne; exact absurd hne (by simp)
            · have hca' : chg (vl n C.gates a') = S := by
                rw [← hu0.2, ← hu0_eq]; exact (chg_congr (Or.inr heq')).symm
              exact absurd ⟨by omega, hca'⟩ (Nat.find_min hex (by omega))
          have hidx0_mem : idx0 ∈ binSub S :=
            Finset.mem_filter.2 ⟨hidx0_bin, hu0_eq.symm ▸ hu0.2.symm ▸ hne, by rw [hu0_eq, hu0.2]⟩
          have hSa : chg (vl n C.gates a) ⊂ S := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨by rw [← hu0.2, hun]; exact Finset.subset_union_left, fun he => ?_⟩
            have : chg (vl n C.gates b) ⊆ chg (vl n C.gates a) := by
              rw [he, ← hu0.2, hun]; exact Finset.subset_union_right
            obtain ⟨x, hx⟩ := hnb
            exact Finset.disjoint_left.1 hdj (this hx) hx
          have hSb : chg (vl n C.gates b) ⊂ S := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨by rw [← hu0.2, hun]; exact Finset.subset_union_right, fun he => ?_⟩
            have : chg (vl n C.gates a) ⊆ chg (vl n C.gates b) := by
              rw [he, ← hu0.2, hun]; exact Finset.subset_union_left
            obtain ⟨x, hx⟩ := hna
            exact Finset.disjoint_left.1 hdj hx (this hx)
          have hca_lt : (chg (vl n C.gates a)).card < k := hcard ▸ Finset.card_lt_card hSa
          have hcb_lt : (chg (vl n C.gates b)).card < k := hcard ▸ Finset.card_lt_card hSb
          have hba := ih _ hca_lt _ rfl hna ⟨a, lt_trans ha hu0.1, rfl⟩
          have hbb := ih _ hcb_lt _ rfl hnb ⟨b, lt_trans hb hu0.1, rfl⟩
          have hdisj_ab : Disjoint (binSub (chg (vl n C.gates a))) (binSub (chg (vl n C.gates b))) := by
            rw [Finset.disjoint_left]; intro x hx1 hx2
            have h1 := (Finset.mem_filter.1 hx1).2
            have h2 := (Finset.mem_filter.1 hx2).2
            obtain ⟨y, hy⟩ := h1.1
            exact Finset.disjoint_left.1 hdj (h1.2 hy) (h2.2 hy)
          have hsub_er : binSub (chg (vl n C.gates a)) ∪ binSub (chg (vl n C.gates b)) ⊆ (binSub S).erase idx0 := by
            intro x hx
            rw [Finset.mem_erase]
            have hne_x : x ≠ idx0 := by
              rintro rfl
              rcases Finset.mem_union.1 hx with h1 | h2
              · have hs := (Finset.mem_filter.1 h1).2.2
                rw [hu0_eq, hu0.2] at hs
                exact hSa.2 hs
              · have hs := (Finset.mem_filter.1 h2).2.2
                rw [hu0_eq, hu0.2] at hs
                exact hSb.2 hs
            refine ⟨hne_x, ?_⟩
            rcases Finset.mem_union.1 hx with h1 | h2
            · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2.1,
                Finset.Subset.trans (Finset.mem_filter.1 h1).2.2 hSa.1⟩
            · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1, (Finset.mem_filter.1 h2).2.1,
                Finset.Subset.trans (Finset.mem_filter.1 h2).2.2 hSb.1⟩
          have hcard_u : S.card = (chg (vl n C.gates a)).card + (chg (vl n C.gates b)).card := by
            rw [← hu0.2, hun, Finset.card_union_of_disjoint hdj]
          have hcard_er := Finset.card_le_card hsub_er
          rw [Finset.card_union_of_disjoint hdisj_ab, Finset.card_erase_of_mem hidx0_mem] at hcard_er
          have hpa := Finset.card_pos.2 hna
          have hpb := Finset.card_pos.2 hnb
          have hpos_b : 1 ≤ (binSub S).card := Finset.card_pos.2 ⟨idx0, hidx0_mem⟩
          omega

  let binLog : Finset ℕ := binIdx.filter fun idx =>
    ¬ ((chg (vl n C.gates (n + 2 + idx))).Nonempty ∧ ∃ j : Fin d, chg (vl n C.gates (n + 2 + idx)) ⊆ colorClass color j)
  have hbin_disj_j : ∀ j1 j2 : Fin d, j1 ≠ j2 →
      Disjoint (binSub (colorClass color j1)) (binSub (colorClass color j2)) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]; intro idx h1 h2
    obtain ⟨i, hi⟩ := (Finset.mem_filter.1 h1).2.1
    have hc1 := (Finset.mem_filter.1 ((Finset.mem_filter.1 h1).2.2 hi)).2
    have hc2 := (Finset.mem_filter.1 ((Finset.mem_filter.1 h2).2.2 hi)).2
    exact hne (hc1.symm.trans hc2)
  have hbin_disj_log : Disjoint binLog (Finset.univ.biUnion fun j : Fin d => binSub (colorClass color j)) := by
    rw [Finset.disjoint_left]; intro idx h1 h2
    rw [Finset.mem_biUnion] at h2
    obtain ⟨j, -, hj⟩ := h2
    exact (Finset.mem_filter.1 h1).2 ⟨(Finset.mem_filter.1 hj).2.1, j, (Finset.mem_filter.1 hj).2.2⟩
  have hbin_sub_all : binLog ∪ (Finset.univ.biUnion fun j : Fin d => binSub (colorClass color j)) ⊆ binIdx := by
    intro idx hi
    rcases Finset.mem_union.1 hi with h1 | h2
    · exact (Finset.mem_filter.1 h1).1
    · rw [Finset.mem_biUnion] at h2
      obtain ⟨j, -, hj⟩ := h2
      exact (Finset.mem_filter.1 hj).1
  have hbin_sum_le : binLog.card + ∑ j : Fin d, (binSub (colorClass color j)).card ≤ n - 1 := by
    have h1 := Finset.card_le_card hbin_sub_all
    rw [Finset.card_union_of_disjoint hbin_disj_log,
      Finset.card_biUnion (fun j1 _ j2 _ hne => hbin_disj_j j1 j2 hne), hbin_card] at h1
    have hsp := notCount_add_nonNotCount C
    omega
  have hbin_each_ge : ∀ j : Fin d, (colorClass color j).card - 1 ≤ (binSub (colorClass color j)).card :=
    fun j => hbin_ge _ _ rfl (colorClass_nonempty color hsurj j) ⟨tap j, htap_lt j, htap_chg j⟩
  have hsum_color_sub : ∑ j : Fin d, ((colorClass color j).card - 1) = n - d := by
    have hge1 : ∀ j : Fin d, 1 ≤ (colorClass color j).card := fun j =>
      Finset.card_pos.2 (colorClass_nonempty color hsurj j)
    have hadd : (∑ j : Fin d, ((colorClass color j).card - 1)) + d =
        ∑ j : Fin d, (colorClass color j).card := by
      have : (∑ j : Fin d, ((colorClass color j).card - 1)) + ∑ _j : Fin d, 1 =
          ∑ j : Fin d, ((colorClass color j).card - 1 + 1) := by rw [← Finset.sum_add_distrib]
      have h1 : ∑ _j : Fin d, (1 : ℕ) = d := by simp
      rw [h1] at this; rw [this]
      exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hge1 j)
    rw [sum_card_colorClass color] at hadd; omega
  have hbinLog_le : binLog.card ≤ d - 1 := by
    have hsum_ge : n - d ≤ ∑ j : Fin d, (binSub (colorClass color j)).card := by
      rw [← hsum_color_sub]
      exact Finset.sum_le_sum fun j _ => hbin_each_ge j
    have hn_ge_d : d ≤ n := by
      rw [← sum_card_colorClass color]
      calc d = ∑ _j : Fin d, 1 := by simp
        _ ≤ ∑ j : Fin d, (colorClass color j).card :=
            Finset.sum_le_sum fun j _ => Finset.card_pos.2 (colorClass_nonempty color hsurj j)
    omega

  have hlog_union : ∀ u < n + 2 + C.gates.length,
      (∀ j : Fin d, ¬ chg (vl n C.gates u) ⊆ colorClass color j) →
      ∀ j : Fin d, (chg (vl n C.gates u) ∩ colorClass color j).Nonempty →
        colorClass color j ⊆ chg (vl n C.gates u) := by
    intro u hu hnot j hne_int
    rcases hlam u hu (tap j) (htap_lt j) with h1 | h2 | h3
    · rw [htap_chg j] at h1; exact absurd h1 (hnot j)
    · rw [htap_chg j] at h2; exact h2
    · rw [htap_chg j] at h3
      obtain ⟨i, hi⟩ := hne_int
      exact absurd (Finset.mem_inter.1 hi).2 (Finset.disjoint_left.1 h3 (Finset.mem_inter.1 hi).1)

  have hlog_child : ∀ u < n + 2 + C.gates.length,
      (∀ j : Fin d, ¬ chg (vl n C.gates u) ⊆ colorClass color j) →
      ∀ a < n + 2 + C.gates.length, ∀ b < n + 2 + C.gates.length,
      (chg (vl n C.gates a)).Nonempty → (chg (vl n C.gates b)).Nonempty →
      Disjoint (chg (vl n C.gates a)) (chg (vl n C.gates b)) →
      chg (vl n C.gates u) = chg (vl n C.gates a) ∪ chg (vl n C.gates b) →
      ∀ j : Fin d, chg (vl n C.gates a) ⊆ colorClass color j → chg (vl n C.gates a) = colorClass color j := by
    intro u hu hnot a ha b hb hna hnb hdj hun j hsub
    have hint : (chg (vl n C.gates u) ∩ colorClass color j).Nonempty := by
      obtain ⟨i, hi⟩ := hna
      exact ⟨i, Finset.mem_inter.2 ⟨by rw [hun]; exact Finset.mem_union_left _ hi, hsub hi⟩⟩
    have hcj_sub : colorClass color j ⊆ chg (vl n C.gates u) := hlog_union u hu hnot j hint
    by_contra hne
    have hss : chg (vl n C.gates a) ⊂ colorClass color j :=
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩
    obtain ⟨i, hi_c, hi_na⟩ := Finset.exists_of_ssubset hss
    have hi_u : i ∈ chg (vl n C.gates u) := hcj_sub hi_c
    rw [hun, Finset.mem_union] at hi_u
    have hi_b : i ∈ chg (vl n C.gates b) := hi_u.resolve_left hi_na

    rcases hlam b hb (tap j) (htap_lt j) with h1 | h2 | h3
    · rw [htap_chg j] at h1
      exact hnot j (by rw [hun]; exact Finset.union_subset hsub h1)
    · rw [htap_chg j] at h2
      obtain ⟨i0, hi0⟩ := hna
      exact Finset.disjoint_left.1 hdj hi0 (h2 (hsub hi0))
    · rw [htap_chg j] at h3
      exact Finset.disjoint_left.1 h3 hi_b hi_c

  let binLogNe : Finset ℕ := binLog.filter fun idx => (chg (vl n C.gates (n + 2 + idx))).Nonempty
  have hbinLog_ge : ∀ k (J : Finset (Fin d)), J.card = k → J.Nonempty →
      (∃ u < n + 2 + C.gates.length, chg (vl n C.gates u) = J.biUnion (colorClass color)) →
      J.card - 1 ≤ (binLogNe.filter fun idx => chg (vl n C.gates (n + 2 + idx)) ⊆ J.biUnion (colorClass color)).card := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro J hcard hne hex
      by_cases hk1 : k ≤ 1
      · omega
      · let S := J.biUnion (colorClass color)
        have hS_ne : S.Nonempty := by
          obtain ⟨j, hj⟩ := hne
          obtain ⟨i, hi⟩ := colorClass_nonempty color hsurj j
          exact ⟨i, Finset.mem_biUnion.2 ⟨j, hj, hi⟩⟩
        have hS_not_single : ∀ j : Fin d, ¬ S ⊆ colorClass color j := by
          intro j hsub
          obtain ⟨j1, hj1, j2, hj2, hne12⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
          have h1 : j1 = j := by
            obtain ⟨i, hi⟩ := colorClass_nonempty color hsurj j1
            have hi' := hsub (Finset.mem_biUnion.2 ⟨j1, hj1, hi⟩)
            exact ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hi').2)
          have h2 : j2 = j := by
            obtain ⟨i, hi⟩ := colorClass_nonempty color hsurj j2
            have hi' := hsub (Finset.mem_biUnion.2 ⟨j2, hj2, hi⟩)
            exact ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hi').2)
          exact hne12 (h1.trans h2.symm)
        let u0 := Nat.find hex
        have hu0 : u0 < n + 2 + C.gates.length ∧ chg (vl n C.gates u0) = S := Nat.find_spec hex
        have hu0_ge : n + 2 ≤ u0 := by
          by_contra hlt
          have h1 := hchg_input u0 (by omega)
          rw [hu0.2] at h1
          obtain ⟨j1, hj1, j2, hj2, hne12⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
          obtain ⟨i1, hi1⟩ := colorClass_nonempty color hsurj j1
          obtain ⟨i2, hi2⟩ := colorClass_nonempty color hsurj j2
          have hne_i : i1 ≠ i2 := fun h => hne12 ((Finset.mem_filter.1 hi1).2.symm.trans
            (h ▸ (Finset.mem_filter.1 hi2).2))
          have h2 : 2 ≤ S.card := Finset.one_lt_card.2 ⟨i1, Finset.mem_biUnion.2 ⟨j1, hj1, hi1⟩,
            i2, Finset.mem_biUnion.2 ⟨j2, hj2, hi2⟩, hne_i⟩
          omega
        rcases hgood u0 hu0_ge hu0.1 with hc | ⟨a, ha, heq⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, _⟩
        · have : S = ∅ := hu0.2.symm.trans (chg_const hc)
          rw [this] at hS_ne; exact absurd hS_ne (by simp)
        · exact absurd ⟨lt_trans ha hu0.1, (chg_congr heq).symm.trans hu0.2⟩ (Nat.find_min hex ha)
        · let idx0 := u0 - (n + 2)
          have hidx0_lt : idx0 < C.gates.length := by omega
          have hu0_eq : n + 2 + idx0 = u0 := by omega
          have hidx0_bin : idx0 ∈ binIdx := by
            rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidx0_lt, ?_⟩
            by_contra hnot
            have hmem_not : idx0 ∈ notIdx := by
              rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidx0_lt, ?_⟩
              cases hb0 : isNotGate (C.gates.getD idx0 ⟨.or, []⟩)
              · rw [hb0] at hnot; simp at hnot
              · rfl
            rcases hnot_gate_eq idx0 hidx0_lt hmem_not with hce | ⟨a', ha', heq'⟩
            · rw [hu0_eq, hu0.2] at hce; rw [hce] at hS_ne; exact absurd hS_ne (by simp)
            · have hca' : chg (vl n C.gates a') = S := by
                rw [← hu0.2, ← hu0_eq]; exact (chg_congr (Or.inr heq')).symm
              exact absurd ⟨by omega, hca'⟩ (Nat.find_min hex (by omega))
          have hidx0_log : idx0 ∈ binLogNe :=
            Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hidx0_bin, fun ⟨_, j, hj⟩ =>
              hS_not_single j (hu0.2 ▸ hu0_eq ▸ hj)⟩, hu0_eq.symm ▸ hu0.2.symm ▸ hS_ne⟩
          let Ja : Finset (Fin d) := J.filter fun j => (chg (vl n C.gates a) ∩ colorClass color j).Nonempty
          let Jb : Finset (Fin d) := J.filter fun j => (chg (vl n C.gates b) ∩ colorClass color j).Nonempty
          have hJa_eq : chg (vl n C.gates a) = Ja.biUnion (colorClass color) := by
            ext i; simp only [Finset.mem_biUnion, Ja, Finset.mem_filter]
            constructor
            · intro hi
              have hiS : i ∈ S := hu0.2 ▸ hun ▸ Finset.mem_union_left _ hi
              obtain ⟨j, hjJ, hij⟩ := Finset.mem_biUnion.1 hiS
              exact ⟨j, ⟨hjJ, i, Finset.mem_inter.2 ⟨hi, hij⟩⟩, hij⟩
            · rintro ⟨j, ⟨_, hi_int⟩, hij⟩
              by_cases hsub : chg (vl n C.gates a) ⊆ colorClass color j
              · rw [hlog_child u0 hu0.1 (hu0.2.symm ▸ hS_not_single) a (lt_trans ha hu0.1)
                  b (lt_trans hb hu0.1) hna hnb hdj hun j hsub]
                exact hij
              · by_cases hsome : ∃ j', chg (vl n C.gates a) ⊆ colorClass color j'
                · obtain ⟨j', hj'⟩ := hsome
                  obtain ⟨i0, hi0⟩ := hi_int
                  have hc1 := (Finset.mem_filter.1 (hj' (Finset.mem_inter.1 hi0).1)).2
                  have hc2 := (Finset.mem_filter.1 (Finset.mem_inter.1 hi0).2).2
                  exact absurd (hc1.symm.trans hc2 ▸ hj') hsub
                · exact hlog_union a (lt_trans ha hu0.1) (fun j' h' => hsome ⟨j', h'⟩) j hi_int hij
          have hJb_eq : chg (vl n C.gates b) = Jb.biUnion (colorClass color) := by
            ext i; simp only [Finset.mem_biUnion, Jb, Finset.mem_filter]
            constructor
            · intro hi
              have hiS : i ∈ S := hu0.2 ▸ hun ▸ Finset.mem_union_right _ hi
              obtain ⟨j, hjJ, hij⟩ := Finset.mem_biUnion.1 hiS
              exact ⟨j, ⟨hjJ, i, Finset.mem_inter.2 ⟨hi, hij⟩⟩, hij⟩
            · rintro ⟨j, ⟨_, hi_int⟩, hij⟩
              by_cases hsub : chg (vl n C.gates b) ⊆ colorClass color j
              · rw [hlog_child u0 hu0.1 (hu0.2.symm ▸ hS_not_single) b (lt_trans hb hu0.1)
                  a (lt_trans ha hu0.1) hnb hna hdj.symm (hun.trans (Finset.union_comm _ _)) j hsub]
                exact hij
              · by_cases hsome : ∃ j', chg (vl n C.gates b) ⊆ colorClass color j'
                · obtain ⟨j', hj'⟩ := hsome
                  obtain ⟨i0, hi0⟩ := hi_int
                  have hc1 := (Finset.mem_filter.1 (hj' (Finset.mem_inter.1 hi0).1)).2
                  have hc2 := (Finset.mem_filter.1 (Finset.mem_inter.1 hi0).2).2
                  exact absurd (hc1.symm.trans hc2 ▸ hj') hsub
                · exact hlog_union b (lt_trans hb hu0.1) (fun j' h' => hsome ⟨j', h'⟩) j hi_int hij
          have hJa_ne : Ja.Nonempty := by
            obtain ⟨i, hi⟩ := hna; rw [hJa_eq] at hi
            obtain ⟨j, hj, _⟩ := Finset.mem_biUnion.1 hi; exact ⟨j, hj⟩
          have hJb_ne : Jb.Nonempty := by
            obtain ⟨i, hi⟩ := hnb; rw [hJb_eq] at hi
            obtain ⟨j, hj, _⟩ := Finset.mem_biUnion.1 hi; exact ⟨j, hj⟩
          have hJ_disj : Disjoint Ja Jb := by
            rw [Finset.disjoint_left]; intro j hj1 hj2
            obtain ⟨i, hi⟩ := colorClass_nonempty color hsurj j
            exact Finset.disjoint_left.1 hdj
              (hJa_eq.symm ▸ Finset.mem_biUnion.2 ⟨j, hj1, hi⟩)
              (hJb_eq.symm ▸ Finset.mem_biUnion.2 ⟨j, hj2, hi⟩)
          have hJ_union : Ja ∪ Jb = J := by
            ext j; simp only [Finset.mem_union, Ja, Jb, Finset.mem_filter]
            constructor
            · rintro (h | h) <;> exact h.1
            · intro hjJ
              obtain ⟨i, hi⟩ := colorClass_nonempty color hsurj j
              have hiS : i ∈ S := Finset.mem_biUnion.2 ⟨j, hjJ, hi⟩
              rw [← hu0.2, hun, Finset.mem_union] at hiS
              rcases hiS with hia | hib
              · exact Or.inl ⟨hjJ, i, Finset.mem_inter.2 ⟨hia, hi⟩⟩
              · exact Or.inr ⟨hjJ, i, Finset.mem_inter.2 ⟨hib, hi⟩⟩
          have hJ_card : J.card = Ja.card + Jb.card := by
            rw [← hJ_union, Finset.card_union_of_disjoint hJ_disj]
          have hpa := Finset.card_pos.2 hJa_ne
          have hpb := Finset.card_pos.2 hJb_ne
          have ha_ih := ih Ja.card (by omega) Ja rfl hJa_ne ⟨a, lt_trans ha hu0.1, hJa_eq⟩
          have hb_ih := ih Jb.card (by omega) Jb rfl hJb_ne ⟨b, lt_trans hb hu0.1, hJb_eq⟩
          let Fa := binLogNe.filter fun idx => chg (vl n C.gates (n + 2 + idx)) ⊆ Ja.biUnion (colorClass color)
          let Fb := binLogNe.filter fun idx => chg (vl n C.gates (n + 2 + idx)) ⊆ Jb.biUnion (colorClass color)
          let Fset := binLogNe.filter fun idx => chg (vl n C.gates (n + 2 + idx)) ⊆ S
          have hF_disj : Disjoint Fa Fb := by
            rw [Finset.disjoint_left]; intro idx h1 h2
            have hne_idx : (chg (vl n C.gates (n + 2 + idx))).Nonempty :=
              (Finset.mem_filter.1 (Finset.mem_filter.1 h1).1).2
            obtain ⟨i, hi⟩ := hne_idx
            exact Finset.disjoint_left.1 hdj
              (hJa_eq ▸ (Finset.mem_filter.1 h1).2 hi)
              (hJb_eq ▸ (Finset.mem_filter.1 h2).2 hi)
          have hidx0_Fset : idx0 ∈ Fset := Finset.mem_filter.2 ⟨hidx0_log, by rw [hu0_eq, hu0.2]⟩
          have hF_sub : Fa ∪ Fb ⊆ Fset.erase idx0 := by
            intro idx hi
            rw [Finset.mem_erase]
            have hne0 : idx ≠ idx0 := by
              rintro rfl
              rcases Finset.mem_union.1 hi with h1 | h2
              · have hs := (Finset.mem_filter.1 h1).2
                rw [hu0_eq, hu0.2, ← hJa_eq] at hs
                obtain ⟨i, hi'⟩ := hnb
                exact Finset.disjoint_left.1 hdj (hs (hu0.2 ▸ hun ▸ Finset.mem_union_right _ hi')) hi'
              · have hs := (Finset.mem_filter.1 h2).2
                rw [hu0_eq, hu0.2, ← hJb_eq] at hs
                obtain ⟨i, hi'⟩ := hna
                exact Finset.disjoint_left.1 hdj hi' (hs (hu0.2 ▸ hun ▸ Finset.mem_union_left _ hi'))
            refine ⟨hne0, ?_⟩
            rcases Finset.mem_union.1 hi with h1 | h2
            · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1,
                Finset.Subset.trans (Finset.mem_filter.1 h1).2 (by rw [← hJa_eq, ← hu0.2, hun]; exact Finset.subset_union_left)⟩
            · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1,
                Finset.Subset.trans (Finset.mem_filter.1 h2).2 (by rw [← hJb_eq, ← hu0.2, hun]; exact Finset.subset_union_right)⟩
          have hle_F := Finset.card_le_card hF_sub
          rw [Finset.card_union_of_disjoint hF_disj, Finset.card_erase_of_mem hidx0_Fset] at hle_F
          have hpos_F : 1 ≤ Fset.card := Finset.card_pos.2 ⟨idx0, hidx0_Fset⟩
          change Ja.card - 1 ≤ Fa.card at ha_ih
          change Jb.card - 1 ≤ Fb.card at hb_ih
          change J.card - 1 ≤ Fset.card
          omega

  have hbinLog_ge_d : d - 1 ≤ binLog.card := by
    have huniv_eq : (Finset.univ : Finset (Fin d)).biUnion (colorClass color) = Finset.univ := by
      ext i; simp [colorClass]
    have h1 := hbinLog_ge d Finset.univ (by simp) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
      ⟨out 0, hout_lt 0, hout0_chg.trans huniv_eq.symm⟩
    have hsub : (binLogNe.filter fun idx => chg (vl n C.gates (n + 2 + idx)) ⊆ Finset.univ.biUnion (colorClass color)) ⊆ binLog :=
      fun idx hi => (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
    have h2 := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega

  have hbin_each_eq : ∀ j : Fin d, (binSub (colorClass color j)).card = (colorClass color j).card - 1 := by
    intro j
    by_contra hne
    have hgt : (colorClass color j).card - 1 < (binSub (colorClass color j)).card :=
      lt_of_le_of_ne (hbin_each_ge j) (Ne.symm hne)
    have hsum_gt : ∑ x : Fin d, ((colorClass color x).card - 1) <
        ∑ x : Fin d, (binSub (colorClass color x)).card :=
      Finset.sum_lt_sum (fun x _ => hbin_each_ge x) ⟨j, Finset.mem_univ _, hgt⟩
    rw [hsum_color_sub] at hsum_gt
    have hn_ge_d : d ≤ n := by
      rw [← sum_card_colorClass color]
      calc d = ∑ _j : Fin d, 1 := by simp
        _ ≤ ∑ j : Fin d, (colorClass color j).card :=
            Finset.sum_le_sum fun j _ => Finset.card_pos.2 (colorClass_nonempty color hsurj j)
    omega

  have hbin_strict : ∀ k (S : Finset (Fin n)), S.card = k → S.Nonempty →
      (∃ u < n + 2 + C.gates.length, chg (vl n C.gates u) = S) →
      (∃ idx ∈ binSub S, ∃ u < n + 2 + idx, chg (vl n C.gates u) = chg (vl n C.gates (n + 2 + idx))) →
      S.card ≤ (binSub S).card := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro S hcard hne hex ⟨idx_dup, hdup_mem, u_prev, hu_prev_lt, hdup_chg⟩
      by_cases hk1 : k ≤ 1
      · have hpos : 1 ≤ (binSub S).card := Finset.card_pos.2 ⟨idx_dup, hdup_mem⟩
        omega
      · let u0 := Nat.find hex
        have hu0 : u0 < n + 2 + C.gates.length ∧ chg (vl n C.gates u0) = S := Nat.find_spec hex
        have hu0_ge : n + 2 ≤ u0 := by
          by_contra hlt; have := hchg_input u0 (by omega); rw [hu0.2] at this; omega
        rcases hgood u0 hu0_ge hu0.1 with hc | ⟨a, ha, heq⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, _⟩
        · have : S = ∅ := hu0.2.symm.trans (chg_const hc)
          rw [this] at hne; exact absurd hne (by simp)
        · exact absurd ⟨lt_trans ha hu0.1, (chg_congr heq).symm.trans hu0.2⟩ (Nat.find_min hex ha)
        · let idx0 := u0 - (n + 2)
          have hidx0_lt : idx0 < C.gates.length := by omega
          have hu0_eq : n + 2 + idx0 = u0 := by omega
          have hidx0_bin : idx0 ∈ binIdx := by
            rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidx0_lt, ?_⟩
            by_contra hnot
            have hmem_not : idx0 ∈ notIdx := by
              rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidx0_lt, ?_⟩
              cases hb0 : isNotGate (C.gates.getD idx0 ⟨.or, []⟩)
              · rw [hb0] at hnot; simp at hnot
              · rfl
            rcases hnot_gate_eq idx0 hidx0_lt hmem_not with hce | ⟨a', ha', heq'⟩
            · rw [hu0_eq, hu0.2] at hce; rw [hce] at hne; exact absurd hne (by simp)
            · have hca' : chg (vl n C.gates a') = S := by
                rw [← hu0.2, ← hu0_eq]; exact (chg_congr (Or.inr heq')).symm
              exact absurd ⟨by omega, hca'⟩ (Nat.find_min hex (by omega))
          have hidx0_mem : idx0 ∈ binSub S :=
            Finset.mem_filter.2 ⟨hidx0_bin, hu0_eq.symm ▸ hu0.2.symm ▸ hne, by rw [hu0_eq, hu0.2]⟩
          have hSa : chg (vl n C.gates a) ⊂ S := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨by rw [← hu0.2, hun]; exact Finset.subset_union_left, fun he => ?_⟩
            obtain ⟨x, hx⟩ := hnb
            exact Finset.disjoint_left.1 hdj (by rw [he, ← hu0.2, hun]; exact Finset.mem_union_right _ hx) hx
          have hSb : chg (vl n C.gates b) ⊂ S := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨by rw [← hu0.2, hun]; exact Finset.subset_union_right, fun he => ?_⟩
            obtain ⟨x, hx⟩ := hna
            exact Finset.disjoint_left.1 hdj hx (by rw [he, ← hu0.2, hun]; exact Finset.mem_union_left _ hx)
          have hdisj_ab : Disjoint (binSub (chg (vl n C.gates a))) (binSub (chg (vl n C.gates b))) := by
            rw [Finset.disjoint_left]; intro x hx1 hx2
            obtain ⟨y, hy⟩ := (Finset.mem_filter.1 hx1).2.1
            exact Finset.disjoint_left.1 hdj ((Finset.mem_filter.1 hx1).2.2 hy) ((Finset.mem_filter.1 hx2).2.2 hy)
          have hcard_u : S.card = (chg (vl n C.gates a)).card + (chg (vl n C.gates b)).card := by
            rw [← hu0.2, hun, Finset.card_union_of_disjoint hdj]
          have hpa := Finset.card_pos.2 hna
          have hpb := Finset.card_pos.2 hnb
          by_cases hsame : chg (vl n C.gates (n + 2 + idx_dup)) = S
          ·
            have hne_dup : idx_dup ≠ idx0 := by
              rintro rfl
              have hlt' : u_prev < u0 := by omega
              exact Nat.find_min hex hlt' ⟨lt_trans hlt' hu0.1, hdup_chg.trans hsame⟩
            have hsub2 : binSub (chg (vl n C.gates a)) ∪ binSub (chg (vl n C.gates b)) ⊆
                ((binSub S).erase idx0).erase idx_dup := by
              intro x hx
              rw [Finset.mem_erase, Finset.mem_erase]
              have hne_d : x ≠ idx_dup := by
                rintro rfl
                rcases Finset.mem_union.1 hx with h1 | h2
                · exact hSa.2 (hsame ▸ (Finset.mem_filter.1 h1).2.2)
                · exact hSb.2 (hsame ▸ (Finset.mem_filter.1 h2).2.2)
              have hne_0 : x ≠ idx0 := by
                rintro rfl
                rcases Finset.mem_union.1 hx with h1 | h2
                · exact hSa.2 (hu0.2 ▸ hu0_eq ▸ (Finset.mem_filter.1 h1).2.2)
                · exact hSb.2 (hu0.2 ▸ hu0_eq ▸ (Finset.mem_filter.1 h2).2.2)
              refine ⟨hne_d, hne_0, ?_⟩
              rcases Finset.mem_union.1 hx with h1 | h2
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2.1,
                  Finset.Subset.trans (Finset.mem_filter.1 h1).2.2 hSa.1⟩
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1, (Finset.mem_filter.1 h2).2.1,
                  Finset.Subset.trans (Finset.mem_filter.1 h2).2.2 hSb.1⟩
            have hba := hbin_ge _ _ rfl hna ⟨a, lt_trans ha hu0.1, rfl⟩
            have hbb := hbin_ge _ _ rfl hnb ⟨b, lt_trans hb hu0.1, rfl⟩
            have hle2 := Finset.card_le_card hsub2
            rw [Finset.card_union_of_disjoint hdisj_ab,
              Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne_dup, hdup_mem⟩),
              Finset.card_erase_of_mem hidx0_mem] at hle2
            have hge2 : 2 ≤ (binSub S).card := Finset.one_lt_card.2 ⟨idx_dup, hdup_mem, idx0, hidx0_mem, hne_dup⟩
            omega
          ·
            have hdup_lt : n + 2 + idx_dup < n + 2 + C.gates.length := by
              have := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hdup_mem).1).1; omega
            have hdup_ne := (Finset.mem_filter.1 hdup_mem).2.1
            have hdup_sub := (Finset.mem_filter.1 hdup_mem).2.2
            have hsub_or : chg (vl n C.gates (n + 2 + idx_dup)) ⊆ chg (vl n C.gates a) ∨
                chg (vl n C.gates (n + 2 + idx_dup)) ⊆ chg (vl n C.gates b) := by
              rcases hlam (n + 2 + idx_dup) hdup_lt a (lt_trans ha hu0.1) with h1 | h2 | h3
              · exact Or.inl h1
              ·
                rcases hlam (n + 2 + idx_dup) hdup_lt b (lt_trans hb hu0.1) with hb1 | hb2 | hb3
                · exact Or.inr hb1
                · exfalso; apply hsame; apply Finset.Subset.antisymm hdup_sub
                  rw [← hu0.2, hun]; exact Finset.union_subset h2 hb2
                · left; intro x hx
                  have hxS := hdup_sub hx
                  rw [← hu0.2, hun, Finset.mem_union] at hxS
                  exact hxS.resolve_right (Finset.disjoint_left.1 hb3 hx)
              · right; intro x hx
                have hxS := hdup_sub hx
                rw [← hu0.2, hun, Finset.mem_union] at hxS
                exact hxS.resolve_left (Finset.disjoint_left.1 h3 hx)
            have hsub_er : binSub (chg (vl n C.gates a)) ∪ binSub (chg (vl n C.gates b)) ⊆ (binSub S).erase idx0 := by
              intro x hx; rw [Finset.mem_erase]
              have hne_0 : x ≠ idx0 := by
                rintro rfl
                rcases Finset.mem_union.1 hx with h1 | h2
                · exact hSa.2 (hu0.2 ▸ hu0_eq ▸ (Finset.mem_filter.1 h1).2.2)
                · exact hSb.2 (hu0.2 ▸ hu0_eq ▸ (Finset.mem_filter.1 h2).2.2)
              refine ⟨hne_0, ?_⟩
              rcases Finset.mem_union.1 hx with h1 | h2
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2.1,
                  Finset.Subset.trans (Finset.mem_filter.1 h1).2.2 hSa.1⟩
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1, (Finset.mem_filter.1 h2).2.1,
                  Finset.Subset.trans (Finset.mem_filter.1 h2).2.2 hSb.1⟩
            have hle_er := Finset.card_le_card hsub_er
            rw [Finset.card_union_of_disjoint hdisj_ab, Finset.card_erase_of_mem hidx0_mem] at hle_er
            have hpos_b : 1 ≤ (binSub S).card := Finset.card_pos.2 ⟨idx0, hidx0_mem⟩
            rcases hsub_or with hda | hdb
            · have hba := ih _ (hcard ▸ Finset.card_lt_card hSa) _ rfl hna ⟨a, lt_trans ha hu0.1, rfl⟩
                ⟨idx_dup, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hdup_mem).1, hdup_ne, hda⟩,
                  u_prev, hu_prev_lt, hdup_chg⟩
              have hbb := hbin_ge _ _ rfl hnb ⟨b, lt_trans hb hu0.1, rfl⟩
              omega
            · have hba := hbin_ge _ _ rfl hna ⟨a, lt_trans ha hu0.1, rfl⟩
              have hbb := ih _ (hcard ▸ Finset.card_lt_card hSb) _ rfl hnb ⟨b, lt_trans hb hu0.1, rfl⟩
                ⟨idx_dup, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hdup_mem).1, hdup_ne, hdb⟩,
                  u_prev, hu_prev_lt, hdup_chg⟩
              omega

  have hbin_unique_local : ∀ j : Fin d, ∀ idx ∈ binSub (colorClass color j),
      ∀ u < n + 2 + idx, chg (vl n C.gates u) ≠ chg (vl n C.gates (n + 2 + idx)) := by
    intro j idx hmem u hu hceq
    have hge := hbin_strict _ _ rfl (colorClass_nonempty color hsurj j) ⟨tap j, htap_lt j, htap_chg j⟩
      ⟨idx, hmem, u, hu, hceq⟩
    have heq := hbin_each_eq j
    have hpos := Finset.card_pos.2 (colorClass_nonempty color hsurj j)
    omega

  have hfalls_local : ∀ (u : ℕ), u < n + 2 + C.gates.length →
      ∀ j : Fin d, (chg (vl n C.gates u)).Nonempty → chg (vl n C.gates u) ⊆ colorClass color j →
      (falls (vl n C.gates u)).card ≤ (notSub (chg (vl n C.gates u))).card ∧
      ((∀ v < u, chg (vl n C.gates v) ≠ chg (vl n C.gates u)) →
        (falls (vl n C.gates u)).card ≤ (notStrict (chg (vl n C.gates u))).card) := by
    intro u
    induction u using Nat.strongRecOn with
    | ind u ih =>
      intro hu j hne hsub
      by_cases hu_in : u < n + 2
      ·
        have hfl0 : falls (vl n C.gates u) = ∅ := by
          ext i; simp only [mem_falls, Finset.notMem_empty, iff_false]
          have hv : ∀ l, vl n C.gates u l = (prefixInput n l).getD u false := fun l =>
            W_append_old [] C.gates (prefixInput n l) u (by rw [prefixInput_len]; simp; omega)
          rw [hv, hv]
          by_cases hlt : u < n
          · rw [prefixInput_lt n _ u hlt, prefixInput_lt n _ u hlt]
            simp only [Fin.val_castSucc, Fin.val_succ, decide_eq_true_eq, decide_eq_false_iff_not]
            omega
          · have : u = n ∨ u = n + 1 := by omega
            rcases this with rfl | rfl
            · rw [prefixInput_n, prefixInput_n]; simp
            · rw [prefixInput_n1, prefixInput_n1]; simp
        rw [hfl0]; simp
      · let idx := u - (n + 2)
        have hidx_lt : idx < C.gates.length := by omega
        have hu_eq : n + 2 + idx = u := by omega
        by_cases hnot : idx ∈ notIdx
        · rcases hnot_gate_eq idx hidx_lt hnot with hce | ⟨a, ha, heqa⟩
          · rw [hu_eq] at hce; rw [hce] at hne; exact absurd hne (by simp)
          · have ha_lt : a < u := by omega
            have hca : chg (vl n C.gates a) = chg (vl n C.gates u) := by
              rw [← hu_eq]; exact (chg_congr (Or.inr heqa)).symm

            refine ⟨?_, fun hmin => absurd hca (hmin a ha_lt)⟩

            let S := chg (vl n C.gates u)
            have hexS : ∃ v < n + 2 + C.gates.length, chg (vl n C.gates v) = S := ⟨a, lt_trans ha_lt hu, hca⟩
            let u0 := Nat.find hexS
            have hu0 : u0 < n + 2 + C.gates.length ∧ chg (vl n C.gates u0) = S := Nat.find_spec hexS
            have hu0_lt : u0 < u := lt_of_le_of_lt (Nat.find_min' hexS ⟨lt_trans ha_lt hu, hca⟩) ha_lt
            have hu0_min : ∀ v < u0, chg (vl n C.gates v) ≠ chg (vl n C.gates u0) := fun v hv he =>
              Nat.find_min hexS hv ⟨lt_trans hv hu0.1, he.trans hu0.2⟩
            have hih0 := (ih u0 hu0_lt hu0.1 j (hu0.2.symm ▸ hne) (hu0.2.symm ▸ hsub)).2 hu0_min
            rw [hu0.2] at hih0
            have hidx_at : idx ∈ notAt S := Finset.mem_filter.2 ⟨hnot, by rw [hu_eq]⟩
            have hdisj_sa : Disjoint (notStrict S) (notAt S) := by
              rw [Finset.disjoint_left]; intro x hx1 hx2
              exact (Finset.mem_filter.1 hx1).2.2.2 (by rw [(Finset.mem_filter.1 hx2).2])
            have hsub_sa : notStrict S ∪ notAt S ⊆ notSub S := by
              intro x hx
              rcases Finset.mem_union.1 hx with h1 | h2
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2.1,
                  (Finset.mem_filter.1 h1).2.2.1⟩
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1,
                  (Finset.mem_filter.1 h2).2.symm ▸ hne, by rw [(Finset.mem_filter.1 h2).2]⟩
            have hcard_sa := Finset.card_le_card hsub_sa
            rw [Finset.card_union_of_disjoint hdisj_sa] at hcard_sa
            have hat_pos : 1 ≤ (notAt S).card := Finset.card_pos.2 ⟨idx, hidx_at⟩
            rcases eq_or_not_of_chg_eq hu0.2.symm with heq0 | hneq0
            · rw [falls_congr heq0]; change (falls (vl n C.gates u0)).card ≤ (notSub S).card; omega
            · have hfr : (falls (vl n C.gates u)).card = (rises (vl n C.gates u0)).card := by
                rw [falls_congr hneq0, falls_not_eq_rises]
              have hrl := rises_le_falls_succ (vl n C.gates u0)
              change (falls (vl n C.gates u)).card ≤ (notSub S).card
              omega
        ·
          have hbin : idx ∈ binIdx := by
            rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidx_lt, ?_⟩
            cases hb0 : isNotGate (C.gates.getD idx ⟨.or, []⟩)
            · rfl
            · exfalso; exact hnot (Finset.mem_filter.2 ⟨Finset.mem_range.2 hidx_lt, hb0⟩)
          have hbin_mem : idx ∈ binSub (colorClass color j) :=
            Finset.mem_filter.2 ⟨hbin, hu_eq.symm ▸ hne, hu_eq.symm ▸ hsub⟩
          have hmin_u : ∀ v < u, chg (vl n C.gates v) ≠ chg (vl n C.gates u) := fun v hv =>
            hu_eq ▸ hbin_unique_local j idx hbin_mem v (by omega)
          rcases hgood u (by omega) hu with hc | ⟨a, ha, heq⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, hop⟩
          · have : chg (vl n C.gates u) = ∅ := chg_const hc
            rw [this] at hne; exact absurd hne (by simp)
          · exact absurd (chg_congr heq).symm (hmin_u a ha)
          · have hSa : chg (vl n C.gates a) ⊂ chg (vl n C.gates u) := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨by rw [hun]; exact Finset.subset_union_left, fun he => ?_⟩
              obtain ⟨x, hx⟩ := hnb
              exact Finset.disjoint_left.1 hdj (by rw [he, hun]; exact Finset.mem_union_right _ hx) hx
            have hSb : chg (vl n C.gates b) ⊂ chg (vl n C.gates u) := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨by rw [hun]; exact Finset.subset_union_right, fun he => ?_⟩
              obtain ⟨x, hx⟩ := hna
              exact Finset.disjoint_left.1 hdj hx (by rw [he, hun]; exact Finset.mem_union_left _ hx)
            have hiha := (ih a ha (lt_trans ha hu) j hna (Finset.Subset.trans hSa.1 hsub)).1
            have hihb := (ih b hb (lt_trans hb hu) j hnb (Finset.Subset.trans hSb.1 hsub)).1
            have hfl_u : falls (vl n C.gates u) = falls (vl n C.gates a) ∪ falls (vl n C.gates b) :=
              (bin_falls_union hop hdj hun).1
            have hfl_card : (falls (vl n C.gates u)).card ≤ (falls (vl n C.gates a)).card + (falls (vl n C.gates b)).card := by
              rw [hfl_u]; exact Finset.card_union_le _ _
            have hdisj_not : Disjoint (notSub (chg (vl n C.gates a))) (notSub (chg (vl n C.gates b))) := by
              rw [Finset.disjoint_left]; intro x hx1 hx2
              obtain ⟨y, hy⟩ := (Finset.mem_filter.1 hx1).2.1
              exact Finset.disjoint_left.1 hdj ((Finset.mem_filter.1 hx1).2.2 hy) ((Finset.mem_filter.1 hx2).2.2 hy)
            have hsub_st : notSub (chg (vl n C.gates a)) ∪ notSub (chg (vl n C.gates b)) ⊆
                notStrict (chg (vl n C.gates u)) := by
              intro x hx
              rcases Finset.mem_union.1 hx with h1 | h2
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2.1,
                  Finset.ssubset_of_subset_of_ssubset (Finset.mem_filter.1 h1).2.2 hSa⟩
              · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1, (Finset.mem_filter.1 h2).2.1,
                  Finset.ssubset_of_subset_of_ssubset (Finset.mem_filter.1 h2).2.2 hSb⟩
            have hle_st := Finset.card_le_card hsub_st
            rw [Finset.card_union_of_disjoint hdisj_not] at hle_st
            have hst_le_sub : (notStrict (chg (vl n C.gates u))).card ≤ (notSub (chg (vl n C.gates u))).card :=
              Finset.card_le_card fun x hx =>
                Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2.1, (Finset.mem_filter.1 hx).2.2.1⟩
            exact ⟨by omega, fun _ => by omega⟩

  let hasNeg (j : Fin d) : Prop :=
    ∃ u < n + 2 + C.gates.length, chg (vl n C.gates u) = colorClass color j ∧
      ∀ l, vl n C.gates u l = !coord X j l
  let extraNot (j : Fin d) : ℕ :=
    if hasNeg j ∧ ¬(j ∈ X 0 ∧ j ∉ X (Fin.last n)) then 1 else 0
  have hnot_each_ge : ∀ j : Fin d,
      (falls (coord X j)).card + extraNot j ≤ (notSub (colorClass color j)).card := by
    intro j
    by_cases hneg : hasNeg j
    · have hneg' : hasNeg j := hneg
      obtain ⟨u_neg, hu_neg_lt, hu_neg_chg, hu_neg_val⟩ := hneg
      have hexC : ∃ v < n + 2 + C.gates.length, chg (vl n C.gates v) = colorClass color j :=
        ⟨tap j, htap_lt j, htap_chg j⟩
      let u0 := Nat.find hexC
      have hu0 : u0 < n + 2 + C.gates.length ∧ chg (vl n C.gates u0) = colorClass color j :=
        Nat.find_spec hexC
      have hu0_min : ∀ v < u0, chg (vl n C.gates v) ≠ chg (vl n C.gates u0) := fun v hv he =>
        Nat.find_min hexC hv ⟨lt_trans hv hu0.1, he.trans hu0.2⟩
      have hih0 := (hfalls_local u0 hu0.1 j (hu0.2.symm ▸ colorClass_nonempty color hsurj j) (by rw [hu0.2])).2 hu0_min
      rw [hu0.2] at hih0

      have hex_opp : ∃ v < n + 2 + C.gates.length, chg (vl n C.gates v) = colorClass color j ∧
          ¬(∀ l, vl n C.gates v l = vl n C.gates u0 l) := by
        by_cases hsame : ∀ l, vl n C.gates u0 l = coord X j l
        · refine ⟨u_neg, hu_neg_lt, hu_neg_chg, fun heq => ?_⟩
          have := (hu_neg_val 0).symm.trans ((heq 0).trans (hsame 0))
          cases coord X j 0 <;> simp at this
        · exact ⟨tap j, htap_lt j, htap_chg j, fun heq => hsame fun l => (heq l).symm.trans ((hval l).1 j)⟩
      let v0 := Nat.find hex_opp
      have hv0 : v0 < n + 2 + C.gates.length ∧ chg (vl n C.gates v0) = colorClass color j ∧
          ¬(∀ l, vl n C.gates v0 l = vl n C.gates u0 l) := Nat.find_spec hex_opp
      have hv0_gt : u0 < v0 := by
        have hle := Nat.find_min' hexC ⟨hv0.1, hv0.2.1⟩
        have hne : u0 ≠ v0 := fun h => hv0.2.2 (fun l => by rw [h])
        omega

      have hv0_ge : n + 2 ≤ v0 := by
        by_contra hlt
        have hu0_n : u0 < n := Nat.lt_of_not_ge fun hge => by
          have hc : chg (vl n C.gates u0) = ∅ := by
            apply chg_const; intro t t'
            have h1 : ∀ l, vl n C.gates u0 l = (prefixInput n l).getD u0 false := fun l =>
              W_append_old [] C.gates (prefixInput n l) u0 (by rw [prefixInput_len]; simp; omega)
            rw [h1 t, h1 t']
            have hcases : u0 = n ∨ u0 = n + 1 := by omega
            rcases hcases with heq | heq
            · rw [heq, prefixInput_n, prefixInput_n]
            · rw [heq, prefixInput_n1, prefixInput_n1]
          rw [hu0.2] at hc; exact absurd (colorClass_nonempty color hsurj j) (by rw [hc]; simp)
        have hv0_n : v0 < n := Nat.lt_of_not_ge fun hge => by
          have hc : chg (vl n C.gates v0) = ∅ := by
            apply chg_const; intro t t'
            have h1 : ∀ l, vl n C.gates v0 l = (prefixInput n l).getD v0 false := fun l =>
              W_append_old [] C.gates (prefixInput n l) v0 (by rw [prefixInput_len]; simp; omega)
            rw [h1 t, h1 t']
            have hcases : v0 = n ∨ v0 = n + 1 := by omega
            rcases hcases with heq | heq
            · rw [heq, prefixInput_n, prefixInput_n]
            · rw [heq, prefixInput_n1, prefixInput_n1]
          rw [hv0.2.1] at hc; exact absurd (colorClass_nonempty color hsurj j) (by rw [hc]; simp)
        have hcu : chg (vl n C.gates u0) = {⟨u0, hu0_n⟩} := by
          ext i; rw [mem_chg, Finset.mem_singleton]
          have h1 : ∀ l, vl n C.gates u0 l = decide (u0 < l.val) := fun l =>
            (W_append_old [] C.gates (prefixInput n l) u0 (by rw [prefixInput_len]; simp; omega)).trans
              (prefixInput_lt n l u0 hu0_n)
          rw [h1, h1]; simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
          constructor
          · intro h; by_contra hne; by_cases hlt' : u0 < i.val
            · have : u0 < i.val + 1 := by omega
              simp [hlt', this] at h
            · have : ¬(u0 < i.val + 1) := by omega
              simp [hlt', this] at h
          · intro hi
            have hlt1 : ¬(u0 < i.val) := by omega
            have hlt2 : u0 < i.val + 1 := by omega
            simp [hlt1, hlt2]
        have hcv : chg (vl n C.gates v0) = {⟨v0, hv0_n⟩} := by
          ext i; rw [mem_chg, Finset.mem_singleton]
          have h1 : ∀ l, vl n C.gates v0 l = decide (v0 < l.val) := fun l =>
            (W_append_old [] C.gates (prefixInput n l) v0 (by rw [prefixInput_len]; simp; omega)).trans
              (prefixInput_lt n l v0 hv0_n)
          rw [h1, h1]; simp only [Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
          constructor
          · intro h; by_contra hne; by_cases hlt' : v0 < i.val
            · have : v0 < i.val + 1 := by omega
              simp [hlt', this] at h
            · have : ¬(v0 < i.val + 1) := by omega
              simp [hlt', this] at h
          · intro hi
            have hlt1 : ¬(v0 < i.val) := by omega
            have hlt2 : v0 < i.val + 1 := by omega
            simp [hlt1, hlt2]
        have heq_sing : ({⟨u0, hu0_n⟩} : Finset (Fin n)) = {⟨v0, hv0_n⟩} :=
          hcu.symm.trans (hu0.2.trans (hv0.2.1.symm.trans hcv))
        have : (⟨u0, hu0_n⟩ : Fin n) = ⟨v0, hv0_n⟩ := Finset.singleton_injective heq_sing
        have : u0 = v0 := congrArg Fin.val this
        omega
      let idxv := v0 - (n + 2)
      have hidxv_lt : idxv < C.gates.length := by omega
      have hv0_eq : n + 2 + idxv = v0 := by omega
      have hidxv_not : idxv ∈ notIdx := by
        by_contra hnot
        have hbin : idxv ∈ binIdx := by
          rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hidxv_lt, ?_⟩
          cases hb0 : isNotGate (C.gates.getD idxv ⟨.or, []⟩)
          · rfl
          · exfalso; exact hnot (Finset.mem_filter.2 ⟨Finset.mem_range.2 hidxv_lt, hb0⟩)
        have hbin_m : idxv ∈ binSub (colorClass color j) :=
          Finset.mem_filter.2 ⟨hbin, hv0_eq.symm ▸ hv0.2.1.symm ▸ colorClass_nonempty color hsurj j,
            by rw [hv0_eq, hv0.2.1]⟩
        exact hbin_unique_local j idxv hbin_m u0 (by omega) (hu0.2.trans (hv0.2.1.symm.trans (by rw [hv0_eq])))
      have hidxv_at : idxv ∈ notAt (colorClass color j) :=
        Finset.mem_filter.2 ⟨hidxv_not, by rw [hv0_eq, hv0.2.1]⟩
      have hdisj_sa : Disjoint (notStrict (colorClass color j)) (notAt (colorClass color j)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        exact (Finset.mem_filter.1 hx1).2.2.2 (by rw [(Finset.mem_filter.1 hx2).2])
      have hsub_sa : notStrict (colorClass color j) ∪ notAt (colorClass color j) ⊆ notSub (colorClass color j) := by
        intro x hx
        rcases Finset.mem_union.1 hx with h1 | h2
        · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2.1,
            (Finset.mem_filter.1 h1).2.2.1⟩
        · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1,
            (Finset.mem_filter.1 h2).2.symm ▸ colorClass_nonempty color hsurj j, by rw [(Finset.mem_filter.1 h2).2]⟩
      have hcard_sa := Finset.card_le_card hsub_sa
      rw [Finset.card_union_of_disjoint hdisj_sa] at hcard_sa
      have hat_pos : 1 ≤ (notAt (colorClass color j)).card := Finset.card_pos.2 ⟨idxv, hidxv_at⟩

      have hrel := falls_not_vs_falls (coord X j)
      have hu0_eq_c : chg (vl n C.gates u0) = chg (coord X j) :=
        hu0.2.trans (chg_coord_eq_colorClass color X hX j).symm
      rcases eq_or_not_of_chg_eq hu0_eq_c with heq_c | hneq_c
      · rw [falls_congr heq_c] at hih0
        have : extraNot j ≤ 1 := by simp only [extraNot]; split_ifs <;> omega
        omega
      · rw [falls_congr hneq_c] at hih0
        by_cases hspec : j ∈ X 0 ∧ j ∉ X (Fin.last n)
        · have hf1 := hrel.1 ⟨by simp [coord, hspec.1], by simp [coord, hspec.2]⟩
          have : extraNot j = 0 := by simp [extraNot, hspec]
          omega
        · have hf2 := hrel.2 (fun ⟨h1, h2⟩ => hspec ⟨by simpa [coord] using h1, by simpa [coord] using h2⟩)
          have : extraNot j = 1 := by simp [extraNot, hneg', hspec]
          omega
    · simp only [extraNot, hneg, false_and, ↓reduceIte, Nat.add_zero]
      have h1 := (hfalls_local (tap j) (htap_lt j) j
        (htap_chg j ▸ colorClass_nonempty color hsurj j) (by rw [htap_chg j])).1
      rw [htap_chg j] at h1
      have htv : ∀ l, vl n C.gates (tap j) l = coord X j l := fun l => (hval l).1 j
      rwa [falls_congr htv] at h1

  let notLog : Finset ℕ := notIdx.filter fun idx =>
    ¬ ((chg (vl n C.gates (n + 2 + idx))).Nonempty ∧ ∃ j : Fin d, chg (vl n C.gates (n + 2 + idx)) ⊆ colorClass color j)
  have hnot_disj_j : ∀ j1 j2 : Fin d, j1 ≠ j2 →
      Disjoint (notSub (colorClass color j1)) (notSub (colorClass color j2)) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]; intro idx h1 h2
    obtain ⟨i, hi⟩ := (Finset.mem_filter.1 h1).2.1
    have hc1 := (Finset.mem_filter.1 ((Finset.mem_filter.1 h1).2.2 hi)).2
    have hc2 := (Finset.mem_filter.1 ((Finset.mem_filter.1 h2).2.2 hi)).2
    exact hne (hc1.symm.trans hc2)
  have hnot_disj_log : Disjoint notLog (Finset.univ.biUnion fun j : Fin d => notSub (colorClass color j)) := by
    rw [Finset.disjoint_left]; intro idx h1 h2
    rw [Finset.mem_biUnion] at h2
    obtain ⟨j, -, hj⟩ := h2
    exact (Finset.mem_filter.1 h1).2 ⟨(Finset.mem_filter.1 hj).2.1, j, (Finset.mem_filter.1 hj).2.2⟩
  have hnot_sub_all : notLog ∪ (Finset.univ.biUnion fun j : Fin d => notSub (colorClass color j)) ⊆ notIdx := by
    intro idx hi
    rcases Finset.mem_union.1 hi with h1 | h2
    · exact (Finset.mem_filter.1 h1).1
    · rw [Finset.mem_biUnion] at h2
      obtain ⟨j, -, hj⟩ := h2
      exact (Finset.mem_filter.1 hj).1
  have hnot_total : walkFalls X + (∑ j : Fin d, extraNot j) + notLog.card ≤ b := by
    have h1 := Finset.card_le_card hnot_sub_all
    rw [Finset.card_union_of_disjoint hnot_disj_log,
      Finset.card_biUnion (fun j1 _ j2 _ hne => hnot_disj_j j1 j2 hne), hnot_card] at h1
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hnot_each_ge j
    rw [Finset.sum_add_distrib] at hsum
    change walkFalls X + ∑ j : Fin d, extraNot j ≤ _ at hsum
    omega
  refine ⟨by omega, ?_⟩

  have hbuild_neg : ∀ k (hk : k ≤ d),
      ∃ (gs0 : List Gate) (negW : Fin d → ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs0, 0⟩ ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * d + 2) ⟨gs0, 0⟩ ∧
        (∀ g ∈ gs0, ∀ i ∈ g.inputs, AllowedIn d (X 0) (X (Fin.last n)) i) ∧
        nonNotCount gs0 = 0 ∧
        PEqualNP.NotBracket.notCount ⟨gs0, 0⟩ =
          ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), extraNot j ∧
        ∀ j : Fin d, j.val < k → hasNeg j →
          negW j < 2 * d + 2 + gs0.length ∧ AllowedIn d (X 0) (X (Fin.last n)) (negW j) ∧
          ∀ l, (W gs0 (logInput d (X l))).getD (negW j) false = !coord X j l := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun _ => 0, by intro g hg; simp at hg, by intro i hi; simp at hi,
        by intro g hg; simp at hg, by simp [nonNotCount], by rw [notCount_eq_filter]; simp,
        fun j hj => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨gs0, negW, hF0, hR0, hA0, hnn0, hnc0, hneg0⟩ := ih (by omega)
      let j0 : Fin d := ⟨k, hk⟩
      have hfilt : Finset.univ.filter (fun j : Fin d => j.val < k + 1) =
          insert j0 (Finset.univ.filter (fun j : Fin d => j.val < k)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, j0]; omega
      have hj0_not : j0 ∉ Finset.univ.filter (fun j : Fin d => j.val < k) := by simp [j0]
      by_cases hextra : hasNeg j0 ∧ ¬(j0 ∈ X 0 ∧ j0 ∉ X (Fin.last n))
      · let gnot : Gate := ⟨GateOp.not, [j0.val]⟩
        let wj := 2 * d + 2 + gs0.length
        refine ⟨gs0 ++ [gnot], fun j => if j = j0 then wj else negW j,
          fanInTwo_append hF0 (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp [gnot]),
          readsBack_snoc hR0 (fun i hi => by simp only [gnot, List.mem_singleton] at hi; subst hi; omega),
          fun g hg i hi => by
            simp only [List.mem_append, List.mem_singleton] at hg
            rcases hg with hg | rfl
            · exact hA0 g hg i hi
            · simp only [gnot, List.mem_singleton] at hi; subst hi; exact Or.inl j0.isLt,
          by rw [nonNotCount_append, hnn0]; rfl,
          by
            rw [hfilt, Finset.sum_insert hj0_not, notCount_append, hnc0]
            have h1 : PEqualNP.NotBracket.notCount ⟨[gnot], 0⟩ = 1 := by rw [notCount_eq_filter]; rfl
            have h2 : extraNot j0 = 1 := by simp [extraNot, hextra]
            omega,
          fun j hj hnj => ?_⟩
        by_cases heq : j = j0
        · subst heq; simp only [↓reduceIte]
          refine ⟨by simp [wj], Or.inr (Or.inr (by omega)), fun l => ?_⟩
          have hnw := new_wire gs0 gnot (logInput d (X l))
          rw [logInput_len] at hnw
          change (W (gs0 ++ [gnot]) (logInput d (X l))).getD (2 * d + 2 + gs0.length) false = _
          rw [hnw]
          have h0 : (W gs0 (logInput d (X l))).getD j0.val false = (logInput d (X l)).getD j0.val false :=
            W_append_old [] gs0 (logInput d (X l)) j0.val (by rw [logInput_len]; simp; omega)
          simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons,
            h0, logInput_pos, coord]
        · have hjk : j.val < k := by
            have : j.val ≠ k := fun h => heq (Fin.ext h)
            omega
          simp only [heq, ↓reduceIte]
          have hprev := hneg0 j hjk hnj
          refine ⟨by simp; omega, hprev.2.1, fun l => ?_⟩
          exact (old_wire gs0 gnot (logInput d (X l)) (negW j) (by rw [logInput_len]; omega)).trans (hprev.2.2 l)
      · refine ⟨gs0, fun j => if j = j0 then d + j0.val else negW j, hF0, hR0, hA0, hnn0, ?_, ?_⟩
        · rw [hfilt, Finset.sum_insert hj0_not, hnc0]
          have h2 : extraNot j0 = 0 := if_neg hextra
          omega
        · intro j hj hnj
          by_cases heq : j = j0
          · subst heq; simp only [↓reduceIte]
            have hspec : j0 ∈ X 0 ∧ j0 ∉ X (Fin.last n) := by
              by_contra hc; exact hextra ⟨hnj, hc⟩
            refine ⟨by have := j0.isLt; omega, Or.inr (Or.inl ⟨j0, rfl, hspec.1, hspec.2⟩), fun l => ?_⟩
            have h0 : (W gs0 (logInput d (X l))).getD (d + j0.val) false = (logInput d (X l)).getD (d + j0.val) false :=
              W_append_old [] gs0 (logInput d (X l)) (d + j0.val) (by rw [logInput_len]; simp; omega)
            exact h0.trans (logInput_neg d (X l) j0)
          · have hjk : j.val < k := by
              have : j.val ≠ k := fun h => heq (Fin.ext h)
              omega
            simp only [heq, ↓reduceIte]
            exact hneg0 j hjk hnj
  obtain ⟨gs0, negW, hF0, hR0, hA0, hnn0, hnc0, hneg0⟩ := hbuild_neg d (le_refl d)
  have huniv_d : Finset.univ.filter (fun j : Fin d => j.val < d) = Finset.univ := by ext j; simp [j.isLt]
  rw [huniv_d] at hnc0

  let CanMap (u : ℕ) : Prop :=
    chg (vl n C.gates u) = ∅ ∨
    (∃ j : Fin d, chg (vl n C.gates u) = colorClass color j) ∨
    (∀ j : Fin d, ¬ chg (vl n C.gates u) ⊆ colorClass color j)
  have hbuild_log : ∀ k (hk : k ≤ C.gates.length),
      ∃ (ds : List Gate) (mp : ℕ → ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs0 ++ ds, 0⟩ ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * d + 2) ⟨gs0 ++ ds, 0⟩ ∧
        (∀ g ∈ gs0 ++ ds, ∀ i ∈ g.inputs, AllowedIn d (X 0) (X (Fin.last n)) i) ∧
        nonNotCount ds ≤ (binLog.filter (· < k)).card ∧
        PEqualNP.NotBracket.notCount ⟨ds, 0⟩ ≤ (notLog.filter (· < k)).card ∧
        ∀ u < n + 2 + k, CanMap u →
          mp u < 2 * d + 2 + (gs0 ++ ds).length ∧
          AllowedIn d (X 0) (X (Fin.last n)) (mp u) ∧
          ∀ l, (W (gs0 ++ ds) (logInput d (X l))).getD (mp u) false = vl n C.gates u l := by
    intro k
    induction k with
    | zero =>
      intro _

      let mp0 : ℕ → ℕ := fun u =>
        if h0 : chg (vl n C.gates u) = ∅ then
          if vl n C.gates u 0 then 2 * d + 1 else 2 * d
        else if h1 : ∃ j : Fin d, chg (vl n C.gates u) = colorClass color j then
          let j := Classical.choose h1
          if ∀ l, vl n C.gates u l = coord X j l then j.val else negW j
        else 2 * d
      refine ⟨[], mp0, by simpa using hF0, by simpa using hR0, by simpa using hA0,
        by simp [nonNotCount], by rw [notCount_eq_filter]; simp, fun u hu hcm => ?_⟩
      simp only [List.append_nil, Nat.add_zero] at hu ⊢
      rcases hcm with hce | ⟨j, hcj⟩ | hnotj
      · simp only [mp0, hce, ↓reduceDIte]
        have hconst := const_of_chg_empty hce
        cases hv0 : vl n C.gates u 0
        · simp only [hv0, Bool.false_eq_true, ↓reduceIte]
          refine ⟨by omega, Or.inr (Or.inr (le_refl _)), fun l => ?_⟩
          have h1 : (W gs0 (logInput d (X l))).getD (2 * d) false = (logInput d (X l)).getD (2 * d) false :=
            W_append_old [] gs0 (logInput d (X l)) (2 * d) (by rw [logInput_len]; simp)
          rw [h1, logInput_false, hconst l 0, hv0]
        · simp only [hv0, ↓reduceIte]
          refine ⟨by omega, Or.inr (Or.inr (by omega)), fun l => ?_⟩
          have h1 : (W gs0 (logInput d (X l))).getD (2 * d + 1) false = (logInput d (X l)).getD (2 * d + 1) false :=
            W_append_old [] gs0 (logInput d (X l)) (2 * d + 1) (by rw [logInput_len]; simp)
          rw [h1, logInput_true, hconst l 0, hv0]
      · have hne_u : chg (vl n C.gates u) ≠ ∅ := by
          rw [hcj]; exact Finset.nonempty_iff_ne_empty.1 (colorClass_nonempty color hsurj j)
        have hexj : ∃ j : Fin d, chg (vl n C.gates u) = colorClass color j := ⟨j, hcj⟩
        set j' := Classical.choose hexj
        have hcj' : chg (vl n C.gates u) = colorClass color j' := Classical.choose_spec hexj
        have hmp_eq : mp0 u = if ∀ l, vl n C.gates u l = coord X j' l then j'.val else negW j' := by
          simp only [mp0, hne_u, ↓reduceDIte, hexj]; rfl
        rw [hmp_eq]
        by_cases hpos : ∀ l, vl n C.gates u l = coord X j' l
        · rw [if_pos hpos]
          refine ⟨by have := j'.isLt; omega, Or.inl j'.isLt, fun l => ?_⟩
          have h1 : (W gs0 (logInput d (X l))).getD j'.val false = (logInput d (X l)).getD j'.val false :=
            W_append_old [] gs0 (logInput d (X l)) j'.val (by rw [logInput_len]; simp; omega)
          rw [h1, logInput_pos, hpos l]; rfl
        · rw [if_neg hpos]
          have hneq : ∀ l, vl n C.gates u l = !coord X j' l :=
            (eq_or_not_of_chg_eq (hcj'.trans (chg_coord_eq_colorClass color X hX j').symm)).resolve_left hpos
          have hnj : hasNeg j' := ⟨u, by omega, hcj', hneq⟩
          have hres := hneg0 j' j'.isLt hnj
          exact ⟨hres.1, hres.2.1, fun l => (hres.2.2 l).trans (hneq l).symm⟩
      ·
        exfalso
        by_cases hce : chg (vl n C.gates u) = ∅
        · exact hnotj ⟨0, hd⟩ (by rw [hce]; exact Finset.empty_subset _)
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hce
          have hcard1 := hchg_input u hu
          have hsing : chg (vl n C.gates u) = {i} :=
            Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun x hx =>
              Finset.card_le_one.1 hcard1 x hx i hi⟩
          exact hnotj (color i) (by rw [hsing, Finset.singleton_subset_iff]; simp [colorClass])
    | succ k ih =>
      intro hk
      obtain ⟨ds, mp, hFd, hRd, hAd, hnnd, hncd, hmp⟩ := ih (by omega)
      let u := n + 2 + k
      have hu_lt : u < n + 2 + C.gates.length := by omega
      have hbin_sub : binLog.filter (· < k) ⊆ binLog.filter (· < k + 1) :=
        fun x hx => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1, by have := (Finset.mem_filter.1 hx).2; omega⟩
      have hnot_sub : notLog.filter (· < k) ⊆ notLog.filter (· < k + 1) :=
        fun x hx => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1, by have := (Finset.mem_filter.1 hx).2; omega⟩

      have noGate : ∀ (w_u : ℕ),
          w_u < 2 * d + 2 + (gs0 ++ ds).length →
          AllowedIn d (X 0) (X (Fin.last n)) w_u →
          (∀ l, (W (gs0 ++ ds) (logInput d (X l))).getD w_u false = vl n C.gates u l) →
          ∃ (ds' : List Gate) (mp' : ℕ → ℕ),
            PEqualNP.MetaComplexity.FanInTwo ⟨gs0 ++ ds', 0⟩ ∧
            PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * d + 2) ⟨gs0 ++ ds', 0⟩ ∧
            (∀ g ∈ gs0 ++ ds', ∀ i ∈ g.inputs, AllowedIn d (X 0) (X (Fin.last n)) i) ∧
            nonNotCount ds' ≤ (binLog.filter (· < k + 1)).card ∧
            PEqualNP.NotBracket.notCount ⟨ds', 0⟩ ≤ (notLog.filter (· < k + 1)).card ∧
            ∀ v < n + 2 + (k + 1), CanMap v →
              mp' v < 2 * d + 2 + (gs0 ++ ds').length ∧
              AllowedIn d (X 0) (X (Fin.last n)) (mp' v) ∧
              ∀ l, (W (gs0 ++ ds') (logInput d (X l))).getD (mp' v) false = vl n C.gates v l := by
        intro w_u hw_lt hw_all hw_val
        refine ⟨ds, fun v => if v = u then w_u else mp v, hFd, hRd, hAd,
          le_trans hnnd (Finset.card_le_card hbin_sub),
          le_trans hncd (Finset.card_le_card hnot_sub), fun v hv hcmv => ?_⟩
        by_cases heq : v = u
        · subst heq; simp only [↓reduceIte]; exact ⟨hw_lt, hw_all, hw_val⟩
        · simp only [heq, ↓reduceIte]; exact hmp v (by omega) hcmv

      by_cases hce : chg (vl n C.gates u) = ∅
      · have hconst := const_of_chg_empty hce
        cases hv0 : vl n C.gates u 0
        · exact noGate (2 * d) (by omega) (Or.inr (Or.inr (le_refl _))) fun l => by
            have h1 : (W (gs0 ++ ds) (logInput d (X l))).getD (2 * d) false = (logInput d (X l)).getD (2 * d) false :=
              W_append_old [] (gs0 ++ ds) (logInput d (X l)) (2 * d) (by rw [logInput_len]; simp)
            rw [h1, logInput_false, hconst l 0, hv0]
        · exact noGate (2 * d + 1) (by omega) (Or.inr (Or.inr (by omega))) fun l => by
            have h1 : (W (gs0 ++ ds) (logInput d (X l))).getD (2 * d + 1) false = (logInput d (X l)).getD (2 * d + 1) false :=
              W_append_old [] (gs0 ++ ds) (logInput d (X l)) (2 * d + 1) (by rw [logInput_len]; simp)
            rw [h1, logInput_true, hconst l 0, hv0]

      · by_cases hcj : ∃ j : Fin d, chg (vl n C.gates u) = colorClass color j
        · obtain ⟨j, hj⟩ := hcj
          by_cases hpos : ∀ l, vl n C.gates u l = coord X j l
          · exact noGate j.val (by have := j.isLt; omega) (Or.inl j.isLt) fun l => by
              have h1 : (W (gs0 ++ ds) (logInput d (X l))).getD j.val false = (logInput d (X l)).getD j.val false :=
                W_append_old [] (gs0 ++ ds) (logInput d (X l)) j.val (by rw [logInput_len]; simp; omega)
              rw [h1, logInput_pos, hpos l]; rfl
          · have hneq : ∀ l, vl n C.gates u l = !coord X j l :=
              (eq_or_not_of_chg_eq (hj.trans (chg_coord_eq_colorClass color X hX j).symm)).resolve_left hpos
            have hres := hneg0 j j.isLt ⟨u, hu_lt, hj, hneq⟩
            exact noGate (negW j) (by simp; omega) hres.2.1 fun l =>
              (W_append_old gs0 ds (logInput d (X l)) (negW j) (by rw [logInput_len]; exact hres.1)).trans
                ((hres.2.2 l).trans (hneq l).symm)

        · by_cases hloc : ∃ j : Fin d, chg (vl n C.gates u) ⊆ colorClass color j
          · refine ⟨ds, mp, hFd, hRd, hAd,
              le_trans hnnd (Finset.card_le_card hbin_sub),
              le_trans hncd (Finset.card_le_card hnot_sub), fun v hv hcmv => ?_⟩
            by_cases heq : v = u
            · subst heq
              exfalso
              rcases hcmv with h1 | h2 | h3
              · exact hce h1
              · exact hcj h2
              · obtain ⟨j, hj⟩ := hloc; exact h3 j hj
            · exact hmp v (by omega) hcmv

          · have hnotj : ∀ j : Fin d, ¬ chg (vl n C.gates u) ⊆ colorClass color j :=
              fun j hj => hloc ⟨j, hj⟩
            rcases hgood u (by omega) hu_lt with hc | ⟨a, ha, heqa⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, hop⟩
            · exact absurd (chg_const hc) hce
            · have hca : chg (vl n C.gates a) = chg (vl n C.gates u) := (chg_congr heqa).symm
              have hcm_a : CanMap a := Or.inr (Or.inr fun j hj => hnotj j (hca ▸ hj))
              have hma := hmp a (by omega) hcm_a
              rcases heqa with hcopy | hneg_a
              · exact noGate (mp a) hma.1 hma.2.1 fun l => (hma.2.2 l).trans (hcopy l).symm
              ·

                have hk_not : k ∈ notIdx := by
                  by_contra hkn
                  have hk_bin : k ∈ binIdx := by
                    rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hk, ?_⟩
                    cases hb0 : isNotGate (C.gates.getD k ⟨.or, []⟩)
                    · rfl
                    · exfalso; exact hkn (Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hb0⟩)
                  have hk_binS : k ∈ binSub Finset.univ :=
                    Finset.mem_filter.2 ⟨hk_bin, Finset.nonempty_iff_ne_empty.2 hce, Finset.subset_univ _⟩
                  have hge_n := hbin_strict n Finset.univ (by simp)
                    ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩ ⟨out 0, hout_lt 0, hout0_chg⟩
                    ⟨k, hk_binS, a, ha, hca⟩
                  have hle_n : (binSub Finset.univ).card ≤ n - 1 := by
                    have h1 := Finset.card_le_card (Finset.filter_subset (fun idx =>
                      (chg (vl n C.gates (n + 2 + idx))).Nonempty ∧ chg (vl n C.gates (n + 2 + idx)) ⊆ Finset.univ) binIdx)
                    rw [hbin_card] at h1
                    change (binSub Finset.univ).card ≤ nonNotCount C.gates at h1
                    have hsp := notCount_add_nonNotCount C
                    omega
                  simp only [Finset.card_univ, Fintype.card_fin] at hge_n
                  omega
                have hk_nlog : k ∈ notLog :=
                  Finset.mem_filter.2 ⟨hk_not, fun ⟨_, j, hj⟩ => hnotj j hj⟩
                let gnot : Gate := ⟨GateOp.not, [mp a]⟩
                let wu := 2 * d + 2 + (gs0 ++ ds).length
                have hnot_inc : (notLog.filter (· < k)).card + 1 ≤ (notLog.filter (· < k + 1)).card := by
                  have hmem : k ∈ notLog.filter (· < k + 1) := Finset.mem_filter.2 ⟨hk_nlog, by omega⟩
                  have hnotm : k ∉ notLog.filter (· < k) := by simp
                  have hsub' : insert k (notLog.filter (· < k)) ⊆ notLog.filter (· < k + 1) :=
                    Finset.insert_subset hmem hnot_sub
                  have := Finset.card_le_card hsub'
                  rw [Finset.card_insert_of_notMem hnotm] at this; exact this
                refine ⟨ds ++ [gnot], fun v => if v = u then wu else mp v,
                  by
                    rw [← List.append_assoc]
                    exact fanInTwo_append hFd (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp [gnot]),
                  by
                    rw [← List.append_assoc]
                    exact readsBack_snoc hRd (fun i hi => by simp only [gnot, List.mem_singleton] at hi; subst hi; exact hma.1),
                  fun g hg i hi => by
                    rw [← List.append_assoc] at hg
                    rcases List.mem_append.1 hg with hg | hg
                    · exact hAd g hg i hi
                    · simp only [List.mem_singleton] at hg; subst hg
                      simp only [gnot, List.mem_singleton] at hi; subst hi; exact hma.2.1,
                  by
                    rw [nonNotCount_append]; have : nonNotCount [gnot] = 0 := rfl
                    have := Finset.card_le_card hbin_sub; omega,
                  by
                    rw [notCount_append]; have : PEqualNP.NotBracket.notCount ⟨[gnot], 0⟩ = 1 := by rw [notCount_eq_filter]; rfl
                    omega,
                  fun v hv hcmv => ?_⟩
                by_cases heq : v = u
                · subst heq; simp only [↓reduceIte]
                  refine ⟨by rw [← List.append_assoc]; simp [wu], Or.inr (Or.inr (by dsimp only [wu]; omega)), fun l => ?_⟩
                  rw [← List.append_assoc]
                  have hnw := new_wire (gs0 ++ ds) gnot (logInput d (X l))
                  rw [logInput_len] at hnw; rw [hnw]
                  simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hma.2.2 l, hneg_a l]
                · simp only [heq, ↓reduceIte]
                  have hprev := hmp v (by omega) hcmv
                  have hlt_v := hprev.1
                  refine ⟨by rw [← List.append_assoc]; simp only [List.length_append, List.length_singleton] at hlt_v ⊢; omega, hprev.2.1, fun l => ?_⟩
                  rw [← List.append_assoc]
                  exact (old_wire (gs0 ++ ds) gnot (logInput d (X l)) (mp v) (by rw [logInput_len]; exact ne_of_lt hlt_v)).trans (hprev.2.2 l)
            ·
              have hcm_a : CanMap a := by
                by_cases hsub_a : ∃ j : Fin d, chg (vl n C.gates a) ⊆ colorClass color j
                · obtain ⟨j, hj⟩ := hsub_a
                  exact Or.inr (Or.inl ⟨j, hlog_child u hu_lt hnotj a (lt_trans ha hu_lt)
                    b (lt_trans hb hu_lt) hna hnb hdj hun j hj⟩)
                · exact Or.inr (Or.inr fun j hj => hsub_a ⟨j, hj⟩)
              have hcm_b : CanMap b := by
                by_cases hsub_b : ∃ j : Fin d, chg (vl n C.gates b) ⊆ colorClass color j
                · obtain ⟨j, hj⟩ := hsub_b
                  exact Or.inr (Or.inl ⟨j, hlog_child u hu_lt hnotj b (lt_trans hb hu_lt)
                    a (lt_trans ha hu_lt) hnb hna hdj.symm (hun.trans (Finset.union_comm _ _)) j hj⟩)
                · exact Or.inr (Or.inr fun j hj => hsub_b ⟨j, hj⟩)
              have hma := hmp a (by omega) hcm_a
              have hmb := hmp b (by omega) hcm_b

              by_cases hk_not : k ∈ notIdx
              ·
                rcases hnot_gate_eq k hk hk_not with hce' | ⟨a', ha', heq'⟩
                · exact absurd hce' hce
                · have hca' : chg (vl n C.gates a') = chg (vl n C.gates u) := (chg_congr (Or.inr heq')).symm
                  have hma' := hmp a' (by omega) (Or.inr (Or.inr fun j hj => hnotj j (hca' ▸ hj)))
                  have hk_nlog : k ∈ notLog := Finset.mem_filter.2 ⟨hk_not, fun ⟨_, j, hj⟩ => hnotj j hj⟩
                  let gnot : Gate := ⟨GateOp.not, [mp a']⟩
                  let wu := 2 * d + 2 + (gs0 ++ ds).length
                  have hnot_inc : (notLog.filter (· < k)).card + 1 ≤ (notLog.filter (· < k + 1)).card := by
                    have hsub' : insert k (notLog.filter (· < k)) ⊆ notLog.filter (· < k + 1) :=
                      Finset.insert_subset (Finset.mem_filter.2 ⟨hk_nlog, by omega⟩) hnot_sub
                    have := Finset.card_le_card hsub'
                    rw [Finset.card_insert_of_notMem (by simp)] at this; exact this
                  refine ⟨ds ++ [gnot], fun v => if v = u then wu else mp v,
                    by rw [← List.append_assoc]; exact fanInTwo_append hFd (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp [gnot]),
                    by rw [← List.append_assoc]; exact readsBack_snoc hRd (fun i hi => by simp only [gnot, List.mem_singleton] at hi; subst hi; exact hma'.1),
                    fun g hg i hi => by
                      rw [← List.append_assoc] at hg
                      rcases List.mem_append.1 hg with hg | hg
                      · exact hAd g hg i hi
                      · simp only [List.mem_singleton] at hg; subst hg
                        simp only [gnot, List.mem_singleton] at hi; subst hi; exact hma'.2.1,
                    by rw [nonNotCount_append]; have : nonNotCount [gnot] = 0 := rfl; have := Finset.card_le_card hbin_sub; omega,
                    by rw [notCount_append]; have h1 : PEqualNP.NotBracket.notCount ⟨[gnot], 0⟩ = 1 := by rw [notCount_eq_filter]; rfl
                       omega,
                    fun v hv hcmv => ?_⟩
                  by_cases heq : v = u
                  · subst heq; simp only [↓reduceIte]
                    refine ⟨by rw [← List.append_assoc]; simp [wu], Or.inr (Or.inr (by dsimp only [wu]; omega)), fun l => ?_⟩
                    rw [← List.append_assoc]
                    have hnw := new_wire (gs0 ++ ds) gnot (logInput d (X l))
                    rw [logInput_len] at hnw; rw [hnw]
                    simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hma'.2.2 l]
                    exact (heq' l).symm
                  · simp only [heq, ↓reduceIte]
                    have hprev := hmp v (by omega) hcmv
                    have hlt_v := hprev.1
                    refine ⟨by rw [← List.append_assoc]; simp only [List.length_append, List.length_singleton] at hlt_v ⊢; omega, hprev.2.1, fun l => ?_⟩
                    rw [← List.append_assoc]
                    exact (old_wire (gs0 ++ ds) gnot (logInput d (X l)) (mp v) (by rw [logInput_len]; exact ne_of_lt hlt_v)).trans (hprev.2.2 l)
              · have hk_bin : k ∈ binIdx := by
                  rw [Finset.mem_filter]; refine ⟨Finset.mem_range.2 hk, ?_⟩
                  cases hb0 : isNotGate (C.gates.getD k ⟨.or, []⟩)
                  · rfl
                  · exfalso; exact hk_not (Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hb0⟩)
                have hk_blog : k ∈ binLog :=
                  Finset.mem_filter.2 ⟨hk_bin, fun ⟨_, j, hj⟩ => hnotj j hj⟩
                have hbin_inc : (binLog.filter (· < k)).card + 1 ≤ (binLog.filter (· < k + 1)).card := by
                  have hsub' : insert k (binLog.filter (· < k)) ⊆ binLog.filter (· < k + 1) :=
                    Finset.insert_subset (Finset.mem_filter.2 ⟨hk_blog, by omega⟩) hbin_sub
                  have := Finset.card_le_card hsub'
                  rw [Finset.card_insert_of_notMem (by simp)] at this; exact this
                let op : GateOp := if ∀ l, vl n C.gates u l = (vl n C.gates a l && vl n C.gates b l) then GateOp.and else GateOp.or
                let gbin : Gate := ⟨op, [mp a, mp b]⟩
                let wu := 2 * d + 2 + (gs0 ++ ds).length
                refine ⟨ds ++ [gbin], fun v => if v = u then wu else mp v,
                  by
                    rw [← List.append_assoc]
                    exact fanInTwo_append hFd (fun x hx => by
                      simp only [List.mem_singleton] at hx; subst hx
                      simp only [gbin, op]; split_ifs <;> simp),
                  by
                    rw [← List.append_assoc]
                    exact readsBack_snoc hRd (fun i hi => by
                      simp only [gbin, List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl; exact hma.1; exact hmb.1),
                  fun g hg i hi => by
                    rw [← List.append_assoc] at hg
                    rcases List.mem_append.1 hg with hg | hg
                    · exact hAd g hg i hi
                    · simp only [List.mem_singleton] at hg; subst hg
                      simp only [gbin, List.mem_cons, List.not_mem_nil, or_false] at hi
                      rcases hi with rfl | rfl; exact hma.2.1; exact hmb.2.1,
                  by
                    rw [nonNotCount_append]
                    have h1 : nonNotCount [gbin] = 1 := by simp only [nonNotCount, isNotGate, gbin, op]; split_ifs <;> rfl
                    omega,
                  by
                    rw [notCount_append]
                    have h1 : PEqualNP.NotBracket.notCount ⟨[gbin], 0⟩ = 0 := by
                      rw [notCount_eq_filter]; simp only [isNotGate, gbin, op]; split_ifs <;> rfl
                    have := Finset.card_le_card hnot_sub; omega,
                  fun v hv hcmv => ?_⟩
                by_cases heq : v = u
                · subst heq; simp only [↓reduceIte]
                  refine ⟨by rw [← List.append_assoc]; simp [wu], Or.inr (Or.inr (by dsimp only [wu]; omega)), fun l => ?_⟩
                  rw [← List.append_assoc]
                  have hnw := new_wire (gs0 ++ ds) gbin (logInput d (X l))
                  rw [logInput_len] at hnw; rw [hnw]
                  simp only [gbin, op]
                  split_ifs with hand
                  · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                      id_eq, Bool.and_true, hma.2.2 l, hmb.2.2 l, hand l]
                  · have hor : ∀ l, vl n C.gates u l = (vl n C.gates a l || vl n C.gates b l) :=
                      hop.resolve_left hand
                    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false, hma.2.2 l, hmb.2.2 l, hor l]
                · simp only [heq, ↓reduceIte]
                  have hprev := hmp v (by omega) hcmv
                  have hlt_v := hprev.1
                  refine ⟨by rw [← List.append_assoc]; simp only [List.length_append, List.length_singleton] at hlt_v ⊢; omega, hprev.2.1, fun l => ?_⟩
                  rw [← List.append_assoc]
                  exact (old_wire (gs0 ++ ds) gbin (logInput d (X l)) (mp v) (by rw [logInput_len]; exact ne_of_lt hlt_v)).trans (hprev.2.2 l)
  obtain ⟨ds, mp, hFd, hRd, hAd, hnnd, hncd, hmp⟩ := hbuild_log C.gates.length (le_refl _)

  have hout_cm : ∀ t : Fin (a + 1), CanMap (out t) := by
    intro t
    have hchg_t : chg (vl n C.gates (out t)) = (M t).biUnion (colorClass color) := by
      ext i
      rw [mem_chg, Finset.mem_biUnion]
      have h1 := (hval i.castSucc).2 t
      have h2 := (hval i.succ).2 t
      change vl n C.gates (out t) i.castSucc = _ at h1
      change vl n C.gates (out t) i.succ = _ at h2
      rw [h1, h2]
      have hstep_mem : ∀ j : Fin d, j ≠ color i → (j ∈ X i.castSucc ↔ j ∈ X i.succ) := fun j hj => by
        have : decide (j ∈ X i.castSucc) = decide (j ∈ X i.succ) := by
          by_contra hne; exact hj ((hX i j).1 hne).symm
        exact decide_eq_decide.1 this
      have hdiff_ci : (color i ∈ X i.castSucc) ↔ (color i ∉ X i.succ) := by
        have := (hX i (color i)).2 rfl
        by_cases hm : color i ∈ X i.castSucc <;> simp [hm] at this ⊢ <;> exact this
      constructor
      · intro hne
        refine ⟨color i, ?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
        by_contra hnotM
        have heq_inter : X i.castSucc ∩ M t = X i.succ ∩ M t := by
          ext j; simp only [Finset.mem_inter]
          by_cases hj : j = color i
          · subst hj; simp [hnotM]
          · rw [hstep_mem j hj]
        rw [heq_inter] at hne; exact hne rfl
      · rintro ⟨j, hjM, hij⟩
        have hjeq : color i = j := (Finset.mem_filter.1 hij).2
        subst hjeq
        have hpar : (X i.castSucc ∩ M t).card % 2 ≠ (X i.succ ∩ M t).card % 2 := by
          by_cases hm : color i ∈ X i.castSucc
          · have hnot : color i ∉ X i.succ := hdiff_ci.1 hm
            have heq_ins : X i.castSucc ∩ M t = insert (color i) (X i.succ ∩ M t) := by
              ext k; simp only [Finset.mem_inter, Finset.mem_insert]
              by_cases hk : k = color i
              · subst hk; simp [hm, hjM]
              · simp [hk, hstep_mem k hk]
            rw [heq_ins, Finset.card_insert_of_notMem (by simp [hnot])]; omega
          · have hmem : color i ∈ X i.succ := by
              by_contra hnot; exact hm (hdiff_ci.2 hnot)
            have heq_ins : X i.succ ∩ M t = insert (color i) (X i.castSucc ∩ M t) := by
              ext k; simp only [Finset.mem_inter, Finset.mem_insert]
              by_cases hk : k = color i
              · subst hk; simp [hmem, hjM]
              · simp [hk, hstep_mem k hk]
            rw [heq_ins, Finset.card_insert_of_notMem (by simp [hm])]; omega
        cases hp : phase t with
        | false =>
          intro heq; apply hpar
          have heq' : decide ((X i.castSucc ∩ M t).card % 2 = 1) = decide ((X i.succ ∩ M t).card % 2 = 1) := by
            simpa [hp] using heq
          have := decide_eq_decide.1 heq'; omega
        | true =>
          intro heq; apply hpar
          have heq' : (!decide ((X i.castSucc ∩ M t).card % 2 = 1)) = (!decide ((X i.succ ∩ M t).card % 2 = 1)) := by
            simpa [hp] using heq
          have := decide_eq_decide.1 (Bool.not_inj heq'); omega
    by_cases hM0 : M t = ∅
    · left; rw [hchg_t, hM0]; simp
    · by_cases hM1 : (M t).card = 1
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hM1
        right; left; exact ⟨j, by rw [hchg_t, hj]; simp⟩
      · right; right; intro j hsub
        have hgt1 : 1 < (M t).card := by
          have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hM0); omega
        obtain ⟨j1, hj1, j2, hj2, hne12⟩ := Finset.one_lt_card.1 hgt1
        obtain ⟨i1, hi1⟩ := colorClass_nonempty color hsurj j1
        obtain ⟨i2, hi2⟩ := colorClass_nonempty color hsurj j2
        have h1 : j1 = j := (Finset.mem_filter.1 hi1).2.symm.trans
          (Finset.mem_filter.1 (hsub (hchg_t.symm ▸ Finset.mem_biUnion.2 ⟨j1, hj1, hi1⟩))).2
        have h2 : j2 = j := (Finset.mem_filter.1 hi2).2.symm.trans
          (Finset.mem_filter.1 (hsub (hchg_t.symm ▸ Finset.mem_biUnion.2 ⟨j2, hj2, hi2⟩))).2
        exact hne12 (h1.trans h2.symm)

  refine ⟨⟨gs0 ++ ds, 0⟩, fun t => mp (out t), hFd, hRd, hAd,
    fun t => ⟨(hmp (out t) (hout_lt t) (hout_cm t)).1, (hmp (out t) (hout_lt t) (hout_cm t)).2.1⟩,
    ?_, ?_, ?_⟩
  · rw [nonNotCount_append, hnn0, Nat.zero_add]
    exact le_trans hnnd (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hbinLog_le)
  · rw [notCount_append, hnc0]
    have hle_nl := le_trans hncd (Finset.card_le_card (Finset.filter_subset _ _))
    omega
  · intro A hA t
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hA
    exact ((hmp (out t) (hout_lt t) (hout_cm t)).2.2 l).trans ((hval l).2 t)

end PEqualNP.Outside.L_lib_1390

theorem PEqualNP.Outside.L_lib_1390 : (∀ d : Nat, 0 < d →
  let walk := fun (n : Nat) (X : Fin (n+1) → Finset (Fin d)) =>
    ∃ color : Fin n → Fin d, Function.Surjective color ∧
      ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j
  let states := fun (n : Nat) (X : Fin (n+1) → Finset (Fin d)) => Finset.univ.image X
  let fit := fun (n : Nat) (X : Fin (n+1) → Finset (Fin d)) (a : Nat)
    (M : Fin (a+1) → Finset (Fin d)) (phase : Fin (a+1) → Bool) (b : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin d → Nat) (out : Fin (a+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧ (∀ t, out t < n+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n-1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ l, let w := C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false,true])
           (∀ j, w.getD (tap j) false = decide (j ∈ X l)) ∧
           ∀ t, w.getD (out t) false = Bool.xor (phase t) (decide (((X l) ∩ M t).card % 2 = 1))
  (∀ (n m : Nat) (X : Fin (n+1) → Finset (Fin d)) (Y : Fin (m+1) → Finset (Fin d)),
    walk n X → walk m Y → m ≤ n → states n X = states m Y →
    X 0 = Y 0 → X (Fin.last n) = Y (Fin.last m) →
    (n-m) % 2 = 0 ∧ ∀ (a : Nat) (M : Fin (a+1) → Finset (Fin d))
      (phase : Fin (a+1) → Bool) (b : Nat), M 0 = Finset.univ →
      (fit n X a M phase (b+(n-m)/2) ↔ fit m Y a M phase b)) ∧
  ∀ (n : Nat) (X : Fin (n+1) → Finset (Fin d)), walk n X →
    ∃ (m : Nat) (Y : Fin (m+1) → Finset (Fin d)), m ≤ n ∧ walk m Y ∧
      states n X = states m Y ∧ X 0 = Y 0 ∧ X (Fin.last n) = Y (Fin.last m) ∧
      m + ((X 0 \ X (Fin.last n)) ∪ (X (Fin.last n) \ X 0)).card ≤ 2*((states n X).card-1)) := by
  intro d hd walk states fit
  constructor
  · intro n m X Y ⟨cX, hsurjX, hX⟩ ⟨cY, hsurjY, hY⟩ hle hst h0 hlast
    obtain ⟨hpar, hdisc⟩ := PEqualNP.Outside.L_lib_1390.walk_parity_and_discount cX X hX cY Y hY hle h0 hlast
    refine ⟨hpar, fun a M phase b hM0 => ⟨fun hfitX => ?_, fun hfitY => ?_⟩⟩
    · obtain ⟨hFX, hLogX⟩ := PEqualNP.Outside.L_lib_1390.physical_to_log hd cX X hsurjX hX M phase (b + (n - m) / 2) hM0 hfitX
      have hLogY : PEqualNP.Outside.L_lib_1390.LogFit d (Finset.univ.image Y) (Y 0) (Y (Fin.last m)) a M phase (b - PEqualNP.Outside.L_lib_1390.walkFalls Y) := by
        have hsub : b + (n - m) / 2 - PEqualNP.Outside.L_lib_1390.walkFalls X = b - PEqualNP.Outside.L_lib_1390.walkFalls Y := by omega
        dsimp only [states] at hst
        rw [← hst, ← h0, ← hlast, ← hsub]
        exact hLogX
      obtain ⟨C, tap, out, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        PEqualNP.Outside.L_lib_1390.log_to_physical hd cY Y hsurjY hY M phase _ hLogY
      have h7' : PEqualNP.NotBracket.notCount C ≤ b := by omega
      exact ⟨C, tap, out, h1, h2, h3, h4, h5, h6, h7', h8⟩
    · obtain ⟨hFY, hLogY⟩ := PEqualNP.Outside.L_lib_1390.physical_to_log hd cY Y hsurjY hY M phase b hM0 hfitY
      have hLogX : PEqualNP.Outside.L_lib_1390.LogFit d (Finset.univ.image X) (X 0) (X (Fin.last n)) a M phase (b - PEqualNP.Outside.L_lib_1390.walkFalls Y) := by
        dsimp only [states] at hst
        rw [hst, h0, hlast]; exact hLogY
      obtain ⟨C, tap, out, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        PEqualNP.Outside.L_lib_1390.log_to_physical hd cX X hsurjX hX M phase _ hLogX
      have h7' : PEqualNP.NotBracket.notCount C ≤ b + (n - m) / 2 := by omega
      exact ⟨C, tap, out, h1, h2, h3, h4, h5, h6, h7', h8⟩
  · intro n X ⟨cX, hsurjX, hX⟩
    exact PEqualNP.Outside.L_lib_1390.walk_shorten cX X hsurjX hX
