import PEqualNP.Defs

/-!
# L-pcx-252

Proof outline:

* Code (Behrend with the norm stored in the strings, no sphere needed).  A word is `B` blocks of
  `t` digits; digit `i` is `x_i` (`b+1` bits) and `s_i` (`b` bits).  Per block:
  string 0 = (x, N(s)), string 1 = (x + s mod 2^(b+1), N(s)), string 2 = (x + 2s mod 2^(b+1)),
  with `N(s) = ∑ s_i^2` (`2b + log t` bits).  `behrend_digits` below is the triangle property for
  one block.  Shorter words are padded by a constant/copy bit, unused string bits copy wire 0.
  Part 1: one block, `b ≈ t ≈ Nat.sqrt k` (loss `≈ 11 sqrt k`, size `O(t b^2) = O(k sqrt k)`).
  Part 2: `b = 2r`, `t = 20 r`, `B = k / (t(b+1) + L)` blocks (loss `≤ k/r` for large `k`,
  size `O(k r)`).
* Circuit: ripple adders / shift-and-add squarers over AND/OR/NOT (XOR = 4 gates) built on the
  `W` framework below; `wires_unique` characterises wires of a `ReadsBack` circuit.
* CNF for party `o`: private vars = its word guess + all gate wires (`gateClauses`, ternary
  Tseitin, `gateClauses_sat`) + per owned row a leading-bits indicator tree over the
  `d = min n (w+1)` distinct sites `(r+j)%n`, `j < d` (pattern `δ ↦ a (δ % n)`), leaf clauses
  `¬e_a ∨ tab r p_a`; output clauses `out ↔ y`.  Map the structured private type to `Fin q` by
  `Fintype.equivFin`.  Counting bijection uses `parties_agree` / `code_eq_of_parties`.
-/

namespace PEqualNP.Outside.L_pcx_252_aux

open PEqualNP.CircuitLowerBounds


/-! ## Wire framework -/

/-- Wires of a bare gate list. -/
def W (gs : List Gate) (x : List Bool) : List Bool := (Circuit.mk gs 0).wires x

theorem wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem W_nil (x : List Bool) : W [] x = x := rfl

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  unfold W Circuit.wires
  rw [List.foldl_append]
  rfl

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W_nil]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem W_prefix (gs hs : List Gate) (x : List Bool) :
    ∃ t, W (gs ++ hs) x = W gs x ++ t := by
  induction hs using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton hs g ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [g.op.eval (g.inputs.map fun i => (W (gs ++ hs) x).getD i false)], ?_⟩
    rw [← List.append_assoc, W_snoc, ht, List.append_assoc]

theorem W_getD_append (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (W (gs ++ hs) x).getD i false = (W gs x).getD i false := by
  obtain ⟨t, ht⟩ := W_prefix gs hs x
  rw [ht, List.getD_append _ _ _ _ (by rw [W_length]; exact hi)]

theorem W_getD_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (W (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [W_length])]
  simp [W_length]

/-- The value of gate `j` in terms of the earlier wires of the whole circuit. -/
theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
          fun i => (C.wires x).getD i false) := by
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD, hj]
  rw [hga] at hrb ⊢
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j+1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons, List.take_append_drop]
  have htl : (C.gates.take j).length = j := by simp; omega
  generalize C.gates[j] = g at hrb hsplit ⊢
  generalize C.gates.take j = T at hsplit htl
  generalize C.gates.drop (j+1) = D at hsplit
  rw [wires_eq_W, hsplit, W_getD_append _ _ _ _ (by simp [htl])]
  conv_lhs => rw [show x.length + j = x.length + T.length by rw [htl]]
  rw [W_getD_last]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hrb i hi
  rw [W_getD_append _ _ _ _ (by simp [htl]; omega), W_getD_append _ _ _ _ (by simp [htl]; omega)]

/-- Under `ReadsBack`, any valuation obeying the gate equations agrees with the wires. -/
theorem wires_unique (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : Fin n → Bool) (val : ℕ → Bool) (hin : ∀ i : Fin n, val i.val = x i)
    (hg : ∀ j < C.gates.length, val (n + j) =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map val)) :
    ∀ i < n + C.gates.length, val i = (C.wires (List.ofFn x)).getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hin' : i < n
    · rw [hin ⟨i, hin'⟩]
      have hlen : (List.ofFn x).length = n := by simp
      rw [wires_eq_W]
      have : (W C.gates (List.ofFn x)) = W ([] ++ C.gates) (List.ofFn x) := by simp
      rw [this, W_getD_append [] C.gates _ _ (by simp; exact hin'), W_nil]
      simp [List.getD_eq_getElem?_getD, hin']
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hlen : (List.ofFn x).length = n := by simp
      have := wires_gate C (List.ofFn x) j hj (by rw [hlen]; exact hrb j hj)
      rw [hlen] at this
      rw [this, hg j hj]
      congr 1
      apply List.map_congr_left
      intro i' hi'
      have := hrb j hj i' hi'
      exact ih i' this (by omega)


/-! ## Tseitin clauses for one gate -/

open PEqualNP.ProofComplexity in
/-- Ternary clauses saying variable `o` carries the value of gate `g` whose wire `i` is `wv i`. -/
def gateClauses {V : Type} [DecidableEq V] (wv : ℕ → V) (g : Gate) (o : V) : Finset (Clause V) :=
  match g.op, g.inputs with
  | .and, [a, b] => {{(o,false),(wv a,true)}, {(o,false),(wv b,true)},
      {(o,true),(wv a,false),(wv b,false)}}
  | .or, [a, b] => {{(o,true),(wv a,false)}, {(o,true),(wv b,false)},
      {(o,false),(wv a,true),(wv b,true)}}
  | .not, [a] => {{(o,true),(wv a,true)}, {(o,false),(wv a,false)}}
  | _, _ => ∅

open PEqualNP.ProofComplexity in
theorem gateClauses_card_le {V : Type} [DecidableEq V] (wv : ℕ → V) (g : Gate) (o : V) :
    (gateClauses wv g o).card ≤ 3 ∧ ∀ cl ∈ gateClauses wv g o, cl.card ≤ 3 := by
  unfold gateClauses
  split
  · refine ⟨Finset.card_le_three, ?_⟩
    intro cl hcl; simp only [Finset.mem_insert, Finset.mem_singleton] at hcl
    rcases hcl with rfl | rfl | rfl
    · exact le_trans (Finset.card_le_two) (by norm_num)
    · exact le_trans (Finset.card_le_two) (by norm_num)
    · exact Finset.card_le_three
  · refine ⟨Finset.card_le_three, ?_⟩
    intro cl hcl; simp only [Finset.mem_insert, Finset.mem_singleton] at hcl
    rcases hcl with rfl | rfl | rfl
    · exact le_trans (Finset.card_le_two) (by norm_num)
    · exact le_trans (Finset.card_le_two) (by norm_num)
    · exact Finset.card_le_three
  · refine ⟨le_trans Finset.card_le_two (by norm_num), ?_⟩
    intro cl hcl; simp only [Finset.mem_insert, Finset.mem_singleton] at hcl
    rcases hcl with rfl | rfl
    · exact le_trans (Finset.card_le_two) (by norm_num)
    · exact le_trans (Finset.card_le_two) (by norm_num)
  · simp

open PEqualNP.ProofComplexity in
theorem gateClauses_sat {V : Type} [DecidableEq V] (wv : ℕ → V) (g : Gate) (o : V)
    (hg : ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (asg : V → Bool) :
    (∀ cl ∈ gateClauses wv g o, ClauseSat asg cl) ↔
      asg o = g.op.eval (g.inputs.map fun i => asg (wv i)) := by
  obtain ⟨op, ins⟩ := g
  simp only at hg ⊢
  rcases hg with ⟨hop | hop, hl⟩ | ⟨hop, hl⟩
  · subst hop
    match ins, hl with
    | [a, b], _ =>
      simp only [gateClauses, GateOp.eval, Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq, ClauseSat, exists_eq_or_imp, exists_eq_left,
        List.map_cons, List.map_nil, List.all_cons, List.all_nil, id]
      cases asg o <;> cases asg (wv a) <;> cases asg (wv b) <;> simp
  · subst hop
    match ins, hl with
    | [a, b], _ =>
      simp only [gateClauses, GateOp.eval, Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq, ClauseSat, exists_eq_or_imp, exists_eq_left,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, id]
      cases asg o <;> cases asg (wv a) <;> cases asg (wv b) <;> simp
  · subst hop
    match ins, hl with
    | [a], _ =>
      simp only [gateClauses, GateOp.eval, Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq, ClauseSat, exists_eq_or_imp, exists_eq_left,
        List.map_cons, List.map_nil, List.headD_cons]
      cases asg o <;> cases asg (wv a) <;> simp


/-! ## The three local words agree -/

/-- If party `o` checks strings `o` and `o-1` of its own guessed word, the cyclic witness
property forces all three guessed words to coincide. -/
theorem parties_agree {n k : ℕ} (code : (Fin n → Bool) → Fin 3 → Fin k → Bool)
    (htri : ∀ v : Fin 3 → (Fin n → Bool), (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) →
      ∀ p, v p = v 0)
    (x : Fin 3 → (Fin n → Bool)) (y : Fin 3 → Fin k → Bool)
    (h : ∀ o e : Fin 3, (e = o ∨ e + 1 = o) → code (x o) e = y e) : ∀ p, x p = x 0 := by
  apply htri x
  intro i
  rw [h i i (Or.inl rfl), h (i+1) i (Or.inr rfl)]

/-- Conversely a single word satisfies every party's two checks exactly when it has code `y`. -/
theorem code_eq_of_parties {n k : ℕ} (code : (Fin n → Bool) → Fin 3 → Fin k → Bool)
    (u : Fin n → Bool) (y : Fin 3 → Fin k → Bool) :
    (∀ o e : Fin 3, (e = o ∨ e + 1 = o) → code u e = y e) ↔ code u = y := by
  constructor
  · intro h; funext e; exact h e e (Or.inl rfl)
  · intro h o e _; rw [h]

/-- Behrend core: midpoint relation plus equal sums of squares forces equality. -/
theorem behrend_core {t : ℕ} (s0 s1 s2 : Fin t → ℕ)
    (hmid : ∀ i, s1 i + s2 i = 2 * s0 i)
    (h01 : ∑ i, s0 i ^ 2 = ∑ i, s1 i ^ 2) (h12 : ∑ i, s1 i ^ 2 = ∑ i, s2 i ^ 2) :
    s1 = s0 ∧ s2 = s0 := by
  have key : ∑ i, (((s1 i : ℤ) - s2 i) ^ 2) = 0 := by
    have e : ∀ i, (((s1 i : ℤ) - s2 i) ^ 2) =
        2 * (s1 i : ℤ) ^ 2 + 2 * (s2 i : ℤ) ^ 2 - 4 * (s0 i : ℤ) ^ 2 := by
      intro i
      have := hmid i
      have h' : (s1 i : ℤ) + s2 i = 2 * s0 i := by exact_mod_cast this
      have : (s0 i : ℤ) = ((s1 i : ℤ) + s2 i) / 2 := by omega
      nlinarith [h']
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have a : ∑ i, (s0 i : ℤ) ^ 2 = ∑ i, (s1 i : ℤ) ^ 2 := by exact_mod_cast h01
    have b : ∑ i, (s1 i : ℤ) ^ 2 = ∑ i, (s2 i : ℤ) ^ 2 := by exact_mod_cast h12
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, a, ← b]
    ring
  have hz : ∀ i ∈ Finset.univ, (((s1 i : ℤ) - s2 i) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 key
  have e12 : ∀ i, s1 i = s2 i := by
    intro i
    have := hz i (Finset.mem_univ _)
    have : (s1 i : ℤ) - s2 i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    omega
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have := hmid i; have := e12 i; omega
  · have := hmid i; have := e12 i; omega

/-- Digit-level Behrend witness lemma. -/
theorem behrend_digits {t b : ℕ} (x0 x1 x2 s0 s1 s2 : Fin t → ℕ)
    (hx0 : ∀ i, x0 i < 2 ^ (b+1)) (hx1 : ∀ i, x1 i < 2 ^ (b+1)) (hx2 : ∀ i, x2 i < 2 ^ (b+1))
    (hs0 : ∀ i, s0 i < 2 ^ b) (hs1 : ∀ i, s1 i < 2 ^ b) (hs2 : ∀ i, s2 i < 2 ^ b)
    (hA : ∀ i, x0 i = x1 i)
    (hB : ∀ i, (x1 i + s1 i) % 2 ^ (b+1) = (x2 i + s2 i) % 2 ^ (b+1))
    (hC : ∀ i, (x2 i + 2 * s2 i) % 2 ^ (b+1) = (x0 i + 2 * s0 i) % 2 ^ (b+1))
    (h01 : ∑ i, s0 i ^ 2 = ∑ i, s1 i ^ 2) (h12 : ∑ i, s1 i ^ 2 = ∑ i, s2 i ^ 2) :
    x1 = x0 ∧ x2 = x0 ∧ s1 = s0 ∧ s2 = s0 := by
  have hM : (2:ℕ) ^ (b+1) = 2 * 2 ^ b := by ring
  have hmid : ∀ i, s1 i + s2 i = 2 * s0 i := by
    intro i
    have b1 := hB i; have c1 := hC i; have a1 := hA i
    have m1 := hs0 i; have m2 := hs1 i; have m3 := hs2 i
    have q1 := hx0 i; have q2 := hx1 i; have q3 := hx2 i
    have e1 : (x1 i + s1 i) ≡ (x2 i + s2 i) [MOD 2^(b+1)] := b1
    have e2 : (x2 i + 2 * s2 i) ≡ (x0 i + 2 * s0 i) [MOD 2^(b+1)] := c1
    have e3 := Nat.ModEq.add e1 e2
    have e4 : (s1 i + s2 i) + (x1 i + x2 i + s2 i) ≡ (2 * s0 i) + (x1 i + x2 i + s2 i) [MOD 2^(b+1)] := by
      have h1 : x1 i + s1 i + (x2 i + 2 * s2 i) = (s1 i + s2 i) + (x1 i + x2 i + s2 i) := by ring
      have h2 : x2 i + s2 i + (x0 i + 2 * s0 i) = (2 * s0 i) + (x1 i + x2 i + s2 i) := by rw [a1]; ring
      rw [h1, h2] at e3; exact e3
    have e5 := Nat.ModEq.add_right_cancel' _ e4
    rw [hM] at e5
    have := Nat.ModEq.eq_of_lt_of_lt e5 (by omega) (by omega)
    exact this
  obtain ⟨h1, h2⟩ := behrend_core s0 s1 s2 hmid h01 h12
  refine ⟨funext fun i => (hA i).symm, funext fun i => ?_, h1, h2⟩
  have b1 := hB i
  rw [show s1 i = s0 i from congrFun h1 i, show s2 i = s0 i from congrFun h2 i] at b1
  have e := Nat.ModEq.add_right_cancel' _ (show x1 i + s0 i ≡ x2 i + s0 i [MOD 2^(b+1)] from b1)
  have := Nat.ModEq.eq_of_lt_of_lt e (hx1 i) (hx2 i)
  rw [← hA i] at this; exact this.symm


/-! ## The CNF part -/

open PEqualNP.ProofComplexity
open PEqualNP.MetaComplexity.NestedCover (gateAt ReadsBack)

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, hj]
  rw [this]; exact List.getElem_mem hj

theorem wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [wires_eq_W]
  have : W C.gates (List.ofFn x) = W ([] ++ C.gates) (List.ofFn x) := by simp
  rw [this, W_getD_append [] C.gates _ _ (by simp; exact hi), W_nil]
  simp [List.getD_eq_getElem?_getD, hi]

def mapF {V W : Type} [DecidableEq W] (g : V → W) (F : Finset (Clause V)) : Finset (Clause W) :=
  F.image fun cl => cl.image fun l => (g l.1, l.2)

theorem mapF_sat {V W : Type} [DecidableEq W] (g : V → W) (F : Finset (Clause V)) (a : W → Bool) :
    Satisfies a ↑(mapF g F) ↔ ∀ cl ∈ F, ClauseSat (a ∘ g) cl := by
  unfold Satisfies mapF
  constructor
  · intro h cl hcl
    obtain ⟨l, hl, hv⟩ := h _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hcl))
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hl
    exact ⟨l', hl', hv⟩
  · intro h cl' hcl'
    obtain ⟨cl, hcl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hcl')
    obtain ⟨l, hl, hv⟩ := h cl hcl
    exact ⟨_, Finset.mem_image_of_mem _ hl, hv⟩

theorem mapF_card_le {V W : Type} [DecidableEq W] (g : V → W) (F : Finset (Clause V)) :
    (mapF g F).card ≤ F.card := Finset.card_image_le

theorem mapF_card3 {V W : Type} [DecidableEq W] (g : V → W) (F : Finset (Clause V))
    (h : ∀ cl ∈ F, cl.card ≤ 3) : ∀ cl ∈ mapF g F, cl.card ≤ 3 := by
  intro cl hcl
  obtain ⟨cl', hcl', rfl⟩ := Finset.mem_image.1 hcl
  exact le_trans Finset.card_image_le (h cl' hcl')

theorem mux_sat {V : Type} [DecidableEq V] (f : V → Bool) (s c0 c1 m : V) :
    (∀ cl ∈ ({{(s,false),(c1,false),(m,true)}, {(s,false),(c1,true),(m,false)},
      {(s,true),(c0,false),(m,true)}, {(s,true),(c0,true),(m,false)}} : Finset (Clause V)),
      ClauseSat f cl) ↔ f m = if f s then f c1 else f c0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, ClauseSat,
    exists_eq_or_imp, exists_eq_left]
  cases f s <;> cases f c0 <;> cases f c1 <;> cases f m <;> simp

theorem eq2_sat {V : Type} [DecidableEq V] (f : V → Bool) (v u : V) :
    (∀ cl ∈ ({{(v,false),(u,true)}, {(v,true),(u,false)}} : Finset (Clause V)),
      ClauseSat f cl) ↔ f v = f u := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, ClauseSat,
    exists_eq_or_imp, exists_eq_left]
  cases f v <;> cases f u <;> simp

theorem mem_filter_any {α : Type} (s : Finset α) (p : α → Prop) (inst : DecidablePred p) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := @Finset.mem_filter α p inst s a

structure Cfg where
  n : ℕ
  k : ℕ
  w : ℕ
  enc : Circuit
  owner : Fin n → Fin 3
  o : Fin 3
  hn : 0 < n
  out : Fin 3 → Fin k → Fin (n + enc.size)

namespace Cfg
variable (c : Cfg)

def d : ℕ := min c.n (c.w + 1)

theorem d_pos : 0 < c.d := by unfold d; have := c.hn; omega

theorem mod_lt_d (δ : Fin (c.w+1)) : δ.val % c.n < c.d := by
  unfold d
  have h1 := Nat.mod_lt δ.val c.hn
  have h2 := Nat.mod_le δ.val c.n
  have h3 := δ.isLt
  omega

abbrev Row : Type := {r : Fin c.n // c.owner r = c.o}
abbrev Bit : Type := {e : Fin 3 // e = c.o ∨ e + 1 = c.o} × Fin c.k
abbrev Node : Type := Σ j : Fin c.d, Fin (2 ^ (j : ℕ))
abbrev P : Type := Fin c.n ⊕ (Fin c.enc.size ⊕ (c.Row × c.Node))
abbrev V : Type := (c.Row × (Fin (c.w + 1) → Bool)) ⊕ (c.Bit ⊕ c.P)

instance instDecRP : DecidableEq (c.Row × (Fin (c.w + 1) → Bool)) := inferInstance
instance instDecBit : DecidableEq c.Bit := inferInstance
instance instDecP : DecidableEq c.P := inferInstance
instance instDecV : DecidableEq c.V := instDecidableEqSum

def wordV (i : Fin c.n) : c.V := Sum.inr (Sum.inr (Sum.inl i))
def gateV (j : Fin c.enc.size) : c.V := Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
def auxV (r : c.Row) (nd : c.Node) : c.V := Sum.inr (Sum.inr (Sum.inr (Sum.inr (r, nd))))
def yV (q : c.Bit) : c.V := Sum.inr (Sum.inl q)
def tabV (r : c.Row) (p : Fin (c.w + 1) → Bool) : c.V := Sum.inl (r, p)

def wv (i : ℕ) : c.V :=
  if h : i < c.n then c.wordV ⟨i, h⟩
  else if h' : i - c.n < c.enc.size then c.gateV ⟨i - c.n, h'⟩
  else c.wordV ⟨0, c.hn⟩

def site (r : Fin c.n) (j : ℕ) : Fin c.n := ⟨(r.val + j) % c.n, Nat.mod_lt _ c.hn⟩

def nodeV (r : c.Row) (j a : ℕ) : c.V :=
  if h : j < c.d then c.auxV r ⟨⟨j, h⟩, ⟨a % 2 ^ j, Nat.mod_lt _ (Nat.two_pow_pos j)⟩⟩
  else c.tabV r (fun δ => a.testBit (δ.val % c.n))

def muxC (r : c.Row) (nd : c.Node) : Finset (Clause c.V) :=
  {{(c.wordV (c.site r.1 nd.1.val), false),
      (c.nodeV r (nd.1.val+1) (nd.2.val + 2^nd.1.val), false), (c.auxV r nd, true)},
   {(c.wordV (c.site r.1 nd.1.val), false),
      (c.nodeV r (nd.1.val+1) (nd.2.val + 2^nd.1.val), true), (c.auxV r nd, false)},
   {(c.wordV (c.site r.1 nd.1.val), true), (c.nodeV r (nd.1.val+1) nd.2.val, false),
      (c.auxV r nd, true)},
   {(c.wordV (c.site r.1 nd.1.val), true), (c.nodeV r (nd.1.val+1) nd.2.val, true),
      (c.auxV r nd, false)}}

def rootN : c.Node := ⟨⟨0, c.d_pos⟩, ⟨0, Nat.two_pow_pos 0⟩⟩

def gateCs : Finset (Clause c.V) :=
  Finset.univ.biUnion fun j : Fin c.enc.size =>
    gateClauses c.wv (gateAt c.enc j) (c.gateV j)

def outCs : Finset (Clause c.V) :=
  Finset.univ.biUnion fun q : c.Bit =>
    {{(c.wv (c.out q.1.1 q.2).val, false), (c.yV q, true)},
     {(c.wv (c.out q.1.1 q.2).val, true), (c.yV q, false)}}

def rowCs : Finset (Clause c.V) :=
  Finset.univ.biUnion fun r : c.Row =>
    insert {(c.auxV r c.rootN, true)} (Finset.univ.biUnion fun nd : c.Node => c.muxC r nd)

def Fp : Finset (Clause c.V) := c.gateCs ∪ c.outCs ∪ c.rowCs

def asg (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) : c.V → Bool :=
  Sum.elim (fun h => tab h.1.val h.2) (Sum.elim (fun bit => y bit.1.val bit.2) a)

def cM (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (x : Fin c.n → Bool) (r : c.Row)
    (j a : ℕ) : Bool :=
  tab r.1 (fun δ => if δ.val % c.n < j then a.testBit (δ.val % c.n)
    else x (c.site r.1 (δ.val % c.n)))

def canon (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (x : Fin c.n → Bool) : c.P → Bool :=
  Sum.elim x (Sum.elim (fun j => (c.enc.wires (List.ofFn x)).getD (c.n + j.val) false)
    (fun p => c.cM tab x p.1 p.2.1.val p.2.2.val))

def chk (code : (Fin c.n → Bool) → Fin 3 → Fin c.k → Bool)
    (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (x : Fin c.n → Bool) : Prop :=
  (∀ e : Fin 3, (e = c.o ∨ e + 1 = c.o) → code x e = y e) ∧
  ∀ r : c.Row, tab r.1 (fun δ => x ⟨(r.1.val + δ.val) % c.n, Nat.mod_lt _ c.hn⟩) = true

variable {c}

theorem cM_step (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (x : Fin c.n → Bool) (r : c.Row)
    (j a : ℕ) (ha : a < 2^j) :
    c.cM tab x r j a = if x (c.site r.1 j) then c.cM tab x r (j+1) (a + 2^j)
      else c.cM tab x r (j+1) a := by
  unfold cM
  split_ifs with hs
  · congr 1; funext δ
    rcases lt_trichotomy (δ.val % c.n) j with h | h | h
    · rw [if_pos h, if_pos (by omega), Nat.add_comm a (2^j), Nat.testBit_two_pow_add_gt h]
    · rw [if_neg (by omega), if_pos (by omega), h, Nat.add_comm a (2^j),
        Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]
      simpa using hs
    · rw [if_neg (by omega), if_neg (by omega)]
  · congr 1; funext δ
    rcases lt_trichotomy (δ.val % c.n) j with h | h | h
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg (by omega), if_pos (by omega), h, Nat.testBit_lt_two_pow ha]
      simpa using hs
    · rw [if_neg (by omega), if_neg (by omega)]

theorem cM_zero (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (x : Fin c.n → Bool) (r : c.Row) :
    c.cM tab x r 0 0 = tab r.1 (fun δ => x ⟨(r.1.val + δ.val) % c.n, Nat.mod_lt _ c.hn⟩) := by
  unfold cM
  congr 1; funext δ
  rw [if_neg (Nat.not_lt_zero _)]
  congr 1
  apply Fin.ext
  simp [site, Nat.add_mod_mod]

theorem nodeV_lt (r : c.Row) (j a : ℕ) (hj : j < c.d) (ha : a < 2^j) :
    c.nodeV r j a = c.auxV r ⟨⟨j, hj⟩, ⟨a, ha⟩⟩ := by
  unfold nodeV; rw [dif_pos hj]
  congr 1
  exact Sigma.ext rfl (heq_of_eq (Fin.ext (Nat.mod_eq_of_lt ha)))

theorem nodeV_ge (r : c.Row) (j a : ℕ) (hj : ¬ j < c.d) :
    c.nodeV r j a = c.tabV r (fun δ => a.testBit (δ.val % c.n)) := by
  unfold nodeV; rw [dif_neg hj]

/-- Values of node variables when the auxiliary part is canonical. -/
theorem nodeV_val (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) (r : c.Row)
    (haux : ∀ nd : c.Node, a (Sum.inr (Sum.inr (r, nd))) =
      c.cM tab (fun i => a (Sum.inl i)) r nd.1.val nd.2.val)
    (j : ℕ) (hj : j ≤ c.d) (a' : ℕ) (ha' : a' < 2^j) :
    c.asg tab y a (c.nodeV r j a') = c.cM tab (fun i => a (Sum.inl i)) r j a' := by
  by_cases h : j < c.d
  · rw [nodeV_lt r j a' h ha']
    exact haux _
  · rw [nodeV_ge r j a' h]
    show tab r.1 _ = _
    unfold cM
    congr 1; funext δ
    rw [if_pos (by have := c.mod_lt_d δ; omega)]

theorem row_canon (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) (r : c.Row)
    (hmux : ∀ nd : c.Node, c.asg tab y a (c.auxV r nd) =
        if c.asg tab y a (c.wordV (c.site r.1 nd.1.val))
        then c.asg tab y a (c.nodeV r (nd.1.val+1) (nd.2.val + 2^nd.1.val))
        else c.asg tab y a (c.nodeV r (nd.1.val+1) nd.2.val)) :
    ∀ nd : c.Node, a (Sum.inr (Sum.inr (r, nd))) =
      c.cM tab (fun i => a (Sum.inl i)) r nd.1.val nd.2.val := by
  have key : ∀ m j, j + m = c.d → ∀ a' < 2^j,
      c.asg tab y a (c.nodeV r j a') = c.cM tab (fun i => a (Sum.inl i)) r j a' := by
    intro m
    induction m with
    | zero =>
      intro j hj a' _
      rw [nodeV_ge r j a' (by omega)]
      show tab r.1 _ = _
      unfold cM
      congr 1; funext δ
      rw [if_pos (by have := c.mod_lt_d δ; omega)]
    | succ m ih =>
      intro j hj a' ha'
      have hjd : j < c.d := by omega
      rw [nodeV_lt r j a' hjd ha', hmux]
      dsimp only
      have hp : (2:ℕ)^(j+1) = 2 * 2^j := by ring
      rw [ih (j+1) (by omega) (a' + 2^j) (by omega), ih (j+1) (by omega) a' (by omega),
        cM_step tab _ r j a' ha']
      rfl
  intro nd
  have := key (c.d - nd.1.val) nd.1.val (by have := nd.1.isLt; omega) nd.2.val nd.2.isLt
  rw [nodeV_lt r _ _ nd.1.isLt nd.2.isLt] at this
  exact this

theorem gate_part (hrb : ReadsBack c.n c.enc)
    (hshape : ∀ g ∈ c.enc.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
    (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) :
    (∀ cl ∈ c.gateCs, ClauseSat (c.asg tab y a) cl) ↔
    ∀ j : Fin c.enc.size, a (Sum.inr (Sum.inl j)) =
      (c.enc.wires (List.ofFn fun i => a (Sum.inl i))).getD (c.n + j.val) false := by
  have hsize : c.enc.size = c.enc.gates.length := rfl
  have step1 : (∀ cl ∈ c.gateCs, ClauseSat (c.asg tab y a) cl) ↔
      ∀ j : Fin c.enc.size, a (Sum.inr (Sum.inl j)) = (gateAt c.enc j).op.eval
        ((gateAt c.enc j).inputs.map fun i => c.asg tab y a (c.wv i)) := by
    unfold gateCs
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro h j
      have hg := gateAt_mem c.enc j (by rw [← hsize]; exact j.isLt)
      exact (gateClauses_sat c.wv _ (c.gateV j) (hshape _ hg) (c.asg tab y a)).1
        (fun cl hcl => h cl ⟨j, hcl⟩)
    · rintro h cl ⟨j, hcl⟩
      have hg := gateAt_mem c.enc j (by rw [← hsize]; exact j.isLt)
      exact (gateClauses_sat c.wv _ (c.gateV j) (hshape _ hg) (c.asg tab y a)).2 (h j) cl hcl
  rw [step1]
  have hlt : ∀ i (h : i < c.n), c.asg tab y a (c.wv i) = a (Sum.inl ⟨i, h⟩) := by
    intro i h; unfold wv; rw [dif_pos h]; rfl
  have hge : ∀ i (h1 : ¬ i < c.n) (h2 : i - c.n < c.enc.size),
      c.asg tab y a (c.wv i) = a (Sum.inr (Sum.inl ⟨i - c.n, h2⟩)) := by
    intro i h1 h2; unfold wv; rw [dif_neg h1, dif_pos h2]; rfl
  have hlen : (List.ofFn fun i => a (Sum.inl i)).length = c.n := by simp
  constructor
  · intro h j
    have hu := wires_unique c.n c.enc hrb (fun i => a (Sum.inl i))
      (fun i => c.asg tab y a (c.wv i)) (fun i => hlt i.val i.isLt) (by
        intro j hj
        rw [hge (c.n + j) (by omega) (by rw [hsize]; omega)]
        have := h ⟨j, hj⟩
        simp only [Nat.add_sub_cancel_left] at this ⊢
        exact this)
    have := hu (c.n + j.val) (by rw [← hsize]; omega)
    rw [hge (c.n + j.val) (by omega) (by omega)] at this
    simp only [Nat.add_sub_cancel_left] at this
    exact this
  · intro h
    have hall : ∀ i < c.n + c.enc.size, c.asg tab y a (c.wv i) =
        (c.enc.wires (List.ofFn fun i => a (Sum.inl i))).getD i false := by
      intro i hi
      by_cases h1 : i < c.n
      · rw [hlt i h1, wires_input]
      · rw [hge i h1 (by omega), h ⟨i - c.n, by omega⟩]
        congr 1; show c.n + (i - c.n) = i; omega
    intro j
    rw [h j]
    have hj : j.val < c.enc.gates.length := by rw [← hsize]; exact j.isLt
    have := wires_gate c.enc (List.ofFn fun i => a (Sum.inl i)) j.val hj
      (by rw [hlen]; exact hrb j.val hj)
    rw [hlen] at this
    rw [this]
    congr 1
    apply List.map_congr_left
    intro i hi
    have := hrb j.val hj i hi
    rw [hall i (by omega)]

theorem out_part (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) :
    (∀ cl ∈ c.outCs, ClauseSat (c.asg tab y a) cl) ↔
    ∀ q : c.Bit, c.asg tab y a (c.wv (c.out q.1.1 q.2).val) = y q.1.1 q.2 := by
  unfold outCs
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro h q; exact (eq2_sat _ _ _).1 (fun cl hcl => h cl ⟨q, hcl⟩)
  · rintro h cl ⟨q, hcl⟩; exact (eq2_sat _ _ _).2 (h q) cl hcl

theorem row_part (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) :
    (∀ cl ∈ c.rowCs, ClauseSat (c.asg tab y a) cl) ↔
    ∀ r : c.Row, c.asg tab y a (c.auxV r c.rootN) = true ∧
      ∀ nd : c.Node, c.asg tab y a (c.auxV r nd) =
        if c.asg tab y a (c.wordV (c.site r.1 nd.1.val))
        then c.asg tab y a (c.nodeV r (nd.1.val+1) (nd.2.val + 2^nd.1.val))
        else c.asg tab y a (c.nodeV r (nd.1.val+1) nd.2.val) := by
  unfold rowCs
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h r
    refine ⟨?_, fun nd => (mux_sat _ _ _ _ _).1 (fun cl hcl => h cl ⟨r, Or.inr ⟨nd, hcl⟩⟩)⟩
    obtain ⟨l, hl, hv⟩ := h _ ⟨r, Or.inl rfl⟩
    rw [Finset.mem_singleton] at hl
    subst hl
    exact hv
  · rintro h cl ⟨r, rfl | ⟨nd, hcl⟩⟩
    · exact ⟨_, Finset.mem_singleton_self _, (h r).1⟩
    · exact (mux_sat _ _ _ _ _).2 ((h r).2 nd) cl hcl

theorem party (hrb : ReadsBack c.n c.enc)
    (hshape : ∀ g ∈ c.enc.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
    (code : (Fin c.n → Bool) → Fin 3 → Fin c.k → Bool)
    (hout : ∀ u e j, (c.enc.wires (List.ofFn u)).getD (c.out e j).val false = code u e j)
    (tab : Fin c.n → (Fin (c.w+1) → Bool) → Bool) (y : Fin 3 → Fin c.k → Bool)
    (a : c.P → Bool) :
    (∀ cl ∈ c.Fp, ClauseSat (c.asg tab y a) cl) ↔
      a = c.canon tab (fun i => a (Sum.inl i)) ∧ c.chk code tab y (fun i => a (Sum.inl i)) := by
  have hF : (∀ cl ∈ c.Fp, ClauseSat (c.asg tab y a) cl) ↔
      (∀ cl ∈ c.gateCs, ClauseSat (c.asg tab y a) cl) ∧
      (∀ cl ∈ c.outCs, ClauseSat (c.asg tab y a) cl) ∧
      (∀ cl ∈ c.rowCs, ClauseSat (c.asg tab y a) cl) := by
    unfold Fp
    simp only [Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun cl h1 => h cl (Or.inl (Or.inl h1)), fun cl h1 => h cl (Or.inl (Or.inr h1)),
        fun cl h1 => h cl (Or.inr h1)⟩
    · rintro ⟨h1, h2, h3⟩ cl ((hc | hc) | hc)
      · exact h1 cl hc
      · exact h2 cl hc
      · exact h3 cl hc
  rw [hF, gate_part hrb hshape, out_part, row_part]
  have hlt : ∀ i (h : i < c.n), c.asg tab y a (c.wv i) = a (Sum.inl ⟨i, h⟩) := by
    intro i h; unfold wv; rw [dif_pos h]; rfl
  have hge : ∀ i (h1 : ¬ i < c.n) (h2 : i - c.n < c.enc.size),
      c.asg tab y a (c.wv i) = a (Sum.inr (Sum.inl ⟨i - c.n, h2⟩)) := by
    intro i h1 h2; unfold wv; rw [dif_neg h1, dif_pos h2]; rfl
  have hall : (∀ j : Fin c.enc.size, a (Sum.inr (Sum.inl j)) =
      (c.enc.wires (List.ofFn fun i => a (Sum.inl i))).getD (c.n + j.val) false) →
      ∀ i < c.n + c.enc.size, c.asg tab y a (c.wv i) =
        (c.enc.wires (List.ofFn fun i => a (Sum.inl i))).getD i false := by
    intro h i hi
    by_cases h1 : i < c.n
    · rw [hlt i h1, wires_input]
    · rw [hge i h1 (by omega), h ⟨i - c.n, by omega⟩]
      congr 1; show c.n + (i - c.n) = i; omega
  constructor
  · rintro ⟨hg, ho, hr⟩
    have haux := fun r => row_canon tab y a r (hr r).2
    refine ⟨?_, ?_, ?_⟩
    · funext p
      rcases p with i | j | ⟨r, nd⟩
      · rfl
      · exact hg j
      · exact haux r nd
    · intro e he
      funext j
      have := ho (⟨e, he⟩, j)
      rw [hall hg _ (c.out e j).isLt, hout] at this
      exact this
    · intro r
      have h1 := (hr r).1
      rw [show c.asg tab y a (c.auxV r c.rootN) = a (Sum.inr (Sum.inr (r, c.rootN))) from rfl,
        haux r] at h1
      have h1' : c.cM tab (fun i => a (Sum.inl i)) r 0 0 = true := h1
      rw [cM_zero] at h1'
      exact h1'
  · rintro ⟨ha, hchk⟩
    have hg : ∀ j : Fin c.enc.size, a (Sum.inr (Sum.inl j)) =
        (c.enc.wires (List.ofFn fun i => a (Sum.inl i))).getD (c.n + j.val) false :=
      fun j => congrFun ha (Sum.inr (Sum.inl j))
    have haux : ∀ r nd, a (Sum.inr (Sum.inr (r, nd))) =
        c.cM tab (fun i => a (Sum.inl i)) r nd.1.val nd.2.val :=
      fun r nd => congrFun ha (Sum.inr (Sum.inr (r, nd)))
    refine ⟨hg, ?_, ?_⟩
    · intro q
      rw [hall hg _ (c.out q.1.1 q.2).isLt, hout, hchk.1 q.1.1 q.1.2]
    · intro r
      refine ⟨?_, ?_⟩
      · show a (Sum.inr (Sum.inr (r, c.rootN))) = true
        rw [haux r]
        show c.cM tab _ r 0 0 = true
        rw [cM_zero]
        exact hchk.2 r
      · intro nd
        show a (Sum.inr (Sum.inr (r, nd))) = _
        rw [haux r nd, nodeV_val tab y a r (haux r) _ (by have := nd.1.isLt; omega) _
          (by have := nd.2.isLt; rw [pow_succ]; omega),
          nodeV_val tab y a r (haux r) _ (by have := nd.1.isLt; omega) _
          (by have := nd.2.isLt; rw [pow_succ]; omega)]
        exact cM_step tab _ r _ _ nd.2.isLt

theorem Fp_card3 : ∀ cl ∈ c.Fp, cl.card ≤ 3 := by
  intro cl hcl
  unfold Fp gateCs outCs rowCs at hcl
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert] at hcl
  rcases hcl with ((⟨j, hj⟩ | ⟨q, hq⟩) | ⟨r, hr | ⟨nd, hnd⟩⟩)
  · exact (gateClauses_card_le _ _ _).2 cl hj
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> exact le_trans Finset.card_le_two (by norm_num)
  · subst hr; simp
  · unfold muxC at hnd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnd
    rcases hnd with rfl | rfl | rfl | rfl <;> exact Finset.card_le_three

theorem card_node : Fintype.card c.Node ≤ 2 ^ c.d := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) c.d, Nat.geomSum_eq (le_refl 2)]
  simp

theorem card_P : Fintype.card c.P ≤ c.n + c.enc.size + c.n * 2 ^ c.d := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  have h1 : Fintype.card c.Row ≤ c.n := by
    have := Fintype.card_subtype_le (fun r : Fin c.n => c.owner r = c.o)
    simpa using this
  have h2 := card_node (c := c)
  have := Nat.mul_le_mul h1 h2
  omega

theorem card_Fp : c.Fp.card ≤ 3 * c.enc.size + 6 * c.k + c.n * (1 + 4 * 2 ^ c.d) := by
  unfold Fp
  have h1 : c.gateCs.card ≤ 3 * c.enc.size := by
    unfold gateCs
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 3
      (fun j _ => (gateClauses_card_le _ _ _).1)) ?_
    simp [Nat.mul_comm]
  have h2 : c.outCs.card ≤ 6 * c.k := by
    unfold outCs
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 2
      (fun q _ => Finset.card_le_two)) ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    have : Fintype.card {e : Fin 3 // e = c.o ∨ e + 1 = c.o} ≤ 3 := by
      have := Fintype.card_subtype_le (fun e : Fin 3 => e = c.o ∨ e + 1 = c.o)
      simpa using this
    have := Nat.mul_le_mul_right c.k this
    omega
  have h3 : c.rowCs.card ≤ c.n * (1 + 4 * 2 ^ c.d) := by
    unfold rowCs
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ (1 + 4 * 2 ^ c.d) (fun r _ => ?_)) ?_
    · refine le_trans (Finset.card_insert_le _ _) ?_
      have : (Finset.univ.biUnion fun nd : c.Node => c.muxC r nd).card ≤ 4 * 2 ^ c.d := by
        refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 (fun nd _ => ?_)) ?_
        · unfold muxC; exact Finset.card_le_four
        · rw [Finset.card_univ, Nat.mul_comm]
          exact Nat.mul_le_mul_left 4 card_node
      omega
    · rw [Finset.card_univ]
      apply Nat.mul_le_mul_right
      have := Fintype.card_subtype_le (fun r : Fin c.n => c.owner r = c.o)
      simpa using this
  have := Finset.card_union_le (c.gateCs ∪ c.outCs) c.rowCs
  have := Finset.card_union_le c.gateCs c.outCs
  omega

end Cfg

theorem cnf_part (n k : ℕ) (enc : Circuit) (out : Fin 3 → Fin k → Fin (n+enc.size))
    (code : (Fin n → Bool) → Fin 3 → Fin k → Bool)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n enc)
    (hshape : ∀ g ∈ enc.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
    (hout : ∀ (u : Fin n → Bool) (e : Fin 3) (j : Fin k),
      (enc.wires (List.ofFn u)).getD (out e j).val false = code u e j)
    (htri : ∀ v : Fin 3 → (Fin n → Bool), (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) →
      ∀ p, v p = v 0) :
    ∀ (hn : 0 < n) (w : ℕ) (owner : Fin n → Fin 3),
      let Pattern := Fin (w+1) → Bool
      let pos := fun (r : Fin n) (off : Fin (w+1)) =>
        (⟨(r.val+off.val)%n, Nat.mod_lt _ hn⟩ : Fin n)
      let V := fun (party : Fin 3) (q : ℕ) =>
        Sum ({r : Fin n // owner r = party} × Pattern)
          (Sum ({e : Fin 3 // e = party ∨ e+1 = party} × Fin k) (Fin q))
      ∃ (priv : Fin 3 → ℕ) (F : (o : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause (V o (priv o)))),
        (∀ o, ∀ cl ∈ F o, cl.card ≤ 3) ∧
        (∑ o : Fin 3, (priv o + (F o).card)) ≤ 128*(n*2^(min n (w+1)) + n + k + enc.size + 1) ∧
        ∀ (tab : Fin n → Pattern → Bool) (y : Fin 3 → Fin k → Bool),
          let passes := fun loc : (o : Fin 3) → Fin (priv o) → Bool =>
            ∀ o : Fin 3, PEqualNP.ProofComplexity.Satisfies
              (Sum.elim (fun h : {r : Fin n // owner r = o} × Pattern => tab h.1.val h.2)
                (Sum.elim (fun bit : {e : Fin 3 // e = o ∨ e+1 = o} × Fin k =>
                  y bit.1.val bit.2) (loc o))) (↑(F o) : Set _)
          (@Finset.filter _ passes (Classical.decPred _) Finset.univ).card =
            (Finset.univ.filter (fun x : Fin n → Bool => code x = y ∧
              ∀ row : Fin n, tab row (fun delta => x (pos row delta)) = true)).card := by
  intro hn w owner Pattern pos V
  classical
  let cf : Fin 3 → Cfg := fun o => ⟨n, k, w, enc, owner, o, hn, out⟩
  let priv : Fin 3 → ℕ := fun o => Fintype.card (cf o).P
  let eo : (o : Fin 3) → (cf o).P ≃ Fin (priv o) := fun o => Fintype.equivFin _
  let f : (o : Fin 3) → (cf o).V → V o (priv o) := fun o => Sum.map id (Sum.map id (eo o))
  refine ⟨priv, fun o => mapF (f o) (cf o).Fp, ?_, ?_, ?_⟩
  · intro o
    exact mapF_card3 (f o) _ (Cfg.Fp_card3 (c := cf o))
  · have hb : ∀ o, priv o + (mapF (f o) (cf o).Fp).card ≤
        4 * n + 4 * enc.size + 6 * k + 5 * (n * 2 ^ (min n (w+1))) := by
      intro o
      have h1 : priv o ≤ n + enc.size + n * 2 ^ (min n (w+1)) := Cfg.card_P (c := cf o)
      have h2 : (mapF (f o) (cf o).Fp).card ≤ 3 * enc.size + 6 * k + n * (1 + 4 * 2 ^ (min n (w+1))) :=
        le_trans (mapF_card_le _ _) (Cfg.card_Fp (c := cf o))
      have : n * (1 + 4 * 2 ^ (min n (w+1))) = n + 4 * (n * 2 ^ (min n (w+1))) := by ring
      omega
    calc (∑ o : Fin 3, (priv o + (mapF (f o) (cf o).Fp).card))
        ≤ ∑ _o : Fin 3, (4 * n + 4 * enc.size + 6 * k + 5 * (n * 2 ^ (min n (w+1)))) :=
          Finset.sum_le_sum (fun o _ => hb o)
      _ ≤ 128*(n*2^(min n (w+1)) + n + k + enc.size + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          omega
  · intro tab y
    intro passes
    have hpass : ∀ loc : (o : Fin 3) → Fin (priv o) → Bool, passes loc ↔
        ∀ o, (loc o ∘ eo o) = (cf o).canon tab (fun i => loc o (eo o (Sum.inl i))) ∧
          (cf o).chk code tab y (fun i => loc o (eo o (Sum.inl i))) := by
      intro loc
      apply forall_congr'
      intro o
      rw [mapF_sat]
      have hc : (Sum.elim (fun h : {r : Fin n // owner r = o} × Pattern => tab h.1.val h.2)
          (Sum.elim (fun bit : {e : Fin 3 // e = o ∨ e+1 = o} × Fin k =>
            y bit.1.val bit.2) (loc o))) ∘ f o = (cf o).asg tab y (loc o ∘ eo o) := by
        funext v
        rcases v with v | v | v <;> rfl
      rw [hc]
      exact Cfg.party (c := cf o) hrb hshape code hout tab y (loc o ∘ eo o)
    refine Finset.card_nbij' (fun loc => fun i => loc 0 (eo 0 (Sum.inl i)))
      (fun x o => (cf o).canon tab x ∘ (eo o).symm) ?_ ?_ ?_ ?_
    · intro loc hloc
      rw [Finset.mem_coe, mem_filter_any] at hloc
      have hloc' := (hpass loc).1 hloc.2
      obtain ⟨X, hX⟩ : ∃ X : Fin 3 → Fin n → Bool, X = fun o i => loc o (eo o (Sum.inl i)) :=
        ⟨_, rfl⟩
      have hc : ∀ o, (cf o).chk code tab y (X o) := by intro o; rw [hX]; exact (hloc' o).2
      have hag := parties_agree code htri X y (fun o e he => (hc o).1 e he)
      have hc0 : ∀ o, (cf o).chk code tab y (X 0) := by intro o; rw [← hag o]; exact hc o
      have hvalid : code (X 0) = y ∧
          ∀ row : Fin n, tab row (fun delta => X 0 (pos row delta)) = true :=
        ⟨(code_eq_of_parties code _ y).1 (fun o e he => (hc0 o).1 e he),
          fun row => (hc0 (owner row)).2 ⟨row, rfl⟩⟩
      rw [hX] at hvalid
      rw [Finset.mem_coe, mem_filter_any]
      exact ⟨Finset.mem_univ _, hvalid⟩
    · intro x hx
      rw [Finset.mem_coe, mem_filter_any] at hx
      rw [Finset.mem_coe, mem_filter_any]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hpass]
      intro o
      have he : ((cf o).canon tab x ∘ (eo o).symm) ∘ eo o = (cf o).canon tab x := by
        funext p; simp
      have hx' : (fun i => ((cf o).canon tab x ∘ (eo o).symm) (eo o (Sum.inl i))) = x := by
        funext i; simp [Cfg.canon]
      refine ⟨?_, ?_⟩
      · show ((cf o).canon tab x ∘ (eo o).symm) ∘ eo o = (cf o).canon tab
          (fun i => ((cf o).canon tab x ∘ (eo o).symm) (eo o (Sum.inl i)))
        rw [congrArg ((cf o).canon tab) hx', he]
      · show (cf o).chk code tab y (fun i => ((cf o).canon tab x ∘ (eo o).symm) (eo o (Sum.inl i)))
        rw [congrArg ((cf o).chk code tab y) hx']
        exact ⟨fun e _ => by rw [hx.2.1], fun r => hx.2.2 r.1⟩
    · intro loc hloc
      rw [Finset.mem_coe, mem_filter_any] at hloc
      have hloc' := (hpass loc).1 hloc.2
      obtain ⟨X, hX⟩ : ∃ X : Fin 3 → Fin n → Bool, X = fun o i => loc o (eo o (Sum.inl i)) :=
        ⟨_, rfl⟩
      have hc : ∀ o, (cf o).chk code tab y (X o) := by intro o; rw [hX]; exact (hloc' o).2
      have hag := parties_agree code htri X y (fun o e he => (hc o).1 e he)
      funext o p
      have hag' : (fun i => loc o (eo o (Sum.inl i))) = (fun i => loc 0 (eo 0 (Sum.inl i))) := by
        have := hag o; rw [hX] at this; exact this
      have key : (cf o).canon tab (fun i => loc 0 (eo 0 (Sum.inl i))) =
          (cf o).canon tab (fun i => loc o (eo o (Sum.inl i))) :=
        congrArg ((cf o).canon tab) hag'.symm
      have h1 := congrFun (hloc' o).1 ((eo o).symm p)
      simp only [Function.comp, Equiv.apply_symm_apply] at h1
      show ((cf o).canon tab (fun i => loc 0 (eo 0 (Sum.inl i))) ∘ (eo o).symm) p = loc o p
      rw [Function.comp_apply, key]
      exact h1.symm
    · intro x _
      funext i
      simp [Cfg.canon]

/-! ## Circuit builder -/

def Sh (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

/-- The gates of `hs`, placed after `m` wires, read only earlier wires and have the right shape. -/
def OkFrom (m : ℕ) (hs : List Gate) : Prop :=
  ∀ q (h : q < hs.length), (∀ i ∈ hs[q].inputs, i < m + q) ∧ Sh hs[q]

theorem OkFrom_append {m : ℕ} {gs hs : List Gate} (h1 : OkFrom m gs)
    (h2 : OkFrom (m + gs.length) hs) : OkFrom m (gs ++ hs) := by
  intro q hq
  rw [List.length_append] at hq
  by_cases hlt : q < gs.length
  · rw [List.getElem_append_left hlt]; exact h1 q hlt
  · rw [List.getElem_append_right (by omega)]
    obtain ⟨h3, h4⟩ := h2 (q - gs.length) (by omega)
    refine ⟨fun i hi => ?_, h4⟩
    have := h3 i hi; omega

def E {n : ℕ} (gs : List Gate) (u : Fin n → Bool) (i : ℕ) : Bool :=
  (W gs (List.ofFn u)).getD i false

theorem E_append {n : ℕ} (gs hs : List Gate) (u : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) : E (gs ++ hs) u i = E gs u i :=
  W_getD_append gs hs _ i (by simp; exact hi)

theorem E_app3 {n : ℕ} (a b c : List Gate) (u : Fin n → Bool) (i : ℕ) (hi : i < n + a.length) :
    E (a ++ b ++ c) u i = E a u i := by
  rw [E_append (a ++ b) c u i (by simp only [List.length_append]; omega), E_append a b u i hi]

theorem E_input {n : ℕ} (gs : List Gate) (u : Fin n → Bool) (i : ℕ) (hi : i < n) :
    E gs u i = u ⟨i, hi⟩ := wires_input ⟨gs, 0⟩ u i hi

theorem E_gate {n : ℕ} (gs hs : List Gate) (u : Fin n → Bool) (q : ℕ) (hq : q < hs.length)
    (hin : ∀ i ∈ hs[q].inputs, i < n + gs.length + q) :
    E (gs ++ hs) u (n + gs.length + q) = hs[q].op.eval (hs[q].inputs.map (E (gs ++ hs) u)) := by
  have hga : gateAt ⟨gs ++ hs, 0⟩ (gs.length + q) = hs[q] := by
    unfold gateAt
    show (gs ++ hs).getD (gs.length + q) _ = _
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ hq]
  have := wires_gate ⟨gs ++ hs, 0⟩ (List.ofFn u) (gs.length + q)
    (by show gs.length + q < (gs ++ hs).length; simp only [List.length_append]; omega)
    (by rw [hga]; intro i hi; have := hin i hi; simp only [List.length_ofFn]; omega)
  rw [hga] at this
  simp only [List.length_ofFn] at this
  unfold E
  rw [show n + gs.length + q = n + (gs.length + q) by omega]
  exact this

theorem E_gate' {n : ℕ} (gs hs : List Gate) (u : Fin n → Bool) (q : ℕ) (g : Gate)
    (hq : q < hs.length) (hg : hs[q] = g) (hin : ∀ i ∈ g.inputs, i < n + gs.length + q) :
    E (gs ++ hs) u (n + gs.length + q) = g.op.eval (g.inputs.map (E (gs ++ hs) u)) := by
  subst hg; exact E_gate gs hs u q hq hin

/-! ### Bit vectors -/

def bval (ρ : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | a :: as => (ρ a).toNat + 2 * bval ρ as

theorem bval_congr {ρ ρ' : ℕ → Bool} : ∀ {as : List ℕ}, (∀ i ∈ as, ρ i = ρ' i) →
    bval ρ as = bval ρ' as
  | [], _ => rfl
  | a :: as, h => by
    simp only [bval]
    rw [h a (List.mem_cons_self ..), bval_congr (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem bval_lt (ρ : ℕ → Bool) : ∀ as : List ℕ, bval ρ as < 2 ^ as.length
  | [] => by simp [bval]
  | a :: as => by
    simp only [bval, List.length_cons, pow_succ]
    have := bval_lt ρ as
    have : (ρ a).toNat ≤ 1 := Bool.toNat_le _
    omega

theorem bval_append (ρ : ℕ → Bool) : ∀ as bs : List ℕ,
    bval ρ (as ++ bs) = bval ρ as + 2 ^ as.length * bval ρ bs
  | [], bs => by simp [bval]
  | a :: as, bs => by
    simp only [List.cons_append, bval, List.length_cons, pow_succ]
    rw [bval_append ρ as bs]; ring

theorem bval_zeros (ρ : ℕ → Bool) (z : ℕ) (hz : ρ z = false) : ∀ m,
    bval ρ (List.replicate m z) = 0
  | 0 => rfl
  | m+1 => by simp [List.replicate_succ, bval, hz, bval_zeros ρ z hz m]

theorem bval_inj {ρ ρ' : ℕ → Bool} : ∀ {as : List ℕ}, bval ρ as = bval ρ' as →
    ∀ i ∈ as, ρ i = ρ' i
  | [], _ => by simp
  | a :: as, h => by
    simp only [bval] at h
    have t1 := Bool.toNat_le (ρ a)
    have t2 := Bool.toNat_le (ρ' a)
    have h1 : (ρ a).toNat = (ρ' a).toNat := by omega
    have h2 : bval ρ as = bval ρ' as := by omega
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · cases hρ : ρ i <;> cases hρ' : ρ' i <;> simp_all
    · exact bval_inj h2 i hi

theorem bval_range' (ρ ρ0 : ℕ → Bool) (s : Bool) : ∀ (l : List ℕ) (m : ℕ),
    (∀ q (hq : q < l.length), ρ (m + q) = (s && ρ0 l[q])) →
    bval ρ (List.range' m l.length) = if s then bval ρ0 l else 0
  | [], m, _ => by simp [bval]
  | v :: l, m, h => by
    rw [List.length_cons, List.range'_succ]
    simp only [bval]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, bval_range' ρ ρ0 s l (m+1) (fun q hq => by
      rw [show m + 1 + q = m + (q + 1) by omega]
      have := h (q+1) (by simp; omega)
      rw [List.getElem_cons_succ] at this
      exact this)]
    cases s <;> simp

/-! ### Zero wire -/

def zg (n : ℕ) : List Gate := [⟨.not, [0]⟩, ⟨.and, [0, n]⟩]

theorem zg_ok {n : ℕ} (hn : 0 < n) : OkFrom n (zg n) := by
  intro q hq
  simp only [zg, List.length_cons, List.length_nil] at hq
  interval_cases q
  · refine ⟨?_, Or.inr ⟨rfl, rfl⟩⟩
    intro i hi; simp [zg] at hi; omega
  · refine ⟨?_, Or.inl ⟨Or.inl rfl, rfl⟩⟩
    intro i hi; simp [zg] at hi; omega

theorem zg_val {n : ℕ} (hn : 0 < n) (u : Fin n → Bool) : E (zg n) u (n + 1) = false := by
  have h0 := E_gate' [] (zg n) u 0 ⟨.not, [0]⟩ (by simp [zg]) rfl (by simpa using hn)
  have h1 := E_gate' [] (zg n) u 1 ⟨.and, [0, n]⟩ (by simp [zg]) rfl (by simp)
  simp only [List.nil_append, List.length_nil, Nat.add_zero, GateOp.eval, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, List.headD_cons, id, Bool.and_true] at h0 h1
  rw [h1, h0]; cases E (zg n) u 0 <;> rfl

/-! ### Full adder and ripple adder -/

def fa (a b c m : ℕ) : List Gate :=
  [⟨.or, [a, b]⟩, ⟨.and, [a, b]⟩, ⟨.not, [m+1]⟩, ⟨.and, [m, m+2]⟩, ⟨.or, [m+3, c]⟩,
   ⟨.and, [m+3, c]⟩, ⟨.not, [m+5]⟩, ⟨.and, [m+4, m+6]⟩, ⟨.or, [m+1, m+5]⟩]

theorem fa_len (a b c m : ℕ) : (fa a b c m).length = 9 := rfl

theorem fa_ok (a b c m : ℕ) (ha : a < m) (hb : b < m) (hc : c < m) : OkFrom m (fa a b c m) := by
  intro q hq
  rw [fa_len] at hq
  interval_cases q <;> refine ⟨?_, by simp [fa, Sh]⟩ <;> intro i hi <;> simp [fa] at hi <;> omega

theorem fa_sem {n : ℕ} (gs : List Gate) (u : Fin n → Bool) (a b c m : ℕ)
    (hm : n + gs.length = m) (ha : a < m) (hb : b < m) (hc : c < m) :
    (E (gs ++ fa a b c m) u (m + 7)).toNat + 2 * (E (gs ++ fa a b c m) u (m + 8)).toNat =
      (E gs u a).toNat + (E gs u b).toNat + (E gs u c).toNat := by
  have g : ∀ (q : ℕ) (g : Gate) (hq : q < (fa a b c m).length), (fa a b c m)[q] = g →
      (∀ i ∈ g.inputs, i < m + q) →
      E (gs ++ fa a b c m) u (m + q) = g.op.eval (g.inputs.map (E (gs ++ fa a b c m) u)) := by
    intro q g hq hg hin
    have := E_gate' gs (fa a b c m) u q g hq hg (by rw [hm]; exact hin)
    rw [hm] at this; exact this
  have e0 := g 0 ⟨.or, [a, b]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e1 := g 1 ⟨.and, [a, b]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e2 := g 2 ⟨.not, [m+1]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e3 := g 3 ⟨.and, [m, m+2]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e4 := g 4 ⟨.or, [m+3, c]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e5 := g 5 ⟨.and, [m+3, c]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e6 := g 6 ⟨.not, [m+5]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e7 := g 7 ⟨.and, [m+4, m+6]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have e8 := g 8 ⟨.or, [m+1, m+5]⟩ (by simp [fa]) rfl (by intro i hi; simp at hi; omega)
  have pa : E (gs ++ fa a b c m) u a = E gs u a := E_append _ _ _ _ (by omega)
  have pb : E (gs ++ fa a b c m) u b = E gs u b := E_append _ _ _ _ (by omega)
  have pc : E (gs ++ fa a b c m) u c = E gs u c := E_append _ _ _ _ (by omega)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, List.headD_cons, id, Bool.and_true, Bool.or_false,
    Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7 e8
  rw [e7, e8, e4, e6, e5, e3, e0, e2, e1, pa, pb, pc]
  cases E gs u a <;> cases E gs u b <;> cases E gs u c <;> rfl

theorem adder_ex {n : ℕ} : ∀ (as bs : List ℕ) (gs : List Gate) (c : ℕ),
    as.length = bs.length → OkFrom n gs → (∀ i ∈ as, i < n + gs.length) →
    (∀ i ∈ bs, i < n + gs.length) → c < n + gs.length →
    ∃ hs ss cout, hs.length = 9 * as.length ∧ OkFrom n (gs ++ hs) ∧ ss.length = as.length ∧
      (∀ i ∈ ss, i < n + (gs ++ hs).length) ∧ cout < n + (gs ++ hs).length ∧
      ∀ u : Fin n → Bool, bval (E (gs ++ hs) u) ss + 2 ^ as.length * (E (gs ++ hs) u cout).toNat =
        bval (E gs u) as + bval (E gs u) bs + (E gs u c).toNat := by
  intro as
  induction as with
  | nil =>
    intro bs gs c hl hok _ _ hc
    have hbs : bs = [] := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp at hl
    subst hbs
    refine ⟨[], [], c, by simp, by simpa using hok, rfl, by simp, by simpa using hc, ?_⟩
    intro u; simp [bval]
  | cons a as ih =>
    intro bs gs c hl hok has hbs hc
    obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons b bs' => exact ⟨b, bs', rfl⟩
    have ha : a < n + gs.length := has a (by simp)
    have hb : b < n + gs.length := hbs b (by simp)
    have hok1 : OkFrom n (gs ++ fa a b c (n + gs.length)) :=
      OkFrom_append hok (fa_ok a b c _ ha hb hc)
    have hlen1 : (gs ++ fa a b c (n + gs.length)).length = gs.length + 9 := by simp [fa_len]
    obtain ⟨hs, ss, cout, h1, h2, h3, h4, h5, h6⟩ := ih bs' (gs ++ fa a b c (n + gs.length))
      (n + gs.length + 8) (by simpa using hl) hok1
      (fun i hi => by have := has i (by simp [hi]); rw [hlen1]; omega)
      (fun i hi => by have := hbs i (by simp [hi]); rw [hlen1]; omega)
      (by rw [hlen1]; omega)
    refine ⟨fa a b c (n + gs.length) ++ hs, (n + gs.length + 7) :: ss, cout, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, fa_len, h1, List.length_cons]; ring
    · rw [← List.append_assoc]; exact h2
    · simp [h3]
    · intro i hi
      rw [← List.append_assoc]
      rcases List.mem_cons.1 hi with rfl | hi
      · simp only [List.length_append] at hlen1 ⊢; omega
      · exact h4 i hi
    · rw [← List.append_assoc]; exact h5
    · intro u
      rw [← List.append_assoc]
      have hfa := fa_sem gs u a b c (n + gs.length) rfl ha hb hc
      have h6u := h6 u
      have e7 : E ((gs ++ fa a b c (n + gs.length)) ++ hs) u (n + gs.length + 7) =
          E (gs ++ fa a b c (n + gs.length)) u (n + gs.length + 7) :=
        E_append _ _ _ _ (by rw [hlen1]; omega)
      have hA : bval (E (gs ++ fa a b c (n + gs.length)) u) as = bval (E gs u) as :=
        bval_congr (fun i hi => E_append _ _ _ _ (has i (by simp [hi])))
      have hB : bval (E (gs ++ fa a b c (n + gs.length)) u) bs' = bval (E gs u) bs' :=
        bval_congr (fun i hi => E_append _ _ _ _ (hbs i (by simp [hi])))
      rw [hA, hB] at h6u
      simp only [bval, List.length_cons, pow_succ]
      rw [e7]
      generalize bval (E ((gs ++ fa a b c (n + gs.length)) ++ hs) u) ss = S at h6u ⊢
      generalize (E ((gs ++ fa a b c (n + gs.length)) ++ hs) u cout).toNat = Co at h6u ⊢
      generalize 2 ^ as.length = P at h6u ⊢
      rw [show P * 2 * Co = 2 * (P * Co) by ring]
      generalize P * Co = X at h6u ⊢
      omega

theorem adder_mod {n : ℕ} (as bs : List ℕ) (gs : List Gate) (c : ℕ)
    (hl : as.length = bs.length) (hok : OkFrom n gs) (has : ∀ i ∈ as, i < n + gs.length)
    (hbs : ∀ i ∈ bs, i < n + gs.length) (hc : c < n + gs.length) :
    ∃ hs ss, hs.length = 9 * as.length ∧ OkFrom n (gs ++ hs) ∧ ss.length = as.length ∧
      (∀ i ∈ ss, i < n + (gs ++ hs).length) ∧
      ∀ u : Fin n → Bool, bval (E (gs ++ hs) u) ss =
        (bval (E gs u) as + bval (E gs u) bs + (E gs u c).toNat) % 2 ^ as.length := by
  obtain ⟨hs, ss, cout, h1, h2, h3, h4, _, h6⟩ := adder_ex as bs gs c hl hok has hbs hc
  refine ⟨hs, ss, h1, h2, h3, h4, fun u => ?_⟩
  rw [← h6 u, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  rw [← h3]; exact bval_lt _ _

/-! ### Rows of shifted products -/

def ands (s : ℕ) (sw : List ℕ) : List Gate := sw.map fun v => ⟨.and, [s, v]⟩

theorem ands_ok (m s : ℕ) (sw : List ℕ) (hs : s < m) (hsw : ∀ i ∈ sw, i < m) :
    OkFrom m (ands s sw) := by
  intro q hq
  simp only [ands, List.length_map] at hq
  simp only [ands, List.getElem_map]
  refine ⟨?_, Or.inl ⟨Or.inl rfl, rfl⟩⟩
  intro i hi
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · omega
  · have := hsw sw[q] (List.getElem_mem hq); omega

theorem ands_val {n : ℕ} (gs : List Gate) (u : Fin n → Bool) (s : ℕ) (sw : List ℕ)
    (hs : s < n + gs.length) (hsw : ∀ i ∈ sw, i < n + gs.length) :
    bval (E (gs ++ ands s sw) u) (List.range' (n + gs.length) sw.length) =
      if E gs u s then bval (E gs u) sw else 0 := by
  apply bval_range'
  intro q hq
  have hq' : q < (ands s sw).length := by simp [ands]; exact hq
  rw [E_gate' gs (ands s sw) u q ⟨.and, [s, sw[q]]⟩ hq' (by simp [ands])
    (by
      intro i hi
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · have := hsw sw[q] (List.getElem_mem hq); omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
    Bool.and_true]
  rw [E_append gs _ u s hs, E_append gs _ u _ (hsw _ (List.getElem_mem hq))]

theorem step_ex {n : ℕ} (gs : List Gate) (acc : List ℕ) (L : ℕ) (s j : ℕ) (sw : List ℕ)
    (z : ℕ) (hok : OkFrom n gs) (hacc : acc.length = L) (haccw : ∀ i ∈ acc, i < n + gs.length)
    (hs : s < n + gs.length) (hsw : ∀ i ∈ sw, i < n + gs.length) (hz : z < n + gs.length)
    (hzv : ∀ u : Fin n → Bool, E gs u z = false) (hjL : j + sw.length ≤ L) :
    ∃ hs' acc', hs'.length = sw.length + 9 * L ∧ OkFrom n (gs ++ hs') ∧ acc'.length = L ∧
      (∀ i ∈ acc', i < n + (gs ++ hs').length) ∧
      ∀ u : Fin n → Bool, bval (E (gs ++ hs') u) acc' =
        (bval (E gs u) acc + if E gs u s then 2 ^ j * bval (E gs u) sw else 0) % 2 ^ L := by
  have hok1 : OkFrom n (gs ++ ands s sw) := OkFrom_append hok (ands_ok _ s sw hs hsw)
  have hlen1 : (gs ++ ands s sw).length = gs.length + sw.length := by simp [ands]
  have hR : (List.replicate j z ++ List.range' (n + gs.length) sw.length ++
      List.replicate (L - j - sw.length) z).length = L := by simp; omega
  have hRw : ∀ i ∈ List.replicate j z ++ List.range' (n + gs.length) sw.length ++
      List.replicate (L - j - sw.length) z, i < n + (gs ++ ands s sw).length := by
    intro i hi
    simp only [List.mem_append, List.mem_replicate, List.mem_range'_1] at hi
    rw [hlen1]; omega
  obtain ⟨hs2, ss, h1, h2, h3, h4, h6⟩ := adder_mod acc
    (List.replicate j z ++ List.range' (n + gs.length) sw.length ++
      List.replicate (L - j - sw.length) z) (gs ++ ands s sw) z (by rw [hacc, hR]) hok1
    (fun i hi => by have := haccw i hi; rw [hlen1]; omega) hRw (by rw [hlen1]; omega)
  refine ⟨ands s sw ++ hs2, ss, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, ands, List.length_map, h1, hacc]
  · rw [← List.append_assoc]; exact h2
  · rw [h3, hacc]
  · rw [← List.append_assoc]; exact h4
  · intro u
    rw [← List.append_assoc, h6 u, hacc]
    have e1 : bval (E (gs ++ ands s sw) u) acc = bval (E gs u) acc :=
      bval_congr (fun i hi => E_append _ _ _ _ (haccw i hi))
    have e2 : E (gs ++ ands s sw) u z = false := by rw [E_append _ _ _ _ hz, hzv]
    have e3 : bval (E (gs ++ ands s sw) u) (List.replicate j z ++
        List.range' (n + gs.length) sw.length ++ List.replicate (L - j - sw.length) z) =
        if E gs u s then 2 ^ j * bval (E gs u) sw else 0 := by
      rw [bval_append, bval_append, bval_zeros _ z e2, bval_zeros _ z e2, ands_val gs u s sw hs hsw]
      simp only [List.length_replicate, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
      split_ifs <;> simp
    rw [e1, e2, e3]; simp

/-! ### Chains of row additions -/

def term (ρ : ℕ → Bool) (sp : ℕ × ℕ × List ℕ) : ℕ :=
  if ρ sp.1 then 2 ^ sp.2.1 * bval ρ sp.2.2 else 0

def termsum (ρ : ℕ → Bool) (specs : List (ℕ × ℕ × List ℕ)) : ℕ := (specs.map (term ρ)).sum

theorem chain_ex {n : ℕ} (L b z : ℕ) : ∀ (specs : List (ℕ × ℕ × List ℕ)) (gs : List Gate)
    (acc : List ℕ), OkFrom n gs → acc.length = L → (∀ i ∈ acc, i < n + gs.length) →
    z < n + gs.length → (∀ u : Fin n → Bool, E gs u z = false) →
    (∀ sp ∈ specs, sp.1 < n + gs.length ∧ (∀ i ∈ sp.2.2, i < n + gs.length) ∧
      sp.2.2.length = b ∧ sp.2.1 + b ≤ L) →
    ∃ hs acc', hs.length = specs.length * (b + 9 * L) ∧ OkFrom n (gs ++ hs) ∧
      acc'.length = L ∧ (∀ i ∈ acc', i < n + (gs ++ hs).length) ∧
      ∀ u : Fin n → Bool, bval (E (gs ++ hs) u) acc' =
        (bval (E gs u) acc + termsum (E gs u) specs) % 2 ^ L := by
  intro specs
  induction specs with
  | nil =>
    intro gs acc hok hacc haccw _ _ _
    refine ⟨[], acc, by simp, by simpa using hok, hacc, by simpa using haccw, fun u => ?_⟩
    simp only [List.append_nil, termsum, List.map_nil, List.sum_nil, Nat.add_zero]
    rw [Nat.mod_eq_of_lt]; rw [← hacc]; exact bval_lt _ _
  | cons sp specs ih =>
    intro gs acc hok hacc haccw hz hzv hsp
    obtain ⟨h1s, h2s, h3s, h4s⟩ := hsp sp (List.mem_cons_self ..)
    obtain ⟨hs1, acc1, a1, a2, a3, a4, a6⟩ := step_ex gs acc L sp.1 sp.2.1 sp.2.2 z hok hacc
      haccw h1s h2s hz hzv (by rw [h3s]; exact h4s)
    have hgrow : n + gs.length ≤ n + (gs ++ hs1).length := by
      simp only [List.length_append]; omega
    obtain ⟨hs2, acc2, b1, b2, b3, b4, b6⟩ := ih (gs ++ hs1) acc1 a2 a3 a4 (by omega)
      (fun u => by rw [E_append _ _ _ _ hz, hzv])
      (fun sp' hsp' => by
        obtain ⟨c1, c2, c3, c4⟩ := hsp sp' (List.mem_cons_of_mem _ hsp')
        exact ⟨by omega, fun i hi => by have := c2 i hi; omega, c3, c4⟩)
    refine ⟨hs1 ++ hs2, acc2, ?_, ?_, b3, ?_, ?_⟩
    · simp only [List.length_append, a1, b1, h3s, List.length_cons]; ring
    · rw [← List.append_assoc]; exact b2
    · rw [← List.append_assoc]; exact b4
    · intro u
      rw [← List.append_assoc, b6 u, a6 u]
      have hts : termsum (E (gs ++ hs1) u) specs = termsum (E gs u) specs := by
        unfold termsum; congr 1; apply List.map_congr_left; intro sp' hsp'
        obtain ⟨c1, c2, _, _⟩ := hsp sp' (List.mem_cons_of_mem _ hsp')
        unfold term
        rw [E_append _ _ _ _ c1, bval_congr (fun i hi => E_append _ _ _ _ (c2 i hi))]
      rw [hts, Nat.mod_add_mod]
      simp only [termsum, List.map_cons, List.sum_cons, term]
      rw [Nat.add_assoc]

def rowsOf (sw : List ℕ) : List ℕ → ℕ → List (ℕ × ℕ × List ℕ)
  | [], _ => []
  | v :: vs, j => (v, j, sw) :: rowsOf sw vs (j+1)

theorem rowsOf_len (sw : List ℕ) : ∀ (ws : List ℕ) (j : ℕ), (rowsOf sw ws j).length = ws.length
  | [], _ => rfl
  | v :: vs, j => by simp [rowsOf, rowsOf_len sw vs (j+1)]

theorem mem_rowsOf (sw : List ℕ) : ∀ (ws : List ℕ) (j : ℕ) (sp : ℕ × ℕ × List ℕ),
    sp ∈ rowsOf sw ws j → sp.1 ∈ ws ∧ sp.2.2 = sw ∧ j ≤ sp.2.1 ∧ sp.2.1 < j + ws.length
  | [], _, sp, h => by simp [rowsOf] at h
  | v :: vs, j, sp, h => by
    simp only [rowsOf, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨a, b, c, d⟩ := mem_rowsOf sw vs (j+1) sp h
      exact ⟨List.mem_cons_of_mem _ a, b, by omega, by simp; omega⟩

theorem termsum_rowsOf (ρ : ℕ → Bool) (sw : List ℕ) : ∀ (ws : List ℕ) (j : ℕ),
    termsum ρ (rowsOf sw ws j) = 2 ^ j * bval ρ ws * bval ρ sw
  | [], j => by simp [rowsOf, termsum, bval]
  | v :: vs, j => by
    have ih := termsum_rowsOf ρ sw vs (j+1)
    simp only [termsum] at ih
    simp only [rowsOf, termsum, List.map_cons, List.sum_cons]
    rw [ih]
    unfold term
    dsimp only
    simp only [bval, pow_succ]
    cases ρ v
    · simp only [Bool.false_eq_true, if_false, Bool.toNat_false]; ring
    · simp only [eq_self_iff_true, if_true, Bool.toNat_true]; ring

theorem termsum_append (ρ : ℕ → Bool) (l1 l2 : List (ℕ × ℕ × List ℕ)) :
    termsum ρ (l1 ++ l2) = termsum ρ l1 + termsum ρ l2 := by
  simp [termsum]

theorem termsum_flatMap (ρ : ℕ → Bool) (f : ℕ → List (ℕ × ℕ × List ℕ)) : ∀ t,
    termsum ρ ((List.range t).flatMap f) = ∑ i ∈ Finset.range t, termsum ρ (f i)
  | 0 => by simp [termsum]
  | t+1 => by
    rw [List.range_succ, List.flatMap_append, termsum_append, termsum_flatMap ρ f t,
      Finset.sum_range_succ]
    simp

theorem length_flatMap_range {β : Type} (f : ℕ → List β) (c : ℕ) : ∀ t,
    (∀ i < t, (f i).length = c) → ((List.range t).flatMap f).length = t * c
  | 0, _ => by simp
  | t+1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_range f c t (fun i hi => h i (by omega))]
    simp [h t (by omega)]
    ring

theorem mem_flatMap_range {β : Type} (f : ℕ → List β) (t : ℕ) (x : β) :
    x ∈ (List.range t).flatMap f ↔ ∃ i < t, x ∈ f i := by
  simp [List.mem_flatMap]

/-! ### The encoder -/

def vin (n z p : ℕ) : ℕ := if p < n then p else z

def Xw (n b z D : ℕ) : List ℕ := (List.range (b+1)).map fun l => vin n z (D * (2*b+1) + l)

def Sw (n b z D : ℕ) : List ℕ := (List.range b).map fun l => vin n z (D * (2*b+1) + (b+1) + l)

theorem vin_lt {n z M : ℕ} (p : ℕ) (hz : z < M) (hn : n ≤ M) : vin n z p < M := by
  unfold vin; split_ifs <;> omega

theorem Xw_lt {n b z M : ℕ} (D : ℕ) (hz : z < M) (hn : n ≤ M) : ∀ i ∈ Xw n b z D, i < M := by
  intro i hi
  simp only [Xw, List.mem_map] at hi
  obtain ⟨l, _, rfl⟩ := hi
  exact vin_lt _ hz hn

theorem Sw_lt {n b z M : ℕ} (D : ℕ) (hz : z < M) (hn : n ≤ M) : ∀ i ∈ Sw n b z D, i < M := by
  intro i hi
  simp only [Sw, List.mem_map] at hi
  obtain ⟨l, _, rfl⟩ := hi
  exact vin_lt _ hz hn

theorem digits_ex {n : ℕ} (b z : ℕ) : ∀ (Ds : List ℕ) (gs : List Gate), OkFrom n gs →
    z < n + gs.length → (∀ u : Fin n → Bool, E gs u z = false) →
    ∃ (hs : List Gate) (S1 S2 : ℕ → List ℕ), hs.length = Ds.length * (18 * (b+1)) ∧ OkFrom n (gs ++ hs) ∧
      ∀ D ∈ Ds, (S1 D).length = b+1 ∧ (S2 D).length = b+1 ∧
        (∀ i ∈ S1 D, i < n + (gs ++ hs).length) ∧ (∀ i ∈ S2 D, i < n + (gs ++ hs).length) ∧
        ∀ u : Fin n → Bool,
          bval (E (gs ++ hs) u) (S1 D) =
            (bval (E gs u) (Xw n b z D) + bval (E gs u) (Sw n b z D)) % 2^(b+1) ∧
          bval (E (gs ++ hs) u) (S2 D) =
            (bval (E gs u) (Xw n b z D) + 2 * bval (E gs u) (Sw n b z D)) % 2^(b+1) := by
  intro Ds
  induction Ds with
  | nil =>
    intro gs hok _ _
    exact ⟨[], fun _ => [], fun _ => [], by simp, by simpa using hok, by simp⟩
  | cons D Ds ih =>
    intro gs hok hz hzv
    have hX := Xw_lt (n := n) (b := b) D hz (by omega)
    have hS := Sw_lt (n := n) (b := b) D hz (by omega)
    obtain ⟨hs1, s1, a1, a2, a3, a4, a6⟩ := adder_mod (Xw n b z D) (Sw n b z D ++ [z]) gs z
      (by simp [Xw, Sw]) hok hX
      (by intro i hi; simp only [List.mem_append, List.mem_singleton] at hi
          rcases hi with hi | rfl; exact hS i hi; exact hz) hz
    have g1 : n + gs.length ≤ n + (gs ++ hs1).length := by
      simp only [List.length_append]; omega
    obtain ⟨hs2, s2, b1, b2, b3, b4, b6⟩ := adder_mod (Xw n b z D) (z :: Sw n b z D) (gs ++ hs1) z
      (by simp [Xw, Sw]) a2 (fun i hi => by have := hX i hi; omega)
      (by intro i hi; simp only [List.mem_cons] at hi
          rcases hi with rfl | hi; omega; have := hS i hi; omega) (by omega)
    have g2 : n + (gs ++ hs1).length ≤ n + (gs ++ hs1 ++ hs2).length := by
      simp only [List.length_append]; omega
    obtain ⟨hs3, S1', S2', c1, c2, c3⟩ := ih (gs ++ hs1 ++ hs2) b2 (by omega)
      (fun u => by rw [E_app3 gs hs1 hs2 u z hz, hzv])
    have hfin : gs ++ (hs1 ++ hs2 ++ hs3) = gs ++ hs1 ++ hs2 ++ hs3 := by simp
    have g3 : n + (gs ++ hs1 ++ hs2).length ≤ n + (gs ++ hs1 ++ hs2 ++ hs3).length := by
      simp only [List.length_append]; omega
    refine ⟨hs1 ++ hs2 ++ hs3, fun D' => if D' = D then s1 else S1' D',
      fun D' => if D' = D then s2 else S2' D', ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, a1, b1, c1, Xw, List.length_map,
        List.length_range]; ring
    · rw [hfin]; exact c2
    · intro D' hD'
      rw [hfin]
      have pX : ∀ u : Fin n → Bool, bval (E (gs ++ hs1 ++ hs2) u) (Xw n b z D') =
          bval (E gs u) (Xw n b z D') := fun u =>
        bval_congr (fun i hi => E_app3 gs hs1 hs2 u i (Xw_lt (n := n) (b := b) D' hz (by omega) i hi))
      have pS : ∀ u : Fin n → Bool, bval (E (gs ++ hs1 ++ hs2) u) (Sw n b z D') =
          bval (E gs u) (Sw n b z D') := fun u =>
        bval_congr (fun i hi => E_app3 gs hs1 hs2 u i (Sw_lt (n := n) (b := b) D' hz (by omega) i hi))
      by_cases hDD : D' = D
      · subst hDD
        simp only [eq_self_iff_true, if_true]
        have hS' : ∀ i ∈ z :: Sw n b z D', i < n + gs.length := by
          intro i hi; rcases List.mem_cons.1 hi with rfl | hi
          · exact hz
          · exact hS i hi
        refine ⟨by rw [a3]; simp [Xw], by rw [b3]; simp [Xw], fun i hi => ?_, fun i hi => ?_,
          fun u => ⟨?_, ?_⟩⟩
        · have := a4 i hi; omega
        · have := b4 i hi; omega
        · rw [bval_congr (fun i hi => E_app3 (gs ++ hs1) hs2 hs3 u i (a4 i hi)), a6 u,
            bval_append]
          simp [bval, hzv u, Xw]
        · rw [bval_congr (fun i hi => E_append (gs ++ hs1 ++ hs2) hs3 u i (b4 i hi)), b6 u,
            bval_congr (fun i hi => E_append gs hs1 u i (hX i hi)),
            bval_congr (fun i hi => E_append gs hs1 u i (hS' i hi)), E_append gs hs1 u z hz]
          simp [bval, hzv u, Xw]
      · simp only [if_neg hDD]
        have hmem : D' ∈ Ds := by
          rcases List.mem_cons.1 hD' with h | h
          · exact absurd h hDD
          · exact h
        obtain ⟨d1, d2, d3, d4, d5⟩ := c3 D' hmem
        refine ⟨d1, d2, d3, d4, fun u => ?_⟩
        rw [(d5 u).1, (d5 u).2, pX u, pS u]
        exact ⟨rfl, rfl⟩

theorem norms_ex {n : ℕ} (b t L z : ℕ) (hL : 2 * b ≤ L) : ∀ (βs : List ℕ) (gs : List Gate),
    OkFrom n gs → z < n + gs.length → (∀ u : Fin n → Bool, E gs u z = false) →
    ∃ (hs : List Gate) (Nr : ℕ → List ℕ), hs.length = βs.length * (t * b * (b + 9 * L)) ∧
      OkFrom n (gs ++ hs) ∧
      ∀ β ∈ βs, (Nr β).length = L ∧ (∀ i ∈ Nr β, i < n + (gs ++ hs).length) ∧
        ∀ u : Fin n → Bool, bval (E (gs ++ hs) u) (Nr β) =
          (∑ i ∈ Finset.range t, bval (E gs u) (Sw n b z (β*t+i)) ^ 2) % 2^L := by
  intro βs
  induction βs with
  | nil =>
    intro gs hok _ _
    exact ⟨[], fun _ => [], by simp, by simpa using hok, by simp⟩
  | cons β βs ih =>
    intro gs hok hz hzv
    have hspec : ∀ sp ∈ (List.range t).flatMap
        (fun i => rowsOf (Sw n b z (β*t+i)) (Sw n b z (β*t+i)) 0),
        sp.1 < n + gs.length ∧ (∀ i ∈ sp.2.2, i < n + gs.length) ∧ sp.2.2.length = b ∧
          sp.2.1 + b ≤ L := by
      intro sp hsp
      rw [mem_flatMap_range] at hsp
      obtain ⟨i, _, hi⟩ := hsp
      obtain ⟨m1, m2, _, m4⟩ := mem_rowsOf _ _ _ sp hi
      refine ⟨Sw_lt _ hz (by omega) _ m1, ?_, ?_, ?_⟩
      · rw [m2]; exact Sw_lt _ hz (by omega)
      · rw [m2]; simp [Sw]
      · simp [Sw] at m4; omega
    obtain ⟨hs1, acc, a1, a2, a3, a4, a6⟩ := chain_ex L b z _ gs (List.replicate L z) hok
      (by simp) (by intro i hi; rw [List.mem_replicate] at hi; omega) hz hzv hspec
    have g1 : n + gs.length ≤ n + (gs ++ hs1).length := by
      simp only [List.length_append]; omega
    obtain ⟨hs2, Nr', c1, c2, c3⟩ := ih (gs ++ hs1) a2 (by omega)
      (fun u => by rw [E_append _ _ _ _ hz, hzv])
    have hfin : gs ++ (hs1 ++ hs2) = gs ++ hs1 ++ hs2 := by simp
    have g2 : n + (gs ++ hs1).length ≤ n + (gs ++ hs1 ++ hs2).length := by
      simp only [List.length_append]; omega
    refine ⟨hs1 ++ hs2, fun β' => if β' = β then acc else Nr' β', ?_, ?_, ?_⟩
    · rw [List.length_append, a1, c1, length_flatMap_range
        (fun i => rowsOf (Sw n b z (β*t+i)) (Sw n b z (β*t+i)) 0) b t (fun i _ => by
        rw [rowsOf_len]; simp [Sw])]
      simp only [List.length_cons]; ring
    · rw [hfin]; exact c2
    · intro β' hβ'
      rw [hfin]
      by_cases hbb : β' = β
      · subst hbb
        simp only [eq_self_iff_true, if_true]
        refine ⟨a3, fun i hi => by have := a4 i hi; omega, fun u => ?_⟩
        rw [bval_congr (fun i hi => E_append (gs ++ hs1) hs2 u i (a4 i hi)), a6 u,
          bval_zeros _ z (hzv u), termsum_flatMap]
        simp only [termsum_rowsOf, pow_zero, Nat.one_mul, Nat.zero_add, sq]
      · simp only [if_neg hbb]
        have hmem : β' ∈ βs := by
          rcases List.mem_cons.1 hβ' with h | h
          · exact absurd h hbb
          · exact h
        obtain ⟨d1, d2, d3⟩ := c3 β' hmem
        refine ⟨d1, d2, fun u => ?_⟩
        rw [d3 u]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [bval_congr (fun j hj => E_append gs hs1 u j (Sw_lt _ hz (by omega) j hj))]

theorem encoder (n b t B L : ℕ) (hn : 0 < n) (hL : 2 * b ≤ L) :
    ∃ (gs : List Gate) (S1 S2 Nr : ℕ → List ℕ),
      OkFrom n gs ∧ gs.length = 2 + B * t * (18 * (b+1)) + B * (t * b * (b + 9 * L)) ∧
      n + 1 < n + gs.length ∧ (∀ u : Fin n → Bool, E gs u (n+1) = false) ∧
      (∀ D < B * t, (S1 D).length = b+1 ∧ (S2 D).length = b+1 ∧
        (∀ i ∈ S1 D, i < n + gs.length) ∧ (∀ i ∈ S2 D, i < n + gs.length) ∧
        ∀ u : Fin n → Bool,
          bval (E gs u) (S1 D) =
            (bval (E gs u) (Xw n b (n+1) D) + bval (E gs u) (Sw n b (n+1) D)) % 2^(b+1) ∧
          bval (E gs u) (S2 D) =
            (bval (E gs u) (Xw n b (n+1) D) + 2 * bval (E gs u) (Sw n b (n+1) D)) % 2^(b+1)) ∧
      (∀ β < B, (Nr β).length = L ∧ (∀ i ∈ Nr β, i < n + gs.length) ∧
        ∀ u : Fin n → Bool, bval (E gs u) (Nr β) =
          (∑ i ∈ Finset.range t, bval (E gs u) (Sw n b (n+1) (β*t+i)) ^ 2) % 2^L) := by
  have hz0 : n + 1 < n + (zg n).length := by simp [zg]
  obtain ⟨hs1, S1, S2, a1, a2, a3⟩ := digits_ex (n := n) b (n+1) (List.range (B*t)) (zg n)
    (zg_ok hn) hz0 (zg_val hn)
  have g1 : n + (zg n).length ≤ n + (zg n ++ hs1).length := by
    simp only [List.length_append]; omega
  obtain ⟨hs2, Nr, b1, b2, b3⟩ := norms_ex (n := n) b t L (n+1) hL (List.range B) (zg n ++ hs1)
    a2 (by omega) (fun u => by rw [E_append _ _ _ _ hz0, zg_val hn])
  have g2 : n + (zg n ++ hs1).length ≤ n + (zg n ++ hs1 ++ hs2).length := by
    simp only [List.length_append]; omega
  have hXS : ∀ (gs gs' : List Gate) (D : ℕ), n + 1 < n + gs.length →
      ∀ u : Fin n → Bool, bval (E (gs ++ gs') u) (Xw n b (n+1) D) = bval (E gs u) (Xw n b (n+1) D) ∧
        bval (E (gs ++ gs') u) (Sw n b (n+1) D) = bval (E gs u) (Sw n b (n+1) D) := by
    intro gs gs' D h u
    exact ⟨bval_congr (fun i hi => E_append _ _ _ _ (Xw_lt _ h (by omega) i hi)),
      bval_congr (fun i hi => E_append _ _ _ _ (Sw_lt _ h (by omega) i hi))⟩
  refine ⟨zg n ++ hs1 ++ hs2, S1, S2, Nr, b2, ?_, by omega, ?_, ?_, ?_⟩
  · simp only [List.length_append, zg, List.length_cons, List.length_nil, a1, b1,
      List.length_range]
  · intro u
    rw [E_app3 (zg n) hs1 hs2 u (n+1) hz0, zg_val hn]
  · intro D hD
    obtain ⟨d1, d2, d3, d4, d5⟩ := a3 D (List.mem_range.2 hD)
    refine ⟨d1, d2, fun i hi => by have := d3 i hi; omega, fun i hi => by have := d4 i hi; omega,
      fun u => ?_⟩
    rw [bval_congr (fun i hi => E_append _ _ _ _ (d3 i hi)),
      bval_congr (fun i hi => E_append _ _ _ _ (d4 i hi)), (d5 u).1, (d5 u).2,
      (hXS (zg n ++ hs1) hs2 D (by omega) u).1, (hXS (zg n ++ hs1) hs2 D (by omega) u).2,
      (hXS (zg n) hs1 D hz0 u).1, (hXS (zg n) hs1 D hz0 u).2]
    exact ⟨rfl, rfl⟩
  · intro β hβ
    obtain ⟨d1, d2, d3⟩ := b3 β (List.mem_range.2 hβ)
    refine ⟨d1, d2, fun u => ?_⟩
    rw [d3 u]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [(hXS (zg n ++ hs1) hs2 (β*t+i) (by omega) u).2]

/-! ## Assembling `fits` -/

def FitsBody (n k budget : ℕ) : Prop :=
  let Word := Fin n → Bool
  let Msg := Fin 3 → Fin k → Bool
  ∃ (enc : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin 3 → Fin k → Fin (n+enc.size))
      (code : Word → Msg),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n enc ∧ enc.size ≤ budget ∧
    (∀ g ∈ enc.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧
    (∀ (u : Word) (e : Fin 3) (j : Fin k), (enc.wires (List.ofFn u)).getD (out e j).val false = code u e j) ∧
    (∀ v : Fin 3 → Word, (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) → ∀ p, v p = v 0) ∧
    ∀ (hn : 0 < n) (w : ℕ) (owner : Fin n → Fin 3),
      let Pattern := Fin (w+1) → Bool
      let pos := fun (r : Fin n) (off : Fin (w+1)) =>
        (⟨(r.val+off.val)%n, Nat.mod_lt _ hn⟩ : Fin n)
      let V := fun (party : Fin 3) (q : ℕ) =>
        Sum ({r : Fin n // owner r = party} × Pattern)
          (Sum ({e : Fin 3 // e = party ∨ e+1 = party} × Fin k) (Fin q))
      ∃ (priv : Fin 3 → ℕ) (F : (o : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause (V o (priv o)))),
        (∀ o, ∀ cl ∈ F o, cl.card ≤ 3) ∧
        (∑ o : Fin 3, (priv o + (F o).card)) ≤ 128*(n*2^(min n (w+1)) + n + k + enc.size + 1) ∧
        ∀ (tab : Fin n → Pattern → Bool) (y : Msg),
          let passes := fun loc : (o : Fin 3) → Fin (priv o) → Bool =>
            ∀ o : Fin 3, PEqualNP.ProofComplexity.Satisfies
              (Sum.elim (fun h : {r : Fin n // owner r = o} × Pattern => tab h.1.val h.2)
                (Sum.elim (fun bit : {e : Fin 3 // e = o ∨ e+1 = o} × Fin k =>
                  y bit.1.val bit.2) (loc o))) (↑(F o) : Set _)
          (@Finset.filter _ passes (Classical.decPred _) Finset.univ).card =
            (Finset.univ.filter (fun x : Word => code x = y ∧
              ∀ row : Fin n, tab row (fun delta => x (pos row delta)) = true)).card

theorem getD_lt (l : List ℕ) (j d M : ℕ) (hl : ∀ a ∈ l, a < M) (hd : d < M) : l.getD j d < M := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hl _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hd

theorem sumsq_lt (t b L : ℕ) (f : ℕ → ℕ) (ht : 0 < t) (htL : t * 4 ^ b ≤ 2 ^ L)
    (hf : ∀ i < t, f i < 2 ^ b) : ∑ i ∈ Finset.range t, f i ^ 2 < 2 ^ L := by
  have h4 : (4:ℕ) ^ b = 2 ^ b * 2 ^ b := by rw [← mul_pow]; norm_num
  have hP : 0 < (4:ℕ) ^ b := by positivity
  have h1 : ∀ i ∈ Finset.range t, f i ^ 2 ≤ 4 ^ b - 1 := by
    intro i hi
    have := hf i (Finset.mem_range.1 hi)
    have : f i * f i < 2 ^ b * 2 ^ b := Nat.mul_lt_mul'' this this
    rw [sq]
    omega
  calc ∑ i ∈ Finset.range t, f i ^ 2 ≤ ∑ _i ∈ Finset.range t, (4 ^ b - 1) := Finset.sum_le_sum h1
    _ = t * (4 ^ b - 1) := by simp
    _ < t * (4 ^ b - 1) + t := by omega
    _ = t * 4 ^ b := by
        rw [show (4:ℕ) ^ b = (4 ^ b - 1) + 1 by omega, Nat.mul_succ]
        congr 1
    _ ≤ 2 ^ L := htL

theorem word_eq (n b B t z : ℕ) (gs : List Gate) (u u' : Fin n → Bool)
    (hcap : n ≤ B * t * (2 * b + 1))
    (hX : ∀ D < B * t, bval (E gs u) (Xw n b z D) = bval (E gs u') (Xw n b z D))
    (hS : ∀ D < B * t, bval (E gs u) (Sw n b z D) = bval (E gs u') (Sw n b z D)) : u = u' := by
  funext q
  have hq := q.isLt
  have e : q.val / (2*b+1) * (2*b+1) + q.val % (2*b+1) = q.val := Nat.div_add_mod' q.val (2*b+1)
  have hr := Nat.mod_lt q.val (show 0 < 2*b+1 by omega)
  have hD : q.val / (2*b+1) < B * t := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  rw [← E_input gs u q.val hq, ← E_input gs u' q.val hq]
  by_cases hrb : q.val % (2*b+1) < b + 1
  · apply bval_inj (hX _ hD)
    simp only [Xw, List.mem_map, List.mem_range]
    refine ⟨q.val % (2*b+1), hrb, ?_⟩
    unfold vin; rw [e, if_pos hq]
  · apply bval_inj (hS _ hD)
    simp only [Sw, List.mem_map, List.mem_range]
    refine ⟨q.val % (2*b+1) - (b+1), by omega, ?_⟩
    unfold vin
    rw [show q.val / (2*b+1) * (2*b+1) + (b+1) + (q.val % (2*b+1) - (b+1)) = q.val by omega,
      if_pos hq]

theorem fits_of_params (n k budget b t B L : ℕ) (hn : 0 < n) (ht : 0 < t) (hL : 2 * b ≤ L)
    (htL : t * 4 ^ b ≤ 2 ^ L) (hcap : n ≤ B * t * (2 * b + 1))
    (hk : B * t * (b + 1) + B * L ≤ k)
    (hsize : 2 + B * t * (18 * (b+1)) + B * (t * b * (b + 9 * L)) ≤ budget) :
    FitsBody n k budget := by
  obtain ⟨gs, S1, S2, Nr, hok, hlen, hz, hzv, hD, hβ⟩ := encoder n b t B L hn hL
  obtain ⟨l0, hl0⟩ : ∃ l : List ℕ,
      l = (List.range (B*t)).flatMap (Xw n b (n+1)) ++ (List.range B).flatMap Nr := ⟨_, rfl⟩
  obtain ⟨l1, hl1⟩ : ∃ l : List ℕ,
      l = (List.range (B*t)).flatMap S1 ++ (List.range B).flatMap Nr := ⟨_, rfl⟩
  obtain ⟨l2, hl2⟩ : ∃ l : List ℕ, l = (List.range (B*t)).flatMap S2 := ⟨_, rfl⟩
  have hNrlen : ((List.range B).flatMap Nr).length = B * L :=
    length_flatMap_range Nr L B (fun β hβ' => (hβ β hβ').1)
  have len0 : l0.length ≤ k := by
    rw [hl0, List.length_append, hNrlen,
      length_flatMap_range _ (b+1) (B*t) (fun D _ => by simp [Xw])]
    exact hk
  have len1 : l1.length ≤ k := by
    rw [hl1, List.length_append, hNrlen,
      length_flatMap_range _ (b+1) (B*t) (fun D hD' => (hD D hD').1)]
    exact hk
  have len2 : l2.length ≤ k := by
    rw [hl2, length_flatMap_range _ (b+1) (B*t) (fun D hD' => (hD D hD').2.1)]
    omega
  have w0 : ∀ a ∈ l0, a < n + gs.length := by
    intro a ha
    rw [hl0, List.mem_append, mem_flatMap_range, mem_flatMap_range] at ha
    rcases ha with ⟨D, _, hD'⟩ | ⟨β, hβ', hN⟩
    · exact Xw_lt D hz (by omega) a hD'
    · exact (hβ β hβ').2.1 a hN
  have w1 : ∀ a ∈ l1, a < n + gs.length := by
    intro a ha
    rw [hl1, List.mem_append, mem_flatMap_range, mem_flatMap_range] at ha
    rcases ha with ⟨D, hD1, hD'⟩ | ⟨β, hβ', hN⟩
    · exact (hD D hD1).2.2.1 a hD'
    · exact (hβ β hβ').2.1 a hN
  have w2 : ∀ a ∈ l2, a < n + gs.length := by
    intro a ha
    rw [hl2, mem_flatMap_range] at ha
    obtain ⟨D, hD1, hD'⟩ := ha
    exact (hD D hD1).2.2.2.1 a hD'
  let outL : Fin 3 → List ℕ := ![l0, l1, l2]
  have wout : ∀ e, ∀ a ∈ outL e, a < n + gs.length := by
    intro e; fin_cases e
    · exact w0
    · exact w1
    · exact w2
  have lout : ∀ e, (outL e).length ≤ k := by
    intro e; fin_cases e
    · exact len0
    · exact len1
    · exact len2
  let enc : Circuit := ⟨gs, 0⟩
  have hsz : enc.size = gs.length := rfl
  let out : Fin 3 → Fin k → Fin (n + enc.size) := fun e j =>
    ⟨(outL e).getD j.val 0, getD_lt _ _ _ _ (wout e) (by omega)⟩
  let code : (Fin n → Bool) → Fin 3 → Fin k → Bool := fun u e j => E gs u ((outL e).getD j.val 0)
  have hrb : ReadsBack n enc := by
    intro j hj i hi
    have : gateAt enc j = gs[j] := by simp [enc, gateAt, List.getD, hj]
    rw [this] at hi
    exact (hok j hj).1 i hi
  have hshape : ∀ g ∈ enc.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    exact (hok j hj).2
  have hout : ∀ (u : Fin n → Bool) (e : Fin 3) (j : Fin k),
      (enc.wires (List.ofFn u)).getD (out e j).val false = code u e j := fun u e j => rfl
  have hcode : ∀ (u u' : Fin n → Bool) (e : Fin 3), code u e = code u' e →
      ∀ a ∈ outL e, E gs u a = E gs u' a := by
    intro u u' e h a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
    have := congrFun h ⟨j, lt_of_lt_of_le hj (lout e)⟩
    simp only [code] at this
    rw [List.getD_eq_getElem _ _ hj] at this
    exact this
  have htri : ∀ v : Fin 3 → (Fin n → Bool), (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) →
      ∀ p, v p = v 0 := by
    intro v hv
    have E0 := hcode (v 0) (v 1) 0 (hv 0)
    have E1 := hcode (v 1) (v 2) 1 (hv 1)
    have E2 := hcode (v 2) (v 0) 2 (hv 2)
    have m0X : ∀ D < B * t, ∀ a ∈ Xw n b (n+1) D, a ∈ outL 0 := by
      intro D hD' a ha
      show a ∈ l0
      rw [hl0, List.mem_append, mem_flatMap_range]; exact Or.inl ⟨D, hD', ha⟩
    have m0N : ∀ β < B, ∀ a ∈ Nr β, a ∈ outL 0 := by
      intro β hβ' a ha
      show a ∈ l0
      rw [hl0, List.mem_append, mem_flatMap_range, mem_flatMap_range]; exact Or.inr ⟨β, hβ', ha⟩
    have m1S : ∀ D < B * t, ∀ a ∈ S1 D, a ∈ outL 1 := by
      intro D hD' a ha
      show a ∈ l1
      rw [hl1, List.mem_append, mem_flatMap_range]; exact Or.inl ⟨D, hD', ha⟩
    have m1N : ∀ β < B, ∀ a ∈ Nr β, a ∈ outL 1 := by
      intro β hβ' a ha
      show a ∈ l1
      rw [hl1, List.mem_append, mem_flatMap_range, mem_flatMap_range]; exact Or.inr ⟨β, hβ', ha⟩
    have m2S : ∀ D < B * t, ∀ a ∈ S2 D, a ∈ outL 2 := by
      intro D hD' a ha
      show a ∈ l2
      rw [hl2, mem_flatMap_range]; exact ⟨D, hD', ha⟩
    -- the digit-level conclusions
    have key : ∀ β < B, ∀ i < t,
        bval (E gs (v 1)) (Xw n b (n+1) (β*t+i)) = bval (E gs (v 0)) (Xw n b (n+1) (β*t+i)) ∧
        bval (E gs (v 2)) (Xw n b (n+1) (β*t+i)) = bval (E gs (v 0)) (Xw n b (n+1) (β*t+i)) ∧
        bval (E gs (v 1)) (Sw n b (n+1) (β*t+i)) = bval (E gs (v 0)) (Sw n b (n+1) (β*t+i)) ∧
        bval (E gs (v 2)) (Sw n b (n+1) (β*t+i)) = bval (E gs (v 0)) (Sw n b (n+1) (β*t+i)) := by
      intro β hβ'
      have hDt : ∀ i < t, β * t + i < B * t := by
        intro i hi
        have : (β + 1) * t ≤ B * t := Nat.mul_le_mul_right t hβ'
        have : (β + 1) * t = β * t + t := by ring
        omega
      let x : Fin 3 → Fin t → ℕ := fun e i => bval (E gs (v e)) (Xw n b (n+1) (β*t+i.val))
      let s : Fin 3 → Fin t → ℕ := fun e i => bval (E gs (v e)) (Sw n b (n+1) (β*t+i.val))
      have hxb : ∀ e i, x e i < 2 ^ (b+1) := by
        intro e i
        have := bval_lt (E gs (v e)) (Xw n b (n+1) (β*t+i.val))
        have hl : (Xw n b (n+1) (β*t+i.val)).length = b + 1 := by simp [Xw]
        rw [hl] at this
        exact this
      have hsb : ∀ e i, s e i < 2 ^ b := by
        intro e i
        have := bval_lt (E gs (v e)) (Sw n b (n+1) (β*t+i.val))
        have hl : (Sw n b (n+1) (β*t+i.val)).length = b := by simp [Sw]
        rw [hl] at this
        exact this
      have hA : ∀ i, x 0 i = x 1 i := fun i =>
        bval_congr (fun a ha => E0 a (m0X _ (hDt i.val i.isLt) a ha))
      have hB : ∀ i, (x 1 i + s 1 i) % 2 ^ (b+1) = (x 2 i + s 2 i) % 2 ^ (b+1) := by
        intro i
        have h1 := ((hD _ (hDt i.val i.isLt)).2.2.2.2 (v 1)).1
        have h2 := ((hD _ (hDt i.val i.isLt)).2.2.2.2 (v 2)).1
        have h12 : bval (E gs (v 1)) (S1 (β*t+i.val)) = bval (E gs (v 2)) (S1 (β*t+i.val)) :=
          bval_congr (fun a ha => E1 a (m1S _ (hDt i.val i.isLt) a ha))
        rw [← h1, ← h2]; exact h12
      have hC : ∀ i, (x 2 i + 2 * s 2 i) % 2 ^ (b+1) = (x 0 i + 2 * s 0 i) % 2 ^ (b+1) := by
        intro i
        have h1 := ((hD _ (hDt i.val i.isLt)).2.2.2.2 (v 2)).2
        have h2 := ((hD _ (hDt i.val i.isLt)).2.2.2.2 (v 0)).2
        have h12 : bval (E gs (v 2)) (S2 (β*t+i.val)) = bval (E gs (v 0)) (S2 (β*t+i.val)) :=
          bval_congr (fun a ha => E2 a (m2S _ (hDt i.val i.isLt) a ha))
        rw [← h1, ← h2]; exact h12
      have hsum : ∀ e, ∑ i, s e i ^ 2 =
          ∑ i ∈ Finset.range t, bval (E gs (v e)) (Sw n b (n+1) (β*t+i)) ^ 2 := fun e =>
        Fin.sum_univ_eq_sum_range (fun i => bval (E gs (v e)) (Sw n b (n+1) (β*t+i)) ^ 2) t
      have hlt : ∀ e, ∑ i ∈ Finset.range t, bval (E gs (v e)) (Sw n b (n+1) (β*t+i)) ^ 2 < 2 ^ L :=
        fun e => sumsq_lt t b L _ ht htL (fun i hi => hsb e ⟨i, hi⟩)
      have hnorm : ∀ e e', bval (E gs (v e)) (Nr β) = bval (E gs (v e')) (Nr β) →
          ∑ i, s e i ^ 2 = ∑ i, s e' i ^ 2 := by
        intro e e' h
        rw [(hβ β hβ').2.2 (v e), (hβ β hβ').2.2 (v e'), Nat.mod_eq_of_lt (hlt e),
          Nat.mod_eq_of_lt (hlt e')] at h
        rw [hsum, hsum]; exact h
      have h01 := hnorm 0 1 (bval_congr (fun a ha => E0 a (m0N β hβ' a ha)))
      have h12 := hnorm 1 2 (bval_congr (fun a ha => E1 a (m1N β hβ' a ha)))
      obtain ⟨r1, r2, r3, r4⟩ := behrend_digits (x 0) (x 1) (x 2) (s 0) (s 1) (s 2)
        (hxb 0) (hxb 1) (hxb 2) (hsb 0) (hsb 1) (hsb 2) hA hB hC h01 h12
      intro i hi
      exact ⟨congrFun r1 ⟨i, hi⟩, congrFun r2 ⟨i, hi⟩, congrFun r3 ⟨i, hi⟩, congrFun r4 ⟨i, hi⟩⟩
    have keyD : ∀ D < B * t,
        bval (E gs (v 1)) (Xw n b (n+1) D) = bval (E gs (v 0)) (Xw n b (n+1) D) ∧
        bval (E gs (v 2)) (Xw n b (n+1) D) = bval (E gs (v 0)) (Xw n b (n+1) D) ∧
        bval (E gs (v 1)) (Sw n b (n+1) D) = bval (E gs (v 0)) (Sw n b (n+1) D) ∧
        bval (E gs (v 2)) (Sw n b (n+1) D) = bval (E gs (v 0)) (Sw n b (n+1) D) := by
      intro D hD'
      have e : D / t * t + D % t = D := Nat.div_add_mod' D t
      have := key (D / t) ((Nat.div_lt_iff_lt_mul ht).2 hD') (D % t) (Nat.mod_lt _ ht)
      rw [e] at this
      exact this
    have hv1 : v 1 = v 0 := word_eq n b B t (n+1) gs _ _ hcap (fun D hD' => (keyD D hD').1)
      (fun D hD' => (keyD D hD').2.2.1)
    have hv2 : v 2 = v 0 := word_eq n b B t (n+1) gs _ _ hcap (fun D hD' => (keyD D hD').2.1)
      (fun D hD' => (keyD D hD').2.2.2)
    intro p
    fin_cases p
    · rfl
    · exact hv1
    · exact hv2
  exact ⟨enc, out, code, hrb, by rw [hsz, hlen]; exact hsize, hshape, hout, htri,
    cnf_part n k enc out code hrb hshape hout htri⟩

/-! ## Parameters -/

theorem part1_fits (n k : ℕ) (hn : 0 < n) (hk : 100 ≤ k)
    (hnk : n + 100 * (Nat.sqrt k + 1) ≤ 2 * k) : FitsBody n k (100 * k * (Nat.sqrt k + 1)) := by
  obtain ⟨q, hq⟩ : ∃ q, q = Nat.sqrt k := ⟨_, rfl⟩
  rw [← hq] at hnk ⊢
  have hq1 : q * q ≤ k := by rw [hq]; exact Nat.sqrt_le k
  have hq2 : k < (q+1)*(q+1) := by rw [hq]; exact Nat.lt_succ_sqrt k
  have hq10 : 10 ≤ q := by rw [hq, Nat.le_sqrt]; omega
  have h10q : 10 * q ≤ q * q := Nat.mul_le_mul_right q hq10
  obtain ⟨t, htdef⟩ : ∃ t, t = (k - 3*q) / (q+1) := ⟨_, rfl⟩
  have ht1 : t * (q+1) ≤ k - 3*q := by rw [htdef]; exact Nat.div_mul_le_self _ _
  have ht2 : k - 3*q < t * (q+1) + (q+1) := by rw [htdef]; exact Nat.lt_div_mul_add (by omega)
  have htq : t ≤ q := by
    by_contra h0
    have h : q + 1 ≤ t := by omega
    have : (q+1)*(q+1) ≤ t*(q+1) := Nat.mul_le_mul_right _ h
    omega
  have htpos : 0 < t := by
    rw [htdef]; apply Nat.div_pos _ (by omega); omega
  have e1 : t * (q+1) = t*q + t := by ring
  apply fits_of_params n k _ q t 1 (3*q) hn htpos (by omega)
  · have : (2:ℕ)^(3*q) = 2^q * 4^q := by
      rw [show 3*q = q + 2*q by ring, pow_add, pow_mul]; norm_num
    rw [this]
    exact Nat.mul_le_mul_right _ (le_trans htq (Nat.lt_two_pow_self (n := q)).le)
  · have e2 : 1 * t * (2*q+1) = 2*(t*q) + t := by ring
    rw [e2]; omega
  · have e3 : 1 * t * (q+1) + 1 * (3*q) = t*q + t + 3*q := by ring
    rw [e3]; omega
  · have e3 : 2 + 1 * t * (18 * (q+1)) + 1 * (t * q * (q + 9 * (3*q))) =
        2 + 18 * (t*q) + 18 * t + 28 * (t*q*q) := by ring
    have e4 : 100 * k * (q+1) = 100 * (k*q) + 100 * k := by ring
    have h6 : t*q*q ≤ k*q := Nat.mul_le_mul_right q (by omega)
    rw [e3, e4]; omega

theorem part2_fits (r : ℕ) (hr : 0 < r) (n k : ℕ) (hn : 0 < n)
    (hk : 8 * r * (40 * r^2 + 25 * r + 5) ≤ k) (hnk : n + (k + r - 1) / r ≤ 2 * k) :
    FitsBody n k (100 * (r+1) * k) := by
  obtain ⟨blk, hblk⟩ : ∃ m, m = 40 * r^2 + 25 * r + 5 := ⟨_, rfl⟩
  rw [← hblk] at hk
  have hblk0 : 0 < blk := by rw [hblk]; positivity
  obtain ⟨B, hBdef⟩ : ∃ B, B = k / blk := ⟨_, rfl⟩
  have hB : 8 * r ≤ B := by rw [hBdef]; exact (Nat.le_div_iff_mul_le hblk0).2 hk
  have hBk : B * blk ≤ k := by rw [hBdef]; exact Nat.div_mul_le_self k blk
  have hR : k < B * blk + blk := by rw [hBdef]; exact Nat.lt_div_mul_add hblk0
  apply fits_of_params n k _ (2*r) (20*r) B (5*r+5) hn (by omega) (by omega)
  · have e1 : (4:ℕ)^(2*r) = 16^r := by rw [pow_mul]; norm_num
    have e2 : (2:ℕ)^(5*r+5) = 32 * (2^r * 16^r) := by
      rw [pow_add, pow_mul, ← mul_pow]; norm_num; ring
    rw [e1, e2]
    have h2r : r < 2^r := Nat.lt_two_pow_self
    calc 20 * r * 16^r ≤ (32 * 2^r) * 16^r := Nat.mul_le_mul_right _ (by omega)
      _ = 32 * (2^r * 16^r) := by ring
  · -- capacity
    obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (k + r - 1) / r := ⟨_, rfl⟩
    rw [← hQdef] at hnk
    have hQ0 : k + r - 1 < Q * r + r := by rw [hQdef]; exact Nat.lt_div_mul_add hr
    have hQ : k ≤ Q * r := by omega
    obtain ⟨R, hRdef⟩ : ∃ R, R = k - B * blk := ⟨_, rfl⟩
    have hkR : k = B * blk + R := by omega
    have hRlt : R < blk := by omega
    have h1 : r * (n + Q) ≤ r * (2 * k) := Nat.mul_le_mul_left r hnk
    have hrk : r * k = r * (B * blk + R) := by rw [← hkR]
    have hA1 : 2 * r * R ≤ 2 * r * blk := Nat.mul_le_mul_left _ hRlt.le
    have hA2 : 2 * r * blk ≤ 8 * r * (10 * r^2 + 15 * r + 5) := by
      rw [hblk]; nlinarith [sq_nonneg r]
    have hA3 : 8 * r * (10 * r^2 + 15 * r + 5) ≤ B * (10 * r^2 + 15 * r + 5) :=
      Nat.mul_le_mul_right _ hB
    have goal : r * n ≤ r * (B * (20 * r) * (2 * (2 * r) + 1)) := by
      rw [hblk] at hrk hkR
      nlinarith [h1, hQ, hrk, hkR, hA1, hA2, hA3]
    exact Nat.le_of_mul_le_mul_left goal hr
  · have : B * (20 * r) * (2 * r + 1) + B * (5 * r + 5) = B * blk := by rw [hblk]; ring
    rw [this]; exact hBk
  · have hB1 : 1 ≤ B := by omega
    calc 2 + B * (20 * r) * (18 * (2 * r + 1)) + B * (20 * r * (2 * r) * (2 * r + 9 * (5 * r + 5)))
        ≤ 100 * (r + 1) * (B * blk) := by
          rw [hblk]
          nlinarith [Nat.zero_le (B * r^3), Nat.zero_le (B * r^2), Nat.zero_le (B * r), hB1]
      _ ≤ 100 * (r + 1) * k := Nat.mul_le_mul_left _ hBk
end PEqualNP.Outside.L_pcx_252_aux

theorem PEqualNP.Outside.L_pcx_252 : let fits := fun (n k budget : ℕ) =>
  let Word := Fin n → Bool
  let Msg := Fin 3 → Fin k → Bool
  ∃ (enc : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin 3 → Fin k → Fin (n+enc.size))
      (code : Word → Msg),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n enc ∧ enc.size ≤ budget ∧
    (∀ g ∈ enc.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧
    (∀ (u : Word) (e : Fin 3) (j : Fin k), (enc.wires (List.ofFn u)).getD (out e j).val false = code u e j) ∧
    (∀ v : Fin 3 → Word, (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) → ∀ p, v p = v 0) ∧
    ∀ (hn : 0 < n) (w : ℕ) (owner : Fin n → Fin 3),
      let Pattern := Fin (w+1) → Bool
      let pos := fun (r : Fin n) (off : Fin (w+1)) =>
        (⟨(r.val+off.val)%n, Nat.mod_lt _ hn⟩ : Fin n)
      let V := fun (party : Fin 3) (q : ℕ) =>
        Sum ({r : Fin n // owner r = party} × Pattern)
          (Sum ({e : Fin 3 // e = party ∨ e+1 = party} × Fin k) (Fin q))
      ∃ (priv : Fin 3 → ℕ) (F : (o : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause (V o (priv o)))),
        (∀ o, ∀ cl ∈ F o, cl.card ≤ 3) ∧
        (∑ o : Fin 3, (priv o + (F o).card)) ≤ 128*(n*2^(min n (w+1)) + n + k + enc.size + 1) ∧
        ∀ (tab : Fin n → Pattern → Bool) (y : Msg),
          let passes := fun loc : (o : Fin 3) → Fin (priv o) → Bool =>
            ∀ o : Fin 3, PEqualNP.ProofComplexity.Satisfies
              (Sum.elim (fun h : {r : Fin n // owner r = o} × Pattern => tab h.1.val h.2)
                (Sum.elim (fun bit : {e : Fin 3 // e = o ∨ e+1 = o} × Fin k =>
                  y bit.1.val bit.2) (loc o))) (↑(F o) : Set _)
          (@Finset.filter _ passes (Classical.decPred _) Finset.univ).card =
            (Finset.univ.filter (fun x : Word => code x = y ∧
              ∀ row : Fin n, tab row (fun delta => x (pos row delta)) = true)).card
∃ A : ℕ, 0 < A ∧
  (∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, 0 < n →
    n + A*(Nat.sqrt k + 1) ≤ 2*k → fits n k (A*k*(Nat.sqrt k + 1))) ∧
  ∀ r : ℕ, 0 < r → ∃ threshold : ℕ, ∀ k : ℕ, threshold ≤ k →
    ∀ n : ℕ, 0 < n → n + (k+r-1)/r ≤ 2*k → fits n k (A*(r+1)*k) := by
  intro fits
  refine ⟨100, by norm_num, ⟨100, fun k hk n hn hnk => ?_⟩,
    fun r hr => ⟨8 * r * (40 * r^2 + 25 * r + 5), fun k hk n hn hnk => ?_⟩⟩
  · exact PEqualNP.Outside.L_pcx_252_aux.part1_fits n k hn hk hnk
  · exact PEqualNP.Outside.L_pcx_252_aux.part2_fits r hr n k hn hk hnk
