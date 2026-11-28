import Mathlib
import PEqualNP.Defs

-- Coloured steps on the ordered inputs: with a connected adjacent-pair obstruction no circuit with at most
-- n - 1 gates other than NOT has a wire changing at every step and one tap per colour changing exactly at
-- the steps of that colour; for the doubled odd cycle the obstruction holds and 3d - 1 such gates suffice.
--
-- First part. Induction over the gate list, last gate removed, with a labelling of the steps by classes:
-- (W) every wire changes only at steps of one class, (N) there are at least n minus (gates other than NOT)
-- classes, (S) IF that count is exact and every class is the whole change set of a wire THEN change sets
-- are nested or disjoint, nested ones have a fixed side, and a change set with two or more steps is the
-- change set of an AND or OR of two wires with disjoint nonempty change sets. A NOT, a constant and a copy
-- keep the labelling; an AND or OR of wires in different classes joins the two classes. At the end the
-- wire changing everywhere makes the premise of (S) true. So that wire has the change set of g = a AND b
-- (or OR) with the change sets A of a and B of b disjoint and covering all steps. A colour class is the
-- change set of its tap, so by nesting it lies inside A or inside B. The colours with a step in A form a
-- nonempty set that is not everything, so for either parity the obstruction gives adjacent steps i, i + 1
-- with exactly one in A. The gate g alternates, so it takes its forcing value (true for AND, false for OR)
-- at all levels of one parity; there a has that value too. Take that parity: a has the same value at
-- levels i and i + 2 but changes at exactly one of the two steps between them, which is impossible.
--
-- Second part. On a path 0, 1, ..., d - 1 a nonempty set that is not everything is left between some c and
-- c + 1; the step c or c + d has the wanted parity because d is odd, and its successor has colour c + 1.
-- The circuit: 2d NOT gates of the inputs, the taps x_j AND NOT x_(j+d), the single-level tests
-- x_(2m) AND NOT x_(2m+1) with the test for m = 0 last, and d - 1 OR gates collecting the tests, each
-- reading the wire just before it. Its wire values are given by one table, checked gate by gate.

namespace PEqualNP.Outside.L_lib_1378

open PEqualNP.CircuitLowerBounds

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

/-! ### Words on the ordered inputs -/

/-- The steps at which a word changes. -/
def chg {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc ≠ f i.succ

theorem mem_chg {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ chg f ↔ f i.castSucc ≠ f i.succ := by
  simp [chg]

theorem chg_const {n : ℕ} {f : Fin (n + 1) → Bool} (h : ∀ t t', f t = f t') : chg f = ∅ := by
  ext i
  rw [mem_chg]
  simp [h i.castSucc i.succ]

theorem chg_congr {n : ℕ} {f g : Fin (n + 1) → Bool}
    (h : (∀ t, g t = f t) ∨ (∀ t, g t = !f t)) : chg g = chg f := by
  ext i
  rw [mem_chg, mem_chg]
  rcases h with h | h
  · rw [h, h]
  · rw [h, h]
    cases f i.castSucc <;> cases f i.succ <;> simp

/-- Nested or disjoint. -/
def Lam {n : ℕ} (A B : Finset (Fin n)) : Prop := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- On the change set of `f` the words `f` and `g` are always equal or always opposite. -/
def Pol {n : ℕ} (f g : Fin (n + 1) → Bool) : Prop :=
  (∀ i ∈ chg f, f i.castSucc = g i.castSucc) ∨ (∀ i ∈ chg f, f i.castSucc ≠ g i.castSucc)

theorem Pol.left {n : ℕ} {f f' g : Fin (n + 1) → Bool}
    (h : (∀ t, f' t = f t) ∨ (∀ t, f' t = !f t)) (hp : Pol f g) : Pol f' g := by
  have hc := chg_congr h
  unfold Pol at *
  rw [hc]
  rcases h with h | h
  · rcases hp with hp | hp
    · exact Or.inl fun i hi => by rw [h]; exact hp i hi
    · exact Or.inr fun i hi => by rw [h]; exact hp i hi
  · rcases hp with hp | hp
    · refine Or.inr fun i hi => ?_
      rw [h, ← hp i hi]
      cases f i.castSucc <;> simp
    · refine Or.inl fun i hi => ?_
      have := hp i hi
      rw [h]
      revert this
      cases f i.castSucc <;> cases g i.castSucc <;> simp

theorem Pol.right {n : ℕ} {f g g' : Fin (n + 1) → Bool}
    (h : (∀ t, g' t = g t) ∨ (∀ t, g' t = !g t)) (hp : Pol f g) : Pol f g' := by
  unfold Pol at *
  rcases h with h | h
  · rcases hp with hp | hp
    · exact Or.inl fun i hi => by rw [h]; exact hp i hi
    · exact Or.inr fun i hi => by rw [h]; exact hp i hi
  · rcases hp with hp | hp
    · refine Or.inr fun i hi => ?_
      rw [h, hp i hi]
      cases g i.castSucc <;> simp
    · refine Or.inl fun i hi => ?_
      have := hp i hi
      rw [h]
      revert this
      cases f i.castSucc <;> cases g i.castSucc <;> simp

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
    (hi : i ∈ chg f) (hb : i ∉ chg b) : f i.castSucc = a i.castSucc := by
  rw [mem_chg] at hi hb
  have hb' : b i.castSucc = b i.succ := not_not.1 hb
  rcases hop with h | h
  · rw [h, h, ← hb'] at hi; rw [h]; exact bool_and_l _ _ _ hi
  · rw [h, h, ← hb'] at hi; rw [h]; exact bool_or_l _ _ _ hi

theorem bin_right {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (ha : i ∉ chg a) : f i.castSucc = b i.castSucc := by
  rw [mem_chg] at hi ha
  have ha' : a i.castSucc = a i.succ := not_not.1 ha
  rcases hop with h | h
  · rw [h, h, ← ha'] at hi; rw [h]; exact bool_and_r _ _ _ hi
  · rw [h, h, ← ha'] at hi; rw [h]; exact bool_or_r _ _ _ hi

/-! ### The invariant -/

/-- Word `u` has the change set of an AND or OR of two words with disjoint nonempty change sets. -/
def Split {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K u : ℕ) : Prop :=
  ∃ g < K, ∃ a < K, ∃ b < K, chg (F g) = chg (F u) ∧
    ((∀ t, F g t = (F a t && F b t)) ∨ (∀ t, F g t = (F a t || F b t))) ∧
    Disjoint (chg (F a)) (chg (F b)) ∧ (chg (F a)).Nonempty ∧ (chg (F b)).Nonempty

theorem Split.mono {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K u : ℕ} (h : Split F K u) :
    Split F (K + 1) u := by
  obtain ⟨g, hg, a, ha, b, hb, rest⟩ := h
  exact ⟨g, Nat.lt_succ_of_lt hg, a, Nat.lt_succ_of_lt ha, b, Nat.lt_succ_of_lt hb, rest⟩

theorem Split.retarget {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K u u' : ℕ} (h : Split F K u')
    (e : chg (F u) = chg (F u')) : Split F K u := by
  obtain ⟨g, hg, a, ha, b, hb, e', rest⟩ := h
  exact ⟨g, hg, a, ha, b, hb, e'.trans e.symm, rest⟩

/-- The first `K` words have nested or disjoint change sets and fixed sides, and every change set with
two or more steps is split by an AND or OR. -/
def Str {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) : Prop :=
  (∀ u < K, ∀ v < K, Lam (chg (F u)) (chg (F v))) ∧
  (∀ u < K, ∀ v < K, chg (F u) ⊆ chg (F v) → Pol (F u) (F v)) ∧
  (∀ u < K, 2 ≤ (chg (F u)).card → Split F K u)

/-- The steps of one class. -/
def blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => cls j = c

theorem mem_blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) (j : Fin n) : j ∈ blk cls c ↔ cls j = c := by
  simp [blk]

/-- The invariant for the first `K` words after `P` gates other than NOT. -/
def Inv {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K P : ℕ) : Prop :=
  ∃ cls : Fin n → ℕ,
    (∀ u < K, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls i = cls j) ∧
    n ≤ (Finset.univ.image cls).card + P ∧
    ((n = (Finset.univ.image cls).card + P ∧
        ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i)) → Str F K)

theorem Inv.slack {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P : ℕ} (h : Inv F K P) :
    Inv F K (P + 1) := by
  obtain ⟨cls, hW, hN, -⟩ := h
  exact ⟨cls, hW, by omega, fun hp => absurd hp.1 (by omega)⟩

theorem Inv.congr {n : ℕ} {F F' : ℕ → Fin (n + 1) → Bool} {K P : ℕ}
    (h : ∀ u < K, F' u = F u) (hI : Inv F K P) : Inv F' K P := by
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu
    rw [h u hu]
    exact hW u hu
  · rintro ⟨heq, hfull⟩
    obtain ⟨hlam, hpol, hsp⟩ := hS ⟨heq, fun i => by
      obtain ⟨u, hu, e⟩ := hfull i
      exact ⟨u, hu, by rw [← h u hu]; exact e⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rw [h u hu, h v hv]
      exact hlam u hu v hv
    · intro u hu v hv hs
      rw [h u hu, h v hv] at hs ⊢
      exact hpol u hu v hv hs
    · intro u hu hcard
      rw [h u hu] at hcard
      obtain ⟨g, hg, a, ha, b, hb, e, hop, hd, hna, hnb⟩ := hsp u hu hcard
      refine ⟨g, hg, a, ha, b, hb, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h g hg, h u hu]; exact e
      · rw [h g hg, h a ha, h b hb]; exact hop
      · rw [h a ha, h b hb]; exact hd
      · rw [h a ha]; exact hna
      · rw [h b hb]; exact hnb

/-- A new word that never changes. -/
theorem Inv.const {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P : ℕ} (hc : chg (F K) = ∅)
    (h : Inv F K P) : Inv F (K + 1) P := by
  obtain ⟨cls, hW, hN, hS⟩ := h
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
    · exact hW u hu i hi j hj
    · rw [hu, hc] at hi
      exact absurd hi (Finset.notMem_empty i)
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, hue⟩
      · exfalso
        have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
        rw [← hue, hu, hc] at hi
        exact Finset.notMem_empty i hi
    obtain ⟨hlam, hpol, hsp⟩ := hS ⟨heq, hfullK⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
        · exact hlam u hu v hv
        · exact Or.inr (Or.inl (by rw [hv, hc]; exact Finset.empty_subset _))
      · exact Or.inl (by rw [hu, hc]; exact Finset.empty_subset _)
    · intro u hu v hv hsub
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
        · exact hpol u hu v hv hsub
        · refine Or.inl fun i hi => ?_
          have := hsub hi
          rw [hv, hc] at this
          exact absurd this (Finset.notMem_empty i)
      · refine Or.inl fun i hi => ?_
        rw [hu, hc] at hi
        exact absurd hi (Finset.notMem_empty i)
    · intro u hu hcard
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact (hsp u hu hcard).mono
      · rw [hu, hc] at hcard
        simp at hcard

/-- A new word that is an old word or its negation. -/
theorem Inv.same {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P a : ℕ} (ha : a < K)
    (h : (∀ t, F K t = F a t) ∨ (∀ t, F K t = !F a t)) (hI : Inv F K P) : Inv F (K + 1) P := by
  have hc : chg (F K) = chg (F a) := chg_congr h
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
    · exact hW u hu i hi j hj
    · rw [hu, hc] at hi hj
      exact hW a ha i hi j hj
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, hue⟩
      · rw [hu, hc] at hue
        exact ⟨a, ha, hue⟩
    obtain ⟨hlam, hpol, hsp⟩ := hS ⟨heq, hfullK⟩
    have key : ∀ u, u < K + 1 → ∃ u', u' < K ∧ chg (F u) = chg (F u') ∧
        ((∀ t, F u t = F u' t) ∨ (∀ t, F u t = !F u' t)) := by
      intro u hu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, rfl, Or.inl fun _ => rfl⟩
      · rw [hu]
        exact ⟨a, ha, hc, h⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      obtain ⟨u', hu', eu, -⟩ := key u hu
      obtain ⟨v', hv', ev, -⟩ := key v hv
      rw [eu, ev]
      exact hlam u' hu' v' hv'
    · intro u hu v hv hsub
      obtain ⟨u', hu', eu, ru⟩ := key u hu
      obtain ⟨v', hv', ev, rv⟩ := key v hv
      rw [eu, ev] at hsub
      exact Pol.left ru (Pol.right rv (hpol u' hu' v' hv' hsub))
    · intro u hu hcard
      obtain ⟨u', hu', eu, -⟩ := key u hu
      rw [eu] at hcard
      exact ((hsp u' hu' hcard).mono).retarget eu

/-- A new word that is the AND or the OR of two old words. -/
theorem Inv.bin {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P a b : ℕ} (ha : a < K) (hb : b < K)
    (hop : (∀ t, F K t = (F a t && F b t)) ∨ (∀ t, F K t = (F a t || F b t)))
    (hI : Inv F K P) : Inv F (K + 1) (P + 1) := by
  have hsub : chg (F K) ⊆ chg (F a) ∪ chg (F b) := bin_sub hop
  obtain ⟨cls, hW, hN, hS⟩ := hI
  by_cases hm : ∀ x ∈ chg (F a), ∀ y ∈ chg (F b), cls x = cls y
  · -- the two wires change in one class: nothing is joined
    refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
    intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
    · exact hW u hu i hi j hj
    · rw [hu] at hi hj
      rcases Finset.mem_union.1 (hsub hi) with hi | hi <;>
        rcases Finset.mem_union.1 (hsub hj) with hj | hj
      · exact hW a ha i hi j hj
      · exact hm i hi j hj
      · exact (hm j hj i hi).symm
      · exact hW b hb i hi j hj
  · -- two classes are joined
    simp only [not_forall] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hm
    obtain ⟨cls', hcls'⟩ : ∃ cls' : Fin n → ℕ,
        ∀ i, cls' i = if cls i = cls y then cls x else cls i := ⟨_, fun _ => rfl⟩
    have hA : ∀ i ∈ chg (F a), cls i = cls x := fun i hi => hW a ha i hi x hx
    have hB : ∀ i ∈ chg (F b), cls i = cls y := fun i hi => hW b hb i hi y hy
    have hH : ∀ i ∈ chg (F K), cls' i = cls x := by
      intro i hi
      rcases Finset.mem_union.1 (hsub hi) with h | h
      · rw [hcls', hA i h]; simp
      · rw [hcls', hB i h]; simp
    have hW' : ∀ u < K + 1, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls' i = cls' j := by
      intro u hu i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rw [hcls', hcls', hW u hu i hi j hj]
      · rw [hu] at hi hj
        rw [hH i hi, hH j hj]
    have himg : Finset.univ.image cls' =
        (Finset.univ.image cls).image (fun c => if c = cls y then cls x else c) := by
      rw [Finset.image_image]
      congr 1
      funext i
      exact hcls' i
    have hcard : (Finset.univ.image cls).card ≤ (Finset.univ.image cls').card + 1 := by
      rw [himg]
      have h1 : ((Finset.univ.image cls).erase (cls y)).card ≤
          ((Finset.univ.image cls).image (fun c => if c = cls y then cls x else c)).card := by
        rw [← Finset.card_image_of_injOn (f := fun c => if c = cls y then cls x else c)
          (s := (Finset.univ.image cls).erase (cls y))]
        · exact Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset _ _))
        · intro c hc d hd hcd
          have hc' : c ≠ cls y := (Finset.mem_erase.1 (Finset.mem_coe.1 hc)).1
          have hd' : d ≠ cls y := (Finset.mem_erase.1 (Finset.mem_coe.1 hd)).1
          simpa [hc', hd'] using hcd
      have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.image cls) (a := cls y)
      omega
    refine ⟨cls', hW', by omega, ?_⟩
    rintro ⟨heq, hfull⟩
    have hcardeq : n = (Finset.univ.image cls).card + P := by omega
    have hx' : cls' x = cls x := by rw [hcls']; simp
    have hy' : cls' y = cls x := by rw [hcls']; simp
    -- the joined class can only be the change set of the new word
    obtain ⟨hxK, hyK, hKe⟩ : x ∈ chg (F K) ∧ y ∈ chg (F K) ∧ chg (F K) = blk cls' (cls x) := by
      obtain ⟨u, hu, hue⟩ := hfull x
      rw [hx'] at hue
      have hxm : x ∈ chg (F u) := by rw [hue]; exact (mem_blk _ _ _).2 hx'
      have hym : y ∈ chg (F u) := by rw [hue]; exact (mem_blk _ _ _).2 hy'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact absurd (hW u hu x hxm y hym) hxy
      · rw [hu] at hxm hym hue
        exact ⟨hxm, hym, hue⟩
    have hmemK : ∀ i, i ∈ chg (F K) ↔ (cls i = cls x ∨ cls i = cls y) := by
      intro i
      rw [hKe, mem_blk, hcls']
      by_cases h1 : cls i = cls y
      · simp [h1]
      · simp [h1]
    have hAe : chg (F a) = blk cls (cls x) := by
      ext i
      rw [mem_blk]
      constructor
      · exact hA i
      · intro hi
        have hiK : i ∈ chg (F K) := (hmemK i).2 (Or.inl hi)
        rcases Finset.mem_union.1 (hsub hiK) with h | h
        · exact h
        · exact absurd (hi.symm.trans (hB i h)) hxy
    have hBe : chg (F b) = blk cls (cls y) := by
      ext i
      rw [mem_blk]
      constructor
      · exact hB i
      · intro hi
        have hiK : i ∈ chg (F K) := (hmemK i).2 (Or.inr hi)
        rcases Finset.mem_union.1 (hsub hiK) with h | h
        · exact absurd ((hA i h).symm.trans hi) hxy
        · exact h
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      by_cases h1 : cls i = cls x
      · exact ⟨a, ha, by rw [h1]; exact hAe⟩
      by_cases h2 : cls i = cls y
      · exact ⟨b, hb, by rw [h2]; exact hBe⟩
      obtain ⟨u, hu, hue⟩ := hfull i
      have hi' : cls' i = cls i := by rw [hcls']; simp [h2]
      have hblk : blk cls' (cls' i) = blk cls (cls i) := by
        rw [hi']
        ext j
        rw [mem_blk, mem_blk, hcls']
        by_cases h3 : cls j = cls y
        · have e1 : (if cls j = cls y then cls x else cls j) = cls x := by simp [h3]
          rw [e1]
          constructor
          · intro h; exact absurd h.symm h1
          · intro h; exact absurd (h3.symm.trans h).symm h2
        · have e1 : (if cls j = cls y then cls x else cls j) = cls j := by simp [h3]
          rw [e1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, by rw [hue, hblk]⟩
      · exfalso
        rw [hu] at hue
        have hiK : i ∈ chg (F K) := by rw [hue]; exact (mem_blk _ _ _).2 rfl
        rcases (hmemK i).1 hiK with h | h
        · exact h1 h
        · exact h2 h
    obtain ⟨hlam, hpol, hsp⟩ := hS ⟨hcardeq, hfullK⟩
    have hKu : chg (F K) = chg (F a) ∪ chg (F b) := by
      apply Finset.Subset.antisymm hsub
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · exact (hmemK i).2 (Or.inl (hA i h))
      · exact (hmemK i).2 (Or.inr (hB i h))
    have hdisj : ∀ i, i ∈ chg (F a) → i ∉ chg (F b) := fun i h1 h2 =>
      hxy ((hA i h1).symm.trans (hB i h2))
    have hold : ∀ u < K, chg (F u) ⊆ chg (F a) ∨ chg (F u) ⊆ chg (F b) ∨
        Disjoint (chg (F u)) (chg (F K)) := by
      intro u hu
      by_cases he : ∃ z, z ∈ chg (F u) ∧ cls z = cls x
      · obtain ⟨z, hz, hzc⟩ := he
        refine Or.inl fun w hw => ?_
        rw [hAe, mem_blk]
        exact (hW u hu w hw z hz).trans hzc
      by_cases he2 : ∃ z, z ∈ chg (F u) ∧ cls z = cls y
      · obtain ⟨z, hz, hzc⟩ := he2
        refine Or.inr (Or.inl fun w hw => ?_)
        rw [hBe, mem_blk]
        exact (hW u hu w hw z hz).trans hzc
      refine Or.inr (Or.inr ?_)
      rw [Finset.disjoint_left]
      intro w hw hwK
      rcases (hmemK w).1 hwK with h | h
      · exact he ⟨w, hw, h⟩
      · exact he2 ⟨w, hw, h⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
      · exact hlam u hu v hv
      · rw [hv]
        rcases hold u hu with h | h | h
        · exact Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_left))
        · exact Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_right))
        · exact Or.inr (Or.inr h)
      · rw [hu]
        rcases hold v hv with h | h | h
        · exact Or.inr (Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_left)))
        · exact Or.inr (Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_right)))
        · exact Or.inr (Or.inr h.symm)
      · rw [hu, hv]
        exact Or.inl (Finset.Subset.refl _)
    · intro u hu v hv hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
      · exact hpol u hu v hv hs
      · rw [hv] at hs ⊢
        by_cases hem : chg (F u) = ∅
        · refine Or.inl fun i hi => ?_
          rw [hem] at hi
          exact absurd hi (Finset.notMem_empty i)
        obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.2 hem
        rcases hold u hu with h | h | h
        · have hk : ∀ i ∈ chg (F u), F K i.castSucc = F a i.castSucc := fun i hi =>
            bin_left hop i (hs hi) (hdisj i (h hi))
          rcases hpol u hu a ha h with hp | hp
          · exact Or.inl fun i hi => by rw [hk i hi]; exact hp i hi
          · exact Or.inr fun i hi => by rw [hk i hi]; exact hp i hi
        · have hk : ∀ i ∈ chg (F u), F K i.castSucc = F b i.castSucc := fun i hi =>
            bin_right hop i (hs hi) (fun hia => hdisj i hia (h hi))
          rcases hpol u hu b hb h with hp | hp
          · exact Or.inl fun i hi => by rw [hk i hi]; exact hp i hi
          · exact Or.inr fun i hi => by rw [hk i hi]; exact hp i hi
        · exact absurd (hs hz) (Finset.disjoint_left.1 h hz)
      · rw [hu] at hs
        exact absurd (hW v hv x (hs hxK) y (hs hyK)) hxy
      · rw [hu, hv]
        exact Or.inl fun _ _ => rfl
    · intro u hu hcard
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact (hsp u hu hcard).mono
      · rw [hu]
        exact ⟨K, Nat.lt_succ_self K, a, Nat.lt_succ_of_lt ha, b, Nat.lt_succ_of_lt hb, rfl, hop,
          Finset.disjoint_left.2 (fun i h1 h2 => hdisj i h1 h2), ⟨x, hx⟩, ⟨y, hy⟩⟩

/-! ### The circuit -/

/-- The ordered input number `t`. -/
def inp (n : ℕ) (t : Fin (n + 1)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i.val < t.val)) ++ [false, true]

theorem inp_len (n : ℕ) (t : Fin (n + 1)) : (inp n t).length = n + 2 := by simp [inp]

/-- The value of wire `u` on the ordered input number `t`. -/
def vl (n : ℕ) (gs : List Gate) (u : ℕ) (t : Fin (n + 1)) : Bool := (W gs (inp n t)).getD u false

theorem vl_old (n : ℕ) (gs : List Gate) (g : Gate) (u : ℕ) (hu : u < n + 2 + gs.length) :
    vl n (gs ++ [g]) u = vl n gs u := by
  funext t
  exact old_wire gs g (inp n t) u (by rw [inp_len]; omega)

theorem vl_new (n : ℕ) (gs : List Gate) (g : Gate) (t : Fin (n + 1)) :
    vl n (gs ++ [g]) (n + 2 + gs.length) t = g.op.eval (g.inputs.map fun i => vl n gs i t) := by
  have h := new_wire gs g (inp n t)
  rw [inp_len] at h
  exact h

theorem inp_getD (n : ℕ) (t : Fin (n + 1)) (u : ℕ) :
    (inp n t).getD u false = if u < n then decide (u < t.val) else decide (u = n + 1) := by
  unfold inp
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · obtain ⟨d, rfl⟩ : ∃ d, u = n + d := ⟨u - n, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rcases d with _ | _ | d
    · simp
    · simp
    · simp

theorem base_chg (n u : ℕ) (i : Fin n) (hi : i ∈ chg (vl n [] u)) : i.val = u := by
  rw [mem_chg] at hi
  simp only [vl, W, List.foldl_nil, inp_getD, Fin.val_castSucc, Fin.val_succ] at hi
  split_ifs at hi with h
  · by_contra hne
    apply hi
    have : (u < i.val) ↔ (u < i.val + 1) := by omega
    simp [this]
  · exact absurd rfl hi

theorem inv_base (n : ℕ) : Inv (vl n []) (n + 2) 0 := by
  refine ⟨fun i => i.val, ?_, ?_, ?_⟩
  · intro u _ i hi j hj
    show i.val = j.val
    rw [base_chg n u i hi, base_chg n u j hj]
  · rw [Finset.card_image_of_injective _ Fin.val_injective]
    simp
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · intro u _ v _
      by_cases h : ∃ i, i ∈ chg (vl n [] u) ∧ i ∈ chg (vl n [] v)
      · obtain ⟨i, h1, h2⟩ := h
        have huv : u = v := (base_chg n u i h1).symm.trans (base_chg n v i h2)
        rw [huv]
        exact Or.inl (Finset.Subset.refl _)
      · refine Or.inr (Or.inr ?_)
        rw [Finset.disjoint_left]
        intro i h1 h2
        exact h ⟨i, h1, h2⟩
    · intro u _ v _ hs
      by_cases h : ∃ i, i ∈ chg (vl n [] u)
      · obtain ⟨i, h1⟩ := h
        have huv : u = v := (base_chg n u i h1).symm.trans (base_chg n v i (hs h1))
        rw [huv]
        exact Or.inl fun _ _ => rfl
      · exact Or.inl fun i hi => absurd ⟨i, hi⟩ h
    · intro u _ hcard
      exfalso
      have hle : (chg (vl n [] u)).card ≤ 1 := Finset.card_le_one.2 fun i hi j hj =>
        Fin.ext ((base_chg n u i hi).trans (base_chg n u j hj).symm)
      omega

theorem inv_all (isNot : Gate → Bool) (hisNot : ∀ g, isNot g = true ↔ g.op = GateOp.not) (n : ℕ) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 2 + j) →
      Inv (vl n gs) (n + 2 + gs.length) (gs.filter fun g => !isNot g).length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ _; exact inv_base n
  | append_singleton gs g ih =>
    intro hF hR
    have ih' := ih (fun g' hg' => hF g' (List.mem_append_left _ hg'))
      (fun j g' hj a ha => hR j g' (by
        have hjl : j < gs.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hj
          simp at hj
        rw [List.getElem?_append_left hjl]
        exact hj) a ha)
    obtain ⟨hgop, hglen⟩ := hF g (by simp)
    have hin : ∀ a ∈ g.inputs, a < n + 2 + gs.length := hR gs.length g (by simp)
    have hI : Inv (vl n (gs ++ [g])) (n + 2 + gs.length) (gs.filter fun g => !isNot g).length :=
      Inv.congr (fun u hu => vl_old n gs g u hu) ih'
    have hnew : ∀ t, vl n (gs ++ [g]) (n + 2 + gs.length) t =
        g.op.eval (g.inputs.map fun i => vl n (gs ++ [g]) i t) := by
      intro t
      rw [vl_new]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [vl_old n gs g i (hin i hi)]
    have e1 : n + 2 + (gs ++ [g]).length = n + 2 + gs.length + 1 := by simp [Nat.add_assoc]
    have e2 : ((gs ++ [g]).filter fun g => !isNot g).length =
        (gs.filter fun g => !isNot g).length + (if isNot g then 0 else 1) := by
      rw [List.filter_append]
      cases h : isNot g <;> simp [h]
    rw [e1, e2]
    by_cases hn : isNot g = true
    · -- a NOT gate
      have hop : g.op = GateOp.not := (hisNot g).1 hn
      have e3 : (if isNot g = true then 0 else 1) = 0 := by simp [hn]
      rw [e3, Nat.add_zero]
      rcases hgi : g.inputs with _ | ⟨a, rest⟩
      · apply Inv.const _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi]
        rfl
      · apply Inv.same (hin a (by rw [hgi]; simp)) _ hI
        refine Or.inr fun t => ?_
        rw [hnew, hgi, hop]
        rfl
    · -- an AND or OR gate
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hgop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd ((hisNot g).2 h) hn
      have e3 : (if isNot g = true then 0 else 1) = 1 := by simp [hn]
      rw [e3]
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · apply Inv.slack
        apply Inv.const _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi]
        rfl
      · apply Inv.slack
        apply Inv.same (hin a (by rw [hgi]; simp)) _ hI
        refine Or.inl fun t => ?_
        rw [hnew, hgi]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
      · apply Inv.bin (hin a (by rw [hgi]; simp)) (hin b (by rw [hgi]; simp)) _ hI
        rcases hop with h | h
        · refine Or.inl fun t => ?_
          rw [hnew, hgi, h]
          simp [GateOp.eval]
        · refine Or.inr fun t => ?_
          rw [hnew, hgi, h]
          simp [GateOp.eval]
      · rw [hgi] at hglen
        simp at hglen

theorem filter_split (p : Gate → Bool) (l : List Gate) :
    (l.filter p).length + (l.filter fun g => !p g).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h] <;> omega

theorem main (n : ℕ) (C : Circuit) (root : Fin (n + 2 + C.size))
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hP : C.size - PEqualNP.NotBracket.notCount C ≤ n - 1)
    (hroot : chg (vl n C.gates root.val) = Finset.univ) :
    Str (vl n C.gates) (n + 2 + C.gates.length) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨?_, ?_, ?_⟩
    · intro u _ v _
      exact Or.inl (by rw [Finset.eq_empty_of_isEmpty (chg (vl 0 C.gates u))]; exact Finset.empty_subset _)
    · intro u _ v _ _
      exact Or.inl fun i _ => i.elim0
    · intro u _ hcard
      rw [Finset.eq_empty_of_isEmpty (chg (vl 0 C.gates u))] at hcard
      simp at hcard
  have hP2 := hP
  unfold PEqualNP.NotBracket.notCount Circuit.size at hP2
  obtain ⟨isNot, hisNot, hPle⟩ : ∃ isNot : Gate → Bool,
      (∀ g, isNot g = true ↔ g.op = GateOp.not) ∧
        C.gates.length - (C.gates.filter isNot).length ≤ n - 1 := by
    refine ⟨_, ?_, hP2⟩
    intro g
    simp only [decide_eq_true_eq]
  have hInv := inv_all isNot hisNot n C.gates
    (fun g hg => by
      obtain ⟨h1, h2⟩ := hF g hg
      refine ⟨?_, h2⟩
      simpa using h1)
    (fun j g hj a ha => by
      have hjl : j < C.gates.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hj
        simp at hj
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, hj]
        rfl
      exact hR j hjl a (by rw [e]; exact ha))
  obtain ⟨cls, hW, hN, hS⟩ := hInv
  have hsplit := filter_split isNot C.gates
  have hall : ∀ i j : Fin n, cls i = cls j := fun i j =>
    hW root.val root.isLt i (by rw [hroot]; exact Finset.mem_univ _) j
      (by rw [hroot]; exact Finset.mem_univ _)
  have hc1 : (Finset.univ.image cls).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro c hc d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hd
    exact hall i j
  apply hS
  refine ⟨by omega, fun i => ⟨root.val, root.isLt, ?_⟩⟩
  rw [hroot]
  ext j
  rw [mem_blk]
  simp [hall j i]

/-! ### Colours on the steps -/

/-- A word that changes at every step alternates. -/
theorem alt_word {n : ℕ} (f : Fin (n + 1) → Bool) (hf : chg f = Finset.univ) :
    ∀ (t : ℕ) (ht : t < n + 1),
      f ⟨t, ht⟩ = Bool.xor (f ⟨0, Nat.succ_pos n⟩) (decide (t % 2 = 1)) := by
  intro t
  induction t with
  | zero => intro ht; simp
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    have hstep := (mem_chg f ⟨t, htn⟩).1 (by rw [hf]; exact Finset.mem_univ _)
    have e1 : Fin.castSucc (⟨t, htn⟩ : Fin n) = (⟨t, by omega⟩ : Fin (n + 1)) := rfl
    have e2 : Fin.succ (⟨t, htn⟩ : Fin n) = (⟨t + 1, ht⟩ : Fin (n + 1)) := rfl
    rw [e1, e2, ih (by omega)] at hstep
    have hpar : decide ((t + 1) % 2 = 1) = !decide (t % 2 = 1) := by
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · have h' : (t + 1) % 2 = 1 := by omega
        simp [h, h']
      · have h' : (t + 1) % 2 = 0 := by omega
        simp [h, h']
    rw [hpar]
    revert hstep
    cases f ⟨0, Nat.succ_pos n⟩ <;> cases decide (t % 2 = 1) <;> cases f ⟨t + 1, ht⟩ <;> simp

theorem partA (n d : ℕ) (color : Fin n → Fin d) (hd : 2 ≤ d) (hsurj : Function.Surjective color)
    (hobs : ∀ (U : Finset (Fin d)) (p : Fin 2), U.Nonempty → U ≠ Finset.univ →
      ∃ i j : Fin n, j.val = i.val + 1 ∧ i.val % 2 = p.val ∧ ¬ (color i ∈ U ↔ color j ∈ U))
    (C : Circuit) (root : ℕ) (tap : Fin d → ℕ)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hroot : root < n + 2 + C.size) (htap : ∀ j, tap j < n + 2 + C.size)
    (hP : C.size - PEqualNP.NotBracket.notCount C ≤ n - 1)
    (hr : chg (vl n C.gates root) = Finset.univ)
    (ht : ∀ j i, i ∈ chg (vl n C.gates (tap j)) ↔ color i = j) : False := by
  obtain ⟨hlam, -, hsp⟩ := main n C ⟨root, hroot⟩ hF hR hP hr
  have hn2 : 2 ≤ n := by
    have h := Fintype.card_le_of_surjective color hsurj
    simp only [Fintype.card_fin] at h
    omega
  have hcardr : 2 ≤ (chg (vl n C.gates root)).card := by
    rw [hr, Finset.card_univ, Fintype.card_fin]
    exact hn2
  obtain ⟨g, hg, a, ha, b, hb, hge, hop, hdis, hna, hnb⟩ := hsp root hroot hcardr
  rw [hr] at hge
  have hAB : ∀ i, i ∈ chg (vl n C.gates a) ∨ i ∈ chg (vl n C.gates b) := fun i =>
    Finset.mem_union.1 (bin_sub hop (by rw [hge]; exact Finset.mem_univ i))
  -- steps of one colour are on the same side
  have hclass : ∀ i i' : Fin n, color i = color i' →
      (i ∈ chg (vl n C.gates a) ↔ i' ∈ chg (vl n C.gates a)) := by
    intro i i' hc
    have hi : i ∈ chg (vl n C.gates (tap (color i))) := (ht _ i).2 rfl
    have hi' : i' ∈ chg (vl n C.gates (tap (color i))) := (ht _ i').2 hc.symm
    rcases hlam (tap (color i)) (htap _) a ha with h | h | h
    · exact ⟨fun _ => h hi', fun _ => h hi⟩
    · rcases hlam (tap (color i)) (htap _) b hb with h2 | h2 | h2
      · exfalso
        obtain ⟨z, hz⟩ := hna
        exact Finset.disjoint_left.1 hdis hz (h2 (h hz))
      · exfalso
        obtain ⟨j', hj'⟩ : ∃ j' : Fin d, j' ≠ color i := by
          by_cases h0 : (color i).val = 0
          · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
          · exact ⟨⟨0, by omega⟩, fun e => h0 (by rw [← e])⟩
        obtain ⟨z, hz⟩ := hsurj j'
        have hzT : z ∈ chg (vl n C.gates (tap (color i))) := by
          rcases hAB z with h3 | h3
          · exact h h3
          · exact h2 h3
        exact hj' (hz.symm.trans ((ht _ z).1 hzT))
      · have e1 : i ∈ chg (vl n C.gates a) := by
          rcases hAB i with h3 | h3
          · exact h3
          · exact absurd h3 (Finset.disjoint_left.1 h2 hi)
        have e2 : i' ∈ chg (vl n C.gates a) := by
          rcases hAB i' with h3 | h3
          · exact h3
          · exact absurd h3 (Finset.disjoint_left.1 h2 hi')
        exact ⟨fun _ => e2, fun _ => e1⟩
    · exact ⟨fun h1 => absurd h1 (Finset.disjoint_left.1 h hi),
        fun h1 => absurd h1 (Finset.disjoint_left.1 h hi')⟩
  -- the colours with a step on the side of `a`
  have hU : ∀ i, color i ∈ (chg (vl n C.gates a)).image color ↔ i ∈ chg (vl n C.gates a) := by
    intro i
    constructor
    · intro h
      obtain ⟨i0, hi0, e⟩ := Finset.mem_image.1 h
      exact (hclass i0 i e).1 hi0
    · intro h
      exact Finset.mem_image_of_mem color h
  have hUne : ((chg (vl n C.gates a)).image color).Nonempty := hna.image color
  have hUuniv : (chg (vl n C.gates a)).image color ≠ Finset.univ := by
    intro hUu
    obtain ⟨z, hz⟩ := hnb
    have hzU : color z ∈ (chg (vl n C.gates a)).image color := by rw [hUu]; exact Finset.mem_univ _
    exact Finset.disjoint_left.1 hdis ((hU z).1 hzU) hz
  -- wire `a` over two adjacent steps of which it changes at exactly one
  have hcross : ∀ i j : Fin n, j.val = i.val + 1 →
      ¬ (i ∈ chg (vl n C.gates a) ↔ j ∈ chg (vl n C.gates a)) →
      vl n C.gates a i.castSucc ≠ vl n C.gates a j.succ := by
    intro i j hji hx
    have es : i.succ = j.castSucc := Fin.ext (by simp [hji])
    have h1 := mem_chg (vl n C.gates a) i
    have h2 := mem_chg (vl n C.gates a) j
    rw [es] at h1
    by_cases hi : i ∈ chg (vl n C.gates a)
    · have hj : j ∉ chg (vl n C.gates a) := fun hj => hx ⟨fun _ => hj, fun _ => hi⟩
      have q1 := h1.1 hi
      have q2 : vl n C.gates a j.castSucc = vl n C.gates a j.succ :=
        not_not.1 (fun q => hj (h2.2 q))
      rw [← q2]
      exact q1
    · have hj : j ∈ chg (vl n C.gates a) := by
        by_contra hj
        exact hx ⟨fun h => absurd h hi, fun h => absurd h hj⟩
      have q1 : vl n C.gates a i.castSucc = vl n C.gates a j.castSucc :=
        not_not.1 (fun q => hi (h1.2 q))
      rw [q1]
      exact h2.1 hj
  have hgalt := alt_word (vl n C.gates g) hge
  have hfin : ∀ e : Bool, (∀ t, vl n C.gates g t = e → vl n C.gates a t = e) → False := by
    intro e he
    obtain ⟨p0, hp0⟩ : ∃ p0 : Fin 2, ∀ (t : ℕ) (ht : t < n + 1), t % 2 = p0.val →
        vl n C.gates g ⟨t, ht⟩ = e := by
      by_cases h0 : vl n C.gates g ⟨0, Nat.succ_pos n⟩ = e
      · refine ⟨0, fun t ht hpar => ?_⟩
        have hp' : t % 2 = 0 := by simpa using hpar
        have hdec : decide (t % 2 = 1) = false := by simp [hp']
        rw [hgalt t ht, hdec, h0]
        simp
      · refine ⟨1, fun t ht hpar => ?_⟩
        have hp' : t % 2 = 1 := by simpa using hpar
        have hdec : decide (t % 2 = 1) = true := by simp [hp']
        rw [hgalt t ht, hdec]
        revert h0
        cases vl n C.gates g ⟨0, Nat.succ_pos n⟩ <;> cases e <;> simp
    obtain ⟨i, j, hji, hip, hx⟩ := hobs _ p0 hUne hUuniv
    rw [hU i, hU j] at hx
    have v0 := he _ (hp0 i.val (by omega) hip)
    have v2 := he _ (hp0 (j.val + 1) (by omega) (by omega))
    exact hcross i j hji hx (v0.trans v2.symm)
  rcases hop with hand | hor
  · refine hfin true fun t h => ?_
    rw [hand] at h
    simp at h
    exact h.1
  · refine hfin false fun t h => ?_
    rw [hor] at h
    simp at h
    exact h.1

/-- On a path a nonempty set that is not everything is left between two neighbours. -/
theorem path_cross (d : ℕ) (U : Finset (Fin d)) (hne : U.Nonempty) (huniv : U ≠ Finset.univ) :
    ∃ c : ℕ, ∃ h : c + 1 < d,
      ¬ ((⟨c, by omega⟩ : Fin d) ∈ U ↔ (⟨c + 1, h⟩ : Fin d) ∈ U) := by
  by_contra hcon
  have hall : ∀ (c : ℕ) (h : c + 1 < d),
      ((⟨c, by omega⟩ : Fin d) ∈ U ↔ (⟨c + 1, h⟩ : Fin d) ∈ U) := by
    intro c h
    by_contra hc
    exact hcon ⟨c, h, hc⟩
  have hprop : ∀ (c : ℕ) (h : c < d),
      ((⟨c, h⟩ : Fin d) ∈ U ↔ (⟨0, by omega⟩ : Fin d) ∈ U) := by
    intro c
    induction c with
    | zero => intro h; exact Iff.rfl
    | succ c ih => intro h; exact (hall c h).symm.trans (ih (by omega))
  obtain ⟨z, hz⟩ := hne
  apply huniv
  ext w
  simp only [Finset.mem_univ, iff_true]
  exact (hprop w.val w.isLt).2 ((hprop z.val z.isLt).1 hz)

theorem obs_mod (D : ℕ) (hD : D % 2 = 1) (color : Fin (2 * D) → Fin D)
    (hcol : ∀ i, (color i).val = i.val % D) :
    ∀ (U : Finset (Fin D)) (p : Fin 2), U.Nonempty → U ≠ Finset.univ →
      ∃ i j : Fin (2 * D), j.val = i.val + 1 ∧ i.val % 2 = p.val ∧
        ¬ (color i ∈ U ↔ color j ∈ U) := by
  intro U p hne huniv
  obtain ⟨c, hc, hx⟩ := path_cross D U hne huniv
  have hp : p.val < 2 := p.isLt
  obtain ⟨i, hi1, hi2, hi3⟩ : ∃ i : ℕ, i + 1 < 2 * D ∧ i % 2 = p.val ∧ (i = c ∨ i = c + D) := by
    by_cases hpar : c % 2 = p.val
    · exact ⟨c, by omega, hpar, Or.inl rfl⟩
    · exact ⟨c + D, by omega, by omega, Or.inr rfl⟩
  refine ⟨⟨i, by omega⟩, ⟨i + 1, hi1⟩, rfl, hi2, ?_⟩
  have e1 : color ⟨i, by omega⟩ = ⟨c, by omega⟩ := by
    apply Fin.ext
    rw [hcol]
    show i % D = c
    rcases hi3 with h | h
    · rw [h]; exact Nat.mod_eq_of_lt (by omega)
    · rw [h, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : color ⟨i + 1, hi1⟩ = ⟨c + 1, hc⟩ := by
    apply Fin.ext
    rw [hcol]
    show (i + 1) % D = c + 1
    rcases hi3 with h | h
    · rw [h]; exact Nat.mod_eq_of_lt hc
    · rw [h, show c + D + 1 = c + 1 + D by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hc
  rw [e1, e2]
  exact hx

/-! ### The circuit for the doubled cycle -/

theorem W_append (l1 l2 : List Gate) (w : List Bool) : W (l1 ++ l2) w = W l2 (W l1 w) := by
  simp [W, List.foldl_append]

/-- A list of gates given by a rule computes a table of values if every gate does. -/
theorem W_spec (Ev : ℕ → Bool) (f : ℕ → Gate) (xs : List Bool)
    (hxs : ∀ w < xs.length, xs.getD w false = Ev w) :
    ∀ m : ℕ, (∀ j < m, (f j).op.eval ((f j).inputs.map Ev) = Ev (xs.length + j)) →
      (∀ j < m, ∀ a ∈ (f j).inputs, a < xs.length + j) →
      ∀ w < xs.length + m, (W ((List.range m).map f) xs).getD w false = Ev w := by
  intro m
  induction m with
  | zero =>
    intro _ _ w hw
    simpa [W] using hxs w (by omega)
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

/-- The NOT of input `k`. -/
def notG (k : ℕ) : Gate := ⟨GateOp.not, [k]⟩

/-- The gates after the NOT gates: `D` taps, `D` single-level tests (the test for level 1 last),
`D - 1` ORs. -/
def posG (D j : ℕ) : Gate :=
  if j < D then ⟨GateOp.and, [j, 2 * D + 2 + (j + D)]⟩
  else if j < 2 * D then
    ⟨GateOp.and, [2 * (2 * D - 1 - j), 2 * D + 2 + (2 * (2 * D - 1 - j) + 1)]⟩
  else ⟨GateOp.or, [4 * D + 2 + j - 1, 8 * D - j]⟩

theorem posG_tap (D j : ℕ) (h : j < D) : posG D j = ⟨GateOp.and, [j, 2 * D + 2 + (j + D)]⟩ := by
  simp [posG, h]

theorem posG_test (D j : ℕ) (h1 : ¬ j < D) (h2 : j < 2 * D) :
    posG D j = ⟨GateOp.and, [2 * (2 * D - 1 - j), 2 * D + 2 + (2 * (2 * D - 1 - j) + 1)]⟩ := by
  simp [posG, h1, h2]

theorem posG_or (D j : ℕ) (h1 : ¬ j < D) (h2 : ¬ j < 2 * D) :
    posG D j = ⟨GateOp.or, [4 * D + 2 + j - 1, 8 * D - j]⟩ := by
  simp [posG, h1, h2]

/-- The circuit. -/
def circ (D : ℕ) : Circuit :=
  ⟨(List.range (2 * D)).map notG ++ (List.range (3 * D - 1)).map (posG D), 0⟩

/-- The value of wire `w` at level `t`. -/
def E (D t w : ℕ) : Bool :=
  if w < 2 * D then decide (w < t)
  else if w < 2 * D + 2 then decide (w = 2 * D + 1)
  else if w < 4 * D + 2 then decide (t ≤ w - (2 * D + 2))
  else if w < 5 * D + 2 then decide (w - (4 * D + 2) < t ∧ t ≤ w - (4 * D + 2) + D)
  else if w < 6 * D + 2 then decide (t = 2 * (6 * D + 1 - w) + 1)
  else decide (t % 2 = 1 ∧ t ≤ 2 * (w - (6 * D + 1)) + 1)

theorem E_in (D t w : ℕ) (h : w < 2 * D) : E D t w = decide (w < t) := by
  simp [E, h]

theorem E_not (D t k : ℕ) (h : k < 2 * D) : E D t (2 * D + 2 + k) = decide (t ≤ k) := by
  have a2 : ¬ (2 * D + 2 + k < 2 * D) := by omega
  have a3 : ¬ (2 * D + 2 + k < 2 * D + 2) := by omega
  have a4 : 2 * D + 2 + k < 4 * D + 2 := by omega
  have a5 : 2 * D + 2 + k - (2 * D + 2) = k := by omega
  simp [E, a2, a3, a4, a5]

theorem E_tap (D t j : ℕ) (h : j < D) :
    E D t (4 * D + 2 + j) = decide (j < t ∧ t ≤ j + D) := by
  have a2 : ¬ (4 * D + 2 + j < 2 * D) := by omega
  have a3 : ¬ (4 * D + 2 + j < 2 * D + 2) := by omega
  have a4 : ¬ (4 * D + 2 + j < 4 * D + 2) := by omega
  have a5 : 4 * D + 2 + j < 5 * D + 2 := by omega
  have a6 : 4 * D + 2 + j - (4 * D + 2) = j := by omega
  simp [E, a2, a3, a4, a5, a6]

theorem E_test (D t m w : ℕ) (h : m < D) (hw : w = 6 * D + 1 - m) :
    E D t w = decide (t = 2 * m + 1) := by
  have a2 : ¬ (w < 2 * D) := by omega
  have a3 : ¬ (w < 2 * D + 2) := by omega
  have a4 : ¬ (w < 4 * D + 2) := by omega
  have a5 : ¬ (w < 5 * D + 2) := by omega
  have a6 : w < 6 * D + 2 := by omega
  have a7 : 6 * D + 1 - w = m := by omega
  simp [E, a2, a3, a4, a5, a6, a7]

theorem E_or (D t r w : ℕ) (h : 1 ≤ r) (hw : w = 6 * D + 1 + r) :
    E D t w = decide (t % 2 = 1 ∧ t ≤ 2 * r + 1) := by
  have a2 : ¬ (w < 2 * D) := by omega
  have a3 : ¬ (w < 2 * D + 2) := by omega
  have a4 : ¬ (w < 4 * D + 2) := by omega
  have a5 : ¬ (w < 5 * D + 2) := by omega
  have a6 : ¬ (w < 6 * D + 2) := by omega
  have a7 : w - (6 * D + 1) = r := by omega
  simp [E, a2, a3, a4, a5, a6, a7]

theorem circ_val (D t : ℕ) (hD : 0 < D) :
    ∀ w < 7 * D + 1, (W (circ D).gates (inpN (2 * D) t)).getD w false = E D t w := by
  have h0 : ∀ w < (inpN (2 * D) t).length, (inpN (2 * D) t).getD w false = E D t w := by
    intro w hw
    rw [inpN_len] at hw
    rw [inpN_getD]
    by_cases h1 : w < 2 * D
    · simp [E, h1]
    · have h2 : w < 2 * D + 2 := hw
      simp [E, h1, h2]
  have h1 := W_spec (E D t) notG (inpN (2 * D) t) h0 (2 * D)
    (by
      intro j hj
      rw [inpN_len, E_not D t j hj]
      show (!(([j].map (E D t)).headD false)) = decide (t ≤ j)
      simp only [List.map_cons, List.map_nil, List.headD_cons]
      rw [E_in D t j hj, ← decide_not, decide_eq_decide]
      omega)
    (by
      intro j hj a ha
      rw [inpN_len]
      simp [notG] at ha
      omega)
  have hl1 : (W ((List.range (2 * D)).map notG) (inpN (2 * D) t)).length = 4 * D + 2 := by
    rw [W_len, inpN_len]
    simp
    omega
  have h2 := W_spec (E D t) (posG D) (W ((List.range (2 * D)).map notG) (inpN (2 * D) t))
    (by
      intro w hw
      rw [hl1] at hw
      exact h1 w (by rw [inpN_len]; omega))
    (3 * D - 1)
    (by
      intro j hj
      rw [hl1]
      by_cases c1 : j < D
      · rw [posG_tap D j c1, E_tap D t j c1]
        show (([j, 2 * D + 2 + (j + D)].map (E D t)).all id) = _
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
        rw [E_in D t j (by omega), E_not D t (j + D) (by omega), Bool.decide_and]
      · by_cases c2 : j < 2 * D
        · rw [posG_test D j c1 c2, E_test D t (2 * D - 1 - j) (4 * D + 2 + j) (by omega) (by omega)]
          show (([2 * (2 * D - 1 - j), 2 * D + 2 + (2 * (2 * D - 1 - j) + 1)].map (E D t)).all id) = _
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
          rw [E_in D t _ (by omega), E_not D t _ (by omega), ← Bool.decide_and, decide_eq_decide]
          omega
        · rw [posG_or D j c1 c2]
          show (([4 * D + 2 + j - 1, 8 * D - j].map (E D t)).any id) = _
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
          rw [E_test D t (j - 2 * D + 1) (8 * D - j) (by omega) (by omega),
            E_or D t (j - 2 * D + 1) (4 * D + 2 + j) (by omega) (by omega)]
          by_cases c3 : j = 2 * D
          · rw [E_test D t 0 (4 * D + 2 + j - 1) (by omega) (by omega), ← Bool.decide_or,
              decide_eq_decide]
            omega
          · rw [E_or D t (j - 2 * D) (4 * D + 2 + j - 1) (by omega) (by omega), ← Bool.decide_or,
              decide_eq_decide]
            omega)
    (by
      intro j hj a ha
      rw [hl1]
      by_cases c1 : j < D
      · rw [posG_tap D j c1] at ha
        simp at ha
        omega
      · by_cases c2 : j < 2 * D
        · rw [posG_test D j c1 c2] at ha
          simp at ha
          omega
        · rw [posG_or D j c1 c2] at ha
          simp at ha
          omega)
  intro w hw
  show (W ((List.range (2 * D)).map notG ++ (List.range (3 * D - 1)).map (posG D))
    (inpN (2 * D) t)).getD w false = E D t w
  rw [W_append]
  exact h2 w (by rw [hl1]; omega)

theorem circ_gate (D j : ℕ) (d : Gate) (hj : j < 5 * D - 1) :
    (circ D).gates.getD j d = if j < 2 * D then notG j else posG D (j - 2 * D) := by
  unfold circ
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt h),
      List.getD_eq_getElem _ _ (by simp; omega)]
    simp

theorem circ_size (D : ℕ) (hD : 0 < D) : (circ D).gates.length = 5 * D - 1 := by
  simp [circ]
  omega

theorem circ_nots (D : ℕ) (isNot : Gate → Bool) (hisNot : ∀ g, isNot g = true ↔ g.op = GateOp.not) :
    ((circ D).gates.filter isNot).length = 2 * D := by
  have e1 : ((List.range (2 * D)).map notG).filter isNot = (List.range (2 * D)).map notG := by
    apply List.filter_eq_self.2
    intro g hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact (hisNot _).2 rfl
  have e2 : ((List.range (3 * D - 1)).map (posG D)).filter isNot = [] := by
    apply List.filter_eq_nil_iff.2
    intro g hg hc
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    have hop := (hisNot _).1 hc
    unfold posG at hop
    split_ifs at hop
  show (((List.range (2 * D)).map notG ++ (List.range (3 * D - 1)).map (posG D)).filter isNot).length
    = 2 * D
  rw [List.filter_append, e1, e2]
  simp

theorem fit_circ (D : ℕ) (hD : 2 ≤ D) (color : Fin (2 * D) → Fin D)
    (hcol : ∀ i, (color i).val = i.val % D) :
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (root : Nat) (tap : Fin D → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * D + 2) C ∧
      root < 2 * D + 2 + C.size ∧ (∀ j, tap j < 2 * D + 2 + C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ 3 * D - 1 ∧
      PEqualNP.NotBracket.notCount C ≤ 2 * D ∧
      ((∀ i : Fin (2 * D), (W C.gates (inpN (2 * D) i.val)).getD root false ≠
          (W C.gates (inpN (2 * D) (i.val + 1))).getD root false) ∧
        ∀ (j : Fin D) (i : Fin (2 * D)), ((W C.gates (inpN (2 * D) i.val)).getD (tap j) false ≠
          (W C.gates (inpN (2 * D) (i.val + 1))).getD (tap j) false) ↔ color i = j) := by
  have hsz : (circ D).size = 5 * D - 1 := circ_size D (by omega)
  obtain ⟨isNot, hisNot, hnc⟩ : ∃ isNot : Gate → Bool,
      (∀ g, isNot g = true ↔ g.op = GateOp.not) ∧
        PEqualNP.NotBracket.notCount (circ D) = ((circ D).gates.filter isNot).length := by
    refine ⟨_, ?_, rfl⟩
    intro g
    simp only [decide_eq_true_eq]
  have hnots : PEqualNP.NotBracket.notCount (circ D) = 2 * D := by
    rw [hnc]
    exact circ_nots D isNot hisNot
  refine ⟨circ D, 7 * D, fun j => 4 * D + 2 + j.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h
      exact ⟨by simp [notG], by simp [notG]⟩
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h
      unfold posG
      split_ifs
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
  · intro j hj i hi
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [circ_gate D j _ (by rw [← circ_size D (by omega)]; exact hj)] at hi
    split_ifs at hi with c0
    · simp [notG] at hi
      omega
    · by_cases c1 : j - 2 * D < D
      · rw [posG_tap D _ c1] at hi
        simp at hi
        omega
      · by_cases c2 : j - 2 * D < 2 * D
        · rw [posG_test D _ c1 c2] at hi
          simp at hi
          omega
        · rw [posG_or D _ c1 c2] at hi
          simp at hi
          have hj' : j < 5 * D - 1 := by rw [← circ_size D (by omega)]; exact hj
          omega
  · rw [hsz]; omega
  · intro j
    have hj := j.isLt
    show 4 * D + 2 + j.val < 2 * D + 2 + (circ D).size
    rw [hsz]
    omega
  · rw [hsz, hnots]; omega
  · rw [hnots]
  · intro i
    have hi := i.isLt
    rw [circ_val D i.val (by omega) (7 * D) (by omega),
      circ_val D (i.val + 1) (by omega) (7 * D) (by omega),
      E_or D i.val (D - 1) (7 * D) (by omega) (by omega),
      E_or D (i.val + 1) (D - 1) (7 * D) (by omega) (by omega)]
    intro heq
    rw [decide_eq_decide] at heq
    omega
  · intro j i
    have hi := i.isLt
    have hj := j.isLt
    rw [circ_val D i.val (by omega) (4 * D + 2 + j.val) (by omega),
      circ_val D (i.val + 1) (by omega) (4 * D + 2 + j.val) (by omega),
      E_tap D i.val j.val hj, E_tap D (i.val + 1) j.val hj, Ne, decide_eq_decide, Fin.ext_iff, hcol]
    have hmod : i.val % D = if i.val < D then i.val else i.val - D := by
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [Nat.mod_eq_sub_mod (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    split_ifs with h
    · constructor
      · intro hx
        by_contra hne
        apply hx
        constructor <;> intro <;> omega
      · intro he hx
        omega
    · constructor
      · intro hx
        by_contra hne
        apply hx
        constructor <;> intro <;> omega
      · intro he hx
        omega

end PEqualNP.Outside.L_lib_1378

theorem PEqualNP.Outside.L_lib_1378 :
let obstruction := fun (n d : Nat) (color : Fin n → Fin d) =>
  ∀ (U : Finset (Fin d)) (p : Fin 2), U.Nonempty → U ≠ Finset.univ →
    ∃ i j : Fin n, j.val = i.val+1 ∧ i.val % 2 = p.val ∧
      ¬ (color i ∈ U ↔ color j ∈ U)
let fit := fun (n d : Nat) (color : Fin n → Fin d) (p b : Nat) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (root : Nat) (tap : Fin d → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    root < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    let flip := fun (w : Nat) (i : Fin n) =>
      let atLevel := fun (t : Nat) => (C.wires
        (List.ofFn (fun k : Fin n => decide (k.val < t)) ++ [false,true])).getD w false
      atLevel i.val ≠ atLevel (i.val+1)
    (∀ i, flip root i) ∧ ∀ j i, flip (tap j) i ↔ color i = j
(∀ (n d : Nat) (color : Fin n → Fin d), 2 ≤ d → Function.Surjective color →
  obstruction n d color → ∀ b, ¬ fit n d color (n-1) b) ∧
∀ h : Nat, 0 < h →
  let d := 2*h+1
  ∀ color : Fin (2*d) → Fin d, (∀ i, (color i).val = i.val % d) →
    obstruction (2*d) d color ∧ (∀ b, ¬ fit (2*d) d color (2*d-1) b) ∧
    fit (2*d) d color (3*d-1) (2*d) := by
  intro obstruction fit
  have hA : ∀ (n d : Nat) (color : Fin n → Fin d), 2 ≤ d → Function.Surjective color →
      obstruction n d color → ∀ b, ¬ fit n d color (n-1) b := by
    intro n d color hd hsurj hobs b hfit
    obtain ⟨C, root, tap, hF, hR, hroot, htap, hP, -, hflip⟩ := hfit
    obtain ⟨hr, ht⟩ := hflip
    refine PEqualNP.Outside.L_lib_1378.partA n d color hd hsurj hobs C root tap hF hR hroot htap hP
      ?_ ?_
    · ext i
      simp only [Finset.mem_univ, iff_true]
      exact (PEqualNP.Outside.L_lib_1378.mem_chg _ i).2 (hr i)
    · intro j i
      rw [PEqualNP.Outside.L_lib_1378.mem_chg]
      exact ht j i
  refine ⟨hA, ?_⟩
  intro h hh d color hcol
  have hobs : obstruction (2*d) d color :=
    PEqualNP.Outside.L_lib_1378.obs_mod (2 * h + 1) (by omega) color hcol
  refine ⟨hobs, ?_, ?_⟩
  · refine hA (2*d) d color (by omega) ?_ hobs
    intro j
    refine ⟨⟨j.val, by omega⟩, Fin.ext ?_⟩
    rw [hcol]
    exact Nat.mod_eq_of_lt j.isLt
  · obtain ⟨C, root, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      PEqualNP.Outside.L_lib_1378.fit_circ (2 * h + 1) (by omega) color hcol
    exact ⟨C, root, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩
