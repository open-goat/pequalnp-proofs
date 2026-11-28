import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33646

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F2 : Type := ZMod 2

def b2f (b : Bool) : F2 := if b then 1 else 0

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (x : F2) : x + x = 0 := by
  rcases f2_cases x with rfl | rfl <;> decide

lemma f2_eq_of_add_eq_zero {x y : F2} (h : x + y = 0) : x = y := by
  rcases f2_cases x with rfl | rfl <;> rcases f2_cases y with rfl | rfl <;> first | rfl | exact absurd h (by decide)

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_not (a : Bool) : b2f (!a) = b2f a + 1 := by
  cases a <;> decide

lemma b2f_inj {a b : Bool} (h : b2f a = b2f b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthStep (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]

def wireStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun a => ws.getD a false))]

def depthsOf (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl depthStep (List.replicate width 0)

def wiresOf (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl wireStep inp

lemma nat_max_zero (a : ℕ) : max a 0 = a := max_eq_left (Nat.zero_le a)

lemma foldl_depthStep_length (ds : List ℕ) (gs : List Gate) :
    (gs.foldl depthStep ds).length = ds.length + gs.length := by
  induction gs generalizing ds with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, depthStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma depthsOf_length (width : ℕ) (gs : List Gate) :
    (depthsOf width gs).length = width + gs.length := by
  simp [depthsOf, foldl_depthStep_length]

lemma foldl_wireStep_length (ws : List Bool) (gs : List Gate) :
    (gs.foldl wireStep ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_length (gs : List Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  simp [wiresOf, foldl_wireStep_length]

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma foldl_depthStep_getD_old (ds : List ℕ) (gs : List Gate) (w : ℕ) (hw : w < ds.length) :
    (gs.foldl depthStep ds).getD w 0 = ds.getD w 0 := by
  induction gs generalizing ds with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (depthStep ds g).length := by simp [depthStep]; omega
    rw [ih (depthStep ds g) hw']
    exact getD_append_left ds _ w 0 hw

lemma foldl_wireStep_getD_old (ws : List Bool) (gs : List Gate) (w : ℕ) (hw : w < ws.length) :
    (gs.foldl wireStep ws).getD w false = ws.getD w false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (wireStep ws g).length := by simp [wireStep]; omega
    rw [ih (wireStep ws g) hw']
    exact getD_append_left ws _ w false hw

lemma gate_eval_expand_two (op : GateOp) :
    ∃ c0 c1 c2 : F2, ∀ x y : Bool,
      b2f (op.eval [x, y]) =
        c0 + c1 * b2f x + c2 * b2f y +
        b2f (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2f x * b2f y) := by
  refine ⟨b2f (op.eval [false, false]),
    b2f (op.eval [true, false]) + b2f (op.eval [false, false]),
    b2f (op.eval [false, true]) + b2f (op.eval [false, false]), ?_⟩
  intro x y
  have hb0 : b2f false = 0 := rfl
  have hb1 : b2f true = 1 := rfl
  simp only [b2f_xor]
  cases x <;> cases y
  · simp only [hb0, mul_zero, add_zero]
  · simp only [hb0, hb1, mul_zero, mul_one, add_zero]
    have h := f2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [hb0, hb1, mul_zero, mul_one, add_zero]
    have h := f2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [hb1, mul_one]
    have h1 := f2_add_self (b2f (op.eval [false, false]))
    have h2 := f2_add_self (b2f (op.eval [false, true]))
    have h3 := f2_add_self (b2f (op.eval [true, false]))
    linear_combination -h1 - h1 - h2 - h3

lemma gate_eval_expand_one (op : GateOp) :
    ∃ c0 c1 : F2, ∀ x : Bool, b2f (op.eval [x]) = c0 + c1 * b2f x := by
  refine ⟨b2f (op.eval [false]), b2f (op.eval [true]) + b2f (op.eval [false]), ?_⟩
  intro x
  have hb0 : b2f false = 0 := rfl
  have hb1 : b2f true = 1 := rfl
  cases x <;> simp only [hb0, hb1, mul_zero, mul_one, add_zero]
  have h := f2_add_self (b2f (op.eval [false]))
  linear_combination -h

-- Section 1: Matrix rank lemmas over F2

lemma rank_vecMulVec_le {n m : ℕ} (p : Fin n → F2) (q : Fin m → F2) :
    (Matrix.of fun i j => p i * q j).rank ≤ 1 := by
  let A : Matrix (Fin n) (Fin m) F2 := Matrix.of fun i j => p i * q j
  have hsub : LinearMap.range A.mulVecLin ≤ Submodule.span F2 {p} := by
    rintro _ ⟨v, rfl⟩
    have heq : A.mulVecLin v = (∑ j : Fin m, q j * v j) • p := by
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, A,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton p))
  have hle1 : Module.finrank F2 (LinearMap.range A.mulVecLin) ≤ Module.finrank F2 (Submodule.span F2 {p}) :=
    Submodule.finrank_mono hsub
  have hle2 : Module.finrank F2 (Submodule.span F2 {p}) ≤ 1 := by
    have h := finrank_span_le_card (R := F2) ({p} : Set (Fin n → F2))
    simpa using h
  exact le_trans hle1 hle2

lemma rank_add_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A B : Matrix ι κ F2) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have heq : (A + B).mulVecLin v = A.mulVecLin v + B.mulVecLin v := by
      ext i; simp
    rw [heq]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h1 : Module.finrank F2 (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank F2 (↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)) :=
    Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank F2 (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank F2 (LinearMap.range A.mulVecLin) + Module.finrank F2 (LinearMap.range B.mulVecLin)
  omega

lemma rank_zero_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    (0 : Matrix ι κ F2).rank = 0 := by
  simp [Matrix.rank]

lemma rank_sum_le {τ ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s : Finset τ) (M : τ → Matrix ι κ F2) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (rank_add_le _ _) (Nat.add_le_add_left ih _)


lemma oneEach_getD {n m : ℕ} (x : Fin n) (y : Fin m) (w : ℕ) (hw : w < n + m) :
    (oneEach x y).getD w false =
      if h : w < n then decide (x.val = w) else decide (y.val = w - n) := by
  simp only [oneEach]
  by_cases h : w < n
  · rw [dif_pos h]
    have hlen : w < (List.ofFn (fun i : Fin n => decide (i = x))).length := by simp [h]
    rw [getD_append_left _ _ w false hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some]
    by_cases hx : x.val = w
    · have : (⟨w, h⟩ : Fin n) = x := Fin.ext hx.symm
      simp [this, hx]
    · have : (⟨w, h⟩ : Fin n) ≠ x := fun he => hx (congrArg Fin.val he).symm
      simp [this, hx]
  · rw [dif_neg h]
    have hge : (List.ofFn (fun i : Fin n => decide (i = x))).length ≤ w := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.length_ofFn,
      List.getElem?_ofFn]
    have hwn : w - n < m := by omega
    rw [dif_pos hwn, Option.getD_some]
    by_cases hy : y.val = w - n
    · have : (⟨w - n, hwn⟩ : Fin m) = y := Fin.ext hy.symm
      simp [this, hy]
    · have : (⟨w - n, hwn⟩ : Fin m) ≠ y := fun he => hy (congrArg Fin.val he).symm
      simp [this, hy]

lemma foldr_max_le_iff (l : List ℕ) (b : ℕ) :
    l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b := by
  induction l with
  | nil => simp
  | cons a t ih => simp [max_le_iff, ih]

lemma circuit_depth1_decomp (n m : ℕ) (gs : List Gate)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + m + j)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ M : Fin gs.length → Matrix (Fin n) (Fin m) F2,
      (∀ k, (M k).rank ≤ 2) ∧
      (∀ k : Fin gs.length, nlGate (gs.get k) = true →
        (depthsOf (n + m) gs).getD (n + m + k.val) 0 ≤ 1 →
        ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
          ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD (n + m + k.val) false) =
            M k x y + α x + β y + c) ∧
      ∀ w < n + m + gs.length,
        ((depthsOf (n + m) gs).getD w 0 = 0 →
          ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
            ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD w false) = α x + β y + c) ∧
        ((depthsOf (n + m) gs).getD w 0 ≤ 1 →
          ∃ (coeff : Fin gs.length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
            (∀ k, coeff k ≠ 0 →
              nlGate (gs.get k) = true ∧ (depthsOf (n + m) gs).getD (n + m + k.val) 0 ≤ 1) ∧
            ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD w false) =
              (∑ k : Fin gs.length, coeff k * M k x y) + α x + β y + c) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k, ?_⟩
    intro w hw
    simp only [List.length_nil, add_zero] at hw
    have hw_rep : ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
        ∀ x y, b2f ((wiresOf [] (oneEach x y)).getD w false) = α x + β y + c := by
      by_cases h : w < n
      · refine ⟨fun x => b2f (decide (x.val = w)), fun _ => 0, 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach_getD x y w hw, h, ↓reduceDIte, add_zero]
      · refine ⟨fun _ => 0, fun y => b2f (decide (y.val = w - n)), 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach_getD x y w hw, h, ↓reduceDIte, zero_add, add_zero]
    refine ⟨fun _ => hw_rep, fun _ => ?_⟩
    obtain ⟨α, β, c, hxy⟩ := hw_rep
    exact ⟨fun k => Fin.elim0 k, α, β, c, fun k => Fin.elim0 k, fun x y => by
      rw [hxy x y]; simp⟩
  | append_singleton gs g ih =>
    have hrb_gs : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + m + j := by
      intro j hj i hi
      have h1 := hrb j (by simp; omega) i
      have hgd : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        getD_append_left gs [g] j _ hj
      rw [hgd] at h1
      exact h1 hi
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hfan_g : g.inputs.length ≤ 2 := hfan g (by simp)
    have hrb_g : ∀ i ∈ g.inputs, i < n + m + gs.length := by
      intro i hi
      have h1 := hrb gs.length (by simp) i
      rw [getD_append_self gs g _] at h1
      exact h1 hi
    obtain ⟨Mprev, hMrk, hMnl, hWprev⟩ := ih hrb_gs hfan_gs
    let ds := depthsOf (n + m) gs
    have hds_len : ds.length = n + m + gs.length := depthsOf_length (n + m) gs
    have hds_new : depthsOf (n + m) (gs ++ [g]) = depthStep ds g := by
      simp [depthsOf, ds, List.foldl_append]
    have hws_new : ∀ inp, wiresOf (gs ++ [g]) inp = wireStep (wiresOf gs inp) g := fun inp => by
      simp [wiresOf, List.foldl_append]
    have hws_len : ∀ (x : Fin n) (y : Fin m), (wiresOf gs (oneEach x y)).length = n + m + gs.length :=
      fun x y => by simp only [wiresOf_length, oneEach, List.length_append, List.length_ofFn]
    have hd_last : (depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 =
        (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat := by
      rw [hds_new, depthStep, ← hds_len, getD_append_self]
    have hw_last : ∀ (x : Fin n) (y : Fin m), (wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false =
        g.op.eval (g.inputs.map (fun a => (wiresOf gs (oneEach x y)).getD a false)) := by
      intro x y
      rw [hws_new, wireStep, ← hws_len x y, getD_append_self]
    have hd_old_k : ∀ (k : Fin (gs ++ [g]).length) (hk : k.val < gs.length),
        (depthsOf (n + m) (gs ++ [g])).getD (n + m + k.val) 0 = ds.getD (n + m + k.val) 0 := by
      intro k hk
      rw [hds_new, depthStep]
      exact getD_append_left ds _ (n + m + k.val) 0 (by omega)
    -- Determine the new rank-<=2 matrix M_last for gate g
    have hlast_build :
        ∃ (Mlast : Matrix (Fin n) (Fin m) F2),
          Mlast.rank ≤ 2 ∧
          (nlGate g = true → (depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 ≤ 1 →
            ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                Mlast x y + α x + β y + c) ∧
          ((depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 = 0 →
            ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                α x + β y + c) ∧
          ((depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 ≤ 1 →
            ∃ (coeff : Fin (gs ++ [g]).length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              (∀ k, coeff k ≠ 0 →
                nlGate ((gs ++ [g]).get k) = true ∧ (depthsOf (n + m) (gs ++ [g])).getD (n + m + k.val) 0 ≤ 1) ∧
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                (∑ k : Fin (gs ++ [g]).length,
                  coeff k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) +
                α x + β y + c) := by
      cases hgin : g.inputs with
      | nil =>
        have hnl_f : nlGate g = false := by simp [nlGate, hgin]
        refine ⟨0, by simp [rank_zero_eq], fun h _ => by simp [hnl_f] at h, ?_, ?_⟩
        · intro _
          refine ⟨0, 0, b2f (g.op.eval []), fun x y => by rw [hw_last, hgin]; simp⟩
        · intro _
          refine ⟨0, 0, 0, b2f (g.op.eval []), fun k hk => absurd rfl hk, fun x y => by rw [hw_last, hgin]; simp⟩
      | cons a rest =>
        cases rest with
        | nil =>
          have ha_lt : a < n + m + gs.length := hrb_g a (by simp [hgin])
          have hnl_f : nlGate g = false := by simp [nlGate, hgin]
          obtain ⟨c0, c1, hexp⟩ := gate_eval_expand_one g.op
          refine ⟨0, by simp [rank_zero_eq], fun h _ => by simp [hnl_f] at h, ?_, ?_⟩
          · intro hd0
            rw [hd_last, hgin, hnl_f] at hd0
            have hda0 : ds.getD a 0 = 0 := by
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Bool.toNat_false, add_zero, nat_max_zero] at hd0
              omega
            obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 hda0
            refine ⟨fun x => c1 * αa x, fun y => c1 * βa y, c0 + c1 * ca, fun x y => ?_⟩
            rw [hw_last, hgin]
            simp only [List.map_cons, List.map_nil, hexp, hxa x y]
            ring
          · intro hd1
            rw [hd_last, hgin, hnl_f] at hd1
            have hda1 : ds.getD a 0 ≤ 1 := by
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Bool.toNat_false, add_zero, nat_max_zero] at hd1
              omega
            obtain ⟨cfa, αa, βa, ca, hsupp, hxa⟩ := (hWprev a ha_lt).2 hda1
            let cf : Fin (gs ++ [g]).length → F2 := fun k =>
              if hk : k.val < gs.length then c1 * cfa ⟨k.val, hk⟩ else 0
            refine ⟨cf, fun x => c1 * αa x, fun y => c1 * βa y, c0 + c1 * ca, ?_, ?_⟩
            · intro k hk
              by_cases hlt : k.val < gs.length
              · simp only [cf, dif_pos hlt] at hk
                have hne : cfa ⟨k.val, hlt⟩ ≠ 0 := fun h0 => hk (by simp [h0])
                have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
                  simp [List.getElem_append_left hlt]
                rw [hget, hd_old_k k hlt]
                exact hsupp ⟨k.val, hlt⟩ hne
              · simp only [cf, dif_neg hlt] at hk; exact absurd rfl hk
            · intro x y
              rw [hw_last, hgin]
              simp only [List.map_cons, List.map_nil, hexp, hxa x y]
              have hsum : (∑ k : Fin (gs ++ [g]).length,
                  cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else (0 : Matrix _ _ F2) x y)) =
                  c1 * ∑ k : Fin gs.length, cfa k * Mprev k x y := by
                have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                rw [Finset.mul_sum]
                let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                have hlast0 : cf (e (Fin.last gs.length)) = 0 := by
                  simp [cf, e]
                rw [hlast0, zero_mul, add_zero]
                refine Finset.sum_congr rfl fun k _ => ?_
                simp only [cf, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
                ring
              rw [hsum]; ring
        | cons b rest2 =>
          cases rest2 with
          | cons _ _ =>
            simp [hgin] at hfan_g
          | nil =>
            have ha_lt : a < n + m + gs.length := hrb_g a (by simp [hgin])
            have hb_lt : b < n + m + gs.length := hrb_g b (by simp [hgin])
            obtain ⟨c0, c1, c2, hexp⟩ := gate_eval_expand_two g.op
            have hq_eq : b2f (xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true]))) = b2f (nlGate g) := by
              simp [nlGate, hgin]
            by_cases hnl : nlGate g = true
            · -- Nonlinear gate: if depth <= 1 then both inputs have depth 0
              by_cases h0ab : ds.getD a 0 = 0 ∧ ds.getD b 0 = 0
              · obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 h0ab.1
                obtain ⟨αb, βb, cb, hxb⟩ := (hWprev b hb_lt).1 h0ab.2
                let Mlast : Matrix (Fin n) (Fin m) F2 :=
                  Matrix.of fun x y => αa x * βb y + αb x * βa y
                have hMlast_rk : Mlast.rank ≤ 2 := by
                  have h1 : Mlast = Matrix.of (fun x y => αa x * βb y) +
                      Matrix.of (fun x y => αb x * βa y) := by ext x y; simp [Mlast]
                  rw [h1]
                  exact le_trans (rank_add_le _ _)
                    (Nat.add_le_add (rank_vecMulVec_le αa βb) (rank_vecMulVec_le αb βa))
                have hdirect : ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                    Mlast x y +
                    (αa x * αb x + (c1 + cb) * αa x + (c2 + ca) * αb x) +
                    (βa y * βb y + (c1 + cb) * βa y + (c2 + ca) * βb y) +
                    (c0 + c1 * ca + c2 * cb + ca * cb) := by
                  intro x y
                  rw [hw_last, hgin]
                  simp only [List.map_cons, List.map_nil]
                  rw [hexp, hq_eq, hnl, hxa x y, hxb x y]
                  have hb1 : b2f true = 1 := rfl
                  rw [hb1, one_mul]
                  dsimp only [Mlast, Matrix.of_apply]
                  ring
                refine ⟨Mlast, hMlast_rk, fun _ _ => ⟨_, _, _, hdirect⟩, ?_, ?_⟩
                · intro hd0
                  rw [hd_last, hnl] at hd0; simp at hd0
                · intro hd1
                  let cf : Fin (gs ++ [g]).length → F2 := fun k =>
                    if k.val = gs.length then 1 else 0
                  refine ⟨cf,
                    fun x => αa x * αb x + (c1 + cb) * αa x + (c2 + ca) * αb x,
                    fun y => βa y * βb y + (c1 + cb) * βa y + (c2 + ca) * βb y,
                    c0 + c1 * ca + c2 * cb + ca * cb, ?_, ?_⟩
                  · intro k hk
                    have hkeq : k.val = gs.length := by
                      by_contra hne; simp [cf, hne] at hk
                    have hget : (gs ++ [g]).get k = g := by
                      simp [List.getElem_append_right (le_of_eq hkeq.symm), hkeq]
                    rw [hget, hkeq]; exact ⟨hnl, hd1⟩
                  · intro x y
                    rw [hdirect x y]
                    have hsum : (∑ k : Fin (gs ++ [g]).length,
                        cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) =
                        Mlast x y := by
                      have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                      let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                      rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                      have hpref : ∑ k : Fin gs.length,
                          cf (e k.castSucc) * (if hk : (e k.castSucc).val < gs.length then
                            Mprev ⟨(e k.castSucc).val, hk⟩ x y else Mlast x y) = 0 := by
                        refine Finset.sum_eq_zero fun k _ => ?_
                        have hne : (e k.castSucc).val ≠ gs.length := by simp [e]; omega
                        simp [cf, hne]
                      rw [hpref, zero_add]
                      have hnotlt : ¬ (e (Fin.last gs.length)).val < gs.length := by simp [e]
                      have heq : (e (Fin.last gs.length)).val = gs.length := by simp [e]
                      simp [cf, heq, hnotlt]
                    rw [hsum]
              · have hno1 : ¬ (depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 ≤ 1 := by
                  intro hd1
                  rw [hd_last, hgin, hnl] at hd1
                  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                    Bool.toNat_true, nat_max_zero] at hd1
                  apply h0ab; constructor <;> omega
                refine ⟨0, by simp [rank_zero_eq], fun _ hd1 => absurd hd1 hno1, ?_, fun hd1 => absurd hd1 hno1⟩
                intro hd0; rw [hd_last, hnl] at hd0; simp at hd0
            · -- Linear 2-input gate (`nlGate g = false`)
              have hnlf : nlGate g = false := Bool.eq_false_iff.mpr hnl
              refine ⟨0, by simp [rank_zero_eq], fun h _ => by simp [hnlf] at h, ?_, ?_⟩
              · intro hd0
                rw [hd_last, hgin, hnlf] at hd0
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                  Bool.toNat_false, add_zero, nat_max_zero] at hd0
                have hda0 : ds.getD a 0 = 0 := by omega
                have hdb0 : ds.getD b 0 = 0 := by omega
                obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 hda0
                obtain ⟨αb, βb, cb, hxb⟩ := (hWprev b hb_lt).1 hdb0
                refine ⟨fun x => c1 * αa x + c2 * αb x, fun y => c1 * βa y + c2 * βb y,
                  c0 + c1 * ca + c2 * cb, fun x y => ?_⟩
                rw [hw_last, hgin]
                simp only [List.map_cons, List.map_nil]
                rw [hexp, hq_eq, hnlf, hxa x y, hxb x y]
                have hb0 : b2f false = 0 := rfl
                rw [hb0, zero_mul, add_zero]
                ring
              · intro hd1
                rw [hd_last, hgin, hnlf] at hd1
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                  Bool.toNat_false, add_zero, nat_max_zero] at hd1
                have hda1 : ds.getD a 0 ≤ 1 := by omega
                have hdb1 : ds.getD b 0 ≤ 1 := by omega
                obtain ⟨cfa, αa, βa, ca, hsuppa, hxa⟩ := (hWprev a ha_lt).2 hda1
                obtain ⟨cfb, αb, βb, cb, hsuppb, hxb⟩ := (hWprev b hb_lt).2 hdb1
                let cf : Fin (gs ++ [g]).length → F2 := fun k =>
                  if hk : k.val < gs.length then c1 * cfa ⟨k.val, hk⟩ + c2 * cfb ⟨k.val, hk⟩ else 0
                refine ⟨cf, fun x => c1 * αa x + c2 * αb x, fun y => c1 * βa y + c2 * βb y,
                  c0 + c1 * ca + c2 * cb, ?_, ?_⟩
                · intro k hk
                  by_cases hlt : k.val < gs.length
                  · simp only [cf, dif_pos hlt] at hk
                    have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
                      simp [List.getElem_append_left hlt]
                    rw [hget, hd_old_k k hlt]
                    by_cases ha0 : cfa ⟨k.val, hlt⟩ ≠ 0
                    · exact hsuppa ⟨k.val, hlt⟩ ha0
                    · push_neg at ha0
                      have hb0 : cfb ⟨k.val, hlt⟩ ≠ 0 := fun h0 => hk (by simp [ha0, h0])
                      exact hsuppb ⟨k.val, hlt⟩ hb0
                  · simp only [cf, dif_neg hlt] at hk; exact absurd rfl hk
                · intro x y
                  rw [hw_last, hgin]
                  simp only [List.map_cons, List.map_nil]
                  rw [hexp, hq_eq, hnlf, hxa x y, hxb x y]
                  have hb0 : b2f false = 0 := rfl
                  rw [hb0, zero_mul, add_zero]
                  have hsum : (∑ k : Fin (gs ++ [g]).length,
                      cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else (0 : Matrix _ _ F2) x y)) =
                      c1 * (∑ k : Fin gs.length, cfa k * Mprev k x y) +
                      c2 * (∑ k : Fin gs.length, cfb k * Mprev k x y) := by
                    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                    let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                    rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                    have hlast0 : cf (e (Fin.last gs.length)) = 0 := by simp [cf, e]
                    rw [hlast0, zero_mul, add_zero, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl fun k _ => ?_
                    simp only [cf, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
                    ring
                  rw [hsum]; ring
    obtain ⟨Mlast, hMlast_rk, hlast_nl, hlast0, hlast1⟩ := hlast_build
    let M : Fin (gs ++ [g]).length → Matrix (Fin n) (Fin m) F2 := fun k =>
      if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ else Mlast
    refine ⟨M, ?_, ?_, ?_⟩
    · intro k; dsimp only [M]; split_ifs with hk
      · exact hMrk ⟨k.val, hk⟩
      · exact hMlast_rk
    · intro k hnlk hd1k
      by_cases hlt : k.val < gs.length
      · have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
          simp [List.getElem_append_left hlt]
        rw [hget] at hnlk
        rw [hd_old_k k hlt] at hd1k
        obtain ⟨α, β, c, hxy⟩ := hMnl ⟨k.val, hlt⟩ hnlk hd1k
        refine ⟨α, β, c, fun x y => ?_⟩
        have hw_old : (wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + k.val) false =
            (wiresOf gs (oneEach x y)).getD (n + m + k.val) false := by
          rw [hws_new, wireStep]
          exact getD_append_left _ _ (n + m + k.val) false (by rw [hws_len]; omega)
        rw [hw_old, hxy x y]
        simp only [M, hlt, ↓reduceDIte]
      · have hkeq : k.val = gs.length := by
          have := k.isLt; simp at this; omega
        have hget : (gs ++ [g]).get k = g := by
          simp [List.getElem_append_right (le_of_eq hkeq.symm), hkeq]
        rw [hget] at hnlk
        rw [hkeq] at hd1k ⊢
        obtain ⟨α, β, c, hxy⟩ := hlast_nl hnlk hd1k
        refine ⟨α, β, c, fun x y => ?_⟩
        rw [hxy x y]
        simp only [M, hlt, ↓reduceDIte]
    · intro w hw
      have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
      by_cases hlt : w < n + m + gs.length
      · have hd_old : (depthsOf (n + m) (gs ++ [g])).getD w 0 = ds.getD w 0 := by
          rw [hds_new, depthStep]
          exact getD_append_left ds _ w 0 (by omega)
        have hw_old : ∀ x y, (wiresOf (gs ++ [g]) (oneEach x y)).getD w false =
            (wiresOf gs (oneEach x y)).getD w false := fun x y => by
          rw [hws_new, wireStep]
          exact getD_append_left _ _ w false (by rw [hws_len]; omega)
        constructor
        · intro hd0
          rw [hd_old] at hd0
          obtain ⟨α, β, c, hxy⟩ := (hWprev w hlt).1 hd0
          exact ⟨α, β, c, fun x y => by rw [hw_old]; exact hxy x y⟩
        · intro hd1
          rw [hd_old] at hd1
          obtain ⟨cfprev, α, β, c, hsupp, hxy⟩ := (hWprev w hlt).2 hd1
          let cf : Fin (gs ++ [g]).length → F2 := fun k =>
            if hk : k.val < gs.length then cfprev ⟨k.val, hk⟩ else 0
          refine ⟨cf, α, β, c, ?_, ?_⟩
          · intro k hk
            by_cases hklt : k.val < gs.length
            · simp only [cf, dif_pos hklt] at hk
              have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hklt⟩ := by
                simp [List.getElem_append_left hklt]
              rw [hget, hd_old_k k hklt]
              exact hsupp ⟨k.val, hklt⟩ hk
            · simp only [cf, dif_neg hklt] at hk; exact absurd rfl hk
          · intro x y
            rw [hw_old, hxy x y]
            have hsum : (∑ k : Fin (gs ++ [g]).length, cf k * M k x y) =
                ∑ k : Fin gs.length, cfprev k * Mprev k x y := by
              let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
              rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
              have hlast0 : cf (e (Fin.last gs.length)) = 0 := by simp [cf, e]
              rw [hlast0, zero_mul, add_zero]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [cf, M, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
            rw [hsum]
      · have hweq : w = n + m + gs.length := by omega
        subst hweq
        exact ⟨hlast0, fun hd1 => by
          obtain ⟨cf, α, β, c, hsupp, hxy⟩ := hlast1 hd1
          refine ⟨cf, α, β, c, hsupp, fun x y => ?_⟩
          have hsum_eq : (∑ k : Fin (gs ++ [g]).length,
              cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) =
              ∑ k : Fin (gs ++ [g]).length, cf k * M k x y :=
            Finset.sum_congr rfl fun k _ => by dsimp only [M]; split_ifs <;> rfl
          rw [hxy x y, hsum_eq]⟩

lemma dd_rank_le {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) (u : Fin n) (v : Fin m) :
    (Matrix.of fun x y => M x y + M x v + M u y + M u v).rank ≤ M.rank := by
  let L : (Fin m → F2) →ₗ[F2] (Fin n → F2) :=
    { toFun := fun w x => M.mulVec w x + M.mulVec w u
      map_add' := fun w1 w2 => by
        ext x; simp only [Matrix.mulVec_add, Pi.add_apply]; ring
      map_smul' := fun r w => by
        ext x; simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let P : (Fin n → F2) →ₗ[F2] (Fin n → F2) :=
    { toFun := fun z x => z x + z u
      map_add' := fun z1 z2 => by ext x; simp; ring
      map_smul' := fun r z => by ext x; simp; ring }
  let D : Matrix (Fin n) (Fin m) F2 := Matrix.of fun x y => M x y + M x v + M u y + M u v
  have hsub : LinearMap.range D.mulVecLin ≤ (LinearMap.range M.mulVecLin).map P := by
    rintro _ ⟨w, rfl⟩
    let w' : Fin m → F2 := fun y => w y + (if y = v then ∑ z : Fin m, w z else 0)
    refine ⟨M.mulVecLin w', ⟨w', rfl⟩, ?_⟩
    ext x
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.of_apply, D, w']
    have hmul : ∀ a : Fin n, ∑ y : Fin m, M a y * (w y + if y = v then ∑ z, w z else 0) =
        (∑ y, M a y * w y) + M a v * ∑ z, w z := by
      intro a
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    rw [hmul x, hmul u]
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have h1 := Submodule.finrank_mono hsub
  have hmap_eq : (LinearMap.range M.mulVecLin).map P =
      LinearMap.range (P.comp (LinearMap.range M.mulVecLin).subtype) := by
    ext z; simp [Submodule.mem_map]
  have h2 : Module.finrank F2 ((LinearMap.range M.mulVecLin).map P) ≤
      Module.finrank F2 (LinearMap.range M.mulVecLin) := by
    rw [hmap_eq]
    have hrk := LinearMap.finrank_range_add_finrank_ker (P.comp (LinearMap.range M.mulVecLin).subtype)
    omega
  exact le_trans h1 h2

lemma countP_eq_card_filter {α : Type} (l : List α) (p : α → Bool) :
    l.countP p = (Finset.univ.filter (fun k : Fin l.length => p (l.get k) = true)).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, ih]
    have hcard : (Finset.univ.filter (fun k : Fin (a :: t).length => p ((a :: t).get k) = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun k : Fin t.length => p (t.get k) = true)).card := by
      simp only [Finset.card_filter, List.length_cons, Fin.sum_univ_succ]
      cases hpa : p a <;> simp [hpa]
    rw [hcard]
    cases p a <;> simp <;> omega


def isLinearOK (gs : List Gate) (width : ℕ) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < width + j) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2)

lemma isLinearOK_append {width : ℕ} {gs1 gs2 : List Gate}
    (h1 : isLinearOK gs1 width) (h2 : isLinearOK gs2 (width + gs1.length)) :
    isLinearOK (gs1 ++ gs2) width := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    by_cases hlt : j < gs1.length
    · rw [getD_append_left gs1 gs2 j _ hlt] at hi
      exact h1.1 j hlt i hi
    · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
      have hgd : (gs1 ++ gs2).getD j ⟨GateOp.or, []⟩ = gs2.getD (j - gs1.length) ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
      rw [hgd] at hi
      have hj2 : j - gs1.length < gs2.length := by simp at hj; omega
      have hlt2 := h2.1 (j - gs1.length) hj2 i hi
      omega
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact h1.2 g hg1
    · exact h2.2 g hg2

-- Append a single XOR of two earlier wires `a, b < base` (2 linear gates: mod 2 then not)
def xor2Gates (base a b : ℕ) : List Gate :=
  [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [base]⟩]

lemma xor2Gates_ok (base a b : ℕ) (ha : a < base) (hb : b < base) :
    isLinearOK (xor2Gates base a b) base := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [xor2Gates, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [xor2Gates, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [xor2Gates, List.getD_cons_succ, List.getD_cons_zero, List.mem_singleton] at hi
      omega
  · intro g hg
    simp only [xor2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp

lemma isLinearOK_eq {gs : List Gate} {w₁ w₂ : ℕ} (h : isLinearOK gs w₁) (heq : w₁ = w₂) :
    isLinearOK gs w₂ := heq ▸ h

lemma nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma nlGate_and2 (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma xor2Gates_nl (base a b : ℕ) : (xor2Gates base a b).countP nlGate = 0 := by
  simp [xor2Gates, nlGate_mod2, nlGate_not]

lemma xor2Gates_val (ws : List Bool) (a b : ℕ) :
    b2f (((xor2Gates ws.length a b).foldl wireStep ws).getD (ws.length + 1) false) =
      b2f (ws.getD a false) + b2f (ws.getD b false) := by
  simp only [xor2Gates, List.foldl_cons, List.foldl_nil, wireStep, List.map_cons, List.map_nil]
  let v := (GateOp.mod 2).eval [ws.getD a false, ws.getD b false]
  have hl1 : (ws ++ [v]).length = ws.length + 1 := by simp
  have hget1 : (ws ++ [v]).getD ws.length false = v := getD_append_self ws v false
  have hget2 : ((ws ++ [v]) ++ [GateOp.not.eval [(ws ++ [v]).getD ws.length false]]).getD
      (ws.length + 1) false =
      GateOp.not.eval [(ws ++ [v]).getD ws.length false] := by
    rw [← hl1]; exact getD_append_self (ws ++ [v]) _ false
  rw [hget2, hget1]
  dsimp only [v]
  cases ws.getD a false <;> cases ws.getD b false <;> decide

lemma xor2Gates_depth (ds : List ℕ) (a b : ℕ) (d : ℕ)
    (hda : ds.getD a 0 ≤ d) (hdb : ds.getD b 0 ≤ d) :
    ((xor2Gates ds.length a b).foldl depthStep ds).getD (ds.length + 1) 0 ≤ d := by
  simp only [xor2Gates, List.foldl_cons, List.foldl_nil, depthStep, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, nlGate_mod2, nlGate_not, Bool.toNat_false, add_zero, nat_max_zero]
  have hl1 : (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).length = ds.length + 1 := by simp
  have hg1 : (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0 =
      max (ds.getD a 0) (ds.getD b 0) := getD_append_self ds _ 0
  have hg2 : ((ds ++ [max (ds.getD a 0) (ds.getD b 0)]) ++
      [(ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0]).getD (ds.length + 1) 0 =
      (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0 := by
    rw [← hl1]; exact getD_append_self _ _ 0
  rw [hg2, hg1]
  exact max_le hda hdb

-- XOR a list of existing wires `idxs` (all < base) starting from base; returns (gates, outputWire)
def xorListBuild (base : ℕ) (l : List ℕ) : List Gate × ℕ :=
  match l with
  | [] => ([⟨GateOp.or, []⟩], base)
  | [a] => ([], a)
  | a :: b :: rest =>
    let g1 := xor2Gates base a b
    let mid := base + 1
    let res := xorListBuild (base + 2) (mid :: rest)
    (g1 ++ res.1, res.2)
termination_by l.length

lemma xorListBuild_spec_aux : ∀ (k : ℕ) (idxs : List ℕ), idxs.length = k →
    ∀ base : ℕ, (∀ w ∈ idxs, w < base) →
      let p := xorListBuild base idxs
      isLinearOK p.1 base ∧
      p.1.countP nlGate = 0 ∧
      p.2 < base + p.1.length ∧
      (∀ (ws : List Bool), ws.length = base →
        b2f ((p.1.foldl wireStep ws).getD p.2 false) =
          (idxs.map (fun w => b2f (ws.getD w false))).sum) ∧
      (∀ (ds : List ℕ) (d : ℕ), ds.length = base → (∀ w ∈ idxs, ds.getD w 0 ≤ d) →
        (p.1.foldl depthStep ds).getD p.2 0 ≤ d) := by
  intro k
  induction k with
  | zero =>
    intro idxs hk base _
    have hnil : idxs = [] := List.eq_nil_of_length_eq_zero hk
    subst hnil
    simp only [xorListBuild, List.length_singleton, List.map_nil, List.sum_nil]
    have hnl0 : nlGate ⟨GateOp.or, []⟩ = false := by decide
    refine ⟨⟨?_, ?_⟩, by simp [hnl0], by omega, ?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0; simp at hi
    · intro g hg; simp at hg; subst hg; simp
    · intro ws hlen
      simp only [List.foldl_cons, List.foldl_nil, wireStep, List.map_nil]
      rw [← hlen, getD_append_self]; decide
    · intro ds d hlen _
      simp only [List.foldl_cons, List.foldl_nil, depthStep, hnl0, List.map_nil, List.foldr_nil,
        Bool.toNat_false, add_zero]
      rw [← hlen, getD_append_self]; omega
  | succ k ih =>
    intro idxs hk base hlt
    cases idxs with
    | nil => simp at hk
    | cons a rest =>
      cases rest with
      | nil =>
        have ha : a < base := hlt a (by simp)
        simp only [xorListBuild, List.length_nil, add_zero, List.countP_nil, List.foldl_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        refine ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
          trivial, ha, fun _ _ => trivial, fun ds d _ hd => hd a (by simp)⟩
      | cons b rest2 =>
        have ha : a < base := hlt a (by simp)
        have hb : b < base := hlt b (by simp)
        have hlen2 : ((base + 1) :: rest2).length = k := by simp at hk; simp; omega
        have hrest : ∀ w ∈ (base + 1) :: rest2, w < base + 2 := by
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · omega
          · have := hlt w (by simp [hw2]); omega
        obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := ih ((base + 1) :: rest2) hlen2 (base + 2) hrest
        simp only [xorListBuild]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hok1 := xor2Gates_ok base a b ha hb
          have hl : (xor2Gates base a b).length = 2 := rfl
          exact isLinearOK_append hok1 (by simpa [hl] using hok2)
        · rw [List.countP_append, xor2Gates_nl, hnl2]
        · simp only [List.length_append]
          have hl : (xor2Gates base a b).length = 2 := rfl
          omega
        · intro ws hlen
          rw [List.foldl_append]
          let ws1 := (xor2Gates base a b).foldl wireStep ws
          have hlen1 : ws1.length = base + 2 := by
            dsimp only [ws1]; rw [foldl_wireStep_length, hlen]; rfl
          rw [hval2 ws1 hlen1]
          simp only [List.map_cons, List.sum_cons]
          have hmid : b2f (ws1.getD (base + 1) false) = b2f (ws.getD a false) + b2f (ws.getD b false) := by
            dsimp only [ws1]; rw [← hlen]; exact xor2Gates_val ws a b
          have htail : rest2.map (fun w => b2f (ws1.getD w false)) =
              rest2.map (fun w => b2f (ws.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hwlt : w < ws.length := by
              have := hlt w (by simp [hw]); omega
            rw [foldl_wireStep_getD_old ws (xor2Gates base a b) w hwlt]
          rw [hmid, htail, add_assoc]
        · intro ds d hlen hd
          rw [List.foldl_append]
          let ds1 := (xor2Gates base a b).foldl depthStep ds
          have hlen1 : ds1.length = base + 2 := by
            dsimp only [ds1]; rw [foldl_depthStep_length, hlen]; rfl
          refine hdep2 ds1 d hlen1 ?_
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · dsimp only [ds1]; rw [← hlen]
            exact xor2Gates_depth ds a b d (hd a (by simp)) (hd b (by simp))
          · have hwlt : w < ds.length := by
              have := hlt w (by simp [hw2]); omega
            rw [foldl_depthStep_getD_old ds (xor2Gates base a b) w hwlt]
            exact hd w (by simp [hw2])

lemma xorListBuild_spec (idxs : List ℕ) (base : ℕ) (hlt : ∀ w ∈ idxs, w < base) :
    let p := xorListBuild base idxs
    isLinearOK p.1 base ∧
    p.1.countP nlGate = 0 ∧
    p.2 < base + p.1.length ∧
    (∀ (ws : List Bool), ws.length = base →
      b2f ((p.1.foldl wireStep ws).getD p.2 false) =
        (idxs.map (fun w => b2f (ws.getD w false))).sum) ∧
    (∀ (ds : List ℕ) (d : ℕ), ds.length = base → (∀ w ∈ idxs, ds.getD w 0 ≤ d) →
      (p.1.foldl depthStep ds).getD p.2 0 ≤ d) :=
  xorListBuild_spec_aux idxs.length idxs rfl base hlt

lemma sum_filter_nodup_fin {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → Bool) (x : Fin n) :
    ((l.filter p).map (fun i => b2f (decide (x.val = i.val)))).sum =
      if x ∈ l ∧ p x = true then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    by_cases hax : x = a
    · subst hax
      have hxt : x ∉ t := hl.1
      have iht := ih hl.2
      simp only [hxt, false_and, ↓reduceIte] at iht
      cases hpa : p x with
      | false =>
        simp [hpa, iht]
      | true =>
        have hxx : b2f (decide True) = 1 := rfl
        simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons, List.sum_cons, eq_self_iff_true, hxx, iht, add_zero, List.mem_cons, true_or, and_self]
    · have hvne : x.val ≠ a.val := fun h => hax (Fin.ext h)
      have iht := ih hl.2
      cases hpa : p a with
      | false =>
        simp [hpa, iht, hax]
      | true =>
        have hxa : b2f (decide (x.val = a.val)) = 0 := by simp [b2f, hvne]
        simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons, List.sum_cons, hxa, zero_add,
          iht, List.mem_cons, hax, false_or]

lemma sum_finRange_filter {n : ℕ} (α : Fin n → F2) (x : Fin n) :
    (((List.finRange n).filter (fun i => decide (α i = 1))).map
      (fun i => b2f (decide (x.val = i.val)))).sum = α x := by
  rw [sum_filter_nodup_fin (List.finRange n) (List.nodup_finRange n) _ x]
  have hmem : x ∈ List.finRange n := List.mem_finRange x
  rcases f2_cases (α x) with h0 | h1
  · simp [hmem, h0]
  · simp [hmem, h1]

def affineIdxs (n m base : ℕ) (α : Fin n → F2) (β : Fin m → F2) (c : F2) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (α i = 1))).map Fin.val ++
  ((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => n + j.val) ++
  (if c = 1 then [base] else [])

def affineBuild (n m base : ℕ) (α : Fin n → F2) (β : Fin m → F2) (c : F2) : List Gate × ℕ :=
  let g0 : List Gate := [⟨GateOp.and, []⟩]
  let res := xorListBuild (base + 1) (affineIdxs n m base α β c)
  (g0 ++ res.1, res.2)

lemma affineBuild_spec (n m base : ℕ) (hbase : n + m ≤ base)
    (α : Fin n → F2) (β : Fin m → F2) (c : F2) :
    let p := affineBuild n m base α β c
    isLinearOK p.1 base ∧
    p.1.countP nlGate = 0 ∧
    p.2 < base + p.1.length ∧
    (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
      ws.length = base →
      (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
      b2f ((p.1.foldl wireStep ws).getD p.2 false) = α x + β y + c) ∧
    (∀ (ds : List ℕ),
      ds.length = base →
      (∀ w < n + m, ds.getD w 0 = 0) →
      (p.1.foldl depthStep ds).getD p.2 0 = 0) := by
  have hidxs_lt : ∀ w ∈ affineIdxs n m base α β c, w < base + 1 := by
    intro w hw
    simp only [affineIdxs, List.mem_append, List.mem_map, List.mem_filter] at hw
    rcases hw with (⟨i, _, rfl⟩ | ⟨j, _, rfl⟩) | hc
    · omega
    · omega
    · split_ifs at hc with h1
      · simp at hc; omega
      · simp at hc
  obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := xorListBuild_spec (affineIdxs n m base α β c) (base + 1) hidxs_lt
  have hok0 : isLinearOK [⟨GateOp.and, []⟩] base := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0; simp at hi
    · intro g hg; simp at hg; subst hg; simp
  have hnl0 : ([⟨GateOp.and, []⟩] : List Gate).countP nlGate = 0 := by
    have h : nlGate ⟨GateOp.and, []⟩ = false := by decide
    simp [h]
  simp only [affineBuild]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isLinearOK_append hok0 (by simpa using hok2)
  · rw [List.countP_append, hnl0, hnl2]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x y ws hlen hws
    rw [List.foldl_append]
    let ws1 := ([⟨GateOp.and, []⟩] : List Gate).foldl wireStep ws
    have hlen1 : ws1.length = base + 1 := by simp [ws1, wireStep, hlen]
    rw [hval2 ws1 hlen1]
    have hget_old : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := by
      intro w hw
      have h1 := foldl_wireStep_getD_old ws [⟨GateOp.and, []⟩] w (by omega)
      exact h1.trans (hws w hw)
    have hget_base : b2f (ws1.getD base false) = 1 := by
      dsimp only [ws1]
      simp only [List.foldl_cons, List.foldl_nil, wireStep, List.map_nil]
      rw [← hlen, getD_append_self]
      decide
    simp only [affineIdxs, List.map_append, List.sum_append, List.map_map]
    have hsum1 : (((List.finRange n).filter (fun i => decide (α i = 1))).map
        ((fun w => b2f (ws1.getD w false)) ∘ Fin.val)).sum = α x := by
      have hcongr : (((List.finRange n).filter (fun i => decide (α i = 1))).map
          ((fun w => b2f (ws1.getD w false)) ∘ Fin.val)) =
          (((List.finRange n).filter (fun i => decide (α i = 1))).map
          (fun i => b2f (decide (x.val = i.val)))) := by
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, hget_old i.val (by omega),
          oneEach_getD x y i.val (by omega), i.isLt, ↓reduceDIte]
      rw [hcongr]
      exact sum_finRange_filter α x
    have hsum2 : (((List.finRange m).filter (fun j => decide (β j = 1))).map
        ((fun w => b2f (ws1.getD w false)) ∘ fun j => n + j.val)).sum = β y := by
      have hcongr : (((List.finRange m).filter (fun j => decide (β j = 1))).map
          ((fun w => b2f (ws1.getD w false)) ∘ fun j => n + j.val)) =
          (((List.finRange m).filter (fun j => decide (β j = 1))).map
          (fun j => b2f (decide (y.val = j.val)))) := by
        refine List.map_congr_left fun j _ => ?_
        have hnotlt : ¬ n + j.val < n := by omega
        have hsub : n + j.val - n = j.val := by omega
        simp only [Function.comp_apply, hget_old (n + j.val) (by omega),
          oneEach_getD x y (n + j.val) (by omega), hnotlt, ↓reduceDIte, hsub]
      rw [hcongr]
      exact sum_finRange_filter β y
    have hsum3 : ((if c = 1 then [base] else []).map (fun w => b2f (ws1.getD w false))).sum = c := by
      rcases f2_cases c with rfl | rfl
      · simp
      · simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hget_base]
    rw [hsum1, hsum2, hsum3]
  · intro ds hlen hds
    rw [List.foldl_append]
    let ds1 := ([⟨GateOp.and, []⟩] : List Gate).foldl depthStep ds
    have hlen1 : ds1.length = base + 1 := by simp [ds1, depthStep, hlen]
    have h0 : ((xorListBuild (base + 1) (affineIdxs n m base α β c)).1.foldl depthStep ds1).getD
        (xorListBuild (base + 1) (affineIdxs n m base α β c)).2 0 ≤ 0 := by
      refine hdep2 ds1 0 hlen1 ?_
      intro w hw
      simp only [affineIdxs, List.mem_append, List.mem_map, List.mem_filter] at hw
      rcases hw with (⟨i, _, rfl⟩ | ⟨j, _, rfl⟩) | hc
      · rw [foldl_depthStep_getD_old ds _ i.val (by omega), hds i.val (by omega)]
      · rw [foldl_depthStep_getD_old ds _ (n + j.val) (by omega), hds (n + j.val) (by omega)]
      · split_ifs at hc with h1
        · simp only [List.mem_singleton] at hc
          subst hc
          dsimp only [ds1]
          have hnl_and : nlGate ⟨GateOp.and, []⟩ = false := by decide
          simp only [List.foldl_cons, List.foldl_nil, depthStep, hnl_and, List.map_nil,
            List.foldr_nil, Bool.toNat_false, add_zero]
          rw [← hlen, getD_append_self]
        · simp at hc
    exact Nat.eq_zero_of_le_zero h0

def pairGadget (n m base : ℕ) (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2) : List Gate × ℕ :=
  let a1 := affineBuild n m base p1 q2 0
  let base1 := base + a1.1.length
  let a2 := affineBuild n m base1 p2 q1 0
  let base2 := base1 + a2.1.length
  let gand : Gate := ⟨GateOp.and, [a1.2, a2.2]⟩
  (a1.1 ++ a2.1 ++ [gand], base2)

lemma pairGadget_spec (n m base : ℕ) (hbase : n + m ≤ base)
    (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2) :
    let g := pairGadget n m base p1 p2 q1 q2
    isLinearOK g.1 base ∧
    g.1.countP nlGate = 1 ∧
    g.2 < base + g.1.length ∧
    (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
      ws.length = base →
      (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
      b2f ((g.1.foldl wireStep ws).getD g.2 false) =
        p1 x * q1 y + p2 x * q2 y + p1 x * p2 x + q1 y * q2 y) ∧
    (∀ (ds : List ℕ),
      ds.length = base →
      (∀ w < n + m, ds.getD w 0 = 0) →
      (g.1.foldl depthStep ds).getD g.2 0 ≤ 1) := by
  dsimp only [pairGadget]
  set a1 := affineBuild n m base p1 q2 0
  set base1 := base + a1.1.length with hbase1
  set a2 := affineBuild n m base1 p2 q1 0
  set base2 := base1 + a2.1.length with hbase2
  set gand : Gate := ⟨GateOp.and, [a1.2, a2.2]⟩
  obtain ⟨hok1, hnl1, hlt1, hval1, hdep1⟩ := affineBuild_spec n m base hbase p1 q2 0
  change isLinearOK a1.1 base at hok1
  change a1.1.countP nlGate = 0 at hnl1
  change a1.2 < base1 at hlt1
  obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := affineBuild_spec n m base1 (by omega) p2 q1 0
  change isLinearOK a2.1 base1 at hok2
  change a2.1.countP nlGate = 0 at hnl2
  change a2.2 < base2 at hlt2
  have hok_and : isLinearOK [gand] base2 := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [List.getD_cons_zero, gand, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg; simp at hg; subst hg; simp [gand]
  have hnl_and : nlGate gand = true := nlGate_and2 a1.2 a2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h12 := isLinearOK_append hok1 hok2
    exact isLinearOK_append h12 (isLinearOK_eq hok_and (by simp [List.length_append, hbase1, hbase2]; omega))
  · simp [List.countP_append, hnl1, hnl2, hnl_and]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x y ws hlen hws
    rw [List.foldl_append, List.foldl_append]
    let ws1 := a1.1.foldl wireStep ws
    have hlen1 : ws1.length = base1 := by simp [ws1, foldl_wireStep_length, hlen, hbase1]
    have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
      (foldl_wireStep_getD_old ws a1.1 w (by omega)).trans (hws w hw)
    let ws2 := a2.1.foldl wireStep ws1
    have hlen2 : ws2.length = base2 := by simp [ws2, foldl_wireStep_length, hlen1, hbase2]
    have hw1 : b2f (ws2.getD a1.2 false) = p1 x + q2 y := by
      have hold := foldl_wireStep_getD_old ws1 a2.1 a1.2 (by omega)
      rw [hold, hval1 x y ws hlen hws, add_zero]
    have hw2 : b2f (ws2.getD a2.2 false) = p2 x + q1 y := by
      rw [hval2 x y ws1 hlen1 hws1, add_zero]
    simp only [List.foldl_cons, List.foldl_nil, wireStep, gand, List.map_cons, List.map_nil]
    change b2f ((ws2 ++ [GateOp.and.eval [ws2.getD a1.2 false, ws2.getD a2.2 false]]).getD base2 false) = _
    rw [← hlen2, getD_append_self]
    have hand : b2f (GateOp.and.eval [ws2.getD a1.2 false, ws2.getD a2.2 false]) =
        b2f (ws2.getD a1.2 false) * b2f (ws2.getD a2.2 false) := by
      cases ws2.getD a1.2 false <;> cases ws2.getD a2.2 false <;> decide
    rw [hand, hw1, hw2]
    ring
  · intro ds hlen hds
    rw [List.foldl_append, List.foldl_append]
    let ds1 := a1.1.foldl depthStep ds
    have hlen1 : ds1.length = base1 := by simp [ds1, foldl_depthStep_length, hlen, hbase1]
    have hds1 : ∀ w < n + m, ds1.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old ds a1.1 w (by omega)).trans (hds w hw)
    let ds2 := a2.1.foldl depthStep ds1
    have hlen2 : ds2.length = base2 := by simp [ds2, foldl_depthStep_length, hlen1, hbase2]
    have hd1 : ds2.getD a1.2 0 = 0 := by
      rw [foldl_depthStep_getD_old ds1 a2.1 a1.2 (by omega), hdep1 ds hlen hds]
    have hd2 : ds2.getD a2.2 0 = 0 := hdep2 ds1 hlen1 hds1
    simp only [List.foldl_cons, List.foldl_nil, depthStep, gand, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, hnl_and, Bool.toNat_true, nat_max_zero]
    change (ds2 ++ [max (ds2.getD a1.2 0) (ds2.getD a2.2 0) + 1]).getD base2 0 ≤ 1
    rw [← hlen2, getD_append_self, hd1, hd2]
    omega

def pairListBuild (n m : ℕ) :
    ℕ → List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2)) → List Gate × List ℕ
  | _, [] => ([], [])
  | base, (p1, p2, q1, q2) :: rest =>
    let g1 := pairGadget n m base p1 p2 q1 q2
    let r := pairListBuild n m (base + g1.1.length) rest
    (g1.1 ++ r.1, g1.2 :: r.2)

lemma pairListBuild_spec (n m : ℕ)
    (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))) :
    ∀ base : ℕ, n + m ≤ base →
      let res := pairListBuild n m base pairs
      isLinearOK res.1 base ∧
      res.1.countP nlGate = pairs.length ∧
      (∀ w ∈ res.2, w < base + res.1.length) ∧
      (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
        ws.length = base →
        (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
        (res.2.map (fun w => b2f ((res.1.foldl wireStep ws).getD w false))).sum =
          (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
          (pairs.map (fun t => t.1 x * t.2.1 x)).sum +
          (pairs.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum) ∧
      (∀ (ds : List ℕ),
        ds.length = base →
        (∀ w < n + m, ds.getD w 0 = 0) →
        ∀ w ∈ res.2, (res.1.foldl depthStep ds).getD w 0 ≤ 1) := by
  induction pairs with
  | nil =>
    intro base _
    simp only [pairListBuild, List.length_nil, List.countP_nil, List.map_nil, List.sum_nil, add_zero]
    exact ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
      trivial, fun _ h => by simp at h, fun _ _ _ _ _ => trivial,
      fun _ _ _ _ h => by simp at h⟩
  | cons hd rest ih =>
    rcases hd with ⟨p1, p2, q1, q2⟩
    intro base hbase
    dsimp only [pairListBuild]
    set g1 := pairGadget n m base p1 p2 q1 q2
    set r := pairListBuild n m (base + g1.1.length) rest
    obtain ⟨hok1, hnl1, hlt1, hval1, hdep1⟩ := pairGadget_spec n m base hbase p1 p2 q1 q2
    change isLinearOK g1.1 base at hok1
    change g1.1.countP nlGate = 1 at hnl1
    change g1.2 < base + g1.1.length at hlt1
    obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := ih (base + g1.1.length) (by omega)
    change isLinearOK r.1 (base + g1.1.length) at hok2
    change r.1.countP nlGate = rest.length at hnl2
    change ∀ w ∈ r.2, w < base + g1.1.length + r.1.length at hlt2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact isLinearOK_append hok1 hok2
    · rw [List.countP_append, hnl1, hnl2]; simp; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      simp only [List.length_append]
      rcases hw with rfl | hw2
      · omega
      · have := hlt2 w hw2; omega
    · intro x y ws hlen hws
      rw [List.foldl_append]
      let ws1 := g1.1.foldl wireStep ws
      have hlen1 : ws1.length = base + g1.1.length := by simp [ws1, foldl_wireStep_length, hlen]
      have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
        (foldl_wireStep_getD_old ws g1.1 w (by omega)).trans (hws w hw)
      simp only [List.map_cons, List.sum_cons]
      have hhead : b2f ((r.1.foldl wireStep ws1).getD g1.2 false) =
          p1 x * q1 y + p2 x * q2 y + p1 x * p2 x + q1 y * q2 y := by
        have hlt1' : g1.2 < ws1.length := by rw [hlen1]; exact hlt1
        rw [foldl_wireStep_getD_old ws1 r.1 g1.2 hlt1']
        exact hval1 x y ws hlen hws
      rw [hhead, hval2 x y ws1 hlen1 hws1]
      ring
    · intro ds hlen hds w hw
      rw [List.foldl_append]
      let ds1 := g1.1.foldl depthStep ds
      have hlen1 : ds1.length = base + g1.1.length := by simp [ds1, foldl_depthStep_length, hlen]
      have hds1 : ∀ w < n + m, ds1.getD w 0 = 0 := fun w hw =>
        (foldl_depthStep_getD_old ds g1.1 w (by omega)).trans (hds w hw)
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw2
      · have hlt1' : g1.2 < ds1.length := by rw [hlen1]; exact hlt1
        rw [foldl_depthStep_getD_old ds1 r.1 g1.2 hlt1']
        exact hdep1 ds hlen hds
      · exact hdep2 ds1 hlen1 hds1 w hw2



-- Section A: Linear algebra over F2 for L-meta-33664

def vdot {q : ℕ} (a z : Fin q → F2) : F2 := ∑ k : Fin q, a k * z k

lemma vdot_zero_left {q : ℕ} (z : Fin q → F2) : vdot 0 z = 0 := by
  simp [vdot]

lemma vdot_add_left {q : ℕ} (a b z : Fin q → F2) : vdot (a + b) z = vdot a z + vdot b z := by
  simp only [vdot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma vdot_add_right {q : ℕ} (a z₁ z₂ : Fin q → F2) : vdot a (z₁ + z₂) = vdot a z₁ + vdot a z₂ := by
  simp only [vdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma vdot_single_right {q : ℕ} (a : Fin q → F2) (k : Fin q) :
    vdot a (Pi.single k (1 : F2)) = a k := by
  simp [vdot, Pi.single_apply]

lemma vdot_eq_zero_of_forall {q : ℕ} {a : Fin q → F2} (h : ∀ z, vdot a z = 0) : a = 0 := by
  ext k
  have hk := h (Pi.single k 1)
  rwa [vdot_single_right] at hk

lemma card_vdot_eq_one {q : ℕ} (u : Fin q → F2) (hu : u ≠ 0) :
    2 * (Finset.univ.filter (fun z : Fin q → F2 => vdot u z = 1)).card = Fintype.card (Fin q → F2) := by
  have hex : ∃ k : Fin q, u k ≠ 0 := by
    by_contra hall; push_neg at hall; exact hu (funext hall)
  obtain ⟨k, hk⟩ := hex
  have huk : u k = 1 := by
    rcases f2_cases (u k) with h0 | h1
    · exact absurd h0 hk
    · exact h1
  let e : Fin q → F2 := Pi.single k 1
  have hde : vdot u e = 1 := by rw [vdot_single_right, huk]
  let S1 := Finset.univ.filter (fun z : Fin q → F2 => vdot u z = 1)
  let S0 := Finset.univ.filter (fun z : Fin q → F2 => vdot u z = 0)
  have hbij : S0.card = S1.card := by
    refine Finset.card_bij (fun z _ => z + e) ?_ ?_ ?_
    · intro z hz
      have h0 : vdot u z = 0 := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [vdot_add_right, h0, hde, zero_add]⟩
    · intro z₁ _ z₂ _ h
      have h1 : (z₁ + e) + e = (z₂ + e) + e := congrArg (· + e) h
      have he2 : ∀ z : Fin q → F2, (z + e) + e = z := fun z => by
        ext j; simp only [Pi.add_apply]; rw [add_assoc, f2_add_self, add_zero]
      rwa [he2, he2] at h1
    · intro z hz
      have h1 : vdot u z = 1 := (Finset.mem_filter.mp hz).2
      refine ⟨z + e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [vdot_add_right, h1, hde]; decide
      · ext j; simp only [Pi.add_apply]; rw [add_assoc, f2_add_self, add_zero]
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]; intro z h0 h1
    have e0 := (Finset.mem_filter.mp h0).2
    have e1 := (Finset.mem_filter.mp h1).2
    exact absurd (e0.symm.trans e1) (by decide)
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S0, S1]
    exact ⟨fun _ => trivial, fun _ => f2_cases (vdot u z)⟩
  have hsum : S0.card + S1.card = (Finset.univ : Finset (Fin q → F2)).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  rw [Finset.card_univ] at hsum
  change 2 * S1.card = Fintype.card (Fin q → F2)
  omega

lemma vdot_pair_surj {q : ℕ} (a b : Fin q → F2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Surjective (fun z : Fin q → F2 => ![vdot a z, vdot b z]) := by
  let M : Matrix (Fin 2) (Fin q) F2 := Matrix.of fun i k => if i = 0 then a k else b k
  have hmul : ∀ z, M.mulVecLin z = ![vdot a z, vdot b z] := fun z => by
    ext i; fin_cases i <;> simp [M, vdot, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  have htr_inj : Function.Injective M.transpose.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hcomb : c 0 • a + c 1 • b = 0 := by
      ext k
      have hk := congrFun hc k
      simpa [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using hk
    rcases f2_cases (c 0) with h0 | h0 <;> rcases f2_cases (c 1) with h1 | h1
    · ext i; fin_cases i <;> simp [h0, h1]
    · simp [h0, h1] at hcomb; exact absurd hcomb hb
    · simp [h0, h1] at hcomb; exact absurd hcomb ha
    · simp [h0, h1] at hcomb
      have heq : a = b := funext fun k => f2_eq_of_add_eq_zero (congrFun hcomb k)
      exact absurd heq hab
  have hrk_tr : M.transpose.rank = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    have hker : LinearMap.ker M.transpose.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr htr_inj
    rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    exact h1
  have hrk : M.rank = 2 := by rw [← Matrix.rank_transpose M]; exact hrk_tr
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank, Module.finrank_fin_fun] using hrk)
  intro y
  have hy : y ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, (hmul z).symm.trans hz⟩

lemma card_vdot_pair_nonzero {q : ℕ} (a b : Fin q → F2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    4 * (Finset.univ.filter (fun z : Fin q → F2 => vdot a z ≠ 0 ∨ vdot b z ≠ 0)).card =
      3 * Fintype.card (Fin q → F2) := by
  let L : (Fin q → F2) →ₗ[F2] (Fin 2 → F2) :=
    { toFun := fun z => ![vdot a z, vdot b z]
      map_add' := fun z₁ z₂ => by ext i; fin_cases i <;> simp [vdot_add_right]
      map_smul' := fun r z => by
        ext i; fin_cases i <;> simp [vdot, smul_eq_mul, Finset.mul_sum] <;>
          refine Finset.sum_congr rfl fun k _ => by ring }
  have hsurj : Function.Surjective L := vdot_pair_surj a b ha hb hab
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  have hcard_ker : Fintype.card (LinearMap.ker L) = 2 ^ Module.finrank F2 (LinearMap.ker L) := by
    have h := Module.card_eq_pow_finrank (K := F2) (V := LinearMap.ker L)
    simpa [F2, ZMod.card] using h
  have hcard_V : Fintype.card (Fin q → F2) = 2 ^ q := by
    simp [F2, ZMod.card]
  have h4ker : 4 * Fintype.card (LinearMap.ker L) = Fintype.card (Fin q → F2) := by
    rw [hcard_ker, hcard_V]
    calc 4 * 2 ^ Module.finrank F2 (LinearMap.ker L)
        = 2 ^ (2 + Module.finrank F2 (LinearMap.ker L)) := by rw [pow_add]; ring
      _ = 2 ^ q := congrArg (2 ^ ·) hrn
  have hker_filt : (Finset.univ.filter (fun z : Fin q → F2 => vdot a z = 0 ∧ vdot b z = 0)).card =
      Fintype.card (LinearMap.ker L) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun ⟨z, hz⟩ => ⟨z, by
          simp only [LinearMap.mem_ker]; ext i; fin_cases i <;> simp [L, hz.1, hz.2]⟩
        invFun := fun ⟨z, hz⟩ => ⟨z, by
          simp only [LinearMap.mem_ker] at hz
          exact ⟨by simpa [L] using congrFun hz 0, by simpa [L] using congrFun hz 1⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hdisj : Disjoint (Finset.univ.filter (fun z : Fin q → F2 => vdot a z = 0 ∧ vdot b z = 0))
      (Finset.univ.filter (fun z : Fin q → F2 => vdot a z ≠ 0 ∨ vdot b z ≠ 0)) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    rcases e2 with h | h
    · exact h e1.1
    · exact h e1.2
  have hunion : Finset.univ.filter (fun z : Fin q → F2 => vdot a z = 0 ∧ vdot b z = 0) ∪
      Finset.univ.filter (fun z : Fin q → F2 => vdot a z ≠ 0 ∨ vdot b z ≠ 0) = Finset.univ := by
    ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => by tauto⟩
  have hsum : (Finset.univ.filter (fun z : Fin q → F2 => vdot a z = 0 ∧ vdot b z = 0)).card +
      (Finset.univ.filter (fun z : Fin q → F2 => vdot a z ≠ 0 ∨ vdot b z ≠ 0)).card =
      Fintype.card (Fin q → F2) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  omega

lemma mem_line_of_vdot_imp {q : ℕ} (a b u : Fin q → F2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hu : u ≠ 0) (himp : ∀ z : Fin q → F2, vdot a z = 0 → vdot b z = 0 → vdot u z = 0) :
    u ∈ ({a, b, a + b} : Finset (Fin q → F2)) := by
  by_contra hnot
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  rcases hnot with ⟨hua, hub, huab⟩
  let M : Matrix (Fin 3) (Fin q) F2 :=
    Matrix.of fun i k => if i = 0 then a k else if i = 1 then b k else u k
  have htr_inj : Function.Injective M.transpose.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hcomb : c 0 • a + c 1 • b + c 2 • u = 0 := by
      ext k
      have hk := congrFun hc k
      simpa [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        mul_comm, add_assoc] using hk
    rcases f2_cases (c 0) with h0 | h0 <;> rcases f2_cases (c 1) with h1 | h1 <;>
      rcases f2_cases (c 2) with h2 | h2
    · ext i; fin_cases i <;> simp [h0, h1, h2]
    · simp [h0, h1, h2] at hcomb; exact absurd hcomb hu
    · simp [h0, h1, h2] at hcomb; exact absurd hcomb hb
    · simp [h0, h1, h2] at hcomb
      exact absurd (funext fun k => f2_eq_of_add_eq_zero (congrFun hcomb k)) (Ne.symm hub)
    · simp [h0, h1, h2] at hcomb; exact absurd hcomb ha
    · simp [h0, h1, h2] at hcomb
      exact absurd (funext fun k => f2_eq_of_add_eq_zero (congrFun hcomb k)) (Ne.symm hua)
    · simp [h0, h1, h2] at hcomb
      exact absurd (funext fun k => f2_eq_of_add_eq_zero (congrFun hcomb k)) hab
    · simp [h0, h1, h2] at hcomb
      have heq : a + b = u := funext fun k => f2_eq_of_add_eq_zero (congrFun hcomb k)
      exact absurd heq.symm huab
  have hrk_tr : M.transpose.rank = 3 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    have hker : LinearMap.ker M.transpose.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr htr_inj
    rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    exact h1
  have hrk : M.rank = 3 := by rw [← Matrix.rank_transpose M]; exact hrk_tr
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank, Module.finrank_fin_fun] using hrk)
  have hy : (![0, 0, (1 : F2)] : Fin 3 → F2) ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨z, hz⟩ := hy
  have hz0 : vdot a z = 0 := by simpa [M, vdot, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun hz 0
  have hz1 : vdot b z = 0 := by simpa [M, vdot, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun hz 1
  have hz2 : vdot u z = 1 := by simpa [M, vdot, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun hz 2
  have h0 := himp z hz0 hz1
  exact absurd (h0.symm.trans hz2) (by decide)

lemma line_eq_of_two_mem {q : ℕ} {a b u w : Fin q → F2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (huw : u ≠ w)
    (hu : u ∈ ({a, b, a + b} : Finset (Fin q → F2)))
    (hw : w ∈ ({a, b, a + b} : Finset (Fin q → F2))) :
    ({a, b, a + b} : Finset (Fin q → F2)) = {u, w, u + w} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
  have hadd : ∀ x y : Fin q → F2, x + (x + y) = y := fun x y => by
    ext k; simp only [Pi.add_apply]; rw [← add_assoc, f2_add_self, zero_add]
  have hadd2 : ∀ x y : Fin q → F2, (x + y) + x = y := fun x y => by
    rw [add_comm, hadd]
  have hadd3 : ∀ x y : Fin q → F2, x + (y + x) = y := fun x y => by
    rw [add_comm y x, hadd]
  have hadd4 : ∀ x y : Fin q → F2, (y + x) + x = y := fun x y => by
    rw [add_comm y x, hadd2]
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  · exact absurd rfl huw
  · rfl
  · rw [hadd]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [add_comm]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact absurd rfl huw
  · rw [hadd3]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [hadd2]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [hadd4]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact absurd rfl huw

lemma rank_sum_eq_imp {τ ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s : Finset τ) (M : τ → Matrix ι κ F2)
    (heq : (∑ j ∈ s, M j).rank = ∑ j ∈ s, (M j).rank) :
    (∀ j ∈ s, LinearMap.range (M j).mulVecLin ≤ LinearMap.range (∑ i ∈ s, M i).mulVecLin) ∧
    (∀ t ⊆ s, (∑ j ∈ t, M j).rank = ∑ j ∈ t, (M j).rank) := by
  constructor
  · let S := LinearMap.range (∑ i ∈ s, M i).mulVecLin
    let T := ⨆ i ∈ s, LinearMap.range (M i).mulVecLin
    have hST : S ≤ T := by
      rintro _ ⟨v, rfl⟩
      have hv : (∑ i ∈ s, M i).mulVecLin v = ∑ i ∈ s, (M i).mulVecLin v := by
        ext r
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.sum_apply,
          Finset.sum_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hv]
      refine Submodule.sum_mem T fun i hi => ?_
      exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨v, rfl⟩)
    have hT_dim_gen : ∀ u : Finset τ, Module.finrank F2 ((⨆ i ∈ u, LinearMap.range (M i).mulVecLin) : Submodule F2 (ι → F2)) ≤
        ∑ i ∈ u, (M i).rank := by
      intro u
      induction u using Finset.induction_on with
      | empty =>
        have hbot : ((⨆ i ∈ (∅ : Finset τ), LinearMap.range (M i).mulVecLin) : Submodule F2 (ι → F2)) = ⊥ := by simp
        rw [hbot, finrank_bot]; simp
      | insert a u ha ih =>
        rw [Finset.sum_insert ha]
        have hsup : ((⨆ i ∈ insert a u, LinearMap.range (M i).mulVecLin) : Submodule F2 (ι → F2)) =
            LinearMap.range (M a).mulVecLin ⊔ (⨆ i ∈ u, LinearMap.range (M i).mulVecLin) := by
          simp [Finset.mem_insert, iSup_or, iSup_sup_eq]
        have hfeq : Module.finrank F2 ((⨆ i ∈ insert a u, LinearMap.range (M i).mulVecLin) : Submodule F2 (ι → F2)) =
            Module.finrank F2 ((LinearMap.range (M a).mulVecLin ⊔ ⨆ i ∈ u, LinearMap.range (M i).mulVecLin) : Submodule F2 (ι → F2)) :=
          congrArg (fun X : Submodule F2 (ι → F2) => Module.finrank F2 X) hsup
        rw [hfeq]
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq
          (LinearMap.range (M a).mulVecLin) ((⨆ i ∈ u, LinearMap.range (M i).mulVecLin) : Submodule F2 (ι → F2))
        change Module.finrank F2 _ ≤ Module.finrank F2 (LinearMap.range (M a).mulVecLin) + _
        omega
    have hT_dim : Module.finrank F2 T ≤ ∑ i ∈ s, (M i).rank := hT_dim_gen s
    have hS_dim : Module.finrank F2 S = ∑ i ∈ s, (M i).rank := heq
    have hdim_eq : Module.finrank F2 S = Module.finrank F2 T := by
      have h1 := Submodule.finrank_mono hST
      omega
    have heq_ST : S = T := Submodule.eq_of_le_of_finrank_eq hST hdim_eq
    intro j hj
    change LinearMap.range (M j).mulVecLin ≤ S
    rw [heq_ST]
    exact le_iSup₂ (f := fun i (_ : i ∈ s) => LinearMap.range (M i).mulVecLin) j hj
  · intro t ht
    have hsplit : ∑ j ∈ s, M j = (∑ j ∈ t, M j) + (∑ j ∈ s \ t, M j) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset ht]
    have hsum_rk : ∑ j ∈ s, (M j).rank = (∑ j ∈ t, (M j).rank) + (∑ j ∈ s \ t, (M j).rank) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset ht]
    have h1 : (∑ j ∈ s, M j).rank ≤ (∑ j ∈ t, M j).rank + (∑ j ∈ s \ t, M j).rank := by
      rw [hsplit]; exact rank_add_le _ _
    have h2 : (∑ j ∈ t, M j).rank ≤ ∑ j ∈ t, (M j).rank := rank_sum_le t M
    have h3 : (∑ j ∈ s \ t, M j).rank ≤ ∑ j ∈ s \ t, (M j).rank := rank_sum_le (s \ t) M
    omega

lemma rank_blockDiagonal' {l : ℕ} {d : Fin l → ℕ}
    (B : (i : Fin l) → Matrix (Fin (d i)) (Fin (d i)) F2) :
    (Matrix.blockDiagonal' B).rank = ∑ i : Fin l, (B i).rank := by
  let I := Σ i : Fin l, Fin (d i)
  let e : (∀ i : Fin l, LinearMap.range (B i).mulVecLin) ≃ₗ[F2]
      LinearMap.range (Matrix.blockDiagonal' B).mulVecLin :=
    { toFun := fun f =>
        ⟨fun x => (f x.1).1 x.2, by
          have hv : ∀ i : Fin l, ∃ w : Fin (d i) → F2, (B i).mulVecLin w = (f i).1 := fun i => (f i).2
          choose w hw using hv
          refine ⟨fun x => w x.1 x.2, ?_⟩
          ext ⟨i, r⟩
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
          rw [Fintype.sum_sigma]
          have hzero : ∀ j : Fin l, j ≠ i →
              ∑ c : Fin (d j), Matrix.blockDiagonal' B ⟨i, r⟩ ⟨j, c⟩ * w j c = 0 := fun j hj =>
            Finset.sum_eq_zero fun c _ => by rw [Matrix.blockDiagonal'_apply_ne B r c hj.symm, zero_mul]
          rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun h => absurd (Finset.mem_univ i) h)]
          have heq : ∑ c : Fin (d i), Matrix.blockDiagonal' B ⟨i, r⟩ ⟨i, c⟩ * w i c =
              (B i).mulVecLin (w i) r := by
            simp [Matrix.blockDiagonal'_apply_eq, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
          rw [heq, hw i]⟩
      invFun := fun y => fun i =>
        ⟨fun r => y.1 ⟨i, r⟩, by
          obtain ⟨w, hw⟩ := y.2
          refine ⟨fun c => w ⟨i, c⟩, ?_⟩
          ext r
          have h1 := congrFun hw ⟨i, r⟩
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h1 ⊢
          rw [Fintype.sum_sigma] at h1
          have hzero : ∀ j : Fin l, j ≠ i →
              ∑ c : Fin (d j), Matrix.blockDiagonal' B ⟨i, r⟩ ⟨j, c⟩ * w ⟨j, c⟩ = 0 := fun j hj =>
            Finset.sum_eq_zero fun c _ => by rw [Matrix.blockDiagonal'_apply_ne B r c hj.symm, zero_mul]
          rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun h => absurd (Finset.mem_univ i) h)] at h1
          simpa [Matrix.blockDiagonal'_apply_eq] using h1⟩
      left_inv := fun f => by ext i r; rfl
      right_inv := fun y => by ext ⟨i, r⟩; rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change Module.finrank F2 (LinearMap.range (Matrix.blockDiagonal' B).mulVecLin) = _
  rw [← e.finrank_eq, Module.finrank_pi_fintype]
  rfl

lemma rank_submatrix_succ_le {I : Type} [Fintype I] [DecidableEq I]
    (coord : I ≃ Fin (Fintype.card I)) (M : Matrix (Fin (Fintype.card I + 1)) (Fin (Fintype.card I + 1)) F2) :
    (Matrix.of fun x y : I => M (coord x).succ (coord y).succ).rank ≤ M.rank := by
  let D : Matrix I I F2 := Matrix.of fun x y => M (coord x).succ (coord y).succ
  let P : (Fin (Fintype.card I + 1) → F2) →ₗ[F2] (I → F2) :=
    { toFun := fun v x => v (coord x).succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsub : LinearMap.range D.mulVecLin ≤ (LinearMap.range M.mulVecLin).map P := by
    rintro _ ⟨v, rfl⟩
    let v' : Fin (Fintype.card I + 1) → F2 := Fin.cases 0 (fun j => v (coord.symm j))
    refine ⟨M.mulVecLin v', ⟨v', rfl⟩, ?_⟩
    ext x
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.of_apply, D, Fin.sum_univ_succ, v', Fin.cases_zero, Fin.cases_succ,
      mul_zero, zero_add]
    rw [← Equiv.sum_comp coord]
    refine Finset.sum_congr rfl fun y _ => by simp
  have h1 := Submodule.finrank_mono hsub
  have hmap_eq : (LinearMap.range M.mulVecLin).map P =
      LinearMap.range (P.comp (LinearMap.range M.mulVecLin).subtype) := by
    ext z; simp [Submodule.mem_map]
  have h2 : Module.finrank F2 ((LinearMap.range M.mulVecLin).map P) ≤
      Module.finrank F2 (LinearMap.range M.mulVecLin) := by
    rw [hmap_eq]
    have hrk := LinearMap.finrank_range_add_finrank_ker (P.comp (LinearMap.range M.mulVecLin).subtype)
    omega
  exact le_trans h1 h2

lemma exists_disjoint_subspace_of_fixedpoint_free {n : ℕ}
    (T : (Fin (2 * n) → F2) →ₗ[F2] (Fin (2 * n) → F2))
    (hT_bij : Function.Bijective T)
    (hIT_bij : Function.Bijective ((LinearMap.id : (Fin (2 * n) → F2) →ₗ[F2] (Fin (2 * n) → F2)) + T)) :
    ∃ L : Submodule F2 (Fin (2 * n) → F2),
      Module.finrank F2 L = n ∧ L ⊓ L.map T = ⊥ := by
  suffices h : ∀ d : ℕ, d ≤ n →
      ∃ L : Submodule F2 (Fin (2 * n) → F2), Module.finrank F2 L = d ∧ L ⊓ L.map T = ⊥ by
    exact h n (le_refl n)
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨⊥, finrank_bot F2 (Fin (2 * n) → F2), by simp⟩
  | succ d ih =>
    intro hdn
    obtain ⟨L, hLdim, hLdisj⟩ := ih (by omega)
    let W : Submodule F2 (Fin (2 * n) → F2) := L ⊔ L.map T
    have hTL_dim : Module.finrank F2 (L.map T) = d := by
      have h := (Submodule.equivMapOfInjective T hT_bij.1 L).finrank_eq
      omega
    have hW_dim : Module.finrank F2 W = 2 * d := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq L (L.map T)
      rw [hLdisj, finrank_bot, add_zero, hLdim, hTL_dim] at h
      change Module.finrank F2 ((L ⊔ L.map T) : Submodule F2 (Fin (2 * n) → F2)) = 2 * d
      omega
    let S1 : Submodule F2 (Fin (2 * n) → F2) := W
    let S2 : Submodule F2 (Fin (2 * n) → F2) := W.comap T
    let S3 : Submodule F2 (Fin (2 * n) → F2) := W.comap ((LinearMap.id : (Fin (2 * n) → F2) →ₗ[F2] (Fin (2 * n) → F2)) + T)
    have hcard_S1 : (Finset.univ.filter (fun v => v ∈ S1)).card = 2 ^ (2 * d) := by
      have h := Module.card_eq_pow_finrank (K := F2) (V := S1)
      change Fintype.card S1 = Fintype.card F2 ^ Module.finrank F2 W at h
      rw [hW_dim] at h
      simp only [F2, ZMod.card] at h
      rw [← Fintype.card_subtype]; exact h
    have hcard_S2 : (Finset.univ.filter (fun v => v ∈ S2)).card = 2 ^ (2 * d) := by
      have hbij : (Finset.univ.filter (fun v => v ∈ S2)).card = (Finset.univ.filter (fun v => v ∈ S1)).card := by
        refine Finset.card_bij (fun v _ => T v) ?_ ?_ ?_
        · intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
        · intro v₁ _ v₂ _ h; exact hT_bij.1 h
        · intro w hw
          obtain ⟨v, rfl⟩ := hT_bij.2 w
          exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩, rfl⟩
      rw [hbij, hcard_S1]
    have hcard_S3 : (Finset.univ.filter (fun v => v ∈ S3)).card = 2 ^ (2 * d) := by
      have hbij : (Finset.univ.filter (fun v => v ∈ S3)).card = (Finset.univ.filter (fun v => v ∈ S1)).card := by
        refine Finset.card_bij (fun v _ => ((LinearMap.id : (Fin (2 * n) → F2) →ₗ[F2] (Fin (2 * n) → F2)) + T) v) ?_ ?_ ?_
        · intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
        · intro v₁ _ v₂ _ h; exact hIT_bij.1 h
        · intro w hw
          obtain ⟨v, rfl⟩ := hIT_bij.2 w
          exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩, rfl⟩
      rw [hbij, hcard_S1]
    let U : Finset (Fin (2 * n) → F2) :=
      Finset.univ.filter (fun v => v ∈ S1) ∪
      Finset.univ.filter (fun v => v ∈ S2) ∪
      Finset.univ.filter (fun v => v ∈ S3)
    have hU_lt : U.card < (Finset.univ : Finset (Fin (2 * n) → F2)).card := by
      have h01 : (0 : Fin (2 * n) → F2) ∈ Finset.univ.filter (fun v => v ∈ S1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, S1.zero_mem⟩
      have h02 : (0 : Fin (2 * n) → F2) ∈ Finset.univ.filter (fun v => v ∈ S2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, S2.zero_mem⟩
      have h03 : (0 : Fin (2 * n) → F2) ∈ Finset.univ.filter (fun v => v ∈ S3) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, S3.zero_mem⟩
      have hu12 : (Finset.univ.filter (fun v => v ∈ S1) ∪ Finset.univ.filter (fun v => v ∈ S2)).card + 1 ≤
          (Finset.univ.filter (fun v => v ∈ S1)).card + (Finset.univ.filter (fun v => v ∈ S2)).card := by
        have h := Finset.card_union_add_card_inter
          (Finset.univ.filter (fun v => v ∈ S1)) (Finset.univ.filter (fun v => v ∈ S2))
        have hpos : 1 ≤ (Finset.univ.filter (fun v => v ∈ S1) ∩ Finset.univ.filter (fun v => v ∈ S2)).card :=
          Finset.card_pos.mpr ⟨0, Finset.mem_inter.mpr ⟨h01, h02⟩⟩
        omega
      have hu123 : U.card + 1 ≤
          (Finset.univ.filter (fun v => v ∈ S1) ∪ Finset.univ.filter (fun v => v ∈ S2)).card +
          (Finset.univ.filter (fun v => v ∈ S3)).card := by
        have h := Finset.card_union_add_card_inter
          (Finset.univ.filter (fun v => v ∈ S1) ∪ Finset.univ.filter (fun v => v ∈ S2))
          (Finset.univ.filter (fun v => v ∈ S3))
        have hpos : 1 ≤ ((Finset.univ.filter (fun v => v ∈ S1) ∪ Finset.univ.filter (fun v => v ∈ S2)) ∩
            Finset.univ.filter (fun v => v ∈ S3)).card :=
          Finset.card_pos.mpr ⟨0, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h01, h03⟩⟩
        change (Finset.univ.filter (fun v => v ∈ S1) ∪ Finset.univ.filter (fun v => v ∈ S2) ∪
          Finset.univ.filter (fun v => v ∈ S3)).card + 1 ≤ _
        omega
      have hcard_univ : (Finset.univ : Finset (Fin (2 * n) → F2)).card = 2 ^ (2 * n) := by
        simp [F2, ZMod.card]
      have hpow_le : 4 * 2 ^ (2 * d) ≤ 2 ^ (2 * n) := by
        have h4 : 4 * 2 ^ (2 * d) = 2 ^ (2 * d + 2) := by rw [pow_add]; ring
        rw [h4]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hp1 : 1 ≤ 2 ^ (2 * d) := Nat.one_le_pow _ _ (by norm_num)
      rw [hcard_univ]
      omega
    have hex : ∃ v : Fin (2 * n) → F2, v ∉ U := by
      by_contra hall; push_neg at hall
      have hsub : Finset.univ ⊆ U := fun v _ => hall v
      have := Finset.card_le_card hsub
      omega
    obtain ⟨v, hvU⟩ := hex
    have hv1 : v ∉ W := fun h => hvU (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have hv2 : T v ∉ W := fun h => hvU (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have hv3 : v + T v ∉ W := fun h => hvU (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hvL : v ∉ L := fun h => hv1 (Submodule.mem_sup_left h)
    let L' : Submodule F2 (Fin (2 * n) → F2) := L ⊔ Submodule.span F2 {v}
    have hL'_dim : Module.finrank F2 L' = d + 1 := by
      have hinf : L ⊓ Submodule.span F2 {v} = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x ⟨hxL, hxV⟩
        change x ∈ Submodule.span F2 {v} at hxV
        rw [Submodule.mem_span_singleton] at hxV
        obtain ⟨α, rfl⟩ := hxV
        rcases f2_cases α with rfl | rfl
        · simp
        · rw [one_smul] at hxL; exact absurd hxL hvL
      have hvne : v ≠ 0 := fun h => hvL (h ▸ L.zero_mem)
      have hspan_dim : Module.finrank F2 (Submodule.span F2 ({v} : Set _)) = 1 :=
        finrank_span_singleton hvne
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span F2 {v})
      rw [hinf, finrank_bot, add_zero, hLdim, hspan_dim] at hadd
      exact hadd
    have hL'_disj : L' ⊓ L'.map T = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x ⟨hx1, hx2⟩
      obtain ⟨l₁, hl₁, v₁, hv₁, hx1_eq⟩ := Submodule.mem_sup.mp hx1
      rw [Submodule.mem_span_singleton] at hv₁
      obtain ⟨α, rfl⟩ := hv₁
      obtain ⟨y, hy, hyx⟩ := hx2
      obtain ⟨l₂, hl₂, v₂, hv₂, hy_eq⟩ := Submodule.mem_sup.mp hy
      rw [Submodule.mem_span_singleton] at hv₂
      obtain ⟨β, rfl⟩ := hv₂
      have heq : l₁ + α • v = T l₂ + β • T v := by
        rw [hx1_eq, ← hyx, ← hy_eq, map_add, map_smul]
      rcases f2_cases α with rfl | rfl <;> rcases f2_cases β with rfl | rfl
      · simp only [zero_smul, add_zero] at heq hx1_eq
        have hmem : l₁ ∈ L ⊓ L.map T := ⟨hl₁, ⟨l₂, hl₂, heq.symm⟩⟩
        rw [hLdisj, Submodule.mem_bot] at hmem
        rw [← hx1_eq, hmem]
      · simp only [zero_smul, one_smul, add_zero] at heq
        have hTv : T v = l₁ + T l₂ := by
          ext k
          have hk := congrFun heq k
          have h2 := f2_add_self (T l₂ k)
          simp only [Pi.add_apply] at hk ⊢
          linear_combination -hk - h2
        exact absurd (hTv ▸ Submodule.add_mem_sup hl₁ ⟨l₂, hl₂, rfl⟩) hv2
      · simp only [zero_smul, one_smul, add_zero] at heq
        have hv_eq : v = l₁ + T l₂ := by
          ext k
          have hk := congrFun heq k
          have h2 := f2_add_self (l₁ k)
          simp only [Pi.add_apply] at hk ⊢
          linear_combination hk - h2
        exact absurd (hv_eq ▸ Submodule.add_mem_sup hl₁ ⟨l₂, hl₂, rfl⟩) hv1
      · simp only [one_smul] at heq
        have hvTv : v + T v = l₁ + T l₂ := by
          ext k
          have hk := congrFun heq k
          have h2 := f2_add_self (l₁ k)
          have h3 := f2_add_self (T v k)
          simp only [Pi.add_apply] at hk ⊢
          linear_combination hk - h2 + h3
        exact absurd (hvTv ▸ Submodule.add_mem_sup hl₁ ⟨l₂, hl₂, rfl⟩) hv3
    exact ⟨L', hL'_dim, hL'_disj⟩

lemma split_invertible_pair {n : ℕ} (U W : Matrix (Fin (2 * n)) (Fin (2 * n)) F2)
    (hU : U.rank = 2 * n) (hW : W.rank = 2 * n) (hUW : (U + W).rank = 2 * n) :
    ∃ (pA qA pB qB pC qC : Fin n → Fin (2 * n) → F2),
      (∀ r c, U r c = ∑ k : Fin n, (pA k r * qA k c + pC k r * qC k c)) ∧
      (∀ r c, W r c = ∑ k : Fin n, (pB k r * qB k c + pC k r * qC k c)) := by
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k,
      fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k,
      fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  have hbij_of_rk : ∀ M : Matrix (Fin (2 * n)) (Fin (2 * n)) F2, M.rank = 2 * n → Function.Bijective M.mulVecLin := by
    intro M hM
    have hsurj : Function.Surjective M.mulVecLin := by
      rw [← LinearMap.range_eq_top]
      exact Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank, Module.finrank_fin_fun] using hM)
    have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    change M.rank + Module.finrank F2 (LinearMap.ker M.mulVecLin) = _ at hrn
    rw [hM, Module.finrank_fin_fun] at hrn
    have hker0 : Module.finrank F2 (LinearMap.ker M.mulVecLin) = 0 := by omega
    have hinj : Function.Injective M.mulVecLin :=
      LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)
    exact ⟨hinj, hsurj⟩
  let eU : (Fin (2 * n) → F2) ≃ₗ[F2] (Fin (2 * n) → F2) :=
    LinearEquiv.ofBijective U.mulVecLin (hbij_of_rk U hU)
  let T : (Fin (2 * n) → F2) →ₗ[F2] (Fin (2 * n) → F2) := eU.symm.toLinearMap.comp W.mulVecLin
  have hUT : ∀ v, U.mulVecLin (T v) = W.mulVecLin v := fun v => by
    dsimp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact eU.apply_symm_apply (W.mulVecLin v)
  have hT_bij : Function.Bijective T := eU.symm.bijective.comp (hbij_of_rk W hW)
  let idL : (Fin (2 * n) → F2) →ₗ[F2] (Fin (2 * n) → F2) := LinearMap.id
  have hIT_eq : eU.toLinearMap.comp (idL + T) = (U + W).mulVecLin := by
    apply LinearMap.ext; intro v; ext r
    have h1 : (eU.toLinearMap.comp (idL + T)) v = U.mulVecLin v + W.mulVecLin v := by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, idL, LinearMap.id_apply, map_add,
        LinearEquiv.coe_coe]
      rw [show eU (T v) = W.mulVecLin v from hUT v]
      rfl
    rw [h1]
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  have hIT_bij : Function.Bijective (idL + T) := by
    have hcomp : Function.Bijective (eU.toLinearMap.comp (idL + T)) := by
      rw [hIT_eq]; exact hbij_of_rk (U + W) hUW
    have h1 : Function.Bijective (eU.symm.toLinearMap.comp (eU.toLinearMap.comp (idL + T))) :=
      eU.symm.bijective.comp hcomp
    have hfun : eU.symm.toLinearMap.comp (eU.toLinearMap.comp (idL + T)) = idL + T := by
      apply LinearMap.ext; intro v; simp
    rwa [hfun] at h1
  obtain ⟨L, hLdim, hLdisj⟩ := exists_disjoint_subspace_of_fixedpoint_free T hT_bij hIT_bij
  let bL : Module.Basis (Fin n) F2 L := Module.finBasisOfFinrankEq F2 L hLdim
  let vecs : Fin n ⊕ Fin n → (Fin (2 * n) → F2) :=
    Sum.elim (fun k => (bL k).1) (fun k => T (bL k).1)
  have hlin : LinearIndependent F2 vecs := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    have hsum_L : ∑ k : Fin n, c (Sum.inl k) • (bL k).1 ∈ L :=
      Submodule.sum_mem L fun k _ => Submodule.smul_mem L _ (bL k).2
    have hsum_TL : ∑ k : Fin n, c (Sum.inr k) • T (bL k).1 ∈ L.map T := by
      refine ⟨∑ k : Fin n, c (Sum.inr k) • (bL k).1,
        Submodule.sum_mem L fun k _ => Submodule.smul_mem L _ (bL k).2, ?_⟩
      rw [map_sum]; refine Finset.sum_congr rfl fun k _ => map_smul T _ _
    have heq : ∑ k : Fin n, c (Sum.inl k) • (bL k).1 = ∑ k : Fin n, c (Sum.inr k) • T (bL k).1 :=
      funext fun r => f2_eq_of_add_eq_zero (congrFun hc r)
    have hmem : ∑ k : Fin n, c (Sum.inl k) • (bL k).1 ∈ L ⊓ L.map T := ⟨hsum_L, heq ▸ hsum_TL⟩
    rw [hLdisj, Submodule.mem_bot] at hmem
    have hmemR : ∑ k : Fin n, c (Sum.inr k) • T (bL k).1 = 0 := heq.symm.trans hmem
    have hmemR' : ∑ k : Fin n, c (Sum.inr k) • (bL k).1 = 0 := by
      apply hT_bij.1
      rw [map_zero, map_sum]
      simpa only [map_smul] using hmemR
    have hlinL := Fintype.linearIndependent_iff.mp bL.linearIndependent
    have hcl : ∀ k : Fin n, c (Sum.inl k) = 0 := hlinL (fun k => c (Sum.inl k)) (by
      apply Subtype.ext; simpa [Submodule.coe_sum, SetLike.val_smul] using hmem)
    have hcr : ∀ k : Fin n, c (Sum.inr k) = 0 := hlinL (fun k => c (Sum.inr k)) (by
      apply Subtype.ext; simpa [Submodule.coe_sum, SetLike.val_smul] using hmemR')
    intro idx; cases idx with
    | inl k => exact hcl k
    | inr k => exact hcr k
  have hcard : Fintype.card (Fin n ⊕ Fin n) = Module.finrank F2 (Fin (2 * n) → F2) := by
    simp [Module.finrank_fin_fun]; omega
  let bAll : Module.Basis (Fin n ⊕ Fin n) F2 (Fin (2 * n) → F2) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard
  let e : Fin n → (Fin (2 * n) → F2) := fun k => (bL k).1
  refine ⟨fun k => U.mulVecLin (e k) + W.mulVecLin (e k),
    fun k c => bAll.repr (Pi.single c 1) (Sum.inl k),
    fun k => W.mulVecLin (e k) + W.mulVecLin (T (e k)),
    fun k c => bAll.repr (Pi.single c 1) (Sum.inr k),
    fun k => W.mulVecLin (e k),
    fun k c => bAll.repr (Pi.single c 1) (Sum.inl k) + bAll.repr (Pi.single c 1) (Sum.inr k),
    ?_, ?_⟩
  · intro r c
    have hrep := bAll.sum_repr (Pi.single c (1 : F2))
    have hUrep := congrArg U.mulVecLin hrep
    have hcol : U.mulVecLin (Pi.single c (1 : F2)) r = U r c := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hb_inl : ∀ k : Fin n, bAll (Sum.inl k) = e k := fun k => by
      simp [bAll, vecs, e]
    have hb_inr : ∀ k : Fin n, bAll (Sum.inr k) = T (e k) := fun k => by
      simp [bAll, vecs, e]
    rw [← hcol, ← hUrep, map_sum, Fintype.sum_sum_type]
    simp only [map_smul, hb_inl, hb_inr, hUT, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := f2_add_self (W.mulVecLin (e k) r * bAll.repr (Pi.single c 1) (Sum.inl k))
    linear_combination -h1
  · intro r c
    have hrep := bAll.sum_repr (Pi.single c (1 : F2))
    have hWrep := congrArg W.mulVecLin hrep
    have hcol : W.mulVecLin (Pi.single c (1 : F2)) r = W r c := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hb_inl : ∀ k : Fin n, bAll (Sum.inl k) = e k := fun k => by
      simp [bAll, vecs, e]
    have hb_inr : ∀ k : Fin n, bAll (Sum.inr k) = T (e k) := fun k => by
      simp [bAll, vecs, e]
    rw [← hcol, ← hWrep, map_sum, Fintype.sum_sum_type]
    simp only [map_smul, hb_inl, hb_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := f2_add_self (W.mulVecLin (e k) r * bAll.repr (Pi.single c 1) (Sum.inr k))
    linear_combination -h1

lemma pairListBuild_wires_length (n m : ℕ)
    (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))) :
    ∀ base : ℕ, (pairListBuild n m base pairs).2.length = pairs.length := by
  induction pairs with
  | nil => intro _; rfl
  | cons hd rest ih =>
    rcases hd with ⟨p1, p2, q1, q2⟩
    intro base
    simp only [pairListBuild, List.length_cons, ih]

lemma pairListBuild_wire_val (n m : ℕ)
    (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))) :
    ∀ (base : ℕ), n + m ≤ base →
      ∀ (idx : Fin pairs.length) (x : Fin n) (y : Fin m) (ws : List Bool),
        ws.length = base →
        (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
        b2f (((pairListBuild n m base pairs).1.foldl wireStep ws).getD
            ((pairListBuild n m base pairs).2.getD idx.val 0) false) =
          (pairs.get idx).1 x * (pairs.get idx).2.2.1 y +
          (pairs.get idx).2.1 x * (pairs.get idx).2.2.2 y +
          (pairs.get idx).1 x * (pairs.get idx).2.1 x +
          (pairs.get idx).2.2.1 y * (pairs.get idx).2.2.2 y := by
  induction pairs with
  | nil => intro _ _ idx; exact Fin.elim0 idx
  | cons hd rest ih =>
    rcases hd with ⟨p1, p2, q1, q2⟩
    intro base hbase idx x y ws hlen hws
    dsimp only [pairListBuild]
    set g1 := pairGadget n m base p1 p2 q1 q2
    set r := pairListBuild n m (base + g1.1.length) rest
    obtain ⟨_, _, hlt1, hval1, _⟩ := pairGadget_spec n m base hbase p1 p2 q1 q2
    change g1.2 < base + g1.1.length at hlt1
    rw [List.foldl_append]
    let ws1 := g1.1.foldl wireStep ws
    have hlen1 : ws1.length = base + g1.1.length := by simp [ws1, foldl_wireStep_length, hlen]
    have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
      (foldl_wireStep_getD_old ws g1.1 w (by omega)).trans (hws w hw)
    refine Fin.cases ?_ ?_ idx
    · simp only [Fin.val_zero, List.getD_cons_zero, List.get_eq_getElem, List.getElem_cons_zero]
      rw [foldl_wireStep_getD_old ws1 r.1 g1.2 (by omega)]
      exact hval1 x y ws hlen hws
    · intro idx'
      simp only [Fin.val_succ, List.getD_cons_succ, List.get_eq_getElem, List.getElem_cons_succ]
      exact ih (base + g1.1.length) (by omega) idx' x y ws1 hlen1 hws1



-- ============================================================
-- L-meta-33646: Helper lemmas (linear algebra, Walsh-Hadamard, pairUp, tapsBuildGen)
-- ============================================================

lemma pivot_elim_aux {α : Type} [Fintype α] [DecidableEq α] :
    ∀ (d : ℕ) (S : Finset α) (W : Submodule F2 (α → F2)),
      Module.finrank F2 W = d →
      (∀ w ∈ W, ∀ j, j ∉ S → w j = 0) →
      ∃ R : Finset α, R ⊆ S ∧ R.card + d = S.card ∧
        ∀ c : α → F2, (∀ j, j ∉ S → c j = 0) →
          ∃ w ∈ W, ∀ j, j ∉ R → (c + w) j = 0 := by
  intro d
  induction d with
  | zero =>
    intro S W hdim _
    exact ⟨S, Finset.Subset.refl _, by omega, fun c hc => ⟨0, W.zero_mem, fun j hj => by
      simp only [add_zero]; exact hc j hj⟩⟩
  | succ d ih =>
    intro S W hdim hsupp
    have hne_bot : W ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hdim; omega
    have hex_nz : ∃ w0 ∈ W, w0 ≠ 0 := by
      by_contra hall; push_neg at hall
      apply hne_bot; rw [Submodule.eq_bot_iff]; exact hall
    obtain ⟨w0, hw0W, hw0_ne⟩ := hex_nz
    have hex_j : ∃ j0 : α, w0 j0 ≠ 0 := by
      by_contra hall; push_neg at hall; exact hw0_ne (funext hall)
    obtain ⟨j0, hj0_ne⟩ := hex_j
    have hj0_one : w0 j0 = 1 := by
      rcases f2_cases (w0 j0) with h0 | h1
      · exact absurd h0 hj0_ne
      · exact h1
    have hj0_mem : j0 ∈ S := by
      by_contra hnot; exact hj0_ne (hsupp w0 hw0W j0 hnot)
    let P : W →ₗ[F2] F2 :=
      { toFun := fun w => w.1 j0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hP_surj : Function.Surjective P := by
      intro r
      refine ⟨⟨r • w0, W.smul_mem r hw0W⟩, ?_⟩
      simp [P, hj0_one]
    have hP_range : LinearMap.range P = ⊤ := LinearMap.range_eq_top.mpr hP_surj
    have hrn := LinearMap.finrank_range_add_finrank_ker P
    rw [hP_range, finrank_top, Module.finrank_self, hdim] at hrn
    have hker_dim : Module.finrank F2 (LinearMap.ker P) = d := by omega
    let W' : Submodule F2 (α → F2) := (LinearMap.ker P).map W.subtype
    have hW'_dim : Module.finrank F2 W' = d := by
      have h := (Submodule.equivMapOfInjective W.subtype Subtype.val_injective (LinearMap.ker P)).finrank_eq
      change Module.finrank F2 ((LinearMap.ker P).map W.subtype) = d
      omega
    have hW'_le : W' ≤ W := by
      rintro _ ⟨w, _, rfl⟩; exact w.2
    have hW'_supp : ∀ w ∈ W', ∀ j, j ∉ S.erase j0 → w j = 0 := by
      rintro _ ⟨w, hwker, rfl⟩ j hj
      by_cases hjj : j = j0
      · subst hjj; exact hwker
      · have hnotS : j ∉ S := fun hS => hj (Finset.mem_erase.mpr ⟨hjj, hS⟩)
        exact hsupp w.1 w.2 j hnotS
    obtain ⟨R, hRsub, hRcard, hRclear⟩ := ih (S.erase j0) W' hW'_dim hW'_supp
    have hScard : (S.erase j0).card + 1 = S.card := Finset.card_erase_add_one hj0_mem
    refine ⟨R, Finset.Subset.trans hRsub (Finset.erase_subset j0 S), by omega, ?_⟩
    intro c hc
    let c' : α → F2 := c + c j0 • w0
    have hc'_supp : ∀ j, j ∉ S.erase j0 → c' j = 0 := by
      intro j hj
      by_cases hjj : j = j0
      · subst hjj
        simp only [c', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hj0_one, mul_one, f2_add_self]
      · have hnotS : j ∉ S := fun hS => hj (Finset.mem_erase.mpr ⟨hjj, hS⟩)
        simp only [c', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc j hnotS, hsupp w0 hw0W j hnotS,
          mul_zero, add_zero]
    obtain ⟨w', hw'W', hw'_clear⟩ := hRclear c' hc'_supp
    refine ⟨c j0 • w0 + w', W.add_mem (W.smul_mem _ hw0W) (hW'_le hw'W'), fun j hj => ?_⟩
    have h1 := hw'_clear j hj
    simpa [c', add_assoc] using h1

lemma pivot_elim {α : Type} [Fintype α] [DecidableEq α]
    (W : Submodule F2 (α → F2)) :
    ∃ R : Finset α, R.card + Module.finrank F2 W = Fintype.card α ∧
      ∀ c : α → F2, ∃ w ∈ W, ∀ j, j ∉ R → (c + w) j = 0 := by
  obtain ⟨R, _, hcard, hclear⟩ := pivot_elim_aux (Module.finrank F2 W) Finset.univ W rfl
    (fun _ _ _ h => absurd (Finset.mem_univ _) h)
  rw [Finset.card_univ] at hcard
  exact ⟨R, hcard, fun c => hclear c (fun _ h => absurd (Finset.mem_univ _) h)⟩

lemma rank_fromBlocks_ge_two_mul {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I F2) :
    2 * B.rank ≤ (Matrix.fromBlocks A B B.transpose 0).rank := by
  let M : Matrix (I ⊕ I) (I ⊕ I) F2 := Matrix.fromBlocks A B B.transpose 0
  let im := LinearMap.range M.mulVecLin
  let π2 : (I ⊕ I → F2) →ₗ[F2] (I → F2) :=
    { toFun := fun v i => v (Sum.inr i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : im →ₗ[F2] (I → F2) := π2.comp im.subtype
  have hrange_le : LinearMap.range B.transpose.mulVecLin ≤ LinearMap.range L := by
    rintro _ ⟨u, rfl⟩
    refine ⟨⟨M.mulVecLin (Sum.elim u 0), ⟨Sum.elim u 0, rfl⟩⟩, ?_⟩
    ext i
    simp only [L, π2, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.coe_mk, AddHom.coe_mk,
      M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  have hr1 : B.rank ≤ Module.finrank F2 (LinearMap.range L) := by
    rw [← Matrix.rank_transpose B]
    exact Submodule.finrank_mono hrange_le
  have htop_mem : ∀ y : LinearMap.range B.mulVecLin, Sum.elim y.1 (0 : I → F2) ∈ im := by
    intro y
    obtain ⟨u, hu⟩ := y.2
    refine ⟨Sum.elim 0 u, ?_⟩
    ext x; cases x with
    | inl i =>
      have h1 := congrFun hu i
      simpa only [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] using h1
    | inr i =>
      simp [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  let emb1 : LinearMap.range B.mulVecLin →ₗ[F2] LinearMap.ker L :=
    { toFun := fun y => ⟨⟨Sum.elim y.1 0, htop_mem y⟩, by
        ext i; simp [L, π2]⟩
      map_add' := fun y₁ y₂ => by
        apply Subtype.ext; apply Subtype.ext; ext x; cases x <;> simp
      map_smul' := fun r y => by
        apply Subtype.ext; apply Subtype.ext; ext x; cases x <;> simp }
  have hemb1_inj : Function.Injective emb1 := by
    intro y₁ y₂ h
    apply Subtype.ext; ext i
    have h1 := congrFun (congrArg (fun z : LinearMap.ker L => z.1.1) h) (Sum.inl i)
    simpa [emb1] using h1
  have hr2 : B.rank ≤ Module.finrank F2 (LinearMap.ker L) := by
    have h1 := (LinearEquiv.ofInjective emb1 hemb1_inj).finrank_eq
    have hle := Submodule.finrank_le (LinearMap.range emb1)
    change Module.finrank F2 (LinearMap.range B.mulVecLin) ≤ _
    omega
  have hrnL := LinearMap.finrank_range_add_finrank_ker L
  change Module.finrank F2 (LinearMap.range L) + Module.finrank F2 (LinearMap.ker L) = M.rank at hrnL
  change 2 * B.rank ≤ M.rank
  omega

lemma rank_fromBlocks_offdiag_full {n : ℕ} (M : Matrix (Fin n) (Fin n) F2) (hM : M.rank = n) :
    (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) F2) M M.transpose 0).rank = 2 * n := by
  have hge := rank_fromBlocks_ge_two_mul (0 : Matrix (Fin n) (Fin n) F2) M
  rw [hM] at hge
  have hle : (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) F2) M M.transpose 0).rank ≤
      Module.finrank F2 (Fin n ⊕ Fin n → F2) :=
    Submodule.finrank_le _
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hle
  omega

def chiZ (x : F2) : ℤ := if x = 0 then 1 else -1

lemma chiZ_add (x y : F2) : chiZ (x + y) = chiZ x * chiZ y := by
  rcases f2_cases x with rfl | rfl <;> rcases f2_cases y with rfl | rfl <;> decide

lemma chiZ_zero : chiZ 0 = 1 := rfl

lemma sum_chiZ_vdot {q : ℕ} (u : Fin q → F2) :
    (∑ z : Fin q → F2, chiZ (vdot u z)) = if u = 0 then (Fintype.card (Fin q → F2) : ℤ) else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp only [↓reduceIte, vdot_zero_left, chiZ_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  · simp only [if_neg hu]
    let S1 := Finset.univ.filter (fun z : Fin q → F2 => vdot u z = 1)
    let S0 := Finset.univ.filter (fun z : Fin q → F2 => ¬ vdot u z = 1)
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin q → F2))
      (fun z => vdot u z = 1) (fun z => chiZ (vdot u z))).symm
    rw [hsplit]
    have h1 : ∑ z ∈ S1, chiZ (vdot u z) = -(S1.card : ℤ) := by
      have : ∑ z ∈ S1, chiZ (vdot u z) = ∑ _z ∈ S1, (-1 : ℤ) :=
        Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.mp hz).2]; decide
      rw [this, Finset.sum_const, nsmul_eq_mul]; ring
    have h0 : ∑ z ∈ S0, chiZ (vdot u z) = (S0.card : ℤ) := by
      have : ∑ z ∈ S0, chiZ (vdot u z) = ∑ _z ∈ S0, (1 : ℤ) :=
        Finset.sum_congr rfl fun z hz => by
          have hne : vdot u z ≠ 1 := (Finset.mem_filter.mp hz).2
          rcases f2_cases (vdot u z) with hv | hv
          · rw [hv]; rfl
          · exact absurd hv hne
      rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard1 := card_vdot_eq_one u hu
    have hsum_card : S1.card + S0.card = Fintype.card (Fin q → F2) := by
      have hdisj : Disjoint S1 S0 := by
        rw [Finset.disjoint_left]; intro z h1 h0
        exact (Finset.mem_filter.mp h0).2 (Finset.mem_filter.mp h1).2
      have hunion : S1 ∪ S0 = Finset.univ := by
        ext z; simp only [Finset.mem_union, S1, S0, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => trivial, fun _ => Classical.em _⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    change (∑ z ∈ S1, chiZ (vdot u z)) + (∑ z ∈ S0, chiZ (vdot u z)) = 0
    rw [h1, h0]
    have heq_card : S0.card = S1.card := by
      change 2 * S1.card = Fintype.card (Fin q → F2) at hcard1
      omega
    rw [heq_card]; ring

lemma four_mul_or_nonzero_chiZ {q : ℕ} (a b z : Fin q → F2) :
    (4 : ℤ) * (if vdot a z ≠ 0 ∨ vdot b z ≠ 0 then 1 else 0) =
      3 - chiZ (vdot a z) - chiZ (vdot b z) - chiZ (vdot (a + b) z) := by
  rw [vdot_add_left]
  rcases f2_cases (vdot a z) with ha | ha <;> rcases f2_cases (vdot b z) with hb | hb <;>
    simp [ha, hb, chiZ] <;> decide

lemma two_mul_eq_one_chiZ {q : ℕ} (u z : Fin q → F2) :
    (2 : ℤ) * (if vdot u z = 1 then 1 else 0) = 1 - chiZ (vdot u z) := by
  rcases f2_cases (vdot u z) with h | h <;> simp [h, chiZ]

lemma rank_le_two_decomp {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ F2) (hM : M.rank ≤ 2) :
    ∃ (p1 p2 : ι → F2) (q1 q2 : κ → F2), ∀ r c, M r c = p1 r * q1 c + p2 r * q2 c := by
  set d := M.rank with hd_eq
  let b := Module.finBasisOfFinrankEq F2 (LinearMap.range M.mulVecLin) hd_eq.symm
  let col : κ → LinearMap.range M.mulVecLin := fun c => ⟨M.mulVecLin (Pi.single c 1), ⟨Pi.single c 1, rfl⟩⟩
  let p1 : ι → F2 := fun r => if h : 0 < d then (b ⟨0, h⟩).1 r else 0
  let p2 : ι → F2 := fun r => if h : 1 < d then (b ⟨1, h⟩).1 r else 0
  let q1 : κ → F2 := fun c => if h : 0 < d then b.repr (col c) ⟨0, h⟩ else 0
  let q2 : κ → F2 := fun c => if h : 1 < d then b.repr (col c) ⟨1, h⟩ else 0
  refine ⟨p1, p2, q1, q2, fun r c => ?_⟩
  have hrep := b.sum_repr (col c)
  have hval := congrFun (congrArg Subtype.val hrep) r
  have hcol : (col c).1 r = M r c := by
    simp [col, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Submodule.coe_sum, Finset.sum_apply, hcol] at hval
  rw [← hval]
  have hd : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd with hd0 | hd1 | hd2
  · have hsum0 : (∑ x : Fin d, ((b.repr (col c)) x • b x).1 r) = 0 :=
      Finset.sum_eq_zero fun x _ => absurd x.isLt (by omega)
    rw [hsum0]; simp [p1, p2, q1, q2, hd0]
  · have h0lt : 0 < d := by omega
    have hsum1 : (∑ x : Fin d, ((b.repr (col c)) x • b x).1 r) =
        b.repr (col c) ⟨0, h0lt⟩ * (b ⟨0, h0lt⟩).1 r := by
      have : Finset.univ = ({⟨0, h0lt⟩} : Finset (Fin d)) := by
        ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact Fin.ext (by omega)
      rw [this, Finset.sum_singleton]; rfl
    rw [hsum1]
    simp only [p1, p2, q1, q2, h0lt, show ¬ (1 < d) by omega, ↓reduceDIte, mul_zero, add_zero]
    ring
  · have h0lt : 0 < d := by omega
    have h1lt : 1 < d := by omega
    have hsum2 : (∑ x : Fin d, ((b.repr (col c)) x • b x).1 r) =
        b.repr (col c) ⟨0, h0lt⟩ * (b ⟨0, h0lt⟩).1 r +
        b.repr (col c) ⟨1, h1lt⟩ * (b ⟨1, h1lt⟩).1 r := by
      have h01 : (⟨0, h0lt⟩ : Fin d) ≠ ⟨1, h1lt⟩ := by intro h; cases h
      have : Finset.univ = ({⟨0, h0lt⟩, ⟨1, h1lt⟩} : Finset (Fin d)) := by
        ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        have : x.val = 0 ∨ x.val = 1 := by omega
        rcases this with hx | hx
        · exact Or.inl (Fin.ext hx)
        · exact Or.inr (Fin.ext hx)
      rw [this, Finset.sum_insert (by simp [h01]), Finset.sum_singleton]; rfl
    rw [hsum2]
    simp only [p1, p2, q1, q2, h0lt, h1lt, ↓reduceDIte]
    ring

def pairUp {w : ℕ} : List ((Fin (w + 1) → F2) × (Fin (w + 1) → F2)) →
    List ((Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2))
  | [] => []
  | [(p, q)] => [(p, 0, q, 0)]
  | (p1, q1) :: (p2, q2) :: rest => (p1, p2, q1, q2) :: pairUp rest

lemma pairUp_length {w : ℕ} : ∀ (L : List ((Fin (w + 1) → F2) × (Fin (w + 1) → F2))),
    2 * (pairUp L).length = L.length + L.length % 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | _ :: _ :: rest => by
    have ih := pairUp_length rest
    simp only [pairUp, List.length_cons]
    omega

lemma pairUp_sum {w : ℕ} (r c : Fin (w + 1)) :
    ∀ (L : List ((Fin (w + 1) → F2) × (Fin (w + 1) → F2))),
      ((pairUp L).map (fun t => t.1 r * t.2.2.1 c + t.2.1 r * t.2.2.2 c)).sum =
      (L.map (fun x => x.1 r * x.2 c)).sum
  | [] => by simp [pairUp]
  | [(p, q)] => by simp [pairUp]
  | (p1, q1) :: (p2, q2) :: rest => by
    have ih := pairUp_sum r c rest
    simp only [pairUp, List.map_cons, List.sum_cons, ih]
    ring

def tapsBuildGen {α β : Type} [DecidableEq α] (w : ℕ) (taggedWires : List (β × ℕ))
    (sel : α → β → Bool)
    (corr : α → (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × F2) :
    ℕ → List α → List Gate × (α → ℕ)
  | _, [] => ([], fun _ => 0)
  | base, z :: zs =>
    let aff := affineBuild (w + 1) (w + 1) base (corr z).1 (corr z).2.1 (corr z).2.2
    let base1 := base + aff.1.length
    let selected := (taggedWires.filter (fun p => sel z p.1)).map Prod.snd
    let out := xorListBuild base1 (aff.2 :: selected)
    let base2 := base1 + out.1.length
    let rest := tapsBuildGen w taggedWires sel corr base2 zs
    (aff.1 ++ out.1 ++ rest.1, fun z' => if z' = z then out.2 else rest.2 z')

lemma tapsBuildGen_spec {α β : Type} [DecidableEq α] (w : ℕ) (taggedWires : List (β × ℕ))
    (sel : α → β → Bool)
    (corr : α → (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × F2)
    (zs : List α) :
    ∀ (base : ℕ), (w + 1) + (w + 1) ≤ base →
      (∀ p ∈ taggedWires, p.2 < base) →
      let res := tapsBuildGen w taggedWires sel corr base zs
      isLinearOK res.1 base ∧
      res.1.countP nlGate = 0 ∧
      (∀ z ∈ zs, res.2 z < base + res.1.length) ∧
      (∀ (x y : Fin (w + 1)) (ws : List Bool),
        ws.length = base →
        (∀ u < (w + 1) + (w + 1), ws.getD u false = (oneEach x y).getD u false) →
        ∀ z ∈ zs,
          b2f ((res.1.foldl wireStep ws).getD (res.2 z) false) =
            (corr z).1 x + (corr z).2.1 y + (corr z).2.2 +
            ((taggedWires.filter (fun p => sel z p.1)).map (fun p => b2f (ws.getD p.2 false))).sum) ∧
      (∀ (ds : List ℕ),
        ds.length = base →
        (∀ u < (w + 1) + (w + 1), ds.getD u 0 = 0) →
        (∀ p ∈ taggedWires, ds.getD p.2 0 ≤ 1) →
        ∀ z ∈ zs, (res.1.foldl depthStep ds).getD (res.2 z) 0 ≤ 1) := by
  induction zs with
  | nil =>
    intro base _ _
    simp only [tapsBuildGen, List.countP_nil]
    exact ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
      trivial, fun _ h => by simp at h, fun _ _ _ _ _ _ h => by simp at h,
      fun _ _ _ _ _ h => by simp at h⟩
  | cons z zs ih =>
    intro base hbase hpw
    dsimp only [tapsBuildGen]
    set aff := affineBuild (w + 1) (w + 1) base (corr z).1 (corr z).2.1 (corr z).2.2
    set base1 := base + aff.1.length with hbase1
    set selected := (taggedWires.filter (fun p => sel z p.1)).map Prod.snd
    set out := xorListBuild base1 (aff.2 :: selected)
    set base2 := base1 + out.1.length with hbase2
    set rest := tapsBuildGen w taggedWires sel corr base2 zs
    obtain ⟨hokA, hnlA, hltA, hvalA, hdepA⟩ :=
      affineBuild_spec (w + 1) (w + 1) base hbase (corr z).1 (corr z).2.1 (corr z).2.2
    change isLinearOK aff.1 base at hokA
    change aff.1.countP nlGate = 0 at hnlA
    change aff.2 < base1 at hltA
    have hsel_lt : ∀ u ∈ aff.2 :: selected, u < base1 := by
      intro u hu
      simp only [List.mem_cons, selected, List.mem_map, List.mem_filter] at hu
      rcases hu with rfl | ⟨p, ⟨hp, _⟩, rfl⟩
      · exact hltA
      · have := hpw p hp; omega
    obtain ⟨hokO, hnlO, hltO, hvalO, hdepO⟩ := xorListBuild_spec (aff.2 :: selected) base1 hsel_lt
    change isLinearOK out.1 base1 at hokO
    change out.1.countP nlGate = 0 at hnlO
    change out.2 < base2 at hltO
    obtain ⟨hokR, hnlR, hltR, hvalR, hdepR⟩ :=
      ih base2 (by omega) (fun p hp => by have := hpw p hp; omega)
    change isLinearOK rest.1 base2 at hokR
    change rest.1.countP nlGate = 0 at hnlR
    change ∀ z' ∈ zs, rest.2 z' < base2 + rest.1.length at hltR
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h1 := isLinearOK_append hokA hokO
      exact isLinearOK_append h1 (isLinearOK_eq hokR (by simp [List.length_append, hbase1, hbase2]; omega))
    · simp only [List.countP_append, hnlA, hnlO, hnlR]
    · intro z' hz'
      simp only [List.mem_cons] at hz'
      simp only [List.length_append]
      split_ifs with hzz
      · omega
      · rcases hz' with rfl | hz's
        · exact absurd rfl hzz
        · have := hltR z' hz's; omega
    · intro x y ws hlen hws z' hz'
      rw [List.foldl_append, List.foldl_append]
      let ws1 := aff.1.foldl wireStep ws
      have hlen1 : ws1.length = base1 := by simp [ws1, foldl_wireStep_length, hlen, hbase1]
      have hws1 : ∀ u < (w + 1) + (w + 1), ws1.getD u false = (oneEach x y).getD u false := fun u hu =>
        (foldl_wireStep_getD_old ws aff.1 u (by omega)).trans (hws u hu)
      let ws2 := out.1.foldl wireStep ws1
      have hlen2 : ws2.length = base2 := by simp [ws2, foldl_wireStep_length, hlen1, hbase2]
      have hws2 : ∀ u < (w + 1) + (w + 1), ws2.getD u false = (oneEach x y).getD u false := fun u hu =>
        (foldl_wireStep_getD_old ws1 out.1 u (by omega)).trans (hws1 u hu)
      split_ifs with hzz
      · subst hzz
        rw [foldl_wireStep_getD_old ws2 rest.1 out.2 (by omega)]
        rw [hvalO ws1 hlen1]
        simp only [List.map_cons, List.sum_cons, selected, List.map_map]
        rw [hvalA x y ws hlen hws]
        congr 1
        refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
        have hp_mem : p ∈ taggedWires := (List.mem_filter.mp hp).1
        have hplt : p.2 < ws.length := by have := hpw p hp_mem; omega
        simp only [Function.comp_apply, ws1, foldl_wireStep_getD_old ws aff.1 p.2 hplt]
      · simp only [List.mem_cons] at hz'
        have hz's : z' ∈ zs := hz'.resolve_left hzz
        rw [hvalR x y ws2 hlen2 hws2 z' hz's]
        congr 1
        refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
        have hp_mem : p ∈ taggedWires := (List.mem_filter.mp hp).1
        have hplt : p.2 < base := hpw p hp_mem
        rw [foldl_wireStep_getD_old ws1 out.1 p.2 (by omega),
          foldl_wireStep_getD_old ws aff.1 p.2 (by omega)]
    · intro ds hlen hds hdpw z' hz'
      rw [List.foldl_append, List.foldl_append]
      let ds1 := aff.1.foldl depthStep ds
      have hlen1 : ds1.length = base1 := by simp [ds1, foldl_depthStep_length, hlen, hbase1]
      have hds1 : ∀ u < (w + 1) + (w + 1), ds1.getD u 0 = 0 := fun u hu =>
        (foldl_depthStep_getD_old ds aff.1 u (by omega)).trans (hds u hu)
      let ds2 := out.1.foldl depthStep ds1
      have hlen2 : ds2.length = base2 := by simp [ds2, foldl_depthStep_length, hlen1, hbase2]
      have hds2 : ∀ u < (w + 1) + (w + 1), ds2.getD u 0 = 0 := fun u hu =>
        (foldl_depthStep_getD_old ds1 out.1 u (by omega)).trans (hds1 u hu)
      have hdpw2 : ∀ p ∈ taggedWires, ds2.getD p.2 0 ≤ 1 := fun p hp => by
        have hplt := hpw p hp
        rw [foldl_depthStep_getD_old ds1 out.1 p.2 (by omega),
          foldl_depthStep_getD_old ds aff.1 p.2 (by omega)]
        exact hdpw p hp
      split_ifs with hzz
      · subst hzz
        rw [foldl_depthStep_getD_old ds2 rest.1 out.2 (by omega)]
        refine hdepO ds1 1 hlen1 ?_
        intro u hu
        simp only [List.mem_cons, selected, List.mem_map, List.mem_filter] at hu
        rcases hu with rfl | ⟨p, ⟨hp, _⟩, rfl⟩
        · rw [hdepA ds hlen hds]; omega
        · have hplt := hpw p hp
          rw [foldl_depthStep_getD_old ds aff.1 p.2 (by omega)]
          exact hdpw p hp
      · simp only [List.mem_cons] at hz'
        have hz's : z' ∈ zs := hz'.resolve_left hzz
        exact hdepR ds2 hlen2 hds2 hdpw2 z' hz's

-- ============================================================
-- Direction 1: Lower bound, equality (odd = empty), +1 (odd = H \ {0})
-- ============================================================

lemma lower_bound_dir (q l : ℕ) (s : Fin l → ℕ)
    (a b : Fin l → (Fin q → F2)) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (U W : (i : Fin l) → Matrix (Fin (s i)) (Fin (s i)) F2)
    (hUW : ∀ i, (U i).rank = s i ∧ (W i).rank = s i ∧ (U i + W i).rank = s i)
    (S : Submodule F2 (Matrix (Σ i : Fin l, Fin (s i)) (Σ i : Fin l, Fin (s i)) F2))
    (t : ℕ) :
    let V := Fin q → F2
    let I := Σ i : Fin l, Fin (s i)
    let T := Matrix I I F2
    let line := fun i : Fin l => ({a i, b i, a i + b i} : Finset V)
    let lines := Finset.univ.image line
    let mass := fun H : Finset V => ∑ i, if line i = H then s i else 0
    let N := ∑ i, s i
    let free := Module.finrank F2 S
    let K := fun z : V =>
      Matrix.blockDiagonal' (fun i => vdot (a i) z • U i + vdot (b i) z • W i)
    let w := Fintype.card (I ⊕ I)
    let coord := Fintype.equivFin (I ⊕ I)
    let table := fun (A : T) (z : V) (x y : Fin (w + 1)) =>
      let X := Matrix.fromBlocks A (K z) (K z).transpose (0 : T)
      Fin.cases false (fun i => Fin.cases false (fun j =>
        decide (X (coord.symm i) (coord.symm j) ≠ 0)) y) x
    let m := fun u : V => ∑ H ∈ lines, if u ∈ H then mass H else 0
    let odd := Finset.univ.filter (fun u : V => m u % 2 = 1)
    (∃ (C : Circuit) (tap : T → V → ℕ),
      ReadsBack ((w + 1) + (w + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
      ∀ A ∈ S, ∀ z : V,
        (depthsOf ((w + 1) + (w + 1)) C.gates).getD (tap A z) 0 ≤ 1 ∧
        Represents (table A z) ⟨C.gates, tap A z⟩) →
    free ≤ t ∧ 3 * N ≤ 2 * (t - free) ∧
      (2 * (t - free) = 3 * N → odd = ∅) ∧
      (2 * (t - free) = 3 * N + 1 → ∃ H : Submodule F2 V,
        ∀ u : V, u ∈ odd ↔ u ≠ 0 ∧ u ∈ H) := by
  intro V I T line lines mass N free K w coord table m odd
  rintro ⟨C, tap, hrb, hfan, hcnt, htap⟩
  let width := (w + 1) + (w + 1)
  obtain ⟨M, hMrk, _, hW⟩ := circuit_depth1_decomp (w + 1) (w + 1) C.gates hrb hfan
  let NL1 : Finset (Fin C.gates.length) := Finset.univ.filter (fun j =>
    nlGate (C.gates.get j) = true ∧ (depthsOf width C.gates).getD (width + j.val) 0 ≤ 1)
  have hNL1_card : NL1.card ≤ t := by
    have hsub : NL1 ⊆ Finset.univ.filter (fun j : Fin C.gates.length => nlGate (C.gates.get j) = true) :=
      fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
    have h1 := Finset.card_le_card hsub
    have h2 := (countP_eq_card_filter C.gates nlGate).symm
    omega
  let D : Fin C.gates.length → Matrix (I ⊕ I) (I ⊕ I) F2 := fun j =>
    Matrix.of fun x y =>
      M j (coord x).succ (coord y).succ + M j (coord x).succ 0 + M j 0 (coord y).succ + M j 0 0
  have hDrk : ∀ j : Fin C.gates.length, (D j).rank ≤ 2 := fun j => by
    let ddM : Matrix (Fin (w + 1)) (Fin (w + 1)) F2 :=
      Matrix.of fun r c => M j r c + M j r 0 + M j 0 c + M j 0 0
    have hsub : D j = Matrix.of fun x y : I ⊕ I => ddM (coord x).succ (coord y).succ := rfl
    rw [hsub]
    exact le_trans (rank_submatrix_succ_le coord ddM) (le_trans (dd_rank_le (M j) 0 0) (hMrk j))
  -- Step 1: Every X(A, z) for A in S, z : V lies in span of {D j | j in NL1}
  have hX_span : ∀ A ∈ S, ∀ z : V,
      ∃ c : NL1 → F2, Matrix.fromBlocks A (K z) (K z).transpose (0 : T) = ∑ j : NL1, c j • D j.1 := by
    intro A hA z
    have hrep : ∀ r c, (wiresOf C.gates (oneEach r c)).getD (tap A z) false = table A z r c :=
      fun r c => (htap A hA z).2 r c
    have hwire_rep : ∃ (cf : Fin C.gates.length → F2) (α β : Fin (w + 1) → F2) (c0 : F2),
        (∀ j, cf j ≠ 0 → j ∈ NL1) ∧
        ∀ r c', b2f (table A z r c') = (∑ j : Fin C.gates.length, cf j * M j r c') + α r + β c' + c0 := by
      by_cases hlt : tap A z < width + C.gates.length
      · obtain ⟨cf, α, β, c0, hsupp, hxy⟩ := (hW (tap A z) hlt).2 (htap A hA z).1
        refine ⟨cf, α, β, c0, fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp j hj⟩, fun r c' => ?_⟩
        rw [← hrep r c']; exact hxy r c'
      · refine ⟨0, 0, 0, 0, fun j hj => absurd rfl hj, fun r c' => ?_⟩
        rw [← hrep r c']
        have hge : (wiresOf C.gates (oneEach r c')).length ≤ tap A z := by
          simp only [wiresOf_length, oneEach, List.length_append, List.length_ofFn]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, b2f]
    obtain ⟨cf, α, β, c0, hsupp, hT⟩ := hwire_rep
    refine ⟨fun j => cf j.1, ?_⟩
    ext x y
    let X := Matrix.fromBlocks A (K z) (K z).transpose (0 : T)
    have hX_eq : X x y = b2f (table A z (coord x).succ (coord y).succ) +
        b2f (table A z (coord x).succ 0) + b2f (table A z 0 (coord y).succ) + b2f (table A z 0 0) := by
      simp only [table, Fin.cases_succ, Fin.cases_zero, Equiv.symm_apply_apply, b2f,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      rcases f2_cases (X x y) with h0 | h1
      · simp [X, h0]
      · simp [X, h1]
    change X x y = _
    rw [hX_eq, hT, hT, hT, hT]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hfilt : (∑ j : Fin C.gates.length, cf j * (M j (coord x).succ (coord y).succ +
        M j (coord x).succ 0 + M j 0 (coord y).succ + M j 0 0)) = ∑ j : NL1, cf j.1 * D j.1 x y := by
      rw [← Finset.sum_subset (Finset.subset_univ NL1)]
      · rw [← Finset.sum_attach NL1]; rfl
      · intro j _ hnot
        have hcf0 : cf j = 0 := by by_contra hne; exact hnot (hsupp j hne)
        simp [hcf0]
    rw [← hfilt]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h1 := f2_add_self (α (coord x).succ)
    have h2 := f2_add_self (α 0)
    have h3 := f2_add_self (β (coord y).succ)
    have h4 := f2_add_self (β 0)
    have h5 := f2_add_self c0
    linear_combination h1 + h2 + h3 + h4 + h5 + h5
  -- Step 2: Shorten on S via pivot_elim!
  let φ : (NL1 → F2) →ₗ[F2] Matrix (I ⊕ I) (I ⊕ I) F2 :=
    { toFun := fun c => ∑ j : NL1, c j • D j.1
      map_add' := fun c₁ c₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]; rfl }
  let embS : T →ₗ[F2] Matrix (I ⊕ I) (I ⊕ I) F2 :=
    { toFun := fun A => Matrix.fromBlocks A 0 0 0
      map_add' := fun A₁ A₂ => by ext x y; cases x <;> cases y <;> simp <;> rfl
      map_smul' := fun r A => by ext x y; cases x <;> cases y <;> simp <;> rfl }
  have hembS_inj : Function.Injective embS := by
    intro A₁ A₂ h
    ext r c
    have h1 := congrFun (congrFun h (Sum.inl r)) (Sum.inl c)
    simpa [embS] using h1
  let S' : Submodule F2 (Matrix (I ⊕ I) (I ⊕ I) F2) := S.map embS
  have hS'_dim : Module.finrank F2 S' = free :=
    (Submodule.equivMapOfInjective embS hembS_inj S).finrank_eq.symm
  have hK0 : K 0 = 0 := by
    ext ⟨i, r⟩ ⟨i', c'⟩
    by_cases hi : i = i'
    · subst hi
      simp only [K, Matrix.zero_apply, Matrix.blockDiagonal'_apply_eq]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vdot,
        show ∀ k : Fin q, (0 : V) k = 0 from fun _ => rfl,
        mul_zero, Finset.sum_const_zero, zero_mul, add_zero]
    · simp only [K, Matrix.zero_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hi]
  have hS'_le_range : S' ≤ LinearMap.range φ := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨c, hc⟩ := hX_span A hA 0
    refine ⟨c, ?_⟩
    rw [hK0, Matrix.transpose_zero] at hc
    exact hc.symm
  let Wker : Submodule F2 (NL1 → F2) := S'.comap φ
  have hWker_map : Wker.map φ = S' := by
    ext M; simp only [Submodule.mem_map, Wker, Submodule.mem_comap]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact hc
    · intro hM
      obtain ⟨c, hc⟩ := hS'_le_range hM
      exact ⟨c, hc.symm ▸ hM, hc⟩
  have hfree_le_Wker : free ≤ Module.finrank F2 Wker := by
    rw [← hS'_dim, ← hWker_map]
    have hmap_eq : Wker.map φ = LinearMap.range (φ.comp Wker.subtype) := by
      ext M; simp [Submodule.mem_map]
    rw [hmap_eq]
    have hrn := LinearMap.finrank_range_add_finrank_ker (φ.comp Wker.subtype)
    omega
  obtain ⟨R, hRcard, hRclear⟩ := pivot_elim Wker
  rw [Fintype.card_coe] at hRcard
  have hfree_le_t : free ≤ t := by omega
  have hR_le : R.card ≤ t - free := by omega
  -- Step 3: For each basis vector e_k of V, find A_k in S and coeff supported in R!
  have hbasis_rep : ∀ k : Fin q, ∃ (Ak : T) (ck : NL1 → F2),
      (∀ r, r ∉ R → ck r = 0) ∧
      Matrix.fromBlocks Ak (K (Pi.single k 1)) (K (Pi.single k 1)).transpose 0 = ∑ r ∈ R, ck r • D r.1 := by
    intro k
    obtain ⟨c0, hc0⟩ := hX_span 0 S.zero_mem (Pi.single k 1)
    obtain ⟨w0, hw0W, hclear0⟩ := hRclear c0
    obtain ⟨Ak, _, hAk⟩ := hw0W
    refine ⟨Ak, c0 + w0, hclear0, ?_⟩
    have hphi : φ (c0 + w0) = Matrix.fromBlocks Ak (K (Pi.single k 1)) (K (Pi.single k 1)).transpose 0 := by
      rw [map_add]
      have h1 : φ c0 = Matrix.fromBlocks 0 (K (Pi.single k 1)) (K (Pi.single k 1)).transpose 0 := hc0.symm
      have h2 : φ w0 = Matrix.fromBlocks Ak 0 0 0 := hAk.symm
      rw [h1, h2]
      ext x y; cases x <;> cases y <;> simp
    rw [← hphi]
    dsimp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_subset (Finset.subset_univ R)]
    intro r _ hnot; simp [hclear0 r hnot]
  have hbasis_ex : ∃ (Ak : Fin q → T) (v : NL1 → V),
      ∀ k : Fin q, Matrix.fromBlocks (Ak k) (K (Pi.single k 1)) (K (Pi.single k 1)).transpose 0 =
        ∑ r ∈ R, v r k • D r.1 :=
    ⟨fun k => (hbasis_rep k).choose, fun r k => (hbasis_rep k).choose_spec.choose r,
      fun k => (hbasis_rep k).choose_spec.choose_spec.2⟩
  obtain ⟨Ak, v, hv_basis⟩ := hbasis_ex
  have hK_add : ∀ z₁ z₂ : V, K (z₁ + z₂) = K z₁ + K z₂ := fun z₁ z₂ => by
    ext ⟨i, r⟩ ⟨i', c'⟩
    by_cases hi : i = i'
    · subst hi
      simp only [K, Matrix.add_apply, Matrix.blockDiagonal'_apply_eq]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [vdot_add_right, vdot_add_right]; ring
    · simp only [K, Matrix.add_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hi, add_zero]
  have hK_smul : ∀ (α : F2) (z : V), K (α • z) = α • K z := fun α z => by
    rcases f2_cases α with rfl | rfl
    · simp [hK0]
    · simp
  have hK_sum : ∀ (S0 : Finset (Fin q)) (f : Fin q → V), K (∑ k ∈ S0, f k) = ∑ k ∈ S0, K (f k) := by
    intro S0 f
    induction S0 using Finset.induction_on with
    | empty => simp [hK0]
    | insert k S0 hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, hK_add, ih]
  have hlin_z : ∀ z : V,
      Matrix.fromBlocks (∑ k : Fin q, z k • Ak k) (K z) (K z).transpose 0 =
        ∑ r ∈ R, vdot (v r) z • D r.1 := by
    intro z
    have hz_eq : z = ∑ k : Fin q, z k • Pi.single k (1 : F2) := by
      ext k; simp [Pi.single_apply]
    have hK_decomp : K z = ∑ k : Fin q, z k • K (Pi.single k 1) := by
      conv_lhs => rw [hz_eq, hK_sum]
      exact Finset.sum_congr rfl fun k _ => hK_smul (z k) _
    have hblocks : Matrix.fromBlocks (∑ k : Fin q, z k • Ak k) (K z) (K z).transpose 0 =
        ∑ k : Fin q, z k • Matrix.fromBlocks (Ak k) (K (Pi.single k 1)) (K (Pi.single k 1)).transpose 0 := by
      rw [hK_decomp, Matrix.transpose_sum]
      ext x y
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      cases x <;> cases y <;> simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        mul_zero, Finset.sum_const_zero]
      · exact Finset.sum_congr rfl fun k _ => rfl
    rw [hblocks]
    calc ∑ k : Fin q, z k • Matrix.fromBlocks (Ak k) (K (Pi.single k 1)) (K (Pi.single k 1)).transpose 0
        = ∑ k : Fin q, z k • ∑ r ∈ R, v r k • D r.1 := Finset.sum_congr rfl fun k _ => by rw [hv_basis k]
      _ = ∑ k : Fin q, ∑ r ∈ R, (v r k * z k) • D r.1 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun r _ => by rw [smul_smul, mul_comm]
      _ = ∑ r ∈ R, ∑ k : Fin q, (v r k * z k) • D r.1 := Finset.sum_comm
      _ = ∑ r ∈ R, vdot (v r) z • D r.1 := Finset.sum_congr rfl fun r _ => by rw [← Finset.sum_smul]; rfl
  -- Step 4: Pointwise bound (K z).rank <= |{r in R' | vdot (v r) z = 1}|
  let R' : Finset NL1 := R.filter (fun r => v r ≠ 0)
  have hR'_le : R'.card ≤ t - free := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hR_le
  have hKz_le : ∀ z : V, (K z).rank ≤ (R'.filter (fun r => vdot (v r) z = 1)).card := by
    intro z
    have h1 := rank_fromBlocks_ge_two_mul (∑ k : Fin q, z k • Ak k) (K z)
    rw [hlin_z z] at h1
    have hsum_eq : ∑ r ∈ R, vdot (v r) z • D r.1 =
        ∑ r ∈ R'.filter (fun r => vdot (v r) z = 1), D r.1 := by
      have hsub : R'.filter (fun r => vdot (v r) z = 1) ⊆ R :=
        Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun r hr => ?_
        rw [(Finset.mem_filter.mp hr).2, one_smul]
      · intro r hr hnot
        have h0 : vdot (v r) z = 0 := by
          rcases f2_cases (vdot (v r) z) with h0 | h1
          · exact h0
          · exfalso
            have hvne : v r ≠ 0 := by intro hv0; rw [hv0, vdot_zero_left] at h1; exact absurd h1 (by decide)
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, hvne⟩, h1⟩)
        simp [h0]
    rw [hsum_eq] at h1
    have h2 : (∑ r ∈ R'.filter (fun r => vdot (v r) z = 1), D r.1).rank ≤
        ∑ r ∈ R'.filter (fun r => vdot (v r) z = 1), (D r.1).rank := rank_sum_le _ _
    have h3 : ∑ r ∈ R'.filter (fun r => vdot (v r) z = 1), (D r.1).rank ≤
        2 * (R'.filter (fun r => vdot (v r) z = 1)).card := by
      calc _ ≤ ∑ _r ∈ R'.filter (fun r => vdot (v r) z = 1), 2 := Finset.sum_le_sum fun r _ => hDrk r.1
        _ = 2 * (R'.filter (fun r => vdot (v r) z = 1)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  -- Step 5: Exact Walsh-Hadamard expansion of Delta(z) = |(R'.filter ...)| - (K z).rank >= 0!
  let c : V → ℕ := fun u => (R'.filter (fun r => v r = u)).card
  have hc0 : c 0 = 0 := by
    simp only [c, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r hr; exact (Finset.mem_filter.mp hr).2
  have hm0 : m 0 = 0 := by
    dsimp only [m]
    refine Finset.sum_eq_zero fun H hH => ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    have h0not : (0 : V) ∉ line i := by
      simp only [line, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨(hab i).1.symm, (hab i).2.1.symm, fun h => (hab i).2.2 (funext fun k => ?_)⟩
      exact f2_eq_of_add_eq_zero (congrFun h.symm k)
    simp [h0not]
  have hm_eq_sum : ∀ u : V, m u = ∑ i : Fin l, if u ∈ line i then s i else 0 := by
    intro u
    dsimp only [m, mass]
    have h1 : ∀ H ∈ lines, (if u ∈ H then ∑ i : Fin l, if line i = H then s i else 0 else 0) =
        ∑ i : Fin l, if line i = H then (if u ∈ line i then s i else 0) else 0 := by
      intro H _
      by_cases hu : u ∈ H
      · rw [if_pos hu]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hli : line i = H
        · rw [if_pos hli, if_pos hli, hli, if_pos hu]
        · rw [if_neg hli, if_neg hli]
      · rw [if_neg hu]
        symm; refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hli : line i = H
        · rw [if_pos hli, hli, if_neg hu]
        · rw [if_neg hli]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmem : line i ∈ lines := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [Finset.sum_eq_single (line i) (fun H _ hne => if_neg (Ne.symm hne)) (fun h => absurd hmem h), if_pos rfl]
  have hKz_rk : ∀ z : V, (K z).rank =
      ∑ i : Fin l, if vdot (a i) z ≠ 0 ∨ vdot (b i) z ≠ 0 then s i else 0 := by
    intro z
    dsimp only [K]
    rw [rank_blockDiagonal']
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases f2_cases (vdot (a i) z) with ha0 | ha1 <;> rcases f2_cases (vdot (b i) z) with hb0 | hb1
    · simp [ha0, hb0]
    · simp [ha0, hb1, (hUW i).2.1]
    · simp [ha1, hb0, (hUW i).1]
    · simp [ha1, hb1, (hUW i).2.2]
  let Δ : V → ℤ := fun z => ((R'.filter (fun r => vdot (v r) z = 1)).card : ℤ) - ((K z).rank : ℤ)
  have hΔ_nonneg : ∀ z : V, 0 ≤ Δ z := fun z => by
    dsimp only [Δ]; have := hKz_le z; omega
  have h4K : ∀ z : V, (4 : ℤ) * ((K z).rank : ℤ) =
      3 * (N : ℤ) - ∑ u : V, (m u : ℤ) * chiZ (vdot u z) := by
    intro z
    rw [hKz_rk z]
    push_cast
    rw [Finset.mul_sum]
    have hstep1 : ∑ i : Fin l, (4 : ℤ) * (if vdot (a i) z ≠ 0 ∨ vdot (b i) z ≠ 0 then (s i : ℤ) else 0) =
        ∑ i : Fin l, (3 * (s i : ℤ) - (s i : ℤ) * (chiZ (vdot (a i) z) + chiZ (vdot (b i) z) + chiZ (vdot (a i + b i) z))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 := congrArg ((s i : ℤ) * ·) (four_mul_or_nonzero_chiZ (a i) (b i) z)
      by_cases h : vdot (a i) z ≠ 0 ∨ vdot (b i) z ≠ 0
      · rw [if_pos h] at h4 ⊢; linarith
      · rw [if_neg h] at h4 ⊢; linarith
    rw [hstep1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hNcast : (∑ i : Fin l, (s i : ℤ)) = (N : ℤ) := by dsimp only [N]; push_cast; rfl
    rw [hNcast]
    congr 1
    have hline_sum : ∀ i : Fin l,
        (s i : ℤ) * (chiZ (vdot (a i) z) + chiZ (vdot (b i) z) + chiZ (vdot (a i + b i) z)) =
        ∑ u : V, (if u ∈ line i then (s i : ℤ) else 0) * chiZ (vdot u z) := by
      intro i
      rw [← Finset.sum_subset (Finset.subset_univ (line i))]
      · have hne1 : a i ≠ b i := (hab i).2.2
        have hne2 : a i ≠ a i + b i := fun h => (hab i).2.1 (funext fun k => by
          have hk := congrFun h k; simp only [Pi.add_apply, Pi.zero_apply] at hk ⊢; linear_combination -hk)
        have hne3 : b i ≠ a i + b i := fun h => (hab i).1 (funext fun k => by
          have hk := congrFun h k; simp only [Pi.add_apply, Pi.zero_apply] at hk ⊢; linear_combination -hk)
        simp only [line]
        rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
          Finset.sum_singleton]
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, ↓reduceIte]
        ring
      · intro u _ hu; simp [hu]
    simp_rw [hline_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, hm_eq_sum u]
    push_cast
    rfl
  have h4R : ∀ z : V, (4 : ℤ) * ((R'.filter (fun r => vdot (v r) z = 1)).card : ℤ) =
      2 * (R'.card : ℤ) - ∑ u : V, 2 * (c u : ℤ) * chiZ (vdot u z) := by
    intro z
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    have hstep : ∑ r ∈ R', (4 : ℤ) * (if vdot (v r) z = 1 then 1 else 0) =
        ∑ r ∈ R', (2 - 2 * chiZ (vdot (v r) z)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have h2 := two_mul_eq_one_chiZ (v r) z
      linarith
    rw [hstep, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm (R'.card : ℤ) 2]
    congr 1
    have hfib : ∑ r ∈ R', (2 : ℤ) * chiZ (vdot (v r) z) =
        ∑ u : V, ∑ r ∈ R'.filter (fun r => v r = u), (2 : ℤ) * chiZ (vdot (v r) z) := by
      exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    rw [hfib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have heq : ∑ r ∈ R'.filter (fun r => v r = u), (2 : ℤ) * chiZ (vdot (v r) z) =
        ∑ _r ∈ R'.filter (fun r => v r = u), (2 : ℤ) * chiZ (vdot u z) :=
      Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.mp hr).2]
    rw [heq, Finset.sum_const, nsmul_eq_mul]
    dsimp only [c]; ring
  have h4Δ : ∀ z : V, 4 * Δ z =
      (2 * (R'.card : ℤ) - 3 * (N : ℤ)) + ∑ u : V, ((m u : ℤ) - 2 * (c u : ℤ)) * chiZ (vdot u z) := by
    intro z
    have h1 := h4R z; have h2 := h4K z
    have hdiff : ∑ u : V, ((m u : ℤ) - 2 * (c u : ℤ)) * chiZ (vdot u z) =
        (∑ u : V, (m u : ℤ) * chiZ (vdot u z)) - (∑ u : V, 2 * (c u : ℤ) * chiZ (vdot u z)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => by ring
    dsimp only [Δ]; linarith
  -- Sum 4 * Δ z over all z : V
  have hsum_Δ : 4 * ∑ z : V, Δ z = (Fintype.card V : ℤ) * (2 * (R'.card : ℤ) - 3 * (N : ℤ)) := by
    rw [Finset.mul_sum]
    simp_rw [h4Δ]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hzero : ∑ z : V, ∑ u : V, ((m u : ℤ) - 2 * (c u : ℤ)) * chiZ (vdot u z) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [← Finset.mul_sum, sum_chiZ_vdot]
      by_cases hu : u = 0
      · subst hu; simp [hm0, hc0]
      · simp [hu]
    rw [hzero, add_zero]
  have hcardV_pos : (0 : ℤ) < (Fintype.card V : ℤ) := Int.natCast_pos.mpr Fintype.card_pos
  have hsum_Δ_nonneg : 0 ≤ ∑ z : V, Δ z := Finset.sum_nonneg fun z _ => hΔ_nonneg z
  have h3N_le_R' : 3 * N ≤ 2 * R'.card := by
    have hge0 : (0 : ℤ) ≤ (Fintype.card V : ℤ) * (2 * (R'.card : ℤ) - 3 * (N : ℤ)) := by linarith
    have hge : (0 : ℤ) ≤ 2 * (R'.card : ℤ) - 3 * (N : ℤ) := nonneg_of_mul_nonneg_right hge0 hcardV_pos
    omega
  have h3N_le : 3 * N ≤ 2 * (t - free) := by omega
  -- Walsh coefficient of Δ at any w ≠ 0
  have hwalsh : ∀ w0 : V, w0 ≠ 0 →
      4 * ∑ z : V, Δ z * chiZ (vdot w0 z) = (Fintype.card V : ℤ) * ((m w0 : ℤ) - 2 * (c w0 : ℤ)) := by
    intro w0 hw0
    have h1 : 4 * ∑ z : V, Δ z * chiZ (vdot w0 z) = ∑ z : V, (4 * Δ z) * chiZ (vdot w0 z) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
    rw [h1]
    simp_rw [h4Δ, add_mul, Finset.sum_add_distrib]
    have hpart1 : ∑ z : V, (2 * (R'.card : ℤ) - 3 * (N : ℤ)) * chiZ (vdot w0 z) = 0 := by
      rw [← Finset.mul_sum, sum_chiZ_vdot, if_neg hw0, mul_zero]
    rw [hpart1, zero_add]
    have hpart2 : ∑ z : V, (∑ u : V, ((m u : ℤ) - 2 * (c u : ℤ)) * chiZ (vdot u z)) * chiZ (vdot w0 z) =
        ∑ u : V, ((m u : ℤ) - 2 * (c u : ℤ)) * ∑ z : V, chiZ (vdot (u + w0) z) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => by rw [mul_assoc, ← chiZ_add, ← vdot_add_left]
    rw [hpart2]
    have heq_single : ∀ u : V, u ≠ w0 →
        ((m u : ℤ) - 2 * (c u : ℤ)) * ∑ z : V, chiZ (vdot (u + w0) z) = 0 := by
      intro u hu
      have hne0 : u + w0 ≠ 0 := fun h => hu (funext fun k => f2_eq_of_add_eq_zero (congrFun h k))
      rw [sum_chiZ_vdot, if_neg hne0, mul_zero]
    rw [Finset.sum_eq_single w0 (fun u _ hu => heq_single u hu) (fun h => absurd (Finset.mem_univ w0) h)]
    have hww : w0 + w0 = 0 := funext fun k => f2_add_self (w0 k)
    rw [hww, sum_chiZ_vdot, if_pos rfl, mul_comm]
  -- Helper: if 2 * R'.card = 3 * N then odd = empty
  have hodd_empty_of_eq : 2 * R'.card = 3 * N → odd = ∅ := by
    intro heq
    have hsum0 : ∑ z : V, Δ z = 0 := by
      have : 2 * (R'.card : ℤ) - 3 * (N : ℤ) = 0 := by omega
      rw [this, mul_zero] at hsum_Δ; omega
    have hΔ0 : ∀ z : V, Δ z = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun z' _ => hΔ_nonneg z')).mp hsum0 z (Finset.mem_univ z)
    rw [Finset.filter_eq_empty_iff]
    intro u _
    by_cases hu : u = 0
    · subst hu; simp [hm0]
    · have hw := hwalsh u hu
      have h0 : ∑ z : V, Δ z * chiZ (vdot u z) = 0 :=
        Finset.sum_eq_zero fun z _ => by rw [hΔ0 z, zero_mul]
      rw [h0, mul_zero] at hw
      have hdiff0 : (m u : ℤ) - 2 * (c u : ℤ) = 0 := by
        rcases mul_eq_zero.mp hw.symm with hV | hd
        · omega
        · exact hd
      omega
  refine ⟨hfree_le_t, h3N_le, fun heq => hodd_empty_of_eq (by omega), ?_⟩
  intro heq1
  have hcases : 2 * R'.card = 3 * N ∨ 2 * R'.card = 3 * N + 1 := by omega
  rcases hcases with h0 | h1
  · refine ⟨⊥, fun u => ?_⟩
    rw [hodd_empty_of_eq h0]
    simp
  · -- 2 * R'.card = 3 * N + 1 -> 4 * sum_z Delta z = |V|!
    have hsum_val : 4 * ∑ z : V, Δ z = (Fintype.card V : ℤ) := by
      have : 2 * (R'.card : ℤ) - 3 * (N : ℤ) = 1 := by omega
      rw [this, mul_one] at hsum_Δ; exact hsum_Δ
    let SΔ : Finset V := Finset.univ.filter (fun z : V => 0 < Δ z)
    have hSΔ_ne : SΔ.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hΔ0 : ∀ z : V, Δ z = 0 := fun z => by
        have hnot : ¬ (0 < Δ z) := fun hp => by
          have hm : z ∈ SΔ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
          rw [hempty] at hm; simp at hm
        have := hΔ_nonneg z; omega
      have h0 : ∑ z : V, Δ z = 0 := Finset.sum_eq_zero fun z _ => hΔ0 z
      omega
    obtain ⟨z0, hz0⟩ := hSΔ_ne
    let H : Submodule F2 V :=
      { carrier := { u : V | ∀ z ∈ SΔ, vdot u z = vdot u z0 }
        zero_mem' := fun z _ => by simp [vdot_zero_left], add_mem' := fun {u₁ u₂} h₁ h₂ z hz => by
          simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
          rw [vdot_add_left, vdot_add_left, h₁ z hz, h₂ z hz]
        smul_mem' := fun α {u} hu z hz => by
          simp only [Set.mem_setOf_eq] at hu ⊢
          rcases f2_cases α with rfl | rfl
          · simp [vdot_zero_left]
          · simpa using hu z hz }
    refine ⟨H, fun u => ?_⟩
    by_cases hu0 : u = 0
    · subst hu0
      simp only [odd, Finset.mem_filter, Finset.mem_univ, true_and, hm0, ne_eq, not_true_eq_false, false_and]
      decide
    · have hw := hwalsh u hu0
      have hchi_le : ∀ z : V, -Δ z ≤ Δ z * chiZ (vdot u z) ∧ Δ z * chiZ (vdot u z) ≤ Δ z := fun z => by
        have hd := hΔ_nonneg z
        rcases f2_cases (vdot u z) with h | h <;> simp [h, chiZ] <;> omega
      have hsum_ub : ∑ z : V, Δ z * chiZ (vdot u z) ≤ ∑ z : V, Δ z :=
        Finset.sum_le_sum fun z _ => (hchi_le z).2
      have hsum_lb : -(∑ z : V, Δ z) ≤ ∑ z : V, Δ z * chiZ (vdot u z) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun z _ => (hchi_le z).1
      have hdiff_bd : -1 ≤ (m u : ℤ) - 2 * (c u : ℤ) ∧ (m u : ℤ) - 2 * (c u : ℤ) ≤ 1 := by
        have hlo : (0 : ℤ) ≤ (Fintype.card V : ℤ) * (((m u : ℤ) - 2 * (c u : ℤ)) + 1) := by linarith
        have hhi : (0 : ℤ) ≤ (Fintype.card V : ℤ) * (1 - ((m u : ℤ) - 2 * (c u : ℤ))) := by linarith
        have h1 := nonneg_of_mul_nonneg_right hlo hcardV_pos
        have h2 := nonneg_of_mul_nonneg_right hhi hcardV_pos
        omega
      simp only [odd, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, hu0, not_false_eq_true, true_and]
      constructor
      · intro hmod
        have hpm : (m u : ℤ) - 2 * (c u : ℤ) = 1 ∨ (m u : ℤ) - 2 * (c u : ℤ) = -1 := by omega
        change ∀ z ∈ SΔ, vdot u z = vdot u z0
        rcases hpm with hp | hm
        · rw [hp, mul_one, ← hsum_val] at hw
          have hsum_eq : ∑ z : V, Δ z * (1 - chiZ (vdot u z)) = 0 := by
            have : ∑ z : V, Δ z * (1 - chiZ (vdot u z)) = (∑ z : V, Δ z) - ∑ z : V, Δ z * chiZ (vdot u z) := by
              rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun z _ => by ring
            rw [this]; omega
          have hnn : ∀ z ∈ (Finset.univ : Finset V), 0 ≤ Δ z * (1 - chiZ (vdot u z)) := fun z _ => by
            have hd := hΔ_nonneg z
            rcases f2_cases (vdot u z) with h | h <;> simp [h, chiZ] <;> omega
          have hall0 : ∀ z ∈ SΔ, vdot u z = 0 := fun z hz => by
            have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_eq z (Finset.mem_univ z)
            have hpos : 0 < Δ z := (Finset.mem_filter.mp hz).2
            rcases f2_cases (vdot u z) with h | h
            · exact h
            · simp [h, chiZ] at hterm0; omega
          intro z hz; rw [hall0 z hz, hall0 z0 hz0]
        · rw [hm, mul_neg_one, ← hsum_val] at hw
          have hsum_eq : ∑ z : V, Δ z * (1 + chiZ (vdot u z)) = 0 := by
            have : ∑ z : V, Δ z * (1 + chiZ (vdot u z)) = (∑ z : V, Δ z) + ∑ z : V, Δ z * chiZ (vdot u z) := by
              rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun z _ => by ring
            rw [this]; omega
          have hnn : ∀ z ∈ (Finset.univ : Finset V), 0 ≤ Δ z * (1 + chiZ (vdot u z)) := fun z _ => by
            have hd := hΔ_nonneg z
            rcases f2_cases (vdot u z) with h | h <;> simp [h, chiZ] <;> omega
          have hall1 : ∀ z ∈ SΔ, vdot u z = 1 := fun z hz => by
            have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_eq z (Finset.mem_univ z)
            have hpos : 0 < Δ z := (Finset.mem_filter.mp hz).2
            rcases f2_cases (vdot u z) with h | h
            · simp [h, chiZ] at hterm0; omega
            · exact h
          intro z hz; rw [hall1 z hz, hall1 z0 hz0]
      · intro huH
        have hconst : ∀ z : V, Δ z * chiZ (vdot u z) = Δ z * chiZ (vdot u z0) := fun z => by
          by_cases hz : 0 < Δ z
          · rw [huH z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)]
          · have h0 : Δ z = 0 := by have := hΔ_nonneg z; omega
            simp [h0]
        have hsum_eq : ∑ z : V, Δ z * chiZ (vdot u z) = (∑ z : V, Δ z) * chiZ (vdot u z0) := by
          simp_rw [hconst, ← Finset.sum_mul]
        rw [hsum_eq] at hw
        rcases f2_cases (vdot u z0) with h | h
        · simp only [h, chiZ_zero, mul_one] at hw
          rw [hsum_val] at hw
          have hmul : (Fintype.card V : ℤ) * ((m u : ℤ) - 2 * (c u : ℤ) - 1) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with hV | hd
          · omega
          · omega
        · simp only [h, chiZ, show (1 : F2) ≠ 0 by decide, ↓reduceIte, mul_neg_one] at hw
          have : 4 * -(∑ z : V, Δ z) = -(4 * ∑ z : V, Δ z) := by ring
          rw [this, hsum_val] at hw
          have hmul : (Fintype.card V : ℤ) * ((m u : ℤ) - 2 * (c u : ℤ) + 1) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with hV | hd
          · omega
          · omega

-- ============================================================
-- Direction 2: Explicit circuit construction attaining free + (3*N + D.card + left.card)/2
-- ============================================================

lemma exists_basis_of_span_subset {E : Type} [AddCommGroup E] [Module F2 E] [Finite E]
    (S : Submodule F2 E) (P : E → Prop)
    (hS : S = Submodule.span F2 {x : E | x ∈ S ∧ P x}) :
    ∃ (B : Fin (Module.finrank F2 S) → E) (coeffS : E → Fin (Module.finrank F2 S) → F2),
      (∀ k, P (B k)) ∧ (∀ A ∈ S, A = ∑ k, coeffS A k • B k) := by
  classical
  let gens : Set E := {x : E | x ∈ S ∧ P x}
  obtain ⟨Bset, hBsub, hBspan, hBlin⟩ := exists_linearIndependent F2 gens
  have hBfin : Bset.Finite := Set.toFinite Bset
  letI : Fintype Bset := hBfin.fintype
  have hspan_eq : Submodule.span F2 Bset = S := by rw [hBspan, ← hS]
  let B0 : Bset → S := fun x => ⟨x.1, (hBsub x.2).1⟩
  have hB0_lin : LinearIndependent F2 B0 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hval := congrArg Subtype.val hc
    rw [Submodule.coe_sum] at hval
    exact Fintype.linearIndependent_iff.mp hBlin c (by simpa [B0] using hval)
  have hB0_span : ⊤ ≤ Submodule.span F2 (Set.range B0) := by
    intro x _
    have hx : x.1 ∈ Submodule.span F2 Bset := hspan_eq.symm ▸ x.2
    rw [Finsupp.mem_span_iff_linearCombination] at hx
    obtain ⟨l, hl⟩ := hx
    have hsum : x = ∑ y ∈ l.support, l y • B0 y := by
      apply Subtype.ext
      rw [Submodule.coe_sum, ← hl, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun y _ => rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  let b0 : Module.Basis Bset F2 S := Module.Basis.mk hB0_lin hB0_span
  have hcard_B : Fintype.card Bset = Module.finrank F2 S := (Module.finrank_eq_card_basis b0).symm
  let eqB : Fin (Module.finrank F2 S) ≃ Bset :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard_B])
  let bS : Module.Basis (Fin (Module.finrank F2 S)) F2 S := b0.reindex eqB.symm
  refine ⟨fun k => (eqB k).1, fun A k => if h : A ∈ S then bS.repr ⟨A, h⟩ k else 0,
    fun k => (hBsub (eqB k).2).2, fun A hA => ?_⟩
  have hrep := bS.sum_repr ⟨A, hA⟩
  have hval := congrArg Subtype.val hrep
  dsimp only at hval
  rw [Submodule.coe_sum] at hval
  conv_lhs => rw [← hval]
  have hbS_val : ∀ k : Fin (Module.finrank F2 S), (bS k).1 = (eqB k).1 := fun k => by
    simp [bS, b0, B0]
  refine Finset.sum_congr rfl fun k _ => by
    simp only [dif_pos hA, SetLike.val_smul, hbS_val]

lemma upper_bound_dir (q l : ℕ) (s : Fin l → ℕ)
    (a b : Fin l → (Fin q → F2)) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (U W : (i : Fin l) → Matrix (Fin (s i)) (Fin (s i)) F2)
    (hUW : ∀ i, (U i).rank = s i ∧ (W i).rank = s i ∧ (U i + W i).rank = s i)
    (S : Submodule F2 (Matrix (Σ i : Fin l, Fin (s i)) (Σ i : Fin l, Fin (s i)) F2))
    (hS : S = Submodule.span F2 {A : Matrix (Σ i : Fin l, Fin (s i)) (Σ i : Fin l, Fin (s i)) F2 | A ∈ S ∧ A.rank ≤ 2})
    (D : Finset (Finset (Fin q → F2))) :
    let V := Fin q → F2
    let I := Σ i : Fin l, Fin (s i)
    let T := Matrix I I F2
    let line := fun i : Fin l => ({a i, b i, a i + b i} : Finset V)
    let lines := Finset.univ.image line
    let mass := fun H : Finset V => ∑ i, if line i = H then s i else 0
    let N := ∑ i, s i
    let free := Module.finrank F2 S
    let K := fun z : V =>
      Matrix.blockDiagonal' (fun i => vdot (a i) z • U i + vdot (b i) z • W i)
    let w := Fintype.card (I ⊕ I)
    let coord := Fintype.equivFin (I ⊕ I)
    let table := fun (A : T) (z : V) (x y : Fin (w + 1)) =>
      let X := Matrix.fromBlocks A (K z) (K z).transpose (0 : T)
      Fin.cases false (fun i => Fin.cases false (fun j =>
        decide (X (coord.symm i) (coord.symm j) ≠ 0)) y) x
    let m := fun u : V => ∑ H ∈ lines, if u ∈ H then mass H else 0
    D ⊆ lines → (∀ H ∈ D, 0 < mass H) →
    let left := Finset.univ.filter (fun u : V =>
      (m u + (D.filter (fun H => u ∈ H)).card) % 2 = 1)
    ∃ (C : Circuit) (tap : T → V → ℕ),
      ReadsBack ((w + 1) + (w + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nlGate ≤ free + (3 * N + D.card + left.card) / 2 ∧
      ∀ A ∈ S, ∀ z : V,
        (depthsOf ((w + 1) + (w + 1)) C.gates).getD (tap A z) 0 ≤ 1 ∧
        Represents (table A z) ⟨C.gates, tap A z⟩ := by
  intro V I T line lines mass N free K w coord table m hD_sub hD_pos left
  let width := (w + 1) + (w + 1)
  -- Step 1: Basis of S of size `free` consisting of rank <= 2 matrices!
  obtain ⟨BS, coeffS, hBS_rk, hBS_rep⟩ := exists_basis_of_span_subset S (fun A => A.rank ≤ 2) hS
  -- Decompose each BS k into 2 rank-1 pieces embedded in top-left of Fin (w + 1)
  have hBS_dec : ∀ k : Fin free, ∃ (p1 p2 q1 q2 : Fin (w + 1) → F2),
      ∀ r0 c0 : Fin (w + 1),
        p1 r0 * q1 c0 + p2 r0 * q2 c0 =
          Fin.cases 0 (fun idx1 => Fin.cases 0 (fun idx2 =>
            (Matrix.fromBlocks (BS k) 0 0 0) (coord.symm idx1) (coord.symm idx2)) c0) r0 := by
    intro k
    obtain ⟨u1, u2, v1, v2, hdec⟩ := rank_le_two_decomp (BS k) (hBS_rk k)
    let liftL : (I → F2) → (Fin (w + 1) → F2) := fun f =>
      Fin.cases 0 (fun idx => Sum.elim f 0 (coord.symm idx))
    refine ⟨liftL u1, liftL u2, liftL v1, liftL v2, fun r0 c0 => ?_⟩
    refine Fin.cases (by simp [liftL]) (fun idx1 => ?_) r0
    refine Fin.cases (by simp [liftL]) (fun idx2 => ?_) c0
    simp only [liftL, Fin.cases_succ]
    cases coord.symm idx1 <;> cases coord.symm idx2 <;> simp [hdec]
  have hBS_pieces_ex : ∃ (sP : Fin free → (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2)),
      ∀ k r0 c0, (sP k).1 r0 * (sP k).2.2.1 c0 + (sP k).2.1 r0 * (sP k).2.2.2 c0 =
        Fin.cases 0 (fun idx1 => Fin.cases 0 (fun idx2 =>
          (Matrix.fromBlocks (BS k) 0 0 0) (coord.symm idx1) (coord.symm idx2)) c0) r0 :=
    ⟨fun k => ((hBS_dec k).choose, (hBS_dec k).choose_spec.choose,
      (hBS_dec k).choose_spec.choose_spec.choose,
      (hBS_dec k).choose_spec.choose_spec.choose_spec.choose),
      fun k => (hBS_dec k).choose_spec.choose_spec.choose_spec.choose_spec⟩
  obtain ⟨sP, hsP_eq⟩ := hBS_pieces_ex
  -- Step 2: For each block i : Fin l, split doubled invertible pair ([[0, U i], [U i^T, 0]], [[0, W i], [W i^T, 0]])
  -- into s i rank-1 pieces for each of a i, b i, a i + b i!
  have hblk_dec : ∀ i : Fin l, ∃ (pA qA pB qB pC qC : Fin (s i) → Fin (w + 1) → F2),
      ∀ (z : V) (r0 c0 : Fin (w + 1)),
        (∑ m0 : Fin (s i),
          (vdot (a i) z * (pA m0 r0 * qA m0 c0) +
           vdot (b i) z * (pB m0 r0 * qB m0 c0) +
           vdot (a i + b i) z * (pC m0 r0 * qC m0 c0))) =
        Fin.cases 0 (fun idx1 => Fin.cases 0 (fun idx2 =>
          match coord.symm idx1, coord.symm idx2 with
          | Sum.inl ⟨i1, r1⟩, Sum.inr ⟨i2, c2⟩ =>
            if h1 : i1 = i then if h2 : i2 = i then
              (vdot (a i) z • U i + vdot (b i) z • W i) (h1 ▸ r1) (h2 ▸ c2) else 0 else 0
          | Sum.inr ⟨i1, r1⟩, Sum.inl ⟨i2, c2⟩ =>
            if h1 : i1 = i then if h2 : i2 = i then
              (vdot (a i) z • U i + vdot (b i) z • W i).transpose (h1 ▸ r1) (h2 ▸ c2) else 0 else 0
          | _, _ => 0) c0) r0 := by
    intro i
    let e2 : Fin (s i) ⊕ Fin (s i) ≃ Fin (2 * s i) :=
      (finSumFinEquiv.trans (finCongr (by omega : s i + s i = 2 * s i)))
    let Ui2 : Matrix (Fin (2 * s i)) (Fin (2 * s i)) F2 :=
      Matrix.of fun r c => (Matrix.fromBlocks (0 : Matrix (Fin (s i)) (Fin (s i)) F2) (U i) (U i).transpose 0) (e2.symm r) (e2.symm c)
    let Wi2 : Matrix (Fin (2 * s i)) (Fin (2 * s i)) F2 :=
      Matrix.of fun r c => (Matrix.fromBlocks (0 : Matrix (Fin (s i)) (Fin (s i)) F2) (W i) (W i).transpose 0) (e2.symm r) (e2.symm c)
    have hreidx_rk : ∀ M : Matrix (Fin (s i) ⊕ Fin (s i)) (Fin (s i) ⊕ Fin (s i)) F2,
        (Matrix.of fun r c : Fin (2 * s i) => M (e2.symm r) (e2.symm c)).rank = M.rank := by
      intro M
      let M' : Matrix (Fin (2 * s i)) (Fin (2 * s i)) F2 := Matrix.of fun r c => M (e2.symm r) (e2.symm c)
      let eV : (Fin (s i) ⊕ Fin (s i) → F2) ≃ₗ[F2] (Fin (2 * s i) → F2) :=
        { toFun := fun v r => v (e2.symm r)
          invFun := fun v x => v (e2 x)
          left_inv := fun v => by ext x; simp
          right_inv := fun v => by ext r; simp
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hcomm : ∀ v, M'.mulVecLin (eV v) = eV (M.mulVecLin v) := fun v => by
        ext r
        simp only [M', eV, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
          Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
        rw [← Equiv.sum_comp e2.symm]
      have hmap : (LinearMap.range M.mulVecLin).map eV.toLinearMap = LinearMap.range M'.mulVecLin := by
        ext y; simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨eV v, hcomm v⟩
        · rintro ⟨v, rfl⟩; exact ⟨M.mulVecLin (eV.symm v), ⟨eV.symm v, rfl⟩, by rw [← hcomm, eV.apply_symm_apply]⟩
      change Module.finrank F2 (LinearMap.range M'.mulVecLin) = _
      rw [← hmap]
      exact (Submodule.equivMapOfInjective eV.toLinearMap eV.injective _).finrank_eq.symm
    have hU2_rk : Ui2.rank = 2 * s i := by
      rw [hreidx_rk]; exact rank_fromBlocks_offdiag_full (U i) (hUW i).1
    have hW2_rk : Wi2.rank = 2 * s i := by
      rw [hreidx_rk]; exact rank_fromBlocks_offdiag_full (W i) (hUW i).2.1
    have hUW2_rk : (Ui2 + Wi2).rank = 2 * s i := by
      have heq : Ui2 + Wi2 = Matrix.of fun r c =>
          (Matrix.fromBlocks (0 : Matrix (Fin (s i)) (Fin (s i)) F2) (U i + W i) (U i + W i).transpose 0) (e2.symm r) (e2.symm c) := by
        ext r c
        simp only [Ui2, Wi2, Matrix.add_apply, Matrix.of_apply]
        cases e2.symm r <;> cases e2.symm c <;> simp
      rw [heq, hreidx_rk]
      exact rank_fromBlocks_offdiag_full (U i + W i) (hUW i).2.2
    obtain ⟨pA0, qA0, pB0, qB0, pC0, qC0, hU0, hW0⟩ := split_invertible_pair Ui2 Wi2 hU2_rk hW2_rk hUW2_rk
    let liftBlk : (Fin (2 * s i) → F2) → (Fin (w + 1) → F2) := fun f =>
      Fin.cases 0 (fun idx =>
        match coord.symm idx with
        | Sum.inl ⟨i', r'⟩ => if h : i' = i then f (e2 (Sum.inl (h ▸ r'))) else 0
        | Sum.inr ⟨i', r'⟩ => if h : i' = i then f (e2 (Sum.inr (h ▸ r'))) else 0)
    refine ⟨fun m0 => liftBlk (pA0 m0), fun m0 => liftBlk (qA0 m0),
      fun m0 => liftBlk (pB0 m0), fun m0 => liftBlk (qB0 m0),
      fun m0 => liftBlk (pC0 m0), fun m0 => liftBlk (qC0 m0), ?_⟩
    intro z r0 c0
    refine Fin.cases (by simp [liftBlk]) (fun idx1 => ?_) r0
    refine Fin.cases (by simp [liftBlk]) (fun idx2 => ?_) c0
    have hsum_val : ∀ (a0 b0 : Fin (2 * s i)),
        (∑ m0 : Fin (s i),
          (vdot (a i) z * (pA0 m0 a0 * qA0 m0 b0) +
           vdot (b i) z * (pB0 m0 a0 * qB0 m0 b0) +
           vdot (a i + b i) z * (pC0 m0 a0 * qC0 m0 b0))) =
        vdot (a i) z * Ui2 a0 b0 + vdot (b i) z * Wi2 a0 b0 := fun a0 b0 => by
      rw [hU0 a0 b0, hW0 a0 b0, vdot_add_left, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m0 _ => by ring
    simp only [liftBlk, Fin.cases_succ]
    cases h1 : coord.symm idx1 with
    | inl x1 =>
      rcases x1 with ⟨i1, r1⟩
      cases h2 : coord.symm idx2 with
      | inl x2 =>
        rcases x2 with ⟨i2, c2⟩
        by_cases hi1 : i1 = i <;> by_cases hi2 : i2 = i
        · subst hi1; subst hi2
          simp only [↓reduceDIte]
          rw [hsum_val]; simp [Ui2, Wi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
      | inr x2 =>
        rcases x2 with ⟨i2, c2⟩
        by_cases hi1 : i1 = i <;> by_cases hi2 : i2 = i
        · subst hi1; subst hi2
          simp only [↓reduceDIte]
          rw [hsum_val]; simp [Ui2, Wi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
    | inr x1 =>
      rcases x1 with ⟨i1, r1⟩
      cases h2 : coord.symm idx2 with
      | inl x2 =>
        rcases x2 with ⟨i2, c2⟩
        by_cases hi1 : i1 = i <;> by_cases hi2 : i2 = i
        · subst hi1; subst hi2
          simp only [↓reduceDIte]
          rw [hsum_val]; simp [Ui2, Wi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
      | inr x2 =>
        rcases x2 with ⟨i2, c2⟩
        by_cases hi1 : i1 = i <;> by_cases hi2 : i2 = i
        · subst hi1; subst hi2
          simp only [↓reduceDIte]
          rw [hsum_val]; simp [Ui2, Wi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
        · simp [hi1, hi2]
  -- Extract hidden functions pA..qC via obtain!
  have hblk_ex : ∃ (pA qA pB qB pC qC : (i : Fin l) → Fin (s i) → Fin (w + 1) → F2),
      ∀ (i : Fin l) (z : V) (r0 c0 : Fin (w + 1)),
        (∑ m0 : Fin (s i),
          (vdot (a i) z * (pA i m0 r0 * qA i m0 c0) +
           vdot (b i) z * (pB i m0 r0 * qB i m0 c0) +
           vdot (a i + b i) z * (pC i m0 r0 * qC i m0 c0))) =
        Fin.cases 0 (fun idx1 => Fin.cases 0 (fun idx2 =>
          match coord.symm idx1, coord.symm idx2 with
          | Sum.inl ⟨i1, r1⟩, Sum.inr ⟨i2, c2⟩ =>
            if h1 : i1 = i then if h2 : i2 = i then
              (vdot (a i) z • U i + vdot (b i) z • W i) (h1 ▸ r1) (h2 ▸ c2) else 0 else 0
          | Sum.inr ⟨i1, r1⟩, Sum.inl ⟨i2, c2⟩ =>
            if h1 : i1 = i then if h2 : i2 = i then
              (vdot (a i) z • U i + vdot (b i) z • W i).transpose (h1 ▸ r1) (h2 ▸ c2) else 0 else 0
          | _, _ => 0) c0) r0 :=
    ⟨fun i => (hblk_dec i).choose,
     fun i => (hblk_dec i).choose_spec.choose,
     fun i => (hblk_dec i).choose_spec.choose_spec.choose,
     fun i => (hblk_dec i).choose_spec.choose_spec.choose_spec.choose,
     fun i => (hblk_dec i).choose_spec.choose_spec.choose_spec.choose_spec.choose,
     fun i => (hblk_dec i).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose,
     fun i => (hblk_dec i).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec⟩
  obtain ⟨pA, qA, pB, qB, pC, qC, hblk_sum⟩ := hblk_ex
  -- Step 3: For each H in D, pick one block pickI H with line (pickI H) = H and 0 < s (pickI H)
  have hpick_each : ∀ H : Finset V, H ∈ D → ∃ i : Fin l, line i = H ∧ 0 < s i := by
    intro H hHD
    have hpos := hD_pos H hHD
    by_contra hall; push_neg at hall
    have h0 : mass H = 0 := by
      dsimp only [mass]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hli
      · have := hall i hli; omega
      · rfl
    omega
  have hchosen_ex : ∃ chosenI : Finset (Fin l),
      chosenI.card = D.card ∧
      (∀ i ∈ chosenI, 0 < s i) ∧
      (∀ u : V, (chosenI.filter (fun i => u ∈ line i)).card = (D.filter (fun H => u ∈ H)).card) := by
    let pick : (H : Finset V) → H ∈ D → Fin l := fun H hH => (hpick_each H hH).choose
    let chosenI : Finset (Fin l) := D.attach.image (fun H => pick H.1 H.2)
    have hpick_line : ∀ (H : Finset V) (hH : H ∈ D), line (pick H hH) = H :=
      fun H hH => (hpick_each H hH).choose_spec.1
    have hpick_pos : ∀ (H : Finset V) (hH : H ∈ D), 0 < s (pick H hH) :=
      fun H hH => (hpick_each H hH).choose_spec.2
    have hpick_inj : Function.Injective (fun H : D => pick H.1 H.2) := by
      intro H1 H2 heq
      dsimp only at heq
      apply Subtype.ext
      rw [← hpick_line H1.1 H1.2, ← hpick_line H2.1 H2.2, heq]
    refine ⟨chosenI, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hpick_inj, Finset.card_attach]
    · intro i hi
      obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hi
      exact hpick_pos H.1 H.2
    · intro u
      symm
      refine Finset.card_bij (fun H hH => pick H (Finset.mem_filter.mp hH).1) ?_ ?_ ?_
      · intro H hH
        have hm := Finset.mem_filter.mp hH
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨H, hm.1⟩, Finset.mem_attach _ _, rfl⟩,
          by rw [hpick_line H hm.1]; exact hm.2⟩
      · intro H1 h1 H2 h2 heq
        have := congrArg line heq
        rw [hpick_line H1 (Finset.mem_filter.mp h1).1, hpick_line H2 (Finset.mem_filter.mp h2).1] at this
        exact this
      · intro i hi
        have hm := Finset.mem_filter.mp hi
        obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hm.1
        have hm2 := hm.2; rw [hpick_line H.1 H.2] at hm2
        exact ⟨H.1, Finset.mem_filter.mpr ⟨H.2, hm2⟩, rfl⟩
  obtain ⟨chosenI, hchosen_card, hchosen_pos, hchosen_filt⟩ := hchosen_ex
  -- Step 4: Build rank-1 piece list per block i and per mask u : V!
  let blockPieces : (i : Fin l) → V → List ((Fin (w + 1) → F2) × (Fin (w + 1) → F2)) := fun i u =>
    if h : u = a i then
      if hc : i ∈ chosenI then
        ((List.finRange (s i)).tail).map (fun m0 => (pA i m0, qA i m0))
      else
        (List.finRange (s i)).map (fun m0 => (pA i m0, qA i m0))
    else if u = b i then
      if hc : i ∈ chosenI then
        (pA i ⟨0, hchosen_pos i hc⟩, qA i ⟨0, hchosen_pos i hc⟩) ::
          (List.finRange (s i)).map (fun m0 => (pB i m0, qB i m0))
      else
        (List.finRange (s i)).map (fun m0 => (pB i m0, qB i m0))
    else if u = a i + b i then
      if hc : i ∈ chosenI then
        (pA i ⟨0, hchosen_pos i hc⟩, qA i ⟨0, hchosen_pos i hc⟩) ::
          (List.finRange (s i)).map (fun m0 => (pC i m0, qC i m0))
      else
        (List.finRange (s i)).map (fun m0 => (pC i m0, qC i m0))
    else []
  have hne_ab : ∀ i : Fin l, a i ≠ b i ∧ a i ≠ a i + b i ∧ b i ≠ a i + b i := fun i =>
    ⟨(hab i).2.2,
     fun h => (hab i).2.1 (funext fun k => by have hk := congrFun h k; simp only [Pi.add_apply, Pi.zero_apply] at hk ⊢; linear_combination -hk),
     fun h => (hab i).1 (funext fun k => by have hk := congrFun h k; simp only [Pi.add_apply, Pi.zero_apply] at hk ⊢; linear_combination -hk)⟩
  have hbp_len : ∀ (i : Fin l) (u : V),
      (blockPieces i u).length =
        if u = a i then (if i ∈ chosenI then s i - 1 else s i)
        else if u = b i then (if i ∈ chosenI then s i + 1 else s i)
        else if u = a i + b i then (if i ∈ chosenI then s i + 1 else s i)
        else 0 := by
    intro i u
    dsimp only [blockPieces]
    split_ifs <;> simp [List.length_tail]
  have hbp_len_mod2 : ∀ (i : Fin l) (u : V),
      (blockPieces i u).length % 2 = (if u ∈ line i then s i + (if i ∈ chosenI then 1 else 0) else 0) % 2 := by
    intro i u
    rw [hbp_len i u]
    by_cases h1 : u = a i
    · subst h1
      have hmem : a i ∈ line i := by simp [line]
      rw [if_pos rfl, if_pos hmem]
      by_cases hc : i ∈ chosenI
      · have hp := hchosen_pos i hc; simp [hc]; omega
      · simp [hc]
    · by_cases h2 : u = b i
      · subst h2
        have hmem : b i ∈ line i := by simp [line]
        rw [if_neg h1, if_pos rfl, if_pos hmem]
        by_cases hc : i ∈ chosenI <;> simp [hc]
      · by_cases h3 : u = a i + b i
        · subst h3
          have hmem : a i + b i ∈ line i := by simp [line]
          rw [if_neg h1, if_neg h2, if_pos rfl, if_pos hmem]
          by_cases hc : i ∈ chosenI <;> simp [hc]
        · have hnot : u ∉ line i := by simp [line, h1, h2, h3]
          simp [h1, h2, h3, hnot]
  have hbp_len_sum_u : ∀ i : Fin l,
      (∑ u : V, (blockPieces i u).length) = 3 * s i + if i ∈ chosenI then 1 else 0 := by
    intro i
    rw [← Finset.sum_subset (Finset.subset_univ (line i))]
    · have ⟨h1, h2, h3⟩ := hne_ab i
      simp only [line]
      rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_insert (by simp [h3]), Finset.sum_singleton]
      rw [hbp_len i (a i), hbp_len i (b i), hbp_len i (a i + b i)]
      simp only [↓reduceIte, Ne.symm h1, Ne.symm h2, Ne.symm h3]
      by_cases hc : i ∈ chosenI
      · have hp := hchosen_pos i hc; simp [hc]; omega
      · simp [hc]; omega
    · intro u _ hu
      simp only [line, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
      rw [hbp_len i u]; simp [hu.1, hu.2.1, hu.2.2]
  have hbp_eval_sum : ∀ (i : Fin l) (z : V) (r0 c0 : Fin (w + 1)),
      (∑ u : V, vdot u z * ((blockPieces i u).map (fun x => x.1 r0 * x.2 c0)).sum) =
      (∑ m0 : Fin (s i),
        (vdot (a i) z * (pA i m0 r0 * qA i m0 c0) +
         vdot (b i) z * (pB i m0 r0 * qB i m0 c0) +
         vdot (a i + b i) z * (pC i m0 r0 * qC i m0 c0))) := by
    intro i z r0 c0
    have hfinRange_sum : ∀ (f : Fin (s i) → F2), ((List.finRange (s i)).map f).sum = ∑ m0 : Fin (s i), f m0 := by
      intro f
      have hstl : ((Finset.univ : Finset (Fin (s i))).toList.map f).sum = ∑ m0 : Fin (s i), f m0 := by
        rw [Finset.sum, ← Finset.coe_toList Finset.univ, Multiset.map_coe, Multiset.sum_coe]
      rw [← hstl]
      have hperm : (List.finRange (s i)).Perm (Finset.univ : Finset (Fin (s i))).toList := by
        refine (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (Finset.nodup_toList _)).mpr fun x => by simp
      exact (hperm.map f).sum_eq
    rw [← Finset.sum_subset (Finset.subset_univ (line i))]
    · have ⟨h1, h2, h3⟩ := hne_ab i
      simp only [line]
      rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_insert (by simp [h3]), Finset.sum_singleton]
      dsimp only [blockPieces]
      simp only [↓reduceDIte, Ne.symm h1, Ne.symm h2, Ne.symm h3, ↓reduceIte]
      by_cases hc : i ∈ chosenI
      · simp only [dif_pos hc, List.map_cons, List.sum_cons]
        have hpos := hchosen_pos i hc
        have hfr_cons : ∀ {k : ℕ} (hk : 0 < k), List.finRange k = ⟨0, hk⟩ :: (List.finRange k).tail :=
          fun {k} hk => by cases k with | zero => omega | succ n0 => simp [List.finRange_succ]
        have htail_sum : (((List.finRange (s i)).tail.map (fun m0 => pA i m0 r0 * qA i m0 c0)).sum) =
            (∑ m0 : Fin (s i), pA i m0 r0 * qA i m0 c0) + pA i ⟨0, hpos⟩ r0 * qA i ⟨0, hpos⟩ c0 := by
          have hfull := hfinRange_sum (fun m0 => pA i m0 r0 * qA i m0 c0)
          conv_lhs at hfull => rw [hfr_cons hpos]
          simp only [List.map_cons, List.sum_cons] at hfull
          have hf2 := f2_add_self (pA i ⟨0, hpos⟩ r0 * qA i ⟨0, hpos⟩ c0)
          linear_combination hfull - hf2
        have hA' : (((List.finRange (s i)).tail.map (fun m0 => (pA i m0, qA i m0))).map (fun x => x.1 r0 * x.2 c0)).sum =
            (∑ m0 : Fin (s i), pA i m0 r0 * qA i m0 c0) + pA i ⟨0, hpos⟩ r0 * qA i ⟨0, hpos⟩ c0 := by
          rw [List.map_map]; exact htail_sum
        have hB' : (((List.finRange (s i)).map (fun m0 => (pB i m0, qB i m0))).map (fun x => x.1 r0 * x.2 c0)).sum =
            ∑ m0 : Fin (s i), pB i m0 r0 * qB i m0 c0 := by
          rw [List.map_map]; exact hfinRange_sum (fun m0 => pB i m0 r0 * qB i m0 c0)
        have hC' : (((List.finRange (s i)).map (fun m0 => (pC i m0, qC i m0))).map (fun x => x.1 r0 * x.2 c0)).sum =
            ∑ m0 : Fin (s i), pC i m0 r0 * qC i m0 c0 := by
          rw [List.map_map]; exact hfinRange_sum (fun m0 => pC i m0 r0 * qC i m0 c0)
        rw [hA', hB', hC', Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        have hvab := vdot_add_left (a i) (b i) z
        have hf2a := f2_add_self (vdot (a i) z * (pA i ⟨0, hpos⟩ r0 * qA i ⟨0, hpos⟩ c0))
        have hf2b := f2_add_self (vdot (b i) z * (pA i ⟨0, hpos⟩ r0 * qA i ⟨0, hpos⟩ c0))
        rw [hvab]; linear_combination hf2a + hf2b
      · simp only [dif_neg hc]
        have hA' : (((List.finRange (s i)).map (fun m0 => (pA i m0, qA i m0))).map (fun x => x.1 r0 * x.2 c0)).sum =
            ∑ m0 : Fin (s i), pA i m0 r0 * qA i m0 c0 := by
          rw [List.map_map]; exact hfinRange_sum (fun m0 => pA i m0 r0 * qA i m0 c0)
        have hB' : (((List.finRange (s i)).map (fun m0 => (pB i m0, qB i m0))).map (fun x => x.1 r0 * x.2 c0)).sum =
            ∑ m0 : Fin (s i), pB i m0 r0 * qB i m0 c0 := by
          rw [List.map_map]; exact hfinRange_sum (fun m0 => pB i m0 r0 * qB i m0 c0)
        have hC' : (((List.finRange (s i)).map (fun m0 => (pC i m0, qC i m0))).map (fun x => x.1 r0 * x.2 c0)).sum =
            ∑ m0 : Fin (s i), pC i m0 r0 * qC i m0 c0 := by
          rw [List.map_map]; exact hfinRange_sum (fun m0 => pC i m0 r0 * qC i m0 c0)
        rw [hA', hB', hC', Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    · intro u _ hu
      simp only [line, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
      dsimp only [blockPieces]
      simp [hu.1, hu.2.1, hu.2.2]
  -- Pool pieces per mask u : V across all i : Fin l, then pairUp!
  let piecesU : V → List ((Fin (w + 1) → F2) × (Fin (w + 1) → F2)) := fun u =>
    (List.finRange l).flatMap (fun i => blockPieces i u)
  have hpiecesU_len : ∀ u : V, (piecesU u).length = ∑ i : Fin l, (blockPieces i u).length := by
    intro u
    dsimp only [piecesU]
    rw [List.length_flatMap]
    have hstl : ((Finset.univ : Finset (Fin l)).toList.map (fun i => (blockPieces i u).length)).sum =
        ∑ i : Fin l, (blockPieces i u).length := by
      rw [Finset.sum, ← Finset.coe_toList Finset.univ, Multiset.map_coe, Multiset.sum_coe]
    rw [← hstl]
    have hperm : (List.finRange l).Perm (Finset.univ : Finset (Fin l)).toList := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (Finset.nodup_toList _)).mpr fun x => by simp
    exact (hperm.map _).sum_eq
  have hm_eq_sum : ∀ u : V, m u = ∑ i : Fin l, if u ∈ line i then s i else 0 := by
    intro u
    dsimp only [m, mass]
    have h1 : ∀ H ∈ lines, (if u ∈ H then ∑ i : Fin l, if line i = H then s i else 0 else 0) =
        ∑ i : Fin l, if line i = H then (if u ∈ line i then s i else 0) else 0 := by
      intro H _
      by_cases hu : u ∈ H
      · rw [if_pos hu]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hli : line i = H
        · rw [if_pos hli, if_pos hli, hli, if_pos hu]
        · rw [if_neg hli, if_neg hli]
      · rw [if_neg hu]
        symm; refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hli : line i = H
        · rw [if_pos hli, hli, if_neg hu]
        · rw [if_neg hli]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmem : line i ∈ lines := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [Finset.sum_eq_single (line i) (fun H _ hne => if_neg (Ne.symm hne)) (fun h => absurd hmem h), if_pos rfl]
  have hpiecesU_mod2 : ∀ u : V, (piecesU u).length % 2 = (m u + (D.filter (fun H => u ∈ H)).card) % 2 := by
    intro u
    rw [hpiecesU_len u, ← hchosen_filt u, hm_eq_sum u]
    have hcf : (chosenI.filter (fun i => u ∈ line i)).card =
        ∑ i : Fin l, if u ∈ line i then (if i ∈ chosenI then 1 else 0) else 0 := by
      rw [Finset.card_filter]
      rw [← Finset.sum_subset (Finset.subset_univ chosenI)]
      · refine Finset.sum_congr rfl fun i hi => by simp [hi]
      · intro i _ hi; simp [hi]
    rw [hcf, ← Finset.sum_add_distrib]
    have hsum_mod : ∀ (S0 : Finset (Fin l)) (f g : Fin l → ℕ),
        (∀ i ∈ S0, f i % 2 = g i % 2) → (∑ i ∈ S0, f i) % 2 = (∑ i ∈ S0, g i) % 2 := by
      intro S0 f g hfg
      induction S0 using Finset.induction_on with
      | empty => simp
      | insert i S0 hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        have h1 := hfg i (Finset.mem_insert_self _ _)
        have h2 := ih (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
        omega
    refine hsum_mod Finset.univ _ _ fun i _ => ?_
    rw [hbp_len_mod2 i u]
    split_ifs <;> simp
  -- Step 5: Assemble tagged list of 4-tuples: Sum.inl k (for BS k) and Sum.inr u (for pairUp (piecesU u))
  let allV : List V := (Finset.univ : Finset V).toList
  let taggedPairs : List ((Fin free ⊕ V) × ((Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2))) :=
    ((List.finRange free).map (fun k => (Sum.inl k, sP k))) ++
    (allV.flatMap (fun u => (pairUp (piecesU u)).map (fun t => (Sum.inr u, t))))
  let rawPairs := taggedPairs.map Prod.snd
  have hrawPairs_len : rawPairs.length = free + (3 * N + D.card + left.card) / 2 := by
    simp only [rawPairs, taggedPairs, List.length_map, List.length_append, List.length_finRange,
      List.length_flatMap]
    congr 1
    have hsum_v : (allV.map (fun u => (pairUp (piecesU u)).length)).sum =
        ∑ u : V, (pairUp (piecesU u)).length := by
      dsimp only [allV]
      rw [Finset.sum, ← Finset.coe_toList Finset.univ, Multiset.map_coe, Multiset.sum_coe]
    have h2 : 2 * ∑ u : V, (pairUp (piecesU u)).length = 3 * N + D.card + left.card := by
      rw [Finset.mul_sum]
      simp_rw [pairUp_length]
      rw [Finset.sum_add_distrib]
      have htot_len : ∑ u : V, (piecesU u).length = 3 * N + D.card := by
        simp_rw [hpiecesU_len]
        rw [Finset.sum_comm]
        simp_rw [hbp_len_sum_u, Finset.sum_add_distrib, ← Finset.mul_sum]
        have hch : (∑ i : Fin l, if i ∈ chosenI then 1 else 0) = chosenI.card := by
          rw [← Finset.card_filter]; simp
        rw [hch, hchosen_card]
      have htot_mod : ∑ u : V, (piecesU u).length % 2 = left.card := by
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hpiecesU_mod2 u]
        have hlt : (m u + (D.filter (fun H => u ∈ H)).card) % 2 < 2 := Nat.mod_lt _ (by decide)
        split_ifs with h <;> omega
      rw [htot_len, htot_mod]
    rw [hsum_v]; omega
  -- Build pairListBuild + tapsBuildGen over all (A, z) with A in S!
  let bP := pairListBuild (w + 1) (w + 1) width rawPairs
  let baseP := width + bP.1.length
  have hbaseP : baseP = width + bP.1.length := rfl
  obtain ⟨hokP, hnlP, hltP, _, hdepP⟩ := pairListBuild_spec (w + 1) (w + 1) rawPairs width (le_refl _)
  change isLinearOK bP.1 width at hokP
  change bP.1.countP nlGate = rawPairs.length at hnlP
  change ∀ u ∈ bP.2, u < baseP at hltP
  have hlen_wires : bP.2.length = taggedPairs.length := by
    rw [pairListBuild_wires_length]; simp [rawPairs]
  let taggedWires : List ((Fin free ⊕ V) × ℕ) := (taggedPairs.map Prod.fst).zip bP.2
  let sel : (T × V) → (Fin free ⊕ V) → Bool := fun az tag =>
    match tag with
    | Sum.inl k => decide (coeffS az.1 k = 1)
    | Sum.inr u => decide (vdot u az.2 = 1)
  let corr : (T × V) → (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × F2 := fun az =>
    (fun r0 => ((taggedPairs.filter (fun p => sel az p.1)).map (fun p => p.2.1 r0 * p.2.2.1 r0)).sum,
     fun c0 => ((taggedPairs.filter (fun p => sel az p.1)).map (fun p => p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum,
     0)
  let allAZ : List (T × V) := ((Finset.univ.filter (fun A : T => A ∈ S)) ×ˢ (Finset.univ : Finset V)).toList
  let taps := tapsBuildGen w taggedWires sel corr baseP allAZ
  have hpw_lt : ∀ p ∈ taggedWires, p.2 < baseP := fun p hp => hltP p.2 (List.of_mem_zip hp).2
  obtain ⟨hokT, hnlT, _, hvalT, hdepT⟩ := tapsBuildGen_spec w taggedWires sel corr allAZ baseP (by omega) hpw_lt
  change isLinearOK taps.1 baseP at hokT
  change taps.1.countP nlGate = 0 at hnlT
  let gs := bP.1 ++ taps.1
  have hokAll : isLinearOK gs width := isLinearOK_append hokP (isLinearOK_eq hokT hbaseP.symm)
  refine ⟨⟨gs, 0⟩, fun A z => taps.2 (A, z), hokAll.1, hokAll.2, ?_, ?_⟩
  · simp only [gs, List.countP_append, hnlP, hnlT, add_zero, hrawPairs_len]
    exact le_refl _
  · intro A hA z
    have haz_mem : (A, z) ∈ allAZ := Finset.mem_toList.mpr
      (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩, Finset.mem_univ _⟩)
    constructor
    · let ds0 := List.replicate width 0
      let dsP := bP.1.foldl depthStep ds0
      have hds0_len : ds0.length = width := List.length_replicate
      have hds0_get : ∀ u < width, ds0.getD u 0 = 0 := fun u hu => by
        simp [ds0, List.getD_eq_getElem?_getD, hu]
      have hdsP_len : dsP.length = baseP := by simp [dsP, foldl_depthStep_length, hds0_len, hbaseP]
      have hdsP_get : ∀ u < width, dsP.getD u 0 = 0 := fun u hu =>
        (foldl_depthStep_getD_old ds0 bP.1 u (by omega)).trans (hds0_get u hu)
      have hdpw : ∀ p ∈ taggedWires, dsP.getD p.2 0 ≤ 1 := fun p hp =>
        hdepP ds0 hds0_len hds0_get p.2 (List.of_mem_zip hp).2
      change (gs.foldl depthStep ds0).getD (taps.2 (A, z)) 0 ≤ 1
      simp only [gs, List.foldl_append]
      exact hdepT dsP hdsP_len hdsP_get hdpw (A, z) haz_mem
    · intro r0 c0
      apply b2f_inj
      change b2f ((gs.foldl wireStep (oneEach r0 c0)).getD (taps.2 (A, z)) false) = b2f (table A z r0 c0)
      let ws0 := oneEach r0 c0
      let wsP := bP.1.foldl wireStep ws0
      have hws0_len : ws0.length = width := by
        simp only [ws0, oneEach, List.length_append, List.length_ofFn, width]
      have hws0_get : ∀ u < width, ws0.getD u false = (oneEach r0 c0).getD u false := fun _ _ => rfl
      have hwsP_len : wsP.length = baseP := by simp [wsP, foldl_wireStep_length, hws0_len, hbaseP]
      have hwsP_get : ∀ u < width, wsP.getD u false = (oneEach r0 c0).getD u false := fun u hu =>
        (foldl_wireStep_getD_old ws0 bP.1 u (by omega)).trans (hws0_get u hu)
      simp only [gs, List.foldl_append]
      rw [hvalT r0 c0 wsP hwsP_len hwsP_get (A, z) haz_mem]
      -- Evaluate zip sum using pairListBuild_wire_val
      have hzip_sum : ((taggedWires.filter (fun p => sel (A, z) p.1)).map
          (fun p => b2f (wsP.getD p.2 false))).sum =
          ((taggedPairs.filter (fun p => sel (A, z) p.1)).map
            (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0 +
              p.2.1 r0 * p.2.2.1 r0 + p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum := by
        have hlen_rp : rawPairs.length = taggedPairs.length := by simp [rawPairs]
        have hval_idx : ∀ (idx : Fin taggedPairs.length),
            let t := (taggedPairs.get idx).2
            b2f (wsP.getD (bP.2.getD idx.val 0) false) =
              t.1 r0 * t.2.2.1 c0 + t.2.1 r0 * t.2.2.2 c0 + t.1 r0 * t.2.1 r0 + t.2.2.1 c0 * t.2.2.2 c0 := by
          intro idx
          have hv := pairListBuild_wire_val (w + 1) (w + 1) rawPairs width (le_refl _)
            ⟨idx.val, by rw [hlen_rp]; exact idx.isLt⟩ r0 c0 ws0 hws0_len hws0_get
          simpa [rawPairs, bP, wsP] using hv
        have hfilt_sum : ∀ {γ : Type} (l0 : List γ) (pred : γ → Bool) (f : γ → F2),
            ((l0.filter pred).map f).sum = ∑ idx : Fin l0.length, if pred (l0.get idx) then f (l0.get idx) else 0 := by
          intro γ l0 pred f
          induction l0 with
          | nil => simp
          | cons hd tl ih =>
            simp only [List.length_cons, Fin.sum_univ_succ]
            cases hp : pred hd <;> simp [List.filter_cons, hp, ih]
        rw [hfilt_sum, hfilt_sum]
        have hpw_len : taggedWires.length = taggedPairs.length := by
          simp [taggedWires, List.length_zip, hlen_wires]
        let e : Fin taggedPairs.length ≃ Fin taggedWires.length := finCongr hpw_len.symm
        rw [← Equiv.sum_comp e]
        refine Finset.sum_congr rfl fun idx _ => ?_
        have hget_zip : taggedWires.get (e idx) = ((taggedPairs.get idx).1, bP.2.getD idx.val 0) := by
          have h1 : taggedWires[idx.val]'(by rw [hpw_len]; exact idx.isLt) =
              ((taggedPairs.map Prod.fst)[idx.val]'(by simp),
               bP.2[idx.val]'(by rw [hlen_wires]; exact idx.isLt)) := List.getElem_zip
          have h2 : bP.2.getD idx.val 0 = bP.2[idx.val]'(by rw [hlen_wires]; exact idx.isLt) := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen_wires]; exact idx.isLt)]
          rw [h2]; simpa [e] using h1
        rw [hget_zip, hval_idx idx]
      rw [hzip_sum]
      have hsum_add : ∀ {γ : Type} (l0 : List γ) (f g : γ → F2),
          (l0.map (fun a => f a + g a)).sum = (l0.map f).sum + (l0.map g).sum := by
        intro γ l0 f g
        induction l0 with
        | nil => simp
        | cons hd tl ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      dsimp only [corr]
      have hsplit4 : ((taggedPairs.filter (fun p => sel (A, z) p.1)).map
          (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0 +
            p.2.1 r0 * p.2.2.1 r0 + p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum =
          ((taggedPairs.filter (fun p => sel (A, z) p.1)).map
            (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum +
          ((taggedPairs.filter (fun p => sel (A, z) p.1)).map
            (fun p => p.2.1 r0 * p.2.2.1 r0)).sum +
          ((taggedPairs.filter (fun p => sel (A, z) p.1)).map
            (fun p => p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum := by
        rw [hsum_add, hsum_add]
      rw [hsplit4]
      have hcancel : ((taggedPairs.filter (fun p => sel (A, z) p.1)).map (fun p => p.2.1 r0 * p.2.2.1 r0)).sum +
          ((taggedPairs.filter (fun p => sel (A, z) p.1)).map (fun p => p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum + 0 +
          (((taggedPairs.filter (fun p => sel (A, z) p.1)).map
              (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum +
           ((taggedPairs.filter (fun p => sel (A, z) p.1)).map (fun p => p.2.1 r0 * p.2.2.1 r0)).sum +
           ((taggedPairs.filter (fun p => sel (A, z) p.1)).map (fun p => p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum) =
          ((taggedPairs.filter (fun p => sel (A, z) p.1)).map
            (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum := by
        have h1 := f2_add_self (((taggedPairs.filter (fun p => sel (A, z) p.1)).map (fun p => p.2.1 r0 * p.2.2.1 r0)).sum)
        have h2 := f2_add_self (((taggedPairs.filter (fun p => sel (A, z) p.1)).map (fun p => p.2.2.2.1 c0 * p.2.2.2.2 c0)).sum)
        linear_combination h1 + h2
      rw [hcancel]
      -- Split taggedPairs into S-part + K-part!
      dsimp only [taggedPairs]
      rw [List.filter_append, List.map_append, List.sum_append]
      -- Evaluate S-part!
      have hSpart : ((((List.finRange free).map (fun k => (Sum.inl k, sP k))).filter (fun p => sel (A, z) p.1)).map
          (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum =
          Fin.cases 0 (fun idx1 => Fin.cases 0 (fun idx2 =>
            (Matrix.fromBlocks A 0 0 0) (coord.symm idx1) (coord.symm idx2)) c0) r0 := by
        have h1 : ((((List.finRange free).map (fun k => (Sum.inl k, sP k))).filter (fun p => sel (A, z) p.1)).map
            (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum =
            ∑ k : Fin free, coeffS A k * ((sP k).1 r0 * (sP k).2.2.1 c0 + (sP k).2.1 r0 * (sP k).2.2.2 c0) := by
          rw [List.filter_map, List.map_map]
          have hfr : ∀ (pred : Fin free → Bool) (f : Fin free → F2),
              (((List.finRange free).filter pred).map f).sum = ∑ k : Fin free, if pred k then f k else 0 := by
            intro pred f
            have hstl : (((Finset.univ.filter (fun k : Fin free => pred k = true)).toList).map f).sum =
                ∑ k ∈ Finset.univ.filter (fun k : Fin free => pred k = true), f k := by
              rw [Finset.sum, ← Finset.coe_toList _, Multiset.map_coe, Multiset.sum_coe]
            have hperm : ((List.finRange free).filter pred).Perm
                (Finset.univ.filter (fun k : Fin free => pred k = true)).toList := by
              refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (Finset.nodup_toList _)).mpr fun k => by simp
            rw [(hperm.map f).sum_eq, hstl, Finset.sum_filter]
          rw [hfr]
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp only [Function.comp_apply, sel]
          rcases f2_cases (coeffS A k) with h0 | h1
          · simp [h0]
          · simp [h1]
        rw [h1]
        simp_rw [hsP_eq]
        refine Fin.cases (by simp) (fun idx1 => ?_) r0
        refine Fin.cases (by simp) (fun idx2 => ?_) c0
        simp only [Fin.cases_succ]
        conv_rhs => rw [hBS_rep A hA]
        cases coord.symm idx1 <;> cases coord.symm idx2 <;> simp [Matrix.sum_apply, Matrix.smul_apply] <;> rfl
      -- Evaluate K-part!
      have hKpart : (((allV.flatMap (fun u => (pairUp (piecesU u)).map (fun t => (Sum.inr u, t)))).filter
          (fun p => sel (A, z) p.1)).map
          (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum =
          Fin.cases 0 (fun idx1 => Fin.cases 0 (fun idx2 =>
            (Matrix.fromBlocks 0 (K z) (K z).transpose 0) (coord.symm idx1) (coord.symm idx2)) c0) r0 := by
        have hflat_filt : ∀ (us : List V),
            (((us.flatMap (fun u => (pairUp (piecesU u)).map (fun t => (Sum.inr u, t)))).filter
              (fun p => sel (A, z) p.1)).map
              (fun p => p.2.1 r0 * p.2.2.2.1 c0 + p.2.2.1 r0 * p.2.2.2.2 c0)).sum =
            (us.map (fun u => vdot u z * ((piecesU u).map (fun x => x.1 r0 * x.2 c0)).sum)).sum := by
          intro us
          induction us with
          | nil => simp
          | cons u tl ih =>
            simp only [List.flatMap_cons, List.filter_append, List.map_append, List.sum_append,
              List.map_cons, List.sum_cons, ih]
            congr 1
            have hfilt_false : ∀ {γ : Type} (l0 : List γ), l0.filter (fun _ => false) = [] := by
              intro γ l0; induction l0 with | nil => rfl | cons _ _ ih => simp [ih]
            have hfilt_true : ∀ {γ : Type} (l0 : List γ), l0.filter (fun _ => true) = l0 := by
              intro γ l0; induction l0 with | nil => rfl | cons _ _ ih => simp [ih]
            rw [List.filter_map, List.map_map]
            let Q4 := (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2) × (Fin (w + 1) → F2)
            rcases f2_cases (vdot u z) with h0 | h1
            · have hf : ((fun p : (Fin free ⊕ V) × Q4 => sel (A, z) p.1) ∘ fun t : Q4 => ((Sum.inr u : Fin free ⊕ V), t)) = fun _ => false := by
                funext _; simp [sel, h0]
              rw [hf, hfilt_false, List.map_nil, List.sum_nil, h0, zero_mul]
            · have ht : ((fun p : (Fin free ⊕ V) × Q4 => sel (A, z) p.1) ∘ fun t : Q4 => ((Sum.inr u : Fin free ⊕ V), t)) = fun _ => true := by
                funext _; simp [sel, h1]
              rw [ht, hfilt_true, h1, one_mul]
              exact pairUp_sum r0 c0 (piecesU u)
        rw [hflat_filt allV]
        have hsumV : (allV.map (fun u => vdot u z * ((piecesU u).map (fun x => x.1 r0 * x.2 c0)).sum)).sum =
            ∑ u : V, vdot u z * ((piecesU u).map (fun x => x.1 r0 * x.2 c0)).sum := by
          dsimp only [allV]
          rw [Finset.sum, ← Finset.coe_toList Finset.univ, Multiset.map_coe, Multiset.sum_coe]
        rw [hsumV]
        have hpieces_sum : ∀ u : V, ((piecesU u).map (fun x => x.1 r0 * x.2 c0)).sum =
            ∑ i : Fin l, ((blockPieces i u).map (fun x => x.1 r0 * x.2 c0)).sum := by
          intro u
          dsimp only [piecesU]
          have hfm : ∀ (is : List (Fin l)),
              (((is.flatMap (fun i => blockPieces i u)).map (fun x => x.1 r0 * x.2 c0)).sum) =
              (is.map (fun i => ((blockPieces i u).map (fun x => x.1 r0 * x.2 c0)).sum)).sum := by
            intro is
            induction is with
            | nil => simp
            | cons hd tl ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]
          rw [hfm]
          have hstl : ((Finset.univ : Finset (Fin l)).toList.map
              (fun i => ((blockPieces i u).map (fun x => x.1 r0 * x.2 c0)).sum)).sum =
              ∑ i : Fin l, ((blockPieces i u).map (fun x => x.1 r0 * x.2 c0)).sum := by
            rw [Finset.sum, ← Finset.coe_toList Finset.univ, Multiset.map_coe, Multiset.sum_coe]
          rw [← hstl]
          have hperm : (List.finRange l).Perm (Finset.univ : Finset (Fin l)).toList :=
            (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (Finset.nodup_toList _)).mpr fun x => by simp
          exact (hperm.map _).sum_eq
        simp_rw [hpieces_sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [hbp_eval_sum, hblk_sum]
        refine Fin.cases (by simp) (fun idx1 => ?_) r0
        refine Fin.cases (by simp) (fun idx2 => ?_) c0
        simp only [Fin.cases_succ]
        cases coord.symm idx1 with
        | inl x1 =>
          rcases x1 with ⟨i1, r1⟩
          cases coord.symm idx2 with
          | inl x2 => simp
          | inr x2 =>
            rcases x2 with ⟨i2, c2⟩
            simp only [Matrix.fromBlocks_apply₁₂, K]
            by_cases hi : i1 = i2
            · subst hi
              rw [Matrix.blockDiagonal'_apply_eq]
              rw [Finset.sum_eq_single i1]
              · simp
              · intro i _ hne; simp [Ne.symm hne]
              · intro h; exact absurd (Finset.mem_univ i1) h
            · rw [Matrix.blockDiagonal'_apply_ne (fun i => vdot (a i) z • U i + vdot (b i) z • W i) r1 c2 hi]
              refine Finset.sum_eq_zero fun i _ => ?_
              by_cases h1 : i1 = i
              · subst h1; simp [Ne.symm hi]
              · simp [h1]
        | inr x1 =>
          rcases x1 with ⟨i1, r1⟩
          cases coord.symm idx2 with
          | inl x2 =>
            rcases x2 with ⟨i2, c2⟩
            simp only [Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, K]
            by_cases hi : i2 = i1
            · subst hi
              rw [Matrix.blockDiagonal'_apply_eq]
              rw [Finset.sum_eq_single i2]
              · simp
              · intro i _ hne; simp [Ne.symm hne]
              · intro h; exact absurd (Finset.mem_univ i2) h
            · rw [Matrix.blockDiagonal'_apply_ne (fun i => vdot (a i) z • U i + vdot (b i) z • W i) c2 r1 hi]
              refine Finset.sum_eq_zero fun i _ => ?_
              by_cases h1 : i1 = i
              · subst h1; simp [hi]
              · simp [h1]
          | inr x2 => simp
      rw [hSpart, hKpart]
      refine Fin.cases (by simp [table, b2f]) (fun idx1 => ?_) r0
      refine Fin.cases (by simp [table, b2f]) (fun idx2 => ?_) c0
      simp only [Fin.cases_succ, table, b2f]
      have hsum_blk : (Matrix.fromBlocks A 0 0 0) (coord.symm idx1) (coord.symm idx2) +
          (Matrix.fromBlocks 0 (K z) (K z).transpose 0) (coord.symm idx1) (coord.symm idx2) =
          (Matrix.fromBlocks A (K z) (K z).transpose 0) (coord.symm idx1) (coord.symm idx2) := by
        cases coord.symm idx1 <;> cases coord.symm idx2 <;> simp
      rw [hsum_blk]
      rcases f2_cases ((Matrix.fromBlocks A (K z) (K z).transpose 0) (coord.symm idx1) (coord.symm idx2)) with h0 | h1
      · simp [h0]
      · simp [h1]

end PEqualNP.Outside.L_meta_33646

theorem PEqualNP.Outside.L_meta_33646 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (q l : ℕ) (s : Fin l → ℕ),
  let V := Fin q → F
  let I := Σ i : Fin l, Fin (s i)
  let T := Matrix I I F
  let dot := fun (a z : V) => ∑ j, a j * z j
  ∀ (a b : Fin l → V), (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    ∀ (U W : (i : Fin l) → Matrix (Fin (s i)) (Fin (s i)) F),
      (∀ i, (U i).rank = s i ∧ (W i).rank = s i ∧ (U i + W i).rank = s i) →
      ∀ S : Submodule F T, S = Submodule.span F {A : T | A ∈ S ∧ A.rank ≤ 2} →
        let line := fun i : Fin l => ({a i, b i, a i + b i} : Finset V)
        let lines := Finset.univ.image line
        let mass := fun H : Finset V => ∑ i, if line i = H then s i else 0
        let N := ∑ i, s i
        let free := Module.finrank F S
        let K := fun z : V =>
          Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i)
        let w := Fintype.card (I ⊕ I)
        let coord := Fintype.equivFin (I ⊕ I)
        let table := fun (A : T) (z : V) (x y : Fin (w+1)) =>
          let X := Matrix.fromBlocks A (K z) (K z).transpose (0 : T)
          Fin.cases false (fun i => Fin.cases false (fun j =>
            decide (X (coord.symm i) (coord.symm j) ≠ 0)) y) x
        let bank := fun t : ℕ =>
          ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : T → V → ℕ),
            PEqualNP.MetaComplexity.NestedCover.ReadsBack ((w+1)+(w+1)) C ∧
            (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
            ∀ A ∈ S, ∀ z : V,
              (depths ((w+1)+(w+1)) C).getD (tap A z) 0 ≤ 1 ∧
              PEqualNP.Represents.Represents (table A z) ⟨C.gates, tap A z⟩
        let m := fun u : V => ∑ H ∈ lines, if u ∈ H then mass H else 0
        let odd := Finset.univ.filter (fun u : V => m u % 2 = 1)
        (∀ t : ℕ, bank t → free ≤ t ∧ 3*N ≤ 2*(t-free) ∧
          (2*(t-free) = 3*N → odd = ∅) ∧
          (2*(t-free) = 3*N+1 → ∃ H : Submodule F V,
            ∀ u : V, u ∈ odd ↔ u ≠ 0 ∧ u ∈ H)) ∧
          ∀ D : Finset (Finset V), D ⊆ lines → (∀ H ∈ D, 0 < mass H) →
            let left := Finset.univ.filter (fun u : V =>
              (m u + (D.filter (fun H => u ∈ H)).card) % 2 = 1)
            bank (free + (3*N + D.card + left.card)/2) := by
  intro nonlinear depths F q l s V I T dot a b hab U W hUW S hS line lines mass N free K w coord table bank m odd
  constructor
  · intro t hbank
    exact PEqualNP.Outside.L_meta_33646.lower_bound_dir q l s a b hab U W hUW S t hbank
  · intro D hD_sub hD_pos left
    exact PEqualNP.Outside.L_meta_33646.upper_bound_dir q l s a b hab U W hUW S hS D hD_sub hD_pos
