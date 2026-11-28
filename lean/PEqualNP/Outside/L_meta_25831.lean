import PEqualNP.Defs
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace PEqualNP.Outside.L_meta_25831_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped BigOperators

abbrev F2 := ZMod 2

def isNonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsList (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (isNonlin g).toNat])
    (List.replicate width 0)

def wiresList (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

def b2f (b : Bool) : F2 := if b then 1 else 0

lemma b2f_injective : Function.Injective b2f := by
  intro a b h
  cases a <;> cases b <;> simp [b2f] at h <;> rfl

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_not (a : Bool) : b2f (!a) = 1 + b2f a := by
  cases a <;> decide

lemma f2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> decide

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_sub_eq_add (x y : F2) : x - y = x + y := by
  fin_cases x <;> fin_cases y <;> decide

lemma f2_mod_add_self {V : Type*} [AddCommGroup V] [Module F2 V] (v : V) : v + v = 0 := by
  have h2 : (2 : F2) = 0 := rfl
  rw [← two_smul F2 v, h2, zero_smul]

lemma f2_mod_neg {V : Type*} [AddCommGroup V] [Module F2 V] (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero]
  exact f2_mod_add_self v

lemma list_getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma list_getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma list_getD_singleton_zero {α : Type*} (a d : α) : [a].getD 0 d = a := rfl

lemma wiresList_append (gs1 gs2 : List Gate) (inp : List Bool) :
    wiresList (gs1 ++ gs2) inp = wiresList gs2 (wiresList gs1 inp) := by
  simp [wiresList, List.foldl_append]

lemma wiresList_snoc (gs : List Gate) (g : Gate) (inp : List Bool) :
    wiresList (gs ++ [g]) inp =
      wiresList gs inp ++ [g.op.eval (g.inputs.map fun i => (wiresList gs inp).getD i false)] := by
  simp [wiresList, List.foldl_append]

lemma wiresList_length (gs : List Gate) (inp : List Bool) :
    (wiresList gs inp).length = inp.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresList]
  | append_singleton gs g ih =>
    rw [wiresList_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma wiresList_getD_prefix (gs1 gs2 : List Gate) (inp : List Bool) (w : ℕ)
    (hw : w < inp.length + gs1.length) :
    (wiresList (gs1 ++ gs2) inp).getD w false = (wiresList gs1 inp).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, wiresList_snoc, list_getD_append_left]
    · exact ih
    · rw [wiresList_length, List.length_append]; omega

lemma wiresList_getD_last (gs : List Gate) (g : Gate) (inp : List Bool) :
    (wiresList (gs ++ [g]) inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresList gs inp).getD i false) := by
  rw [wiresList_snoc, list_getD_append_right]
  · rw [wiresList_length, Nat.sub_self]; rfl
  · rw [wiresList_length]

lemma depthsList_snoc (width : ℕ) (gs : List Gate) (g : Gate) :
    depthsList width (gs ++ [g]) =
      depthsList width gs ++
        [(g.inputs.map (fun a => (depthsList width gs).getD a 0)).foldr max 0 + (isNonlin g).toNat] := by
  simp [depthsList, List.foldl_append]

lemma depthsList_length (width : ℕ) (gs : List Gate) :
    (depthsList width gs).length = width + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depthsList]
  | append_singleton gs g ih =>
    rw [depthsList_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma depthsList_getD_prefix (width : ℕ) (gs1 gs2 : List Gate) (w : ℕ)
    (hw : w < width + gs1.length) :
    (depthsList width (gs1 ++ gs2)).getD w 0 = (depthsList width gs1).getD w 0 := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, depthsList_snoc, list_getD_append_left]
    · exact ih
    · rw [depthsList_length, List.length_append]; omega

lemma depthsList_getD_last (width : ℕ) (gs : List Gate) (g : Gate) :
    (depthsList width (gs ++ [g])).getD (width + gs.length) 0 =
      (g.inputs.map (fun a => (depthsList width gs).getD a 0)).foldr max 0 + (isNonlin g).toNat := by
  rw [depthsList_snoc, list_getD_append_right]
  · rw [depthsList_length, Nat.sub_self]; rfl
  · rw [depthsList_length]

lemma oneEach_length {n m : ℕ} (x : Fin n) (y : Fin m) :
    (oneEach x y).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (x : Fin n) (y : Fin m) (i : Fin n) :
    (oneEach x y).getD i.val false = decide (i = x) := by
  unfold oneEach
  rw [list_getD_append_left]
  · simp [List.getD_eq_getElem?_getD]
  · simp

lemma oneEach_getD_right {n m : ℕ} (x : Fin n) (y : Fin m) (j : Fin m) :
    (oneEach x y).getD (n + j.val) false = decide (j = y) := by
  unfold oneEach
  rw [list_getD_append_right]
  · simp [List.getD_eq_getElem?_getD]
  · simp

lemma boxOp_rank_outer {n m : ℕ} (a : Fin n → F2) (b : Fin m → F2) :
    (Matrix.of (fun x y => a x * b y)).rank ≤ 1 := by
  let M : Matrix (Fin n) (Fin m) F2 := Matrix.of (fun x y => a x * b y)
  have hsub : LinearMap.range M.mulVecLin ≤ Submodule.span F2 {a} := by
    rintro _ ⟨v, rfl⟩
    have hv : M.mulVecLin v = (∑ y : Fin m, b y * v y) • a := by
      funext x
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a))
  have h1 : Module.finrank F2 (LinearMap.range M.mulVecLin) ≤ Module.finrank F2 (Submodule.span F2 {a}) :=
    Submodule.finrank_mono hsub
  have h2 : Module.finrank F2 (Submodule.span F2 {a}) ≤ 1 := by
    by_cases ha : a = 0
    · subst ha; rw [Submodule.span_zero_singleton, finrank_bot]; omega
    · rw [finrank_span_singleton ha]
  exact h1.trans h2

lemma rank_add_le {n m : ℕ} (M1 M2 : Matrix (Fin n) (Fin m) F2) :
    (M1 + M2).rank ≤ M1.rank + M2.rank := by
  have hsub : LinearMap.range (M1 + M2).mulVecLin ≤
      LinearMap.range M1.mulVecLin ⊔ LinearMap.range M2.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h1 := Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range M1.mulVecLin) (LinearMap.range M2.mulVecLin)
  change Module.finrank F2 (LinearMap.range (M1 + M2).mulVecLin) ≤
    Module.finrank F2 (LinearMap.range M1.mulVecLin) + Module.finrank F2 (LinearMap.range M2.mulVecLin)
  omega

lemma rank_sum_le {n m : ℕ} {ι : Type*} (S : Finset ι) (M : ι → Matrix (Fin n) (Fin m) F2)
    (hM : ∀ i ∈ S, (M i).rank ≤ 2) :
    (∑ i ∈ S, M i).rank ≤ 2 * S.card := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, mul_zero]
    have h0 : (0 : Matrix (Fin n) (Fin m) F2).rank = 0 := by
      change Module.finrank F2 (LinearMap.range (0 : Matrix (Fin n) (Fin m) F2).mulVecLin) = 0
      simp
    omega
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := rank_add_le (M a) (∑ i ∈ S, M i)
    have h2 := hM a (Finset.mem_insert_self a S)
    have h3 := ih (fun i hi => hM i (Finset.mem_insert_of_mem hi))
    omega

def boxOp {n m : ℕ} (u : Fin n) (v : Fin m) (f : Fin n → Fin m → F2) : Matrix (Fin n) (Fin m) F2 :=
  Matrix.of (fun x y => f x y + f u y + f x v + f u v)

lemma boxOp_add {n m : ℕ} (u : Fin n) (v : Fin m) (f1 f2 : Fin n → Fin m → F2) :
    boxOp u v (fun x y => f1 x y + f2 x y) = boxOp u v f1 + boxOp u v f2 := by
  ext x y
  simp only [boxOp, Matrix.of_apply, Matrix.add_apply]
  ring

lemma boxOp_zero {n m : ℕ} (u : Fin n) (v : Fin m) :
    boxOp u v (fun _ _ => 0) = 0 := by
  ext x y
  simp [boxOp]

lemma boxOp_sep {n m : ℕ} (u : Fin n) (v : Fin m) (c : F2) (α : Fin n → F2) (β : Fin m → F2) :
    boxOp u v (fun x y => c + α x + β y) = 0 := by
  ext x y
  simp only [boxOp, Matrix.of_apply, Matrix.zero_apply]
  have hc := f2_add_self c
  have hx := f2_add_self (α x)
  have hu := f2_add_self (α u)
  have hy := f2_add_self (β y)
  have hv := f2_add_self (β v)
  have h1 : (c + α x + β y) + (c + α u + β y) + (c + α x + β v) + (c + α u + β v) =
      (c + c) + (c + c) + (α x + α x) + (α u + α u) + (β y + β y) + (β v + β v) := by ring
  rw [h1, hc, hx, hu, hy, hv]
  ring

lemma boxOp_mul_sep_rank_le_two {n m : ℕ} (u : Fin n) (v : Fin m)
    (c1 c2 : F2) (α1 α2 : Fin n → F2) (β1 β2 : Fin m → F2) :
    (boxOp u v (fun x y => (c1 + α1 x + β1 y) * (c2 + α2 x + β2 y))).rank ≤ 2 := by
  have heq : boxOp u v (fun x y => (c1 + α1 x + β1 y) * (c2 + α2 x + β2 y)) =
      Matrix.of (fun x y => (α1 x + α1 u) * (β2 y + β2 v)) +
      Matrix.of (fun x y => (α2 x + α2 u) * (β1 y + β1 v)) := by
    ext x y
    simp only [boxOp, Matrix.of_apply, Matrix.add_apply]
    have hchar : ∀ z : F2, z + z = 0 := f2_add_self
    have hdiff : ((c1 + α1 x + β1 y) * (c2 + α2 x + β2 y) +
        (c1 + α1 u + β1 y) * (c2 + α2 u + β2 y) +
        (c1 + α1 x + β1 v) * (c2 + α2 x + β2 v) +
        (c1 + α1 u + β1 v) * (c2 + α2 u + β2 v)) -
        ((α1 x + α1 u) * (β2 y + β2 v) + (α2 x + α2 u) * (β1 y + β1 v)) =
        ((c1 * c2 + c1 * c2) + (c1 * c2 + c1 * c2)) +
        (c1 * α2 x + c1 * α2 x) + (c1 * α2 u + c1 * α2 u) +
        (c1 * β2 y + c1 * β2 y) + (c1 * β2 v + c1 * β2 v) +
        (α1 x * c2 + α1 x * c2) + (α1 u * c2 + α1 u * c2) +
        (α1 x * α2 x + α1 x * α2 x) + (α1 u * α2 u + α1 u * α2 u) +
        (β1 y * c2 + β1 y * c2) + (β1 v * c2 + β1 v * c2) +
        (β1 y * β2 y + β1 y * β2 y) + (β1 v * β2 v + β1 v * β2 v) +
        ((α1 x * β2 y - α1 x * β2 y) + (α1 x * β2 v - α1 x * β2 v) +
         (α1 u * β2 y - α1 u * β2 y) + (α1 u * β2 v - α1 u * β2 v) +
         (α2 x * β1 y - α2 x * β1 y) + (α2 x * β1 v - α2 x * β1 v) +
         (α2 u * β1 y - α2 u * β1 y) + (α2 u * β1 v - α2 u * β1 v)) := by ring
    apply sub_eq_zero.mp
    rw [hdiff]
    simp [hchar]
  rw [heq]
  have h1 := rank_add_le
    (Matrix.of (fun x y => (α1 x + α1 u) * (β2 y + β2 v)))
    (Matrix.of (fun x y => (α2 x + α2 u) * (β1 y + β1 v)))
  have h2 := boxOp_rank_outer (fun x => α1 x + α1 u) (fun y => β2 y + β2 v)
  have h3 := boxOp_rank_outer (fun x => α2 x + α2 u) (fun y => β1 y + β1 v)
  omega

def IsSep {n m : ℕ} (f : Fin n → Fin m → F2) : Prop :=
  ∃ (c : F2) (α : Fin n → F2) (β : Fin m → F2), ∀ x y, f x y = c + α x + β y

lemma isSep_const {n m : ℕ} (c : F2) : IsSep (n := n) (m := m) (fun _ _ => c) :=
  ⟨c, 0, 0, fun _ _ => by simp⟩

lemma isSep_left {n m : ℕ} (α : Fin n → F2) : IsSep (n := n) (m := m) (fun x _ => α x) :=
  ⟨0, α, 0, fun _ _ => by simp⟩

lemma isSep_right {n m : ℕ} (β : Fin m → F2) : IsSep (n := n) (m := m) (fun _ y => β y) :=
  ⟨0, 0, β, fun _ _ => by simp⟩

lemma isSep_add {n m : ℕ} {f1 f2 : Fin n → Fin m → F2} (h1 : IsSep f1) (h2 : IsSep f2) :
    IsSep (fun x y => f1 x y + f2 x y) := by
  rcases h1 with ⟨c1, α1, β1, hf1⟩
  rcases h2 with ⟨c2, α2, β2, hf2⟩
  refine ⟨c1 + c2, fun x => α1 x + α2 x, fun y => β1 y + β2 y, fun x y => ?_⟩
  dsimp only
  rw [hf1 x y, hf2 x y]
  ring

lemma isSep_smul {n m : ℕ} (k : F2) {f : Fin n → Fin m → F2} (h : IsSep f) :
    IsSep (fun x y => k * f x y) := by
  rcases h with ⟨c, α, β, hf⟩
  refine ⟨k * c, fun x => k * α x, fun y => k * β y, fun x y => ?_⟩
  dsimp only
  rw [hf x y]
  ring

lemma unary_bool_poly (φ : Bool → Bool) :
    ∃ c0 c1 : F2, ∀ a : Bool, b2f (φ a) = c0 + c1 * b2f a := by
  refine ⟨b2f (φ false), b2f (φ true) + b2f (φ false), fun a => ?_⟩
  cases a
  · simp [b2f]
  · simp [b2f]
    have h := f2_add_self (b2f (φ false))
    calc b2f (φ true) = b2f (φ true) + (b2f (φ false) + b2f (φ false)) := by rw [h, add_zero]
      _ = b2f (φ false) + (b2f (φ true) + b2f (φ false)) := by ring

lemma binary_bool_poly (φ : Bool → Bool → Bool) :
    let c0 := b2f (φ false false)
    let c1 := b2f (φ true false) + c0
    let c2 := b2f (φ false true) + c0
    let c12 := b2f (xor (xor (φ false false) (φ false true)) (xor (φ true false) (φ true true)))
    ∀ a b : Bool, b2f (φ a b) = c0 + c1 * b2f a + c2 * b2f b + c12 * b2f a * b2f b := by
  intro c0 c1 c2 c12 a b
  cases a <;> cases b <;> cases h00 : φ false false <;> cases h01 : φ false true <;>
    cases h10 : φ true false <;> cases h11 : φ true true <;>
    simp only [c0, c1, c2, c12, h00, h01, h10, h11] <;> decide

lemma foldr_max_eq_zero_iff (l : List ℕ) : l.foldr max 0 = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [ih]

lemma foldr_max_le_iff (l : List ℕ) (k : ℕ) : l.foldr max 0 ≤ k ↔ ∀ x ∈ l, x ≤ k := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [ih]

lemma gate_eval_linear_of_not_nonlin {n m : ℕ} (g : Gate) (hlen : g.inputs.length ≤ 2)
    (hlin : isNonlin g = false) (W : ℕ → Fin n → Fin m → Bool) :
    ∃ (c0 : F2) (c : List (F2 × ℕ)),
      (∀ p ∈ c, p.2 ∈ g.inputs) ∧
      ∀ x y, b2f (g.op.eval (g.inputs.map fun i => W i x y)) =
        c0 + (c.map fun p => p.1 * b2f (W p.2 x y)).sum := by
  cases hin : g.inputs with
  | nil =>
    exact ⟨b2f (g.op.eval []), [], by simp, fun x y => by simp⟩
  | cons i1 t1 =>
    cases t1 with
    | nil =>
      rcases unary_bool_poly (fun a => g.op.eval [a]) with ⟨c0, c1, hpoly⟩
      refine ⟨c0, [(c1, i1)], by simp, fun x y => ?_⟩
      simp [hpoly]
    | cons i2 t2 =>
      cases t2 with
      | nil =>
        have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
            (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
          simp only [isNonlin, hin, List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and] at hlin
          exact hlin
        have hpoly := binary_bool_poly (fun a b => g.op.eval [a, b])
        refine ⟨b2f (g.op.eval [false, false]),
          [(b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false]), i1),
           (b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false]), i2)],
          by simp, fun x y => ?_⟩
        have hp := hpoly (W i1 x y) (W i2 x y)
        have hbf : b2f false = 0 := rfl
        rw [hxor, hbf, zero_mul, zero_mul, add_zero] at hp
        simpa [add_assoc] using hp
      | cons i3 t3 =>
        simp [hin] at hlen

lemma gate_eval_nonlin_box_rank_le_two {n m : ℕ} (u : Fin n) (v : Fin m)
    (g : Gate) (hnl : isNonlin g = true) (W : ℕ → Fin n → Fin m → Bool)
    (hsep : ∀ i ∈ g.inputs, IsSep (fun x y => b2f (W i x y))) :
    (boxOp u v (fun x y => b2f (g.op.eval (g.inputs.map fun i => W i x y)))).rank ≤ 2 := by
  have hlen2 : g.inputs.length = 2 := by
    simp only [isNonlin, Bool.and_eq_true, beq_iff_eq] at hnl
    exact hnl.1
  rcases List.length_eq_two.mp hlen2 with ⟨i1, i2, hin⟩
  rw [hin] at hsep ⊢
  have h1 := hsep i1 (by simp)
  have h2 := hsep i2 (by simp)
  rcases h1 with ⟨a0, α1, β1, hf1⟩
  rcases h2 with ⟨b0, α2, β2, hf2⟩
  have hpoly := binary_bool_poly (fun a b => g.op.eval [a, b])
  have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
    simp only [isNonlin, hin, List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and] at hnl
    exact hnl
  let c0 := b2f (g.op.eval [false, false])
  let c1 := b2f (g.op.eval [true, false]) + c0
  let c2 := b2f (g.op.eval [false, true]) + c0
  have hfun : (fun x y => b2f (g.op.eval [W i1 x y, W i2 x y])) =
      fun x y => (c0 + c1 * (a0 + α1 x + β1 y) + c2 * (b0 + α2 x + β2 y)) +
        (a0 + α1 x + β1 y) * (b0 + α2 x + β2 y) := by
    funext x y
    have hp := hpoly (W i1 x y) (W i2 x y)
    have hbt : b2f true = 1 := rfl
    rw [hxor, hbt, one_mul] at hp
    dsimp only at hf1 hf2
    rw [hp, hf1 x y, hf2 x y]
  change (boxOp u v (fun x y => b2f (g.op.eval [W i1 x y, W i2 x y]))).rank ≤ 2
  rw [hfun, boxOp_add]
  have hsep_lin : IsSep (fun x y => c0 + c1 * (a0 + α1 x + β1 y) + c2 * (b0 + α2 x + β2 y)) :=
    isSep_add (isSep_add (isSep_const c0) (isSep_smul c1 ⟨a0, α1, β1, fun _ _ => rfl⟩))
      (isSep_smul c2 ⟨b0, α2, β2, fun _ _ => rfl⟩)
  rcases hsep_lin with ⟨cs, αs, βs, hcs⟩
  have hbox0 : boxOp u v (fun x y => c0 + c1 * (a0 + α1 x + β1 y) + c2 * (b0 + α2 x + β2 y)) = 0 := by
    have : (fun x y => c0 + c1 * (a0 + α1 x + β1 y) + c2 * (b0 + α2 x + β2 y)) =
        fun x y => cs + αs x + βs y := funext fun x => funext fun y => hcs x y
    rw [this]
    exact boxOp_sep u v cs αs βs
  rw [hbox0, zero_add]
  exact boxOp_mul_sep_rank_le_two u v a0 b0 α1 α2 β1 β2

lemma symmDiff_sum_f2 {α : Type*} {V : Type*} [DecidableEq α] [AddCommGroup V] [Module F2 V]
    (S1 S2 : Finset α) (M : α → V) :
    (∑ i ∈ S1, M i) + (∑ i ∈ S2, M i) = ∑ i ∈ symmDiff S1 S2, M i := by
  have h1 : S1 = (S1 \ S2) ∪ (S1 ∩ S2) := (Finset.sdiff_union_inter S1 S2).symm
  have h2 : S2 = (S2 \ S1) ∪ (S1 ∩ S2) := by
    rw [Finset.inter_comm]
    exact (Finset.sdiff_union_inter S2 S1).symm
  have hd1 : Disjoint (S1 \ S2) (S1 ∩ S2) := Finset.disjoint_sdiff_inter S1 S2
  have hd2 : Disjoint (S2 \ S1) (S1 ∩ S2) := by
    rw [Finset.inter_comm]
    exact Finset.disjoint_sdiff_inter S2 S1
  have hsd : symmDiff S1 S2 = (S1 \ S2) ∪ (S2 \ S1) := rfl
  have hd3 : Disjoint (S1 \ S2) (S2 \ S1) := disjoint_sdiff_sdiff
  rw [hsd, Finset.sum_union hd3]
  have hs1 : ∑ i ∈ S1, M i = (∑ i ∈ S1 \ S2, M i) + (∑ i ∈ S1 ∩ S2, M i) := by
    rw [← Finset.sum_union hd1, Finset.sdiff_union_inter]
  have hs2 : ∑ i ∈ S2, M i = (∑ i ∈ S2 \ S1, M i) + (∑ i ∈ S1 ∩ S2, M i) := by
    rw [← Finset.sum_union hd2, Finset.inter_comm S1 S2, Finset.sdiff_union_inter]
  rw [hs1, hs2]
  have hcancel : (∑ i ∈ S1 ∩ S2, M i) + (∑ i ∈ S1 ∩ S2, M i) = 0 := f2_mod_add_self _
  calc (∑ i ∈ S1 \ S2, M i) + (∑ i ∈ S1 ∩ S2, M i) +
        ((∑ i ∈ S2 \ S1, M i) + (∑ i ∈ S1 ∩ S2, M i))
      = (∑ i ∈ S1 \ S2, M i) + (∑ i ∈ S2 \ S1, M i) +
        ((∑ i ∈ S1 ∩ S2, M i) + (∑ i ∈ S1 ∩ S2, M i)) := by abel
    _ = (∑ i ∈ S1 \ S2, M i) + (∑ i ∈ S2 \ S1, M i) := by rw [hcancel, add_zero]

lemma lower_bound_dir {n m k : ℕ} (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (hA : (boxOp u v (fun x y => b2f (G 0 x y))).rank = k)
    (hB : (boxOp u v (fun x y => b2f (G 1 x y))).rank = k)
    (hAB : (boxOp u v (fun x y => b2f (G 0 x y)) + boxOp u v (fun x y => b2f (G 1 x y))).rank = k)
    (t : ℕ)
    (C : Circuit) (tap : Fin 2 → ℕ)
    (hrb : ReadsBack (n + m) C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP isNonlin ≤ t)
    (htap : ∀ j : Fin 2, (depthsList (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates, tap j⟩) :
    (3 * ((k + 1) / 2) + 1) / 2 ≤ t := by
  classical
  let W : ℕ → Fin n → Fin m → Bool := fun w x y => (wiresList C.gates (oneEach x y)).getD w false
  let D : ℕ → ℕ := fun w => (depthsList (n + m) C.gates).getD w 0
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => isNonlin (C.gates[idx]) = true ∧ D (n + m + idx.val) = 1)
  let Mgate : Fin C.gates.length → Matrix (Fin n) (Fin m) F2 :=
    fun idx => boxOp u v (fun x y => b2f (W (n + m + idx.val) x y))
  have hNL_card : NL.card ≤ t := by
    have h1 : NL.card ≤ (Finset.univ.filter (fun idx : Fin C.gates.length => isNonlin (C.gates[idx]) = true)).card :=
      Finset.card_le_card (fun idx hidx => by
        simp only [NL, Finset.mem_filter, Finset.mem_univ, true_and] at hidx ⊢
        exact hidx.1)
    have h2 : (Finset.univ.filter (fun idx : Fin C.gates.length => isNonlin (C.gates[idx]) = true)).card =
        C.gates.countP isNonlin := by
      rw [List.countP_eq_length_filter]
      have hmap : (Finset.univ.filter (fun idx : Fin C.gates.length => isNonlin (C.gates[idx]) = true)).card =
          ((List.finRange C.gates.length).filter (fun idx => isNonlin (C.gates[idx]))).length := by
        rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange _))]
        congr 1
        ext idx
        simp
      rw [hmap]
      have hfl : (C.gates.filter isNonlin) =
          ((List.finRange C.gates.length).filter (fun idx => isNonlin (C.gates[idx.val]))).map (fun idx => C.gates[idx.val]) := by
        have hcomp : ((List.finRange C.gates.length).filter (isNonlin ∘ fun idx : Fin C.gates.length => C.gates[idx.val])).map
            (fun idx : Fin C.gates.length => C.gates[idx.val]) =
            ((List.finRange C.gates.length).map (fun idx : Fin C.gates.length => C.gates[idx.val])).filter isNonlin :=
          (List.filter_map (f := fun idx : Fin C.gates.length => C.gates[idx.val]) (p := isNonlin) (l := List.finRange C.gates.length)).symm
        rw [List.map_getElem_finRange] at hcomp
        exact hcomp.symm
      rw [hfl, List.length_map]
      rfl
    omega
  have hwire_step : ∀ j (hj : j < C.gates.length),
      (∀ x y, W (n + m + j) x y =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => W i x y)) ∧
      D (n + m + j) = ((C.gates[j]).inputs.map D).foldr max 0 + (isNonlin (C.gates[j])).toNat := by
    intro j hj
    have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
      rw [List.append_assoc]
      exact (List.take_append_drop j C.gates).symm.trans (by rw [List.drop_eq_getElem_cons hj]; rfl)
    have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hrb_j : ∀ i ∈ (C.gates[j]).inputs, i < n + m + j := by
      intro i hi
      have h := hrb j hj i
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
      exact h hi
    constructor
    · intro x y
      simp only [W]
      have hlen_in : (oneEach x y).length = n + m := oneEach_length x y
      conv_lhs => rw [hsplit]
      rw [wiresList_getD_prefix (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j + 1)) (oneEach x y)]
      · have heq : n + m + j = (oneEach x y).length + (C.gates.take j).length := by omega
        rw [heq, wiresList_getD_last]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        have hlt : i < (oneEach x y).length + (C.gates.take j).length := by
          have := hrb_j i hi; omega
        symm
        conv_lhs => rw [hsplit, List.append_assoc]
        exact wiresList_getD_prefix (C.gates.take j) ([C.gates[j]] ++ C.gates.drop (j + 1)) (oneEach x y) i hlt
      · rw [hlen_in, List.length_append, htake_len, List.length_singleton]; omega
    · simp only [D]
      conv_lhs => rw [hsplit]
      rw [depthsList_getD_prefix (n + m) (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j + 1))]
      · have heq : n + m + j = n + m + (C.gates.take j).length := by omega
        rw [heq, depthsList_getD_last]
        congr 2
        refine List.map_congr_left fun i hi => ?_
        have hlt : i < n + m + (C.gates.take j).length := by
          have := hrb_j i hi; omega
        symm
        conv_lhs => rw [hsplit, List.append_assoc]
        exact depthsList_getD_prefix (n + m) (C.gates.take j) ([C.gates[j]] ++ C.gates.drop (j + 1)) i hlt
      · rw [List.length_append, htake_len, List.length_singleton]; omega
  have hsep0 : ∀ w : ℕ, D w = 0 → IsSep (fun x y => b2f (W w x y)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hDw
      by_cases hw_in : w < n + m
      · by_cases hw_l : w < n
        · refine isSep_left (m := m) (fun x => b2f (decide (⟨w, hw_l⟩ = x))) |> fun h => ?_
          rcases h with ⟨c, α, β, hfun⟩
          refine ⟨c, α, β, fun x y => ?_⟩
          have hW : W w x y = decide (⟨w, hw_l⟩ = x) := by
            simp only [W]
            have h1 := wiresList_getD_prefix [] C.gates (oneEach x y) w (by rw [oneEach_length]; simp; omega)
            simp only [List.nil_append] at h1
            rw [h1]
            simp only [wiresList, List.foldl_nil]
            exact oneEach_getD_left x y ⟨w, hw_l⟩
          dsimp only
          rw [hW]
          exact hfun x y
        · have hw_r : w - n < m := by omega
          refine isSep_right (n := n) (fun y => b2f (decide (⟨w - n, hw_r⟩ = y))) |> fun h => ?_
          rcases h with ⟨c, α, β, hfun⟩
          refine ⟨c, α, β, fun x y => ?_⟩
          have hW : W w x y = decide (⟨w - n, hw_r⟩ = y) := by
            simp only [W]
            have h1 := wiresList_getD_prefix [] C.gates (oneEach x y) w (by rw [oneEach_length]; simp; omega)
            simp only [List.nil_append] at h1
            rw [h1]
            simp only [wiresList, List.foldl_nil]
            have hwn : n + (w - n) = w := by omega
            have h2 := oneEach_getD_right x y ⟨w - n, hw_r⟩
            simpa [hwn] using h2
          dsimp only
          rw [hW]
          exact hfun x y
      · by_cases hw_out : w < n + m + C.gates.length
        · set j := w - (n + m)
          have hj : j < C.gates.length := by omega
          have hwj : w = n + m + j := by omega
          rw [hwj] at hDw ⊢
          rcases hwire_step j hj with ⟨hWeq, hDeq⟩
          rw [hDeq] at hDw
          have hnl_zero : (isNonlin (C.gates[j])).toNat = 0 := by omega
          have hnl_false : isNonlin (C.gates[j]) = false := by
            cases h : isNonlin (C.gates[j]) <;> simp [h] at hnl_zero ⊢
          have hmax0 : ((C.gates[j]).inputs.map D).foldr max 0 = 0 := by omega
          have hin0 : ∀ i ∈ (C.gates[j]).inputs, D i = 0 := by
            intro i hi
            exact (foldr_max_eq_zero_iff _).mp hmax0 (D i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
          have hrb_j : ∀ i ∈ (C.gates[j]).inputs, i < n + m + j := by
            intro i hi
            have h := hrb j hj i
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
            exact h hi
          rcases gate_eval_linear_of_not_nonlin (C.gates[j]) (hlen _ (List.getElem_mem hj)) hnl_false W
            with ⟨c0, cs, hcs_in, hcs_eq⟩
          have hlist_sep : ∀ (l : List (F2 × ℕ)), (∀ p ∈ l, p.2 ∈ (C.gates[j]).inputs) →
              IsSep (fun x y => (l.map fun p => p.1 * b2f (W p.2 x y)).sum) := by
            intro l hl
            induction l with
            | nil => simpa using isSep_const 0
            | cons p t iht =>
              simp only [List.map_cons, List.sum_cons]
              apply isSep_add
              · apply isSep_smul
                have hp_in := hl p (by simp)
                exact ih p.2 (hwj ▸ hrb_j p.2 hp_in) (hin0 p.2 hp_in)
              · exact iht (fun q hq => hl q (by simp [hq]))
          have htot := isSep_add (isSep_const c0) (hlist_sep cs hcs_in)
          rcases htot with ⟨c, α, β, hfun⟩
          refine ⟨c, α, β, fun x y => ?_⟩
          dsimp only
          rw [hWeq x y, hcs_eq x y]
          exact hfun x y
        · refine ⟨0, 0, 0, fun x y => ?_⟩
          have hW : W w x y = false := by
            simp only [W, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none]
            · rfl
            · rw [wiresList_length, oneEach_length]; omega
          simp [hW, b2f]
  have hMgate_rk : ∀ idx ∈ NL, (Mgate idx).rank ≤ 2 := by
    intro idx hidx
    simp only [NL, Finset.mem_filter, Finset.mem_univ, true_and] at hidx
    rcases hidx with ⟨hnl, hD1⟩
    rcases hwire_step idx.val idx.isLt with ⟨hWeq, hDeq⟩
    have hnl' : isNonlin (C.gates[idx.val]) = true := hnl
    rw [hDeq, hnl', Bool.toNat_true] at hD1
    have hmax0 : ((C.gates[idx.val]).inputs.map D).foldr max 0 = 0 := by omega
    have hin0 : ∀ i ∈ (C.gates[idx.val]).inputs, D i = 0 := by
      intro i hi
      exact (foldr_max_eq_zero_iff _).mp hmax0 (D i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
    have hfun : (fun x y => b2f (W (n + m + idx.val) x y)) =
        fun x y => b2f ((C.gates[idx.val]).op.eval ((C.gates[idx.val]).inputs.map fun i => W i x y)) := by
      funext x y; rw [hWeq x y]
    change (boxOp u v (fun x y => b2f (W (n + m + idx.val) x y))).rank ≤ 2
    rw [hfun]
    exact gate_eval_nonlin_box_rank_le_two u v (C.gates[idx.val]) hnl' W (fun i hi => hsep0 i (hin0 i hi))
  have hbox_decomp : ∀ w : ℕ, D w ≤ 1 →
      ∃ S : Finset (Fin C.gates.length), S ⊆ NL ∧
        boxOp u v (fun x y => b2f (W w x y)) = ∑ idx ∈ S, Mgate idx := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hDw
      by_cases hD0 : D w = 0
      · refine ⟨∅, Finset.empty_subset _, ?_⟩
        rcases hsep0 w hD0 with ⟨c, α, β, hfun⟩
        have heq : (fun x y => b2f (W w x y)) = fun x y => c + α x + β y :=
          funext fun x => funext fun y => hfun x y
        rw [heq, boxOp_sep, Finset.sum_empty]
      · have hD1 : D w = 1 := by omega
        by_cases hw_in : w < n + m
        · exfalso
          have h0 : D w = 0 := by
            simp only [D]
            have h1 := depthsList_getD_prefix (n + m) [] C.gates w (by simp; omega)
            simp only [List.nil_append] at h1
            rw [h1]
            simp [depthsList, List.getD_eq_getElem?_getD, hw_in]
          omega
        · by_cases hw_out : w < n + m + C.gates.length
          · set j := w - (n + m)
            have hj : j < C.gates.length := by omega
            have hwj : w = n + m + j := by omega
            rw [hwj] at hD1 ⊢
            by_cases hnl : isNonlin (C.gates[j]) = true
            · refine ⟨{⟨j, hj⟩}, ?_, ?_⟩
              · intro idx hidx
                rw [Finset.mem_singleton] at hidx
                subst hidx
                simp [NL, hnl, hD1]
              · simp [Mgate]
            · have hnl_false : isNonlin (C.gates[j]) = false := Bool.eq_false_iff.mpr hnl
              rcases hwire_step j hj with ⟨hWeq, hDeq⟩
              rw [hDeq, hnl_false] at hD1
              have hmax1 : ((C.gates[j]).inputs.map D).foldr max 0 ≤ 1 := by omega
              have hin1 : ∀ i ∈ (C.gates[j]).inputs, D i ≤ 1 := by
                intro i hi
                exact (foldr_max_le_iff _ 1).mp hmax1 (D i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
              have hrb_j : ∀ i ∈ (C.gates[j]).inputs, i < n + m + j := by
                intro i hi
                have h := hrb j hj i
                simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
                exact h hi
              rcases gate_eval_linear_of_not_nonlin (C.gates[j]) (hlen _ (List.getElem_mem hj)) hnl_false W
                with ⟨c0, cs, hcs_in, hcs_eq⟩
              have hlist_box : ∀ (l : List (F2 × ℕ)), (∀ p ∈ l, p.2 ∈ (C.gates[j]).inputs) →
                  ∃ S : Finset (Fin C.gates.length), S ⊆ NL ∧
                    boxOp u v (fun x y => (l.map fun p => p.1 * b2f (W p.2 x y)).sum) = ∑ idx ∈ S, Mgate idx := by
                intro l hl
                induction l with
                | nil =>
                  refine ⟨∅, Finset.empty_subset _, ?_⟩
                  simpa using boxOp_zero u v
                | cons p tl iht =>
                  rcases iht (fun q hq => hl q (by simp [hq])) with ⟨St, hSt_sub, hSt_eq⟩
                  have hp_in := hl p (by simp)
                  rcases ih p.2 (hwj ▸ hrb_j p.2 hp_in) (hin1 p.2 hp_in) with ⟨Sp, hSp_sub, hSp_eq⟩
                  rcases f2_cases p.1 with hp0 | hp1
                  · refine ⟨St, hSt_sub, ?_⟩
                    simp only [List.map_cons, List.sum_cons, hp0, zero_mul, zero_add]
                    exact hSt_eq
                  · refine ⟨symmDiff Sp St, ?_, ?_⟩
                    · intro idx hidx
                      rw [Finset.mem_symmDiff] at hidx
                      rcases hidx with ⟨h, _⟩ | ⟨h, _⟩
                      · exact hSp_sub h
                      · exact hSt_sub h
                    · simp only [List.map_cons, List.sum_cons, hp1, one_mul]
                      rw [boxOp_add, hSp_eq, hSt_eq, symmDiff_sum_f2]
              rcases hlist_box cs hcs_in with ⟨S, hS_sub, hS_eq⟩
              refine ⟨S, hS_sub, ?_⟩
              have hfun : (fun x y => b2f (W (n + m + j) x y)) =
                  fun x y => c0 + (cs.map fun p => p.1 * b2f (W p.2 x y)).sum :=
                funext fun x => funext fun y => by rw [hWeq x y, hcs_eq x y]
              rw [hfun, boxOp_add]
              have hc0 : boxOp u v (fun _ _ => c0) = 0 := by
                simpa using boxOp_sep u v c0 0 0
              rw [hc0, zero_add, hS_eq]
          · exfalso
            have h0 : D w = 0 := by
              simp only [D, List.getD_eq_getElem?_getD]
              rw [List.getElem?_eq_none]
              · rfl
              · rw [depthsList_length]; omega
            omega
  rcases hbox_decomp (tap 0) (htap 0).1 with ⟨S0, hS0_sub, hS0_eq⟩
  rcases hbox_decomp (tap 1) (htap 1).1 with ⟨S1, hS1_sub, hS1_eq⟩
  have hrep0 : (fun x y => b2f (W (tap 0) x y)) = fun x y => b2f (G 0 x y) := by
    funext x y
    have h := (htap 0).2 x y
    exact congrArg b2f h
  have hrep1 : (fun x y => b2f (W (tap 1) x y)) = fun x y => b2f (G 1 x y) := by
    funext x y
    have h := (htap 1).2 x y
    exact congrArg b2f h
  rw [hrep0] at hS0_eq
  rw [hrep1] at hS1_eq
  have hA_le : k ≤ 2 * S0.card := by
    rw [← hA, hS0_eq]
    exact rank_sum_le S0 Mgate (fun idx hidx => hMgate_rk idx (hS0_sub hidx))
  have hB_le : k ≤ 2 * S1.card := by
    rw [← hB, hS1_eq]
    exact rank_sum_le S1 Mgate (fun idx hidx => hMgate_rk idx (hS1_sub hidx))
  have hAB_le : k ≤ 2 * (symmDiff S0 S1).card := by
    rw [← hAB, hS0_eq, hS1_eq, symmDiff_sum_f2]
    exact rank_sum_le (symmDiff S0 S1) Mgate (fun idx hidx => by
      rw [Finset.mem_symmDiff] at hidx
      rcases hidx with ⟨h, _⟩ | ⟨h, _⟩
      · exact hMgate_rk idx (hS0_sub h)
      · exact hMgate_rk idx (hS1_sub h))
  have ha_eq : S0.card = (S0 \ S1).card + (S0 ∩ S1).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S0 S1), Finset.sdiff_union_inter]
  have hb_eq : S1.card = (S1 \ S0).card + (S0 ∩ S1).card := by
    rw [Finset.inter_comm, ← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S1 S0),
      Finset.sdiff_union_inter]
  have hab_eq : (symmDiff S0 S1).card = (S0 \ S1).card + (S1 \ S0).card :=
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  have hunion_eq : (S0 ∪ S1).card = (S0 \ S1).card + (S1 \ S0).card + (S0 ∩ S1).card := by
    have h1 : S0 ∪ S1 = (S0 \ S1) ∪ S1 := (Finset.sdiff_union_self_eq_union).symm
    rw [h1, Finset.card_union_of_disjoint disjoint_sdiff_self_left, hb_eq]
    omega
  have hunion_le : (S0 ∪ S1).card ≤ t :=
    (Finset.card_le_card (Finset.union_subset hS0_sub hS1_sub)).trans hNL_card
  omega

lemma f2_card_submodule {U : Type*} [AddCommGroup U] [Module F2 U] [Fintype U]
    (S : Submodule F2 U) [DecidablePred (· ∈ S)] :
    (Finset.univ.filter (fun x : U => x ∈ S)).card = 2 ^ Module.finrank F2 S := by
  classical
  have h1 : (Finset.univ.filter (fun x : U => x ∈ S)).card = Fintype.card S := by
    rw [Fintype.card_subtype]
  rw [h1]
  let b := Module.finBasis F2 S
  rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma exists_disjoint_image_subspace {U : Type*} [AddCommGroup U] [Module F2 U] [Fintype U]
    (Q : U ≃ₗ[F2] U) (hQ1 : Function.Bijective (LinearMap.id (R := F2) (M := U) + Q.toLinearMap))
    (s : ℕ) (hs : 2 * s ≤ Module.finrank F2 U) :
    ∃ W : Submodule F2 U, Module.finrank F2 W = s ∧ W ⊓ Submodule.map Q.toLinearMap W = ⊥ := by
  classical
  induction s with
  | zero =>
    exact ⟨⊥, finrank_bot F2 U, by simp⟩
  | succ r ih =>
    rcases ih (by omega) with ⟨W, hWdim, hWdisj⟩
    let e1 : U ≃ₗ[F2] U := LinearEquiv.ofBijective (LinearMap.id + Q.toLinearMap) hQ1
    let B1 : Submodule F2 U := W ⊔ Submodule.map Q.toLinearMap W
    let B2 : Submodule F2 U := W ⊔ Submodule.map Q.symm.toLinearMap W
    let B3 : Submodule F2 U := Submodule.comap e1.toLinearMap B1
    have hB1_dim : Module.finrank F2 B1 ≤ 2 * r := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.map Q.toLinearMap W)
      have h2 : Module.finrank F2 (Submodule.map Q.toLinearMap W) ≤ Module.finrank F2 W :=
        Submodule.finrank_map_le Q.toLinearMap W
      rw [hWdim] at h1 h2
      dsimp only [B1]
      omega
    have hB2_dim : Module.finrank F2 B2 ≤ 2 * r := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.map Q.symm.toLinearMap W)
      have h2 : Module.finrank F2 (Submodule.map Q.symm.toLinearMap W) ≤ Module.finrank F2 W :=
        Submodule.finrank_map_le Q.symm.toLinearMap W
      rw [hWdim] at h1 h2
      dsimp only [B2]
      omega
    have hB3_eq : B3 = Submodule.map e1.symm.toLinearMap B1 := by
      ext x
      simp only [B3, Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
      constructor
      · intro hx
        exact ⟨e1 x, hx, e1.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    have hB3_dim : Module.finrank F2 B3 ≤ 2 * r := by
      rw [hB3_eq]
      exact (Submodule.finrank_map_le e1.symm.toLinearMap B1).trans hB1_dim
    let F1 : Finset U := Finset.univ.filter (fun x => x ∈ B1)
    let F2s : Finset U := Finset.univ.filter (fun x => x ∈ B2)
    let F3 : Finset U := Finset.univ.filter (fun x => x ∈ B3)
    have hUcard : Fintype.card U = 2 ^ Module.finrank F2 U := by
      let b := Module.finBasis F2 U
      rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hF1 : F1.card ≤ 2 ^ (2 * r) := by
      rw [f2_card_submodule B1]
      exact Nat.pow_le_pow_right (by omega) hB1_dim
    have hF2 : F2s.card ≤ 2 ^ (2 * r) := by
      rw [f2_card_submodule B2]
      exact Nat.pow_le_pow_right (by omega) hB2_dim
    have hF3 : F3.card ≤ 2 ^ (2 * r) := by
      rw [f2_card_submodule B3]
      exact Nat.pow_le_pow_right (by omega) hB3_dim
    have hlt : (F1 ∪ F2s ∪ F3).card < (Finset.univ : Finset U).card := by
      have hu1 : (F1 ∪ F2s ∪ F3).card ≤ F1.card + F2s.card + F3.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have hpow : 2 ^ (2 * r + 2) ≤ 2 ^ Module.finrank F2 U :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : 2 ^ (2 * r + 2) = 4 * 2 ^ (2 * r) := by
        rw [Nat.pow_add]
        norm_num
        ring
      have hpos : 0 < 2 ^ (2 * r) := Nat.pos_of_ne_zero (by positivity)
      rw [Finset.card_univ, hUcard]
      omega
    have hex : ∃ v : U, v ∉ F1 ∪ F2s ∪ F3 := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset U) ⊆ F1 ∪ F2s ∪ F3 := fun x _ => h x
      have hle := Finset.card_le_card hsub
      omega
    rcases hex with ⟨v, hv⟩
    have hv1 : v ∉ B1 := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [F1, h])))
    have hv2 : v ∉ B2 := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [F2s, h])))
    have hv3 : v ∉ B3 := fun h => hv (Finset.mem_union_right _ (by simp [F3, h]))
    have hvW : v ∉ W := fun h => hv1 (Submodule.mem_sup_left h)
    have hv0 : v ≠ 0 := fun h => hvW (h ▸ W.zero_mem)
    let W' : Submodule F2 U := W ⊔ Submodule.span F2 {v}
    refine ⟨W', ?_, ?_⟩
    · have hinf : W ⊓ Submodule.span F2 {v} = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        rcases hx with ⟨hxW, hxS⟩
        change x ∈ Submodule.span F2 {v} at hxS
        rw [Submodule.mem_span_singleton] at hxS
        rcases hxS with ⟨α, rfl⟩
        rcases f2_cases α with rfl | rfl
        · simp
        · exfalso; simp only [one_smul] at hxW; exact hvW hxW
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F2 {v})
      rw [hinf, finrank_bot, add_zero, hWdim, finrank_span_singleton hv0] at hsup
      exact hsup
    · rw [Submodule.eq_bot_iff]
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      change x ∈ W ⊔ Submodule.span F2 {v} at hx1
      rw [Submodule.mem_sup] at hx1
      rcases hx1 with ⟨w1, hw1, y1, hy1, rfl⟩
      change y1 ∈ Submodule.span F2 {v} at hy1
      rw [Submodule.mem_span_singleton] at hy1
      rcases hy1 with ⟨α, rfl⟩
      change w1 + α • v ∈ Submodule.map Q.toLinearMap W' at hx2
      rw [Submodule.mem_map] at hx2
      rcases hx2 with ⟨z, hz, hz_eq⟩
      change z ∈ W ⊔ Submodule.span F2 {v} at hz
      rw [Submodule.mem_sup] at hz
      rcases hz with ⟨w2, hw2, y2, hy2, rfl⟩
      change y2 ∈ Submodule.span F2 {v} at hy2
      rw [Submodule.mem_span_singleton] at hy2
      rcases hy2 with ⟨β, rfl⟩
      simp only [map_add, map_smul, LinearEquiv.coe_coe] at hz_eq
      rcases f2_cases α with rfl | rfl <;> rcases f2_cases β with rfl | rfl
      · simp only [zero_smul, add_zero] at hz_eq ⊢
        have hmem : w1 ∈ W ⊓ Submodule.map Q.toLinearMap W :=
          ⟨hw1, ⟨w2, hw2, hz_eq⟩⟩
        rw [hWdisj] at hmem
        exact (Submodule.mem_bot F2).mp hmem
      · exfalso
        simp only [zero_smul, one_smul, add_zero] at hz_eq
        have hQv : Q v = w1 + Q w2 := by
          calc Q v = (Q w2 + Q w2) + Q v := by rw [f2_mod_add_self, zero_add]
            _ = (Q w2 + Q v) + Q w2 := by abel
            _ = w1 + Q w2 := by rw [hz_eq]
        have hv_eq : v = w2 + Q.symm w1 := by
          have h := congrArg Q.symm hQv
          simp only [LinearEquiv.symm_apply_apply, map_add] at h
          rw [add_comm] at h
          exact h
        have hmem : v ∈ B2 := by
          rw [hv_eq]
          exact Submodule.add_mem_sup hw2 ⟨w1, hw1, rfl⟩
        exact hv2 hmem
      · exfalso
        simp only [zero_smul, one_smul, add_zero] at hz_eq
        have hv_eq : v = w1 + Q w2 := by
          have h := congrArg (fun t => w1 + t) hz_eq
          rw [← add_assoc, f2_mod_add_self, zero_add] at h
          exact h.symm
        have hmem : v ∈ B1 := by
          rw [hv_eq]
          exact Submodule.add_mem_sup hw1 ⟨w2, hw2, rfl⟩
        exact hv1 hmem
      · exfalso
        simp only [one_smul] at hz_eq
        have he1v : e1 v = w1 + Q w2 := by
          have h1 : e1 v = v + Q v := rfl
          rw [h1]
          have h2 : w1 + v + (Q w2 + Q v) = 0 := by
            rw [← hz_eq]
            exact f2_mod_add_self _
          have h3 : (v + Q v) + (w1 + Q w2) = 0 := by
            calc (v + Q v) + (w1 + Q w2) = w1 + v + (Q w2 + Q v) := by abel
              _ = 0 := h2
          have h4 := congrArg (fun t => t + (w1 + Q w2)) h3
          rw [add_assoc, f2_mod_add_self, add_zero, zero_add] at h4
          exact h4
        have hmem : v ∈ B3 := by
          change e1 v ∈ B1
          rw [he1v]
          exact Submodule.add_mem_sup hw1 ⟨w2, hw2, rfl⟩
        exact hv3 hmem

lemma rank_decomp_endomorphism {U : Type*} [AddCommGroup U] [Module F2 U] [Fintype U]
    (P : U ≃ₗ[F2] U) (hIP : Function.Bijective (LinearMap.id (R := F2) (M := U) + P.toLinearMap)) :
    let k := Module.finrank F2 U
    ∃ (a b c : ℕ) (T : U →ₗ[F2] U),
      a + b + c = (3 * ((k + 1) / 2) + 1) / 2 ∧
      Module.finrank F2 (LinearMap.range T) ≤ 2 * c ∧
      Module.finrank F2 (LinearMap.range (LinearMap.id + T)) ≤ 2 * a ∧
      Module.finrank F2 (LinearMap.range (P.toLinearMap + T)) ≤ 2 * b := by
  classical
  intro k
  let c : ℕ := (k + 1) / 4
  let a : ℕ := (k + 3) / 4
  let b : ℕ := (k + 3) / 4
  let s : ℕ := min (k / 2) (2 * c)
  have habc : a + b + c = (3 * ((k + 1) / 2) + 1) / 2 := by omega
  have hs_le : 2 * s ≤ k := by omega
  have hs_2c : s ≤ 2 * c := by omega
  have hks_2a : k - s ≤ 2 * a := by omega
  have hks_2b : k - s ≤ 2 * b := by omega
  let eIP : U ≃ₗ[F2] U := LinearEquiv.ofBijective (LinearMap.id (R := F2) (M := U) + P.toLinearMap) hIP
  let Q : U ≃ₗ[F2] U := P.trans eIP.symm
  have hIP_Q : ∀ x : U, x + P x = eIP x := fun _ => rfl
  have heIP_Q : ∀ x : U, eIP (Q x) = P x := fun x => eIP.apply_symm_apply (P x)
  have hIQ_eq : LinearMap.id (R := F2) (M := U) + Q.toLinearMap = eIP.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply eIP.injective
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_add,
      heIP_Q, LinearEquiv.apply_symm_apply]
    change (x + P x) + P x = x
    rw [add_assoc, f2_mod_add_self, add_zero]
  have hQ1 : Function.Bijective (LinearMap.id (R := F2) (M := U) + Q.toLinearMap) := by
    rw [hIQ_eq]
    exact eIP.symm.bijective
  rcases exists_disjoint_image_subspace Q hQ1 s hs_le with ⟨W, hWdim, hWdisj⟩
  let V : Submodule F2 U := Submodule.map Q.toLinearMap W
  have hVdim : Module.finrank F2 V = s := by
    have eWV : W ≃ₗ[F2] V := LinearEquiv.ofBijective
      ((Q.toLinearMap.comp W.subtype).codRestrict V (fun w => ⟨w.1, w.2, rfl⟩))
      ⟨fun w1 w2 h => Subtype.ext (Q.injective (congrArg Subtype.val h)),
       fun ⟨y, x, hx, hy⟩ => ⟨⟨x, hx⟩, Subtype.ext hy⟩⟩
    rw [← eWV.finrank_eq, hWdim]
  rcases Submodule.exists_isCompl (W ⊔ V) with ⟨L, hL⟩
  let Wext : Submodule F2 U := W ⊔ L
  have hCompl : IsCompl Wext V := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro x ⟨hxWext, hxV⟩
      change x ∈ W ⊔ L at hxWext
      rw [Submodule.mem_sup] at hxWext
      rcases hxWext with ⟨w, hw, l, hl, rfl⟩
      have hl_mem : l ∈ (W ⊔ V) ⊓ L := by
        refine ⟨?_, hl⟩
        have hl_eq : l = w + (w + l) := by
          rw [← add_assoc, f2_mod_add_self, zero_add]
        rw [hl_eq]
        exact Submodule.add_mem_sup hw hxV
      rw [hL.inf_eq_bot] at hl_mem
      have hl0 : l = 0 := (Submodule.mem_bot F2).mp hl_mem
      subst hl0
      rw [add_zero] at hxV ⊢
      have hwV : w ∈ W ⊓ V := ⟨hw, hxV⟩
      rw [hWdisj] at hwV
      exact (Submodule.mem_bot F2).mp hwV
    · rw [codisjoint_iff]
      calc Wext ⊔ V = W ⊔ L ⊔ V := rfl
        _ = (W ⊔ V) ⊔ L := by rw [sup_right_comm]
        _ = ⊤ := hL.sup_eq_top
  let T : U →ₗ[F2] U := V.subtype.comp (Submodule.projectionOnto V Wext hCompl.symm)
  have hT_on_V : ∀ y : U, y ∈ V → T y = y := fun y hy => by
    simp only [T, LinearMap.comp_apply, Submodule.coe_subtype]
    have h := Submodule.projectionOnto_apply_left hCompl.symm ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hT_on_W : ∀ w : U, w ∈ W → T w = 0 := fun w hw => by
    simp only [T, LinearMap.comp_apply, Submodule.coe_subtype]
    have hw' : w ∈ Wext := Submodule.mem_sup_left hw
    have h := Submodule.projectionOnto_apply_right hCompl.symm ⟨w, hw'⟩
    exact congrArg Subtype.val h
  refine ⟨a, b, c, T, habc, ?_, ?_, ?_⟩
  · have hsub : LinearMap.range T ≤ V := by
      rintro _ ⟨x, rfl⟩
      exact (Submodule.projectionOnto V Wext hCompl.symm x).2
    exact (Submodule.finrank_mono hsub).trans (by omega)
  · have hsub : V ≤ LinearMap.ker (LinearMap.id + T) := by
      intro y hy
      rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hT_on_V y hy]
      exact f2_mod_add_self y
    have hker := Submodule.finrank_mono hsub
    have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id + T)
    omega
  · let φ : W →ₗ[F2] U := (LinearMap.id + Q.toLinearMap).comp W.subtype
    have hφ_inj : Function.Injective φ :=
      hQ1.1.comp Subtype.val_injective
    have hφ_dim : Module.finrank F2 (LinearMap.range φ) = s := by
      have e := LinearEquiv.ofInjective φ hφ_inj
      rw [← e.finrank_eq, hWdim]
    have hsub : LinearMap.range φ ≤ LinearMap.ker (P.toLinearMap + T) := by
      rintro _ ⟨⟨w, hw⟩, rfl⟩
      rw [LinearMap.mem_ker]
      simp only [φ, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.add_apply,
        LinearMap.id_apply, LinearEquiv.coe_coe, map_add]
      have hQwV : Q w ∈ V := ⟨w, hw, rfl⟩
      rw [hT_on_W w hw, hT_on_V (Q w) hQwV, add_zero]
      have hPQ : Q w + P (Q w) = P w := heIP_Q w
      calc P w + (P (Q w) + Q w) = P w + (Q w + P (Q w)) := by abel
        _ = P w + P w := by rw [hPQ]
        _ = 0 := f2_mod_add_self _
    have hker := Submodule.finrank_mono hsub
    have hrn := LinearMap.finrank_range_add_finrank_ker (P.toLinearMap + T)
    omega

lemma rank_decomp_matrices {n m k : ℕ} (A B : Matrix (Fin n) (Fin m) F2)
    (hA : A.rank = k) (hB : B.rank = k) (hAB : (A + B).rank = k)
    (hcols : (Matrix.fromCols A B).rank = k) (hrows : (Matrix.fromRows A B).rank = k) :
    ∃ (a b c : ℕ) (C : Matrix (Fin n) (Fin m) F2),
      a + b + c = (3 * ((k + 1) / 2) + 1) / 2 ∧
      C.rank ≤ 2 * c ∧ (A + C).rank ≤ 2 * a ∧ (B + C).rank ≤ 2 * b := by
  classical
  have hrange_A_le : LinearMap.range A.mulVecLin ≤ LinearMap.range (Matrix.fromCols A B).mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine ⟨Sum.elim x 0, ?_⟩
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have hrange_B_le : LinearMap.range B.mulVecLin ≤ LinearMap.range (Matrix.fromCols A B).mulVecLin := by
    rintro _ ⟨y, rfl⟩
    refine ⟨Sum.elim 0 y, ?_⟩
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  have hrange_A_eq : LinearMap.range A.mulVecLin = LinearMap.range (Matrix.fromCols A B).mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hrange_A_le (by exact hA.trans hcols.symm)
  have hrange_B_eq : LinearMap.range B.mulVecLin = LinearMap.range (Matrix.fromCols A B).mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hrange_B_le (by exact hB.trans hcols.symm)
  have hrange_eq : LinearMap.range B.mulVecLin = LinearMap.range A.mulVecLin :=
    hrange_B_eq.trans hrange_A_eq.symm
  have hker_rows : LinearMap.ker (Matrix.fromRows A B).mulVecLin =
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_inf]
    constructor
    · intro hx
      constructor
      · funext i
        have h := congrFun hx (Sum.inl i)
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inl] using h
      · funext i
        have h := congrFun hx (Sum.inr i)
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inr] using h
    · rintro ⟨hAx, hBx⟩
      funext s
      cases s with
      | inl i =>
        have h := congrFun hAx i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inl] using h
      | inr i =>
        have h := congrFun hBx i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inr] using h
  have hker_A_dim : Module.finrank F2 (LinearMap.ker A.mulVecLin) = m - k := by
    have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrn
    change Module.finrank F2 (LinearMap.range A.mulVecLin) = k at hA
    omega
  have hker_B_dim : Module.finrank F2 (LinearMap.ker B.mulVecLin) = m - k := by
    have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrn
    change Module.finrank F2 (LinearMap.range B.mulVecLin) = k at hB
    omega
  have hker_rows_dim : Module.finrank F2 (LinearMap.ker (Matrix.fromRows A B).mulVecLin) = m - k := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.fromRows A B).mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrn
    change Module.finrank F2 (LinearMap.range (Matrix.fromRows A B).mulVecLin) = k at hrows
    omega
  have hker_A_eq : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = LinearMap.ker A.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [← hker_rows, hker_rows_dim, hker_A_dim])
  have hker_B_eq : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = LinearMap.ker B.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [← hker_rows, hker_rows_dim, hker_B_dim])
  have hker_eq : LinearMap.ker B.mulVecLin = LinearMap.ker A.mulVecLin :=
    hker_B_eq.symm.trans hker_A_eq
  let K0 : Submodule F2 (Fin m → F2) := LinearMap.ker A.mulVecLin
  let W : Submodule F2 (Fin n → F2) := LinearMap.range A.mulVecLin
  rcases Submodule.exists_isCompl K0 with ⟨U, hKU⟩
  have hK0_dim : Module.finrank F2 K0 = m - k := hker_A_dim
  have hU_dim : Module.finrank F2 U = k := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K0 U
    rw [hKU.sup_eq_top, hKU.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_pi, Fintype.card_fin, hK0_dim] at h1
    have hA_le : k ≤ m := by
      have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
      rw [Module.finrank_pi, Fintype.card_fin] at hrn
      change Module.finrank F2 (LinearMap.range A.mulVecLin) = k at hA
      omega
    omega
  have hW_dim : Module.finrank F2 W = k := hA
  let AU : U →ₗ[F2] W := (A.mulVecLin.comp U.subtype).codRestrict W (fun u => ⟨u.1, rfl⟩)
  let BU : U →ₗ[F2] W := (B.mulVecLin.comp U.subtype).codRestrict W (fun u => by
    change B.mulVecLin u.1 ∈ LinearMap.range A.mulVecLin
    rw [← hrange_eq]
    exact ⟨u.1, rfl⟩)
  have hAU_inj : Function.Injective AU := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, huU⟩ huK
    have huA : u ∈ K0 := congrArg Subtype.val (LinearMap.mem_ker.mp huK)
    have hu0 : u ∈ K0 ⊓ U := ⟨huA, huU⟩
    rw [hKU.inf_eq_bot] at hu0
    exact Subtype.ext ((Submodule.mem_bot F2).mp hu0)
  have hBU_inj : Function.Injective BU := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, huU⟩ huK
    have huB : u ∈ LinearMap.ker B.mulVecLin := congrArg Subtype.val (LinearMap.mem_ker.mp huK)
    rw [hker_eq] at huB
    have hu0 : u ∈ K0 ⊓ U := ⟨huB, huU⟩
    rw [hKU.inf_eq_bot] at hu0
    exact Subtype.ext ((Submodule.mem_bot F2).mp hu0)
  have hAU_bij : Function.Bijective AU := by
    refine ⟨hAU_inj, ?_⟩
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have e := LinearEquiv.ofInjective AU hAU_inj
    rw [← e.finrank_eq, hU_dim, hW_dim]
  have hBU_bij : Function.Bijective BU := by
    refine ⟨hBU_inj, ?_⟩
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have e := LinearEquiv.ofInjective BU hBU_inj
    rw [← e.finrank_eq, hU_dim, hW_dim]
  let eAU : U ≃ₗ[F2] W := LinearEquiv.ofBijective AU hAU_bij
  let eBU : U ≃ₗ[F2] W := LinearEquiv.ofBijective BU hBU_bij
  let P : U ≃ₗ[F2] U := eBU.trans eAU.symm
  have hker_AB : LinearMap.ker (A + B).mulVecLin = K0 := by
    have hle : K0 ≤ LinearMap.ker (A + B).mulVecLin := by
      intro x hx
      have hxB : x ∈ LinearMap.ker B.mulVecLin := hker_eq.symm ▸ hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_add, LinearMap.add_apply,
        LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp hxB, add_zero]
    have hdim_AB : Module.finrank F2 (LinearMap.ker (A + B).mulVecLin) = m - k := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (A + B).mulVecLin
      rw [Module.finrank_pi, Fintype.card_fin] at hrn
      change Module.finrank F2 (LinearMap.range (A + B).mulVecLin) = k at hAB
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hIP_inj : Function.Injective (LinearMap.id (R := F2) (M := U) + P.toLinearMap) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, huU⟩ huK
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe] at huK
    have h1 := congrArg eAU huK
    simp only [map_add, map_zero, P, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h1
    have h2 : (A + B).mulVecLin u = 0 := by
      rw [Matrix.mulVecLin_add, LinearMap.add_apply]
      exact congrArg Subtype.val h1
    have huK0 : u ∈ K0 := by rw [← hker_AB]; exact h2
    have hu0 : u ∈ K0 ⊓ U := ⟨huK0, huU⟩
    rw [hKU.inf_eq_bot] at hu0
    exact Subtype.ext ((Submodule.mem_bot F2).mp hu0)
  have hIP_bij : Function.Bijective (LinearMap.id (R := F2) (M := U) + P.toLinearMap) := by
    refine ⟨hIP_inj, ?_⟩
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have e := LinearEquiv.ofInjective (LinearMap.id (R := F2) (M := U) + P.toLinearMap) hIP_inj
    exact e.finrank_eq.symm
  rcases rank_decomp_endomorphism P hIP_bij with ⟨a, b, c, T, habc, hT, hIT, hPT⟩
  rw [hU_dim] at habc
  let projU : (Fin m → F2) →ₗ[F2] U := Submodule.projectionOnto U K0 hKU.symm
  let Clin : (Fin m → F2) →ₗ[F2] (Fin n → F2) := W.subtype.comp (eAU.toLinearMap.comp (T.comp projU))
  let C : Matrix (Fin n) (Fin m) F2 := LinearMap.toMatrix' Clin
  have hC_lin : C.mulVecLin = Clin := Matrix.toLin'_toMatrix' Clin
  have hproj_decomp : ∀ x : Fin m → F2, x - (projU x).1 ∈ K0 := by
    intro x
    have hmem : x ∈ K0 ⊔ U := by rw [hKU.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hmem
    rcases hmem with ⟨k0, hk0, u0, hu0, rfl⟩
    have hp : projU (k0 + u0) = ⟨u0, hu0⟩ := by
      simp only [projU, map_add, Submodule.projectionOnto_apply_right hKU.symm ⟨k0, hk0⟩,
        Submodule.projectionOnto_apply_left hKU.symm ⟨u0, hu0⟩, zero_add]
    rw [hp]
    simpa using hk0
  have hA_proj : A.mulVecLin = W.subtype.comp (eAU.toLinearMap.comp projU) := by
    apply LinearMap.ext; intro x
    have hk := hproj_decomp x
    have h0 : A.mulVecLin (x - (projU x).1) = 0 := hk
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    rfl
  have hB_proj : B.mulVecLin = W.subtype.comp (eAU.toLinearMap.comp (P.toLinearMap.comp projU)) := by
    apply LinearMap.ext; intro x
    have hk : x - (projU x).1 ∈ LinearMap.ker B.mulVecLin := hker_eq.symm ▸ hproj_decomp x
    have h0 : B.mulVecLin (x - (projU x).1) = 0 := hk
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, P, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  have hlift_rk : ∀ L : U →ₗ[F2] U,
      Module.finrank F2 (LinearMap.range (W.subtype.comp (eAU.toLinearMap.comp (L.comp projU)))) ≤
        Module.finrank F2 (LinearMap.range L) := by
    intro L
    have h1 : Module.finrank F2 (LinearMap.range (W.subtype.comp (eAU.toLinearMap.comp (L.comp projU)))) ≤
        Module.finrank F2 (LinearMap.range (L.comp projU)) := by
      rw [LinearMap.range_comp, LinearMap.range_comp]
      exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_map_le _ _)
    have h2 : LinearMap.range (L.comp projU) ≤ LinearMap.range L := by
      rintro _ ⟨x, rfl⟩
      exact ⟨projU x, rfl⟩
    exact h1.trans (Submodule.finrank_mono h2)
  refine ⟨a, b, c, C, habc, ?_, ?_, ?_⟩
  · change Module.finrank F2 (LinearMap.range C.mulVecLin) ≤ 2 * c
    rw [hC_lin]
    exact (hlift_rk T).trans hT
  · change Module.finrank F2 (LinearMap.range (A + C).mulVecLin) ≤ 2 * a
    rw [Matrix.mulVecLin_add, hC_lin, hA_proj]
    have heq : W.subtype.comp (eAU.toLinearMap.comp projU) +
        W.subtype.comp (eAU.toLinearMap.comp (T.comp projU)) =
        W.subtype.comp (eAU.toLinearMap.comp ((LinearMap.id + T).comp projU)) := by
      apply LinearMap.ext; intro x; simp [map_add]
    rw [heq]
    exact (hlift_rk (LinearMap.id + T)).trans hIT
  · change Module.finrank F2 (LinearMap.range (B + C).mulVecLin) ≤ 2 * b
    rw [Matrix.mulVecLin_add, hC_lin, hB_proj]
    have heq : W.subtype.comp (eAU.toLinearMap.comp (P.toLinearMap.comp projU)) +
        W.subtype.comp (eAU.toLinearMap.comp (T.comp projU)) =
        W.subtype.comp (eAU.toLinearMap.comp ((P.toLinearMap + T).comp projU)) := by
      apply LinearMap.ext; intro x; simp [map_add]
    rw [heq]
    exact (hlift_rk (P.toLinearMap + T)).trans hPT

lemma matrix_rank_le_pairs {n m r : ℕ} (M : Matrix (Fin n) (Fin m) F2) (hrk : M.rank ≤ 2 * r) :
    ∃ (u1 u2 : Fin r → Fin n → F2) (v1 v2 : Fin r → Fin m → F2),
      ∀ x y, M x y = ∑ i : Fin r, (u1 i x * v1 i y + u2 i x * v2 i y) := by
  classical
  let b := Module.finBasis F2 (LinearMap.range M.mulVecLin)
  let d := Module.finrank F2 (LinearMap.range M.mulVecLin)
  have hd : d ≤ 2 * r := hrk
  let U : Fin (2 * r) → Fin n → F2 := fun t =>
    if ht : t.val < d then (b ⟨t.val, ht⟩).1 else 0
  let V : Fin (2 * r) → Fin m → F2 := fun t y =>
    if ht : t.val < d then b.repr ⟨M.mulVecLin (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ ⟨t.val, ht⟩ else 0
  have hM : ∀ x y, M x y = ∑ t : Fin (2 * r), U t x * V t y := by
    intro x y
    have hcol : M x y = M.mulVecLin (Pi.single y 1) x := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single y]
      · simp
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · intro hm; exact absurd (Finset.mem_univ y) hm
    rw [hcol]
    have hrepr := b.sum_repr ⟨M.mulVecLin (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩
    have hval : (∑ s : Fin d, b.repr ⟨M.mulVecLin (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ s * (b s).1 x) =
        M.mulVecLin (Pi.single y 1) x := by
      have hsub : (∑ s : Fin d, (LinearMap.range M.mulVecLin).subtype
          (b.repr ⟨M.mulVecLin (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ s • b s)) =
          M.mulVecLin (Pi.single y 1) := by
        rw [← map_sum, hrepr]
        rfl
      have hx := congrFun hsub x
      simpa only [Finset.sum_apply, map_smul, Submodule.coe_subtype, Pi.smul_apply, smul_eq_mul] using hx
    rw [← hval]
    have hsum_eq : ∑ s : Fin d, b.repr ⟨M.mulVecLin (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ s * (b s).1 x =
        ∑ t : Fin (2 * r), U t x * V t y := by
      have hbij : ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * r) => t.val < d), U t x * V t y =
          ∑ s : Fin d, b.repr ⟨M.mulVecLin (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ s * (b s).1 x := by
        refine Finset.sum_bij'
          (fun (t : Fin (2 * r)) (ht : t ∈ Finset.univ.filter (fun t : Fin (2 * r) => t.val < d)) =>
            (⟨t.val, (Finset.mem_filter.mp ht).2⟩ : Fin d))
          (fun (s : Fin d) _ => (⟨s.val, Nat.lt_of_lt_of_le s.isLt hd⟩ : Fin (2 * r)))
          ?_ ?_ ?_ ?_ ?_
        · intro t ht; exact Finset.mem_univ _
        · intro s _; simp [s.isLt]
        · intro t ht; ext; rfl
        · intro s _; ext; rfl
        · intro t ht
          have hlt : t.val < d := (Finset.mem_filter.mp ht).2
          simp only [U, V, hlt, ↓reduceDIte]
          ring
      rw [← hbij]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro t _ ht
      have hge : ¬ t.val < d := by simpa using ht
      simp [U, V, hge]
    exact hsum_eq
  refine ⟨fun i => U ⟨2 * i.val, by omega⟩, fun i => U ⟨2 * i.val + 1, by omega⟩,
    fun i => V ⟨2 * i.val, by omega⟩, fun i => V ⟨2 * i.val + 1, by omega⟩, fun x y => ?_⟩
  rw [hM x y]
  let e : Fin r × Fin 2 ≃ Fin (2 * r) :=
    { toFun := fun p => ⟨2 * p.1.val + p.2.val, by omega⟩
      invFun := fun t => (⟨t.val / 2, by omega⟩, ⟨t.val % 2, by omega⟩)
      left_inv := fun ⟨i, j⟩ => by
        ext
        · simp only []; omega
        · simp only []; omega
      right_inv := fun t => by
        ext; simp only []; omega }
  rw [← Equiv.sum_comp e]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp [e]

def validGates (width : ℕ) (gs : List Gate) : Prop :=
  ReadsBack width ⟨gs, 0⟩ ∧ ∀ g ∈ gs, g.inputs.length ≤ 2

lemma validGates_nil (width : ℕ) : validGates width [] := by
  refine ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩

lemma validGates_snoc {width : ℕ} {gs : List Gate} (hv : validGates width gs) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hin : ∀ a ∈ g.inputs, a < width + gs.length) :
    validGates width (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    simp only [gateAt] at hi
    by_cases hlt : j < gs.length
    · rw [list_getD_append_left gs [g] j _ hlt] at hi
      exact hv.1 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [list_getD_append_right gs [g] gs.length _ (le_refl _), Nat.sub_self,
        list_getD_singleton_zero] at hi
      exact hin i hi
  · intro g' hg'
    rw [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hv.2 g' hg'
    · exact hlen

lemma isNonlin_or_nil : isNonlin ⟨.or, []⟩ = false := rfl
lemma isNonlin_and_nil : isNonlin ⟨.and, []⟩ = false := rfl
lemma isNonlin_not_one (w : ℕ) : isNonlin ⟨.not, [w]⟩ = false := rfl
lemma isNonlin_mod2_two (w1 w2 : ℕ) : isNonlin ⟨.mod 2, [w1, w2]⟩ = false := by
  simp [isNonlin]; decide
lemma isNonlin_and_two (w1 w2 : ℕ) : isNonlin ⟨.and, [w1, w2]⟩ = true := by
  simp [isNonlin]; decide

lemma mod2_two_eval (a b : Bool) : GateOp.eval (.mod 2) [a, b] = !(xor a b) := by
  cases a <;> cases b <;> decide

lemma build_const_false {n m : ℕ} (gs : List Gate) (hv : validGates (n + m) gs) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 = 0 ∧
      ∀ (x : Fin n) (y : Fin m), b2f ((wiresList gs' (oneEach x y)).getD w false) = 0 := by
  let g : Gate := ⟨.or, []⟩
  refine ⟨gs ++ [g], n + m + gs.length, ⟨[g], rfl⟩,
    validGates_snoc hv g (by simp [g]) (by simp [g]), ?_, ?_, ?_, ?_⟩
  · simp [g, List.countP_append, isNonlin_or_nil]
  · simp
  · rw [depthsList_getD_last]; simp [g, isNonlin_or_nil]
  · intro x y
    rw [← oneEach_length x y, wiresList_getD_last]
    rfl

lemma build_const_true {n m : ℕ} (gs : List Gate) (hv : validGates (n + m) gs) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 = 0 ∧
      ∀ (x : Fin n) (y : Fin m), b2f ((wiresList gs' (oneEach x y)).getD w false) = 1 := by
  let g : Gate := ⟨.and, []⟩
  refine ⟨gs ++ [g], n + m + gs.length, ⟨[g], rfl⟩,
    validGates_snoc hv g (by simp [g]) (by simp [g]), ?_, ?_, ?_, ?_⟩
  · simp [g, List.countP_append, isNonlin_and_nil]
  · simp
  · rw [depthsList_getD_last]; simp [g, isNonlin_and_nil]
  · intro x y
    rw [← oneEach_length x y, wiresList_getD_last]
    rfl

lemma build_xor {n m : ℕ} (gs : List Gate) (hv : validGates (n + m) gs)
    (w1 w2 : ℕ) (hw1 : w1 < n + m + gs.length) (hw2 : w2 < n + m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 =
        max ((depthsList (n + m) gs).getD w1 0) ((depthsList (n + m) gs).getD w2 0) ∧
      ∀ (x : Fin n) (y : Fin m), b2f ((wiresList gs' (oneEach x y)).getD w false) =
        b2f ((wiresList gs (oneEach x y)).getD w1 false) +
        b2f ((wiresList gs (oneEach x y)).getD w2 false) := by
  let g1 : Gate := ⟨.mod 2, [w1, w2]⟩
  let gs1 := gs ++ [g1]
  have hv1 : validGates (n + m) gs1 :=
    validGates_snoc hv g1 (by simp [g1]) (by intro a ha; simp [g1] at ha; rcases ha with rfl | rfl <;> assumption)
  let mid := n + m + gs.length
  let g2 : Gate := ⟨.not, [mid]⟩
  let gs2 := gs1 ++ [g2]
  have hmid : mid < n + m + gs1.length := by simp [mid, gs1]
  have hv2 : validGates (n + m) gs2 :=
    validGates_snoc hv1 g2 (by simp [g2]) (by intro a ha; simp [g2] at ha; subst ha; exact hmid)
  refine ⟨gs2, n + m + gs1.length, ⟨[g1, g2], by simp [gs2, gs1]⟩, hv2, ?_, ?_, ?_, ?_⟩
  · simp [gs2, gs1, g1, g2, List.countP_append, isNonlin_mod2_two, isNonlin_not_one]
  · simp [gs2]
  · simp only [gs2]
    rw [depthsList_getD_last]
    simp only [g2, isNonlin_not_one, Bool.toNat_false, add_zero, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Nat.max_zero]
    simp only [mid, gs1]
    rw [depthsList_getD_last]
    simp [g1, isNonlin_mod2_two]
  · intro x y
    have hlen : (oneEach x y).length = n + m := oneEach_length x y
    simp only [gs2]
    rw [← hlen, wiresList_getD_last]
    simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    simp only [mid, gs1]
    rw [← hlen, wiresList_getD_last]
    simp only [g1, List.map_cons, List.map_nil, mod2_two_eval, Bool.not_not]
    exact b2f_xor _ _

lemma build_and {n m : ℕ} (gs : List Gate) (hv : validGates (n + m) gs)
    (w1 w2 : ℕ) (hw1 : w1 < n + m + gs.length) (hw2 : w2 < n + m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin + 1 ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 =
        max ((depthsList (n + m) gs).getD w1 0) ((depthsList (n + m) gs).getD w2 0) + 1 ∧
      ∀ (x : Fin n) (y : Fin m), b2f ((wiresList gs' (oneEach x y)).getD w false) =
        b2f ((wiresList gs (oneEach x y)).getD w1 false) *
        b2f ((wiresList gs (oneEach x y)).getD w2 false) := by
  let g : Gate := ⟨.and, [w1, w2]⟩
  refine ⟨gs ++ [g], n + m + gs.length, ⟨[g], rfl⟩,
    validGates_snoc hv g (by simp [g]) (by intro a ha; simp [g] at ha; rcases ha with rfl | rfl <;> assumption),
    ?_, ?_, ?_, ?_⟩
  · simp [g, List.countP_append, isNonlin_and_two]
  · simp
  · rw [depthsList_getD_last]
    simp [g, isNonlin_and_two]
  · intro x y
    rw [← oneEach_length x y, wiresList_getD_last]
    simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    exact b2f_and _ _

lemma build_xor_list {n m : ℕ} (dmax : ℕ) (gs : List Gate) (hv : validGates (n + m) gs)
    (ws : List ℕ) (hws_lt : ∀ w ∈ ws, w < n + m + gs.length)
    (hws_d : ∀ w ∈ ws, (depthsList (n + m) gs).getD w 0 ≤ dmax) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 ≤ dmax ∧
      ∀ (x : Fin n) (y : Fin m), b2f ((wiresList gs' (oneEach x y)).getD w false) =
        (ws.map fun wi => b2f ((wiresList gs (oneEach x y)).getD wi false)).sum := by
  induction ws generalizing gs with
  | nil =>
    rcases build_const_false gs hv with ⟨gs', w, hext, hv', hcnt, hw, hd, hval⟩
    exact ⟨gs', w, hext, hv', hcnt, hw, by omega, fun x y => by simpa using hval x y⟩
  | cons a tl ih =>
    have ha_lt : a < n + m + gs.length := hws_lt a (by simp)
    have ha_d : (depthsList (n + m) gs).getD a 0 ≤ dmax := hws_d a (by simp)
    rcases ih gs hv (fun w hw => hws_lt w (by simp [hw])) (fun w hw => hws_d w (by simp [hw]))
      with ⟨gs1, wtl, ⟨ext1, rfl⟩, hv1, hcnt1, hwtl_lt, hwtl_d, hwtl_val⟩
    have ha_lt1 : a < n + m + (gs ++ ext1).length := by rw [List.length_append]; omega
    rcases build_xor (gs ++ ext1) hv1 a wtl ha_lt1 hwtl_lt
      with ⟨gs2, wout, ⟨ext2, rfl⟩, hv2, hcnt2, hwout_lt, hwout_d, hwout_val⟩
    refine ⟨gs ++ ext1 ++ ext2, wout, ⟨ext1 ++ ext2, by simp⟩, hv2,
      by rw [hcnt2, hcnt1], hwout_lt, ?_, ?_⟩
    · rw [hwout_d, depthsList_getD_prefix (n + m) gs ext1 a ha_lt]
      exact Nat.max_le.mpr ⟨ha_d, hwtl_d⟩
    · intro x y
      rw [hwout_val x y, hwtl_val x y, wiresList_getD_prefix gs ext1 (oneEach x y) a
        (by rw [oneEach_length]; exact ha_lt)]
      simp

lemma build_sep {n m : ℕ} (gs : List Gate) (hv : validGates (n + m) gs)
    (c : F2) (α : Fin n → F2) (β : Fin m → F2) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 = 0 ∧
      ∀ x y, b2f ((wiresList gs' (oneEach x y)).getD w false) = c + α x + β y := by
  rcases build_const_true gs hv with ⟨gs1, wT, ⟨ext1, rfl⟩, hv1, hcnt1, hwT_lt, hwT_d, hwT_val⟩
  let wsC : List ℕ := if c = 1 then [wT] else []
  let wsX : List ℕ := ((List.finRange n).filter (fun i => decide (α i = 1))).map (fun i => i.val)
  let wsY : List ℕ := ((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => n + j.val)
  let ws : List ℕ := wsC ++ wsX ++ wsY
  have hws_lt : ∀ w ∈ ws, w < n + m + (gs ++ ext1).length := by
    intro w hw
    simp only [ws, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · by_cases hc : c = 1
      · simp [wsC, hc] at hw; subst hw; exact hwT_lt
      · simp [wsC, hc] at hw
    · simp only [wsX, List.mem_map, List.mem_filter] at hw
      rcases hw with ⟨i, _, rfl⟩
      omega
    · simp only [wsY, List.mem_map, List.mem_filter] at hw
      rcases hw with ⟨j, _, rfl⟩
      omega
  have hws_d : ∀ w ∈ ws, (depthsList (n + m) (gs ++ ext1)).getD w 0 ≤ 0 := by
    intro w hw
    simp only [ws, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · by_cases hc : c = 1
      · simp [wsC, hc] at hw; subst hw; omega
      · simp [wsC, hc] at hw
    · simp only [wsX, List.mem_map, List.mem_filter] at hw
      rcases hw with ⟨i, _, rfl⟩
      have h1 := depthsList_getD_prefix (n + m) [] (gs ++ ext1) i.val (by simp; omega)
      simp only [List.nil_append] at h1
      rw [h1]
      have hlt : i.val < n + m := by omega
      simp [depthsList, List.getD_eq_getElem?_getD, hlt]
    · simp only [wsY, List.mem_map, List.mem_filter] at hw
      rcases hw with ⟨j, _, rfl⟩
      have h1 := depthsList_getD_prefix (n + m) [] (gs ++ ext1) (n + j.val) (by simp)
      simp only [List.nil_append] at h1
      rw [h1]
      have hlt : n + j.val < n + m := by omega
      simp [depthsList, List.getD_eq_getElem?_getD, hlt]
  rcases build_xor_list 0 (gs ++ ext1) hv1 ws hws_lt hws_d
    with ⟨gs2, wout, ⟨ext2, rfl⟩, hv2, hcnt2, hwout_lt, hwout_d, hwout_val⟩
  refine ⟨gs ++ ext1 ++ ext2, wout, ⟨ext1 ++ ext2, by simp⟩, hv2,
    by rw [hcnt2, hcnt1], hwout_lt, Nat.eq_zero_of_le_zero hwout_d, ?_⟩
  intro x y
  rw [hwout_val x y]
  simp only [ws, List.map_append, List.sum_append]
  have h01 : (0 : F2) ≠ 1 := by decide
  have hsumC : (wsC.map fun wi => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD wi false)).sum = c := by
    rcases f2_cases c with rfl | rfl
    · simp [wsC, h01]
    · simp only [wsC, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact hwT_val x y
  have hsumX : (wsX.map fun wi => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD wi false)).sum = α x := by
    simp only [wsX, List.map_map]
    change (((List.finRange n).filter (fun i => decide (α i = 1))).map
      (fun i => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD i.val false))).sum = α x
    have hmap : (((List.finRange n).filter (fun i => decide (α i = 1))).map
        (fun i => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD i.val false))) =
        (((List.finRange n).filter (fun i => decide (α i = 1))).map (fun i => b2f (decide (i = x)))) := by
      refine List.map_congr_left fun i _ => ?_
      have h1 := wiresList_getD_prefix [] (gs ++ ext1) (oneEach x y) i.val
        (by rw [oneEach_length]; simp; omega)
      simp only [List.nil_append] at h1
      rw [h1]
      simp only [wiresList, List.foldl_nil]
      rw [oneEach_getD_left x y i]
    rw [hmap]
    have hnodup : ((List.finRange n).filter (fun i => decide (α i = 1))).Nodup :=
      List.Nodup.filter _ (List.nodup_finRange n)
    rw [← List.sum_toFinset _ hnodup]
    have hset : ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset =
        Finset.univ.filter (fun i : Fin n => α i = 1) := by
      ext i; simp
    rw [hset, Finset.sum_filter]
    rw [Finset.sum_eq_single x]
    · rcases f2_cases (α x) with hax | hax
      · rw [hax]; simp [h01]
      · rw [hax]; simp [b2f]
    · intro i _ hix; simp [hix, b2f]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  have hsumY : (wsY.map fun wi => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD wi false)).sum = β y := by
    simp only [wsY, List.map_map]
    change (((List.finRange m).filter (fun j => decide (β j = 1))).map
      (fun j => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD (n + j.val) false))).sum = β y
    have hmap : (((List.finRange m).filter (fun j => decide (β j = 1))).map
        (fun j => b2f ((wiresList (gs ++ ext1) (oneEach x y)).getD (n + j.val) false))) =
        (((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => b2f (decide (j = y)))) := by
      refine List.map_congr_left fun j _ => ?_
      have h1 := wiresList_getD_prefix [] (gs ++ ext1) (oneEach x y) (n + j.val)
        (by rw [oneEach_length]; simp)
      simp only [List.nil_append] at h1
      rw [h1]
      simp only [wiresList, List.foldl_nil]
      rw [oneEach_getD_right x y j]
    rw [hmap]
    have hnodup : ((List.finRange m).filter (fun j => decide (β j = 1))).Nodup :=
      List.Nodup.filter _ (List.nodup_finRange m)
    rw [← List.sum_toFinset _ hnodup]
    have hset : ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset =
        Finset.univ.filter (fun j : Fin m => β j = 1) := by
      ext j; simp
    rw [hset, Finset.sum_filter]
    rw [Finset.sum_eq_single y]
    · rcases f2_cases (β y) with hby | hby
      · rw [hby]; simp [h01]
      · rw [hby]; simp [b2f]
    · intro j _ hjy; simp [hjy, b2f]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  rw [hsumC, hsumX, hsumY]

lemma build_pair_gadget {n m : ℕ} (gs : List Gate) (hv : validGates (n + m) gs)
    (u1 u2 : Fin n → F2) (v1 v2 : Fin m → F2) :
    ∃ (gs' : List Gate) (w : ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin + 1 ∧
      w < n + m + gs'.length ∧
      (depthsList (n + m) gs').getD w 0 ≤ 1 ∧
      ∀ x y, b2f ((wiresList gs' (oneEach x y)).getD w false) =
        u1 x * u2 x + v2 y * v1 y + u1 x * v1 y + u2 x * v2 y := by
  rcases build_sep gs hv 0 u1 v2 with ⟨gs1, wL, ⟨ext1, rfl⟩, hv1, hcnt1, hwL_lt, hwL_d, hwL_val⟩
  rcases build_sep (gs ++ ext1) hv1 0 u2 v1 with ⟨gs2, wR, ⟨ext2, rfl⟩, hv2, hcnt2, hwR_lt, hwR_d, hwR_val⟩
  have hwL_lt2 : wL < n + m + (gs ++ ext1 ++ ext2).length := by
    rw [List.length_append]; omega
  rcases build_and (gs ++ ext1 ++ ext2) hv2 wL wR hwL_lt2 hwR_lt
    with ⟨gs3, wN, ⟨ext3, rfl⟩, hv3, hcnt3, hwN_lt, hwN_d, hwN_val⟩
  refine ⟨gs ++ ext1 ++ ext2 ++ ext3, wN, ⟨ext1 ++ ext2 ++ ext3, by simp [List.append_assoc]⟩,
    hv3, by rw [hcnt3, hcnt2, hcnt1], hwN_lt, ?_, ?_⟩
  · rw [hwN_d, depthsList_getD_prefix (n + m) (gs ++ ext1) ext2 wL hwL_lt, hwL_d, hwR_d]
    simp
  · intro x y
    rw [hwN_val x y, wiresList_getD_prefix (gs ++ ext1) ext2 (oneEach x y) wL
      (by rw [oneEach_length]; exact hwL_lt), hwL_val x y, hwR_val x y]
    ring

lemma build_pair_list {n m : ℕ} (r : ℕ) (gs : List Gate) (hv : validGates (n + m) gs)
    (u1 u2 : Fin r → Fin n → F2) (v1 v2 : Fin r → Fin m → F2) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      (∃ ext, gs' = gs ++ ext) ∧
      validGates (n + m) gs' ∧
      gs'.countP isNonlin = gs.countP isNonlin + r ∧
      (∀ w ∈ ws, w < n + m + gs'.length) ∧
      (∀ w ∈ ws, (depthsList (n + m) gs').getD w 0 ≤ 1) ∧
      ∀ x y, (ws.map fun wi => b2f ((wiresList gs' (oneEach x y)).getD wi false)).sum =
        ∑ i : Fin r, (u1 i x * u2 i x + v2 i y * v1 i y + u1 i x * v1 i y + u2 i x * v2 i y) := by
  induction r generalizing gs with
  | zero =>
    refine ⟨gs, [], ⟨[], by simp⟩, hv, by simp, by simp, by simp, fun x y => by simp⟩
  | succ r ih =>
    rcases build_pair_gadget gs hv (u1 0) (u2 0) (v1 0) (v2 0)
      with ⟨gs1, w0, ⟨ext1, rfl⟩, hv1, hcnt1, hw0_lt, hw0_d, hw0_val⟩
    rcases ih (gs ++ ext1) hv1 (fun i => u1 i.succ) (fun i => u2 i.succ)
        (fun i => v1 i.succ) (fun i => v2 i.succ)
      with ⟨gs2, ws, ⟨ext2, rfl⟩, hv2, hcnt2, hws_lt, hws_d, hws_val⟩
    refine ⟨gs ++ ext1 ++ ext2, w0 :: ws, ⟨ext1 ++ ext2, by simp⟩, hv2,
      by rw [hcnt2, hcnt1]; omega, ?_, ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [List.length_append]; omega
      · exact hws_lt w hw
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [depthsList_getD_prefix (n + m) (gs ++ ext1) ext2 w hw0_lt]
        exact hw0_d
      · exact hws_d w hw
    · intro x y
      simp only [List.map_cons, List.sum_cons]
      rw [wiresList_getD_prefix (gs ++ ext1) ext2 (oneEach x y) w0
        (by rw [oneEach_length]; exact hw0_lt), hw0_val x y, hws_val x y, Fin.sum_univ_succ]

lemma upper_bound_dir {n m k : ℕ} (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (hA : (boxOp u v (fun x y => b2f (G 0 x y))).rank = k)
    (hB : (boxOp u v (fun x y => b2f (G 1 x y))).rank = k)
    (hAB : (boxOp u v (fun x y => b2f (G 0 x y)) + boxOp u v (fun x y => b2f (G 1 x y))).rank = k)
    (hcols : (Matrix.fromCols (boxOp u v (fun x y => b2f (G 0 x y)))
      (boxOp u v (fun x y => b2f (G 1 x y)))).rank = k)
    (hrows : (Matrix.fromRows (boxOp u v (fun x y => b2f (G 0 x y)))
      (boxOp u v (fun x y => b2f (G 1 x y)))).rank = k)
    (t : ℕ) (ht : (3 * ((k + 1) / 2) + 1) / 2 ≤ t) :
    ∃ (C : Circuit) (tap : Fin 2 → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP isNonlin ≤ t ∧
      ∀ j : Fin 2, (depthsList (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
        Represents (G j) ⟨C.gates, tap j⟩ := by
  let A := boxOp u v (fun x y => b2f (G 0 x y))
  let B := boxOp u v (fun x y => b2f (G 1 x y))
  rcases rank_decomp_matrices A B hA hB hAB hcols hrows with ⟨a, b, c, Cmat, habc, hC_rk, hAC_rk, hBC_rk⟩
  rcases matrix_rank_le_pairs Cmat hC_rk with ⟨uC1, uC2, vC1, vC2, hC_eq⟩
  rcases matrix_rank_le_pairs (A + Cmat) hAC_rk with ⟨uA1, uA2, vA1, vA2, hAC_eq⟩
  rcases matrix_rank_le_pairs (B + Cmat) hBC_rk with ⟨uB1, uB2, vB1, vB2, hBC_eq⟩
  rcases build_pair_list c [] (validGates_nil (n + m)) uC1 uC2 vC1 vC2
    with ⟨gs1, wsC, ⟨_, _⟩, hv1, hcnt1, hwsC_lt, hwsC_d, hwsC_val⟩
  rcases build_pair_list a gs1 hv1 uA1 uA2 vA1 vA2
    with ⟨gs2, wsA, ⟨ext2, rfl⟩, hv2, hcnt2, hwsA_lt, hwsA_d, hwsA_val⟩
  rcases build_pair_list b (gs1 ++ ext2) hv2 uB1 uB2 vB1 vB2
    with ⟨gs3, wsB, ⟨ext3, rfl⟩, hv3, hcnt3, hwsB_lt, hwsB_d, hwsB_val⟩
  let c0 : F2 := b2f (G 0 u v)
  let α0 : Fin n → F2 := fun x => b2f (G 0 x v) +
    (∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin a, uA1 i x * uA2 i x)
  let β0 : Fin m → F2 := fun y => b2f (G 0 u y) +
    (∑ i : Fin c, vC2 i y * vC1 i y) + (∑ i : Fin a, vA2 i y * vA1 i y)
  rcases build_sep (gs1 ++ ext2 ++ ext3) hv3 c0 α0 β0
    with ⟨gs4, wCorr0, ⟨ext4, rfl⟩, hv4, hcnt4, hwCorr0_lt, hwCorr0_d, hwCorr0_val⟩
  let c1 : F2 := b2f (G 1 u v)
  let α1 : Fin n → F2 := fun x => b2f (G 1 x v) +
    (∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin b, uB1 i x * uB2 i x)
  let β1 : Fin m → F2 := fun y => b2f (G 1 u y) +
    (∑ i : Fin c, vC2 i y * vC1 i y) + (∑ i : Fin b, vB2 i y * vB1 i y)
  rcases build_sep (gs1 ++ ext2 ++ ext3 ++ ext4) hv4 c1 α1 β1
    with ⟨gs5, wCorr1, ⟨ext5, rfl⟩, hv5, hcnt5, hwCorr1_lt, hwCorr1_d, hwCorr1_val⟩
  let gs5_len := (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5).length
  have hwsC_lt5 : ∀ w ∈ wsC, w < n + m + gs5_len := by
    intro w hw; have := hwsC_lt w hw; simp only [gs5_len, List.length_append] at *; omega
  have hwsA_lt5 : ∀ w ∈ wsA, w < n + m + gs5_len := by
    intro w hw; have := hwsA_lt w hw; simp only [gs5_len, List.length_append] at *; omega
  have hwsB_lt5 : ∀ w ∈ wsB, w < n + m + gs5_len := by
    intro w hw; have := hwsB_lt w hw; simp only [gs5_len, List.length_append] at *; omega
  have hwCorr0_lt5 : wCorr0 < n + m + gs5_len := by
    simp only [gs5_len, List.length_append] at *; omega
  have hwsC_d5 : ∀ w ∈ wsC, (depthsList (n + m) (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5)).getD w 0 ≤ 1 := by
    intro w hw
    have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 = gs1 ++ (ext2 ++ ext3 ++ ext4 ++ ext5) := by
      simp [List.append_assoc]
    rw [hpre, depthsList_getD_prefix (n + m) gs1 _ w (hwsC_lt w hw)]
    exact hwsC_d w hw
  have hwsA_d5 : ∀ w ∈ wsA, (depthsList (n + m) (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5)).getD w 0 ≤ 1 := by
    intro w hw
    have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 = (gs1 ++ ext2) ++ (ext3 ++ ext4 ++ ext5) := by
      simp [List.append_assoc]
    rw [hpre, depthsList_getD_prefix (n + m) (gs1 ++ ext2) _ w (hwsA_lt w hw)]
    exact hwsA_d w hw
  have hwsB_d5 : ∀ w ∈ wsB, (depthsList (n + m) (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5)).getD w 0 ≤ 1 := by
    intro w hw
    have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 = (gs1 ++ ext2 ++ ext3) ++ (ext4 ++ ext5) := by
      simp [List.append_assoc]
    rw [hpre, depthsList_getD_prefix (n + m) (gs1 ++ ext2 ++ ext3) _ w (hwsB_lt w hw)]
    exact hwsB_d w hw
  have hwCorr0_d5 : (depthsList (n + m) (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5)).getD wCorr0 0 ≤ 1 := by
    rw [depthsList_getD_prefix (n + m) (gs1 ++ ext2 ++ ext3 ++ ext4) ext5 wCorr0 hwCorr0_lt]
    omega
  rcases build_xor_list 1 (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5) hv5 (wCorr0 :: (wsC ++ wsA))
    (by
      intro w hw
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hw | hw
      · exact hwCorr0_lt5
      · exact hwsC_lt5 w hw
      · exact hwsA_lt5 w hw)
    (by
      intro w hw
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hw | hw
      · exact hwCorr0_d5
      · exact hwsC_d5 w hw
      · exact hwsA_d5 w hw)
    with ⟨gs6, tap0, ⟨ext6, rfl⟩, hv6, hcnt6, htap0_lt, htap0_d, htap0_val⟩
  rcases build_xor_list 1 (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6) hv6 (wCorr1 :: (wsC ++ wsB))
    (by
      intro w hw
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hw | hw
      · rw [List.length_append]; omega
      · have := hwsC_lt5 w hw; simp [gs5_len] at this ⊢; omega
      · have := hwsB_lt5 w hw; simp [gs5_len] at this ⊢; omega)
    (by
      intro w hw
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hw | hw
      · rw [depthsList_getD_prefix (n + m) _ ext6 w hwCorr1_lt]; omega
      · rw [depthsList_getD_prefix (n + m) _ ext6 w (hwsC_lt5 w hw)]; exact hwsC_d5 w hw
      · rw [depthsList_getD_prefix (n + m) _ ext6 w (hwsB_lt5 w hw)]; exact hwsB_d5 w hw)
    with ⟨gs7, tap1, ⟨ext7, rfl⟩, hv7, hcnt7, htap1_lt, htap1_d, htap1_val⟩
  let gsFinal := gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6 ++ ext7
  refine ⟨⟨gsFinal, 0⟩, fun j => if j = 0 then tap0 else tap1, hv7.1, hv7.2, ?_, ?_⟩
  · have h0 : ([] : List Gate).countP isNonlin = 0 := rfl
    change gsFinal.countP isNonlin ≤ t
    simp only [gsFinal]
    rw [hcnt7, hcnt6, hcnt5, hcnt4, hcnt3, hcnt2, hcnt1, h0]
    omega
  · intro j
    fin_cases j
    · simp only [Fin.zero_eta, ↓reduceIte]
      constructor
      · exact (depthsList_getD_prefix (n + m) _ ext7 tap0 htap0_lt).symm ▸ htap0_d
      · intro x y
        apply b2f_injective
        change b2f ((wiresList gsFinal (oneEach x y)).getD tap0 false) = b2f (G 0 x y)
        simp only [gsFinal]
        rw [wiresList_getD_prefix _ ext7 (oneEach x y) tap0 (by rw [oneEach_length]; exact htap0_lt)]
        rw [htap0_val x y]
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        have h1 : b2f ((wiresList (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5) (oneEach x y)).getD wCorr0 false) =
            c0 + α0 x + β0 y := by
          rw [wiresList_getD_prefix (gs1 ++ ext2 ++ ext3 ++ ext4) ext5 (oneEach x y) wCorr0
            (by rw [oneEach_length]; exact hwCorr0_lt)]
          exact hwCorr0_val x y
        have h2 : (wsC.map fun wi => b2f ((wiresList (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5) (oneEach x y)).getD wi false)).sum =
            ∑ i : Fin c, (uC1 i x * uC2 i x + vC2 i y * vC1 i y + uC1 i x * vC1 i y + uC2 i x * vC2 i y) := by
          have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 = gs1 ++ (ext2 ++ ext3 ++ ext4 ++ ext5) := by
            simp [List.append_assoc]
          rw [hpre]
          have hcongr : wsC.map (fun wi => b2f ((wiresList (gs1 ++ (ext2 ++ ext3 ++ ext4 ++ ext5)) (oneEach x y)).getD wi false)) =
              wsC.map (fun wi => b2f ((wiresList gs1 (oneEach x y)).getD wi false)) :=
            List.map_congr_left fun wi hwi => by
              rw [wiresList_getD_prefix gs1 _ (oneEach x y) wi (by rw [oneEach_length]; exact hwsC_lt wi hwi)]
          rw [hcongr]
          exact hwsC_val x y
        have h3 : (wsA.map fun wi => b2f ((wiresList (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5) (oneEach x y)).getD wi false)).sum =
            ∑ i : Fin a, (uA1 i x * uA2 i x + vA2 i y * vA1 i y + uA1 i x * vA1 i y + uA2 i x * vA2 i y) := by
          have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 = (gs1 ++ ext2) ++ (ext3 ++ ext4 ++ ext5) := by
            simp [List.append_assoc]
          rw [hpre]
          have hcongr : wsA.map (fun wi => b2f ((wiresList ((gs1 ++ ext2) ++ (ext3 ++ ext4 ++ ext5)) (oneEach x y)).getD wi false)) =
              wsA.map (fun wi => b2f ((wiresList (gs1 ++ ext2) (oneEach x y)).getD wi false)) :=
            List.map_congr_left fun wi hwi => by
              rw [wiresList_getD_prefix (gs1 ++ ext2) _ (oneEach x y) wi (by rw [oneEach_length]; exact hwsA_lt wi hwi)]
          rw [hcongr]
          exact hwsA_val x y
        rw [h1, h2, h3]
        have hsumC : ∑ i : Fin c, (uC1 i x * uC2 i x + vC2 i y * vC1 i y + uC1 i x * vC1 i y + uC2 i x * vC2 i y) =
            (∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin c, vC2 i y * vC1 i y) + Cmat x y := by
          rw [hC_eq x y, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        have hsumA : ∑ i : Fin a, (uA1 i x * uA2 i x + vA2 i y * vA1 i y + uA1 i x * vA1 i y + uA2 i x * vA2 i y) =
            (∑ i : Fin a, uA1 i x * uA2 i x) + (∑ i : Fin a, vA2 i y * vA1 i y) + (A x y + Cmat x y) := by
          have hAC := hAC_eq x y
          simp only [Matrix.add_apply] at hAC
          rw [hAC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hsumC, hsumA]
        simp only [c0, α0, β0, A, boxOp, Matrix.of_apply]
        have hz : ∀ z : F2, z + z = 0 := f2_add_self
        have hcalc : b2f (G 0 u v) + (b2f (G 0 x v) + (∑ i : Fin c, uC1 i x * uC2 i x) + ∑ i : Fin a, uA1 i x * uA2 i x) +
            (b2f (G 0 u y) + (∑ i : Fin c, vC2 i y * vC1 i y) + ∑ i : Fin a, vA2 i y * vA1 i y) +
            ((∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin c, vC2 i y * vC1 i y) + Cmat x y +
            ((∑ i : Fin a, uA1 i x * uA2 i x) + (∑ i : Fin a, vA2 i y * vA1 i y) +
              (b2f (G 0 x y) + b2f (G 0 u y) + b2f (G 0 x v) + b2f (G 0 u v) + Cmat x y))) =
            b2f (G 0 x y) + (b2f (G 0 u v) + b2f (G 0 u v)) + (b2f (G 0 x v) + b2f (G 0 x v)) +
            (b2f (G 0 u y) + b2f (G 0 u y)) + (Cmat x y + Cmat x y) +
            ((∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin c, uC1 i x * uC2 i x)) +
            ((∑ i : Fin c, vC2 i y * vC1 i y) + (∑ i : Fin c, vC2 i y * vC1 i y)) +
            ((∑ i : Fin a, uA1 i x * uA2 i x) + (∑ i : Fin a, uA1 i x * uA2 i x)) +
            ((∑ i : Fin a, vA2 i y * vA1 i y) + (∑ i : Fin a, vA2 i y * vA1 i y)) := by ring
        rw [hcalc]
        simp [hz]
    · have hne : (1 : Fin 2) ≠ 0 := by decide
      simp only [Fin.mk_one, hne, ↓reduceIte]
      constructor
      · exact htap1_d
      · intro x y
        apply b2f_injective
        change b2f ((wiresList gsFinal (oneEach x y)).getD tap1 false) = b2f (G 1 x y)
        simp only [gsFinal]
        rw [htap1_val x y]
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        have h1 : b2f ((wiresList (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6) (oneEach x y)).getD wCorr1 false) =
            c1 + α1 x + β1 y := by
          rw [wiresList_getD_prefix (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5) ext6 (oneEach x y) wCorr1
            (by rw [oneEach_length]; exact hwCorr1_lt)]
          exact hwCorr1_val x y
        have h2 : (wsC.map fun wi => b2f ((wiresList (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6) (oneEach x y)).getD wi false)).sum =
            ∑ i : Fin c, (uC1 i x * uC2 i x + vC2 i y * vC1 i y + uC1 i x * vC1 i y + uC2 i x * vC2 i y) := by
          have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6 = gs1 ++ (ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6) := by
            simp [List.append_assoc]
          rw [hpre]
          have hcongr : wsC.map (fun wi => b2f ((wiresList (gs1 ++ (ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6)) (oneEach x y)).getD wi false)) =
              wsC.map (fun wi => b2f ((wiresList gs1 (oneEach x y)).getD wi false)) :=
            List.map_congr_left fun wi hwi => by
              rw [wiresList_getD_prefix gs1 _ (oneEach x y) wi (by rw [oneEach_length]; exact hwsC_lt wi hwi)]
          rw [hcongr]
          exact hwsC_val x y
        have h3 : (wsB.map fun wi => b2f ((wiresList (gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6) (oneEach x y)).getD wi false)).sum =
            ∑ i : Fin b, (uB1 i x * uB2 i x + vB2 i y * vB1 i y + uB1 i x * vB1 i y + uB2 i x * vB2 i y) := by
          have hpre : gs1 ++ ext2 ++ ext3 ++ ext4 ++ ext5 ++ ext6 = (gs1 ++ ext2 ++ ext3) ++ (ext4 ++ ext5 ++ ext6) := by
            simp [List.append_assoc]
          rw [hpre]
          have hcongr : wsB.map (fun wi => b2f ((wiresList ((gs1 ++ ext2 ++ ext3) ++ (ext4 ++ ext5 ++ ext6)) (oneEach x y)).getD wi false)) =
              wsB.map (fun wi => b2f ((wiresList (gs1 ++ ext2 ++ ext3) (oneEach x y)).getD wi false)) :=
            List.map_congr_left fun wi hwi => by
              rw [wiresList_getD_prefix (gs1 ++ ext2 ++ ext3) _ (oneEach x y) wi (by rw [oneEach_length]; exact hwsB_lt wi hwi)]
          rw [hcongr]
          exact hwsB_val x y
        rw [h1, h2, h3]
        have hsumC : ∑ i : Fin c, (uC1 i x * uC2 i x + vC2 i y * vC1 i y + uC1 i x * vC1 i y + uC2 i x * vC2 i y) =
            (∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin c, vC2 i y * vC1 i y) + Cmat x y := by
          rw [hC_eq x y, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        have hsumB : ∑ i : Fin b, (uB1 i x * uB2 i x + vB2 i y * vB1 i y + uB1 i x * vB1 i y + uB2 i x * vB2 i y) =
            (∑ i : Fin b, uB1 i x * uB2 i x) + (∑ i : Fin b, vB2 i y * vB1 i y) + (B x y + Cmat x y) := by
          have hBC := hBC_eq x y
          simp only [Matrix.add_apply] at hBC
          rw [hBC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hsumC, hsumB]
        simp only [c1, α1, β1, B, boxOp, Matrix.of_apply]
        have hz : ∀ z : F2, z + z = 0 := f2_add_self
        have hcalc : b2f (G 1 u v) + (b2f (G 1 x v) + (∑ i : Fin c, uC1 i x * uC2 i x) + ∑ i : Fin b, uB1 i x * uB2 i x) +
            (b2f (G 1 u y) + (∑ i : Fin c, vC2 i y * vC1 i y) + ∑ i : Fin b, vB2 i y * vB1 i y) +
            ((∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin c, vC2 i y * vC1 i y) + Cmat x y +
            ((∑ i : Fin b, uB1 i x * uB2 i x) + (∑ i : Fin b, vB2 i y * vB1 i y) +
              (b2f (G 1 x y) + b2f (G 1 u y) + b2f (G 1 x v) + b2f (G 1 u v) + Cmat x y))) =
            b2f (G 1 x y) + (b2f (G 1 u v) + b2f (G 1 u v)) + (b2f (G 1 x v) + b2f (G 1 x v)) +
            (b2f (G 1 u y) + b2f (G 1 u y)) + (Cmat x y + Cmat x y) +
            ((∑ i : Fin c, uC1 i x * uC2 i x) + (∑ i : Fin c, uC1 i x * uC2 i x)) +
            ((∑ i : Fin c, vC2 i y * vC1 i y) + (∑ i : Fin c, vC2 i y * vC1 i y)) +
            ((∑ i : Fin b, uB1 i x * uB2 i x) + (∑ i : Fin b, uB1 i x * uB2 i x)) +
            ((∑ i : Fin b, vB2 i y * vB1 i y) + (∑ i : Fin b, vB2 i y * vB1 i y)) := by ring
        rw [hcalc]
        simp [hz]

end PEqualNP.Outside.L_meta_25831_aux

theorem PEqualNP.Outside.L_meta_25831 :
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
∀ (n m k : ℕ) (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let F := ZMod 2
  let entry := fun j x y => if G j x y then (1 : F) else 0
  let box : Fin 2 → Matrix (Fin n) (Fin m) F := fun j x y =>
    entry j x y + entry j u y + entry j x v + entry j u v
  let A := box 0
  let B := box 1
  A.rank = k → B.rank = k → (A+B).rank = k →
  (Matrix.fromCols A B).rank = k → (Matrix.fromRows A B).rank = k →
  ∀ t : ℕ, fits n m 2 G t ↔ (3*((k+1)/2)+1)/2 ≤ t := by
  intro nonlinear depths fits n m k G u v F entry box A B hA hB hAB hcols hrows t
  constructor
  · rintro ⟨C, tap, hrb, hlen, hcnt, htap⟩
    exact PEqualNP.Outside.L_meta_25831_aux.lower_bound_dir G u v hA hB hAB t C tap hrb hlen hcnt htap
  · intro ht
    exact PEqualNP.Outside.L_meta_25831_aux.upper_bound_dir G u v hA hB hAB hcols hrows t ht
