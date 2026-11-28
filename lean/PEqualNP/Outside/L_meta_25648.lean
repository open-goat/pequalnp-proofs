import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25648_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

private def b2z (x : Bool) : ZMod 2 := if x then 1 else 0

private def isNonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  revert x
  decide

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

private theorem eval_one_affine (op : GateOp) (x : Bool) :
    b2z (op.eval [x]) =
      b2z (op.eval [false]) + (b2z (op.eval [false]) + b2z (op.eval [true])) * b2z x := by
  cases x
  · simp [b2z]
  · simp only [b2z, ↓reduceIte, mul_one]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    revert a b
    decide

private theorem eval_two_linear (op : GateOp)
    (h : xor (xor (op.eval [false, false]) (op.eval [false, true]))
         (xor (op.eval [true, false]) (op.eval [true, true])) = false)
    (x y : Bool) :
    b2z (op.eval [x, y]) =
      b2z (op.eval [false, false]) +
      (b2z (op.eval [false, false]) + b2z (op.eval [true, false])) * b2z x +
      (b2z (op.eval [false, false]) + b2z (op.eval [false, true])) * b2z y := by
  cases x <;> cases y
  · simp [b2z]
  · simp only [b2z, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, mul_one]
    generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    revert a b
    decide
  · simp only [b2z, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, mul_one]
    generalize op.eval [false, false] = a
    generalize op.eval [true, false] = c
    revert a c
    decide
  · simp only [b2z, ↓reduceIte, mul_one]
    revert h
    generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    generalize op.eval [true, true] = d
    revert a b c d
    decide

private theorem eval_two_nonlin (op : GateOp)
    (h : xor (xor (op.eval [false, false]) (op.eval [false, true]))
         (xor (op.eval [true, false]) (op.eval [true, true])) = true)
    (x y : Bool) :
    let c00 := b2z (op.eval [false, false])
    let c10 := b2z (op.eval [false, false]) + b2z (op.eval [true, false])
    let c01 := b2z (op.eval [false, false]) + b2z (op.eval [false, true])
    b2z (op.eval [x, y]) = (c00 + c10 * c01) + (b2z x + c01) * (b2z y + c10) := by
  cases x <;> cases y
  · simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_add]
    generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    revert a b c
    decide
  · simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_add]
    generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    revert a b c
    decide
  · simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_add]
    generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    revert a b c
    decide
  · simp only [b2z, ↓reduceIte]
    revert h
    generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    generalize op.eval [true, true] = d
    revert a b c d
    decide

private theorem prod_union_zmod2 {α : Type*} [DecidableEq α] (S1 S2 : Finset α)
    (f : α → ZMod 2) :
    (∏ a ∈ S1 ∪ S2, f a) = (∏ a ∈ S1, f a) * (∏ a ∈ S2, f a) := by
  have h1 := Finset.prod_union_inter (s₁ := S1) (s₂ := S2) (f := f)
  have hsub : S1 ∩ S2 ⊆ S1 ∪ S2 := Finset.inter_subset_left.trans Finset.subset_union_left
  have hsplit : (∏ a ∈ S1 ∪ S2, f a) =
      (∏ a ∈ (S1 ∪ S2) \ (S1 ∩ S2), f a) * (∏ a ∈ S1 ∩ S2, f a) :=
    (Finset.prod_sdiff hsub).symm
  have hsq : (∏ a ∈ S1 ∩ S2, f a) * (∏ a ∈ S1 ∩ S2, f a) = ∏ a ∈ S1 ∩ S2, f a := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro a _
    exact zmod2_mul_self (f a)
  rw [← h1, hsplit, mul_assoc, hsq]

private def evalPoly {n m k : ℕ} (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (p : Finset (Fin k) → ZMod 2) (i : Fin n) (j : Fin m) : ZMod 2 :=
  ∑ S : Finset (Fin k), p S * ∏ a ∈ S, (R a i + C a j)

private def DegBound {k : ℕ} (dep : ℕ) (p : Finset (Fin k) → ZMod 2) : Prop :=
  (dep = 0 → p = 0) ∧ ∀ S : Finset (Fin k), p S ≠ 0 → S.card ≤ 2 ^ dep

private theorem evalPoly_zero {n m k : ℕ} (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (i : Fin n) (j : Fin m) : evalPoly R C 0 i j = 0 := by
  simp [evalPoly]

private theorem evalPoly_add {n m k : ℕ} (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (p q : Finset (Fin k) → ZMod 2) (i : Fin n) (j : Fin m) :
    evalPoly R C (p + q) i j = evalPoly R C p i j + evalPoly R C q i j := by
  simp only [evalPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem evalPoly_smul {n m k : ℕ} (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (c : ZMod 2) (p : Finset (Fin k) → ZMod 2) (i : Fin n) (j : Fin m) :
    evalPoly R C (fun S => c * p S) i j = c * evalPoly R C p i j := by
  simp only [evalPoly, mul_assoc, Finset.mul_sum]

private def singlePoly {k : ℕ} (idx : Fin k) : Finset (Fin k) → ZMod 2 :=
  fun S => if S = {idx} then 1 else 0

private theorem evalPoly_single {n m k : ℕ} (R : Fin k → Fin n → ZMod 2)
    (C : Fin k → Fin m → ZMod 2) (idx : Fin k) (i : Fin n) (j : Fin m) :
    evalPoly R C (singlePoly idx) i j = R idx i + C idx j := by
  simp [evalPoly, singlePoly]

private def mulPoly {k : ℕ} (p q : Finset (Fin k) → ZMod 2) (S : Finset (Fin k)) : ZMod 2 :=
  ∑ S1 : Finset (Fin k), ∑ S2 : Finset (Fin k), if S1 ∪ S2 = S then p S1 * q S2 else 0

private theorem evalPoly_mul {n m k : ℕ} (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (p q : Finset (Fin k) → ZMod 2) (i : Fin n) (j : Fin m) :
    evalPoly R C (mulPoly p q) i j = evalPoly R C p i j * evalPoly R C q i j := by
  unfold evalPoly mulPoly
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ S1 : Finset (Fin k),
      (∑ S : Finset (Fin k), ∑ S2 : Finset (Fin k),
        if S1 ∪ S2 = S then p S1 * q S2 * ∏ a ∈ S, (R a i + C a j) else 0) =
      ∑ S2 : Finset (Fin k),
        (p S1 * ∏ a ∈ S1, (R a i + C a j)) * (q S2 * ∏ a ∈ S2, (R a i + C a j)) := by
    intro S1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro S2 _
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [prod_union_zmod2]
    ring
  simp_rw [h1, ← Finset.mul_sum]

private theorem deg_mulPoly {k : ℕ} {D1 D2 : ℕ} {p q : Finset (Fin k) → ZMod 2}
    (hp : ∀ S, p S ≠ 0 → S.card ≤ D1) (hq : ∀ S, q S ≠ 0 → S.card ≤ D2) :
    ∀ S, mulPoly p q S ≠ 0 → S.card ≤ D1 + D2 := by
  intro S hne
  unfold mulPoly at hne
  have hex : ∃ S1 ∈ (Finset.univ : Finset (Finset (Fin k))),
      (∑ S2 : Finset (Fin k), if S1 ∪ S2 = S then p S1 * q S2 else 0) ≠ 0 := by
    by_contra h
    apply hne
    refine Finset.sum_eq_zero ?_
    intro S1 hS1
    by_contra h1
    exact h ⟨S1, hS1, h1⟩
  obtain ⟨S1, _, hS1⟩ := hex
  have hex2 : ∃ S2 ∈ (Finset.univ : Finset (Finset (Fin k))),
      (if S1 ∪ S2 = S then p S1 * q S2 else 0) ≠ 0 := by
    by_contra h
    apply hS1
    refine Finset.sum_eq_zero ?_
    intro S2 hS2
    by_contra h2
    exact h ⟨S2, hS2, h2⟩
  obtain ⟨S2, _, hS2⟩ := hex2
  by_cases hu : S1 ∪ S2 = S
  · simp only [hu, ↓reduceIte] at hS2
    have hp1 : p S1 ≠ 0 := left_ne_zero_of_mul hS2
    have hq2 : q S2 ≠ 0 := right_ne_zero_of_mul hS2
    have hc1 := hp S1 hp1
    have hc2 := hq S2 hq2
    have hcu := Finset.card_union_le S1 S2
    rw [hu] at hcu
    omega
  · simp [hu] at hS2

private def embedFin (k : ℕ) : Fin k ↪ Fin (k + 2) :=
  ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

private def liftPoly {k : ℕ} (p : Finset (Fin k) → ZMod 2) (S : Finset (Fin (k + 2))) : ZMod 2 :=
  ∑ S0 : Finset (Fin k), if S0.map (embedFin k) = S then p S0 else 0

private theorem liftPoly_zero {k : ℕ} : liftPoly (0 : Finset (Fin k) → ZMod 2) = 0 := by
  funext S
  simp [liftPoly]

private theorem degBound_liftPoly {k : ℕ} {dep : ℕ} {p : Finset (Fin k) → ZMod 2}
    (hp : DegBound dep p) : DegBound dep (liftPoly p) := by
  constructor
  · intro h0
    rw [hp.1 h0, liftPoly_zero]
  · intro S hne
    unfold liftPoly at hne
    have hex : ∃ S0 ∈ (Finset.univ : Finset (Finset (Fin k))),
        (if S0.map (embedFin k) = S then p S0 else 0) ≠ 0 := by
      by_contra h
      apply hne
      refine Finset.sum_eq_zero ?_
      intro S0 hS0
      by_contra h1
      exact h ⟨S0, hS0, h1⟩
    obtain ⟨S0, _, hS0⟩ := hex
    by_cases hm : S0.map (embedFin k) = S
    · simp only [hm, ↓reduceIte] at hS0
      rw [← hm, Finset.card_map]
      exact hp.2 S0 hS0
    · simp [hm] at hS0

private theorem evalPoly_liftPoly {n m k : ℕ}
    (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (R' : Fin (k + 2) → Fin n → ZMod 2) (C' : Fin (k + 2) → Fin m → ZMod 2)
    (hR : ∀ a : Fin k, R' (embedFin k a) = R a)
    (hC : ∀ a : Fin k, C' (embedFin k a) = C a)
    (p : Finset (Fin k) → ZMod 2) (i : Fin n) (j : Fin m) :
    evalPoly R' C' (liftPoly p) i j = evalPoly R C p i j := by
  unfold evalPoly liftPoly
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro S0 _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.prod_map]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro a _
  rw [hR a, hC a]

private def extTap {α : Type*} {k : ℕ} (F : Fin k → α) (v1 v2 : α) : Fin (k + 2) → α :=
  fun idx =>
    if h : idx.val < k then F ⟨idx.val, h⟩
    else if idx.val = k then v1
    else v2

private theorem extTap_embed {α : Type*} {k : ℕ} (F : Fin k → α) (v1 v2 : α) (a : Fin k) :
    extTap F v1 v2 (embedFin k a) = F a := by
  have hval : (embedFin k a).val = a.val := rfl
  unfold extTap
  simp only [hval, a.isLt, ↓reduceDIte]

private theorem extTap_last1 {α : Type*} {k : ℕ} (F : Fin k → α) (v1 v2 : α) :
    extTap F v1 v2 ⟨k, by omega⟩ = v1 := by
  simp [extTap]

private theorem extTap_last2 {α : Type*} {k : ℕ} (F : Fin k → α) (v1 v2 : α) :
    extTap F v1 v2 ⟨k + 1, by omega⟩ = v2 := by
  simp [extTap]

private def wiresOf {n m : ℕ} (gs : List Gate) (i : Fin n) (j : Fin m) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) (oneEach i j)

private def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun ds g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (isNonlin g).toNat])
    (List.replicate w 0)

private theorem foldl_wires_len (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) w0).length =
      w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private theorem wiresOf_len {n m : ℕ} (gs : List Gate) (i : Fin n) (j : Fin m) :
    (wiresOf gs i j).length = n + m + gs.length := by
  unfold wiresOf oneEach
  rw [foldl_wires_len, List.length_append, List.length_ofFn, List.length_ofFn]

private theorem foldl_depths_len (gs : List Gate) (d0 : List ℕ) :
    (gs.foldl (fun ds g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (isNonlin g).toNat]) d0).length =
      d0.length + gs.length := by
  induction gs generalizing d0 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private theorem depthsOf_len (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  rw [foldl_depths_len, List.length_replicate]

private theorem wiresOf_append {n m : ℕ} (gs : List Gate) (g : Gate) (i : Fin n) (j : Fin m) :
    wiresOf (gs ++ [g]) i j =
      wiresOf gs i j ++ [g.op.eval (g.inputs.map fun a => (wiresOf gs i j).getD a false)] := by
  unfold wiresOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem depthsOf_append (w : ℕ) (gs : List Gate) (g : Gate) :
    depthsOf w (gs ++ [g]) =
      depthsOf w gs ++ [((g.inputs.map fun a => (depthsOf w gs).getD a 0).foldr max 0) +
        (isNonlin g).toNat] := by
  unfold depthsOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem getD_append_lt {α : Type*} (l : List α) (v d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ [v]).getD k d = l.getD k d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hk]

private theorem getD_append_eq {α : Type*} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  simp

private theorem getD_append_gt {α : Type*} (l : List α) (v d : α) (k : ℕ) (hk : l.length < k) :
    (l ++ [v]).getD k d = d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none]
  · rfl
  · rw [List.length_append, List.length_singleton]
    omega

private theorem circuit_poly_rep {n m : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (R : Fin (2 * gs.countP isNonlin) → Fin n → ZMod 2)
      (C : Fin (2 * gs.countP isNonlin) → Fin m → ZMod 2),
      ∀ w : ℕ, ∃ (r : Fin n → ZMod 2) (c : Fin m → ZMod 2)
        (p : Finset (Fin (2 * gs.countP isNonlin)) → ZMod 2),
        DegBound ((depthsOf (n + m) gs).getD w 0) p ∧
        ∀ (i : Fin n) (j : Fin m),
          b2z ((wiresOf gs i j).getD w false) = r i + c j + evalPoly R C p i j := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun x => Fin.elim0 x, fun x => Fin.elim0 x, ?_⟩
    intro w
    have hdep : (depthsOf (n + m) []).getD w 0 = 0 := by
      unfold depthsOf
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
      by_cases hw : w < n + m
      · rw [List.getElem?_replicate]
        simp [hw]
      · rw [List.getElem?_replicate]
        simp [hw]
    rw [hdep]
    by_cases h1 : w < n
    · refine ⟨fun i => if i.val = w then 1 else 0, 0, 0, ⟨fun _ => rfl, fun _ h => False.elim (h rfl)⟩, ?_⟩
      intro i j
      unfold wiresOf oneEach
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD, evalPoly_zero, add_zero, Pi.zero_apply]
      rw [List.getElem?_append_left (by simp [h1])]
      rw [List.getElem?_ofFn]
      simp only [h1, ↓reduceDIte, Option.getD_some, b2z]
      by_cases hi : i.val = w
      · have hieq : (⟨w, h1⟩ : Fin n) = i := Fin.ext hi.symm
        simp [hi, hieq]
      · have hine : (⟨w, h1⟩ : Fin n) ≠ i := fun h => hi (congrArg Fin.val h).symm
        simp [hi, hine]
    · by_cases h2 : w < n + m
      · refine ⟨0, fun j => if j.val = w - n then 1 else 0, 0, ⟨fun _ => rfl, fun _ h => False.elim (h rfl)⟩, ?_⟩
        intro i j
        unfold wiresOf oneEach
        simp only [List.foldl_nil, List.getD_eq_getElem?_getD, evalPoly_zero, add_zero,
          Pi.zero_apply, zero_add]
        rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_ofFn, List.getElem?_ofFn]
        have hwn : w - n < m := by omega
        simp only [hwn, ↓reduceDIte, Option.getD_some, b2z]
        by_cases hj : j.val = w - n
        · have hjeq : (⟨w - n, hwn⟩ : Fin m) = j := Fin.ext hj.symm
          simp [hj, hjeq]
        · have hjne : (⟨w - n, hwn⟩ : Fin m) ≠ j := fun h => hj (congrArg Fin.val h).symm
          simp [hj, hjne]
      · refine ⟨0, 0, 0, ⟨fun _ => rfl, fun _ h => False.elim (h rfl)⟩, ?_⟩
        intro i j
        unfold wiresOf oneEach
        simp only [List.foldl_nil, List.getD_eq_getElem?_getD, evalPoly_zero, add_zero,
          Pi.zero_apply]
        rw [List.getElem?_eq_none (by simp; omega)]
        simp [b2z]
  | append_singleton gs g ih =>
    have hgs' : ∀ h ∈ gs, h.inputs.length ≤ 2 :=
      fun h hh => hgs h (List.mem_append_left [g] hh)
    have hg : g.inputs.length ≤ 2 :=
      hgs g (List.mem_append_right gs (List.mem_singleton_self g))
    obtain ⟨R, C, hrep⟩ := ih hgs'
    have hcnt : (gs ++ [g]).countP isNonlin = gs.countP isNonlin + (isNonlin g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases isNonlin g <;> simp
    cases hnl : isNonlin g
    · have hcnt0 : 2 * (gs ++ [g]).countP isNonlin = 2 * gs.countP isNonlin := by
        rw [hcnt, hnl]
        simp
      rw [hcnt0]
      refine ⟨R, C, ?_⟩
      intro w
      by_cases hlt : w < n + m + gs.length
      · obtain ⟨r, c, p, hdeg, heval⟩ := hrep w
        refine ⟨r, c, p, ?_, ?_⟩
        · rw [depthsOf_append, getD_append_lt]
          · exact hdeg
          · rw [depthsOf_len]; exact hlt
        · intro i j
          rw [wiresOf_append, getD_append_lt]
          · exact heval i j
          · rw [wiresOf_len]; exact hlt
      · by_cases heq : w = n + m + gs.length
        · subst heq
          have hdep_eq : (depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 =
              (g.inputs.map (fun a => (depthsOf (n + m) gs).getD a 0)).foldr max 0 := by
            rw [depthsOf_append, ← depthsOf_len (n + m) gs, getD_append_eq, hnl]
            simp
          rw [hdep_eq]
          rcases hgi : g.inputs with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩
          · refine ⟨fun _ => b2z (g.op.eval []), 0, 0, ⟨fun _ => rfl, by simp⟩, ?_⟩
            intro i j
            rw [wiresOf_append, ← wiresOf_len gs i j, getD_append_eq, hgi]
            simp [evalPoly_zero]
          · obtain ⟨r1, c1, p1, hdeg1, heval1⟩ := hrep a1
            let e0 := b2z (g.op.eval [false])
            let e1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun i => e0 + e1 * r1 i, fun j => e1 * c1 j, fun S => e1 * p1 S, ?_, ?_⟩
            · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Nat.zero_le, max_eq_left]
              constructor
              · intro h0
                rw [hdeg1.1 h0]
                funext S
                simp
              · intro S hne
                exact hdeg1.2 S (right_ne_zero_of_mul hne)
            · intro i j
              rw [wiresOf_append, ← wiresOf_len gs i j, getD_append_eq, hgi]
              simp only [List.map_cons, List.map_nil]
              rw [eval_one_affine, heval1 i j, evalPoly_smul]
              ring
          · obtain ⟨r1, c1, p1, hdeg1, heval1⟩ := hrep a1
            obtain ⟨r2, c2, p2, hdeg2, heval2⟩ := hrep a2
            have hlin : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold isNonlin at hnl
              rw [hgi] at hnl
              simp only [List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and] at hnl
              exact hnl
            let c00 := b2z (g.op.eval [false, false])
            let c10 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c01 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun i => c00 + c10 * r1 i + c01 * r2 i,
                    fun j => c10 * c1 j + c01 * c2 j,
                    (fun S => c10 * p1 S) + (fun S => c01 * p2 S), ?_, ?_⟩
            · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Nat.zero_le, max_eq_left]
              let d1 := (depthsOf (n + m) gs).getD a1 0
              let d2 := (depthsOf (n + m) gs).getD a2 0
              constructor
              · intro h0
                have h10 : d1 = 0 := by omega
                have h20 : d2 = 0 := by omega
                rw [hdeg1.1 h10, hdeg2.1 h20]
                funext S
                simp
              · intro S hne
                simp only [Pi.add_apply] at hne
                by_cases h1 : p1 S = 0
                · have h2 : p2 S ≠ 0 := by
                    intro h2
                    apply hne
                    simp [h1, h2]
                  have hc2 := hdeg2.2 S h2
                  have hpow : 2 ^ d2 ≤ 2 ^ max d1 d2 :=
                    Nat.pow_le_pow_right (by norm_num) (le_max_right d1 d2)
                  exact hc2.trans hpow
                · have hc1 := hdeg1.2 S h1
                  have hpow : 2 ^ d1 ≤ 2 ^ max d1 d2 :=
                    Nat.pow_le_pow_right (by norm_num) (le_max_left d1 d2)
                  exact hc1.trans hpow
            · intro i j
              rw [wiresOf_append, ← wiresOf_len gs i j, getD_append_eq, hgi]
              simp only [List.map_cons, List.map_nil]
              rw [eval_two_linear g.op hlin, heval1 i j, heval2 i j,
                evalPoly_add, evalPoly_smul, evalPoly_smul]
              ring
          · simp [hgi] at hg
        · refine ⟨0, 0, 0, ?_, ?_⟩
          · rw [depthsOf_append, getD_append_gt]
            · exact ⟨fun _ => rfl, by simp⟩
            · rw [depthsOf_len]; omega
          · intro i j
            rw [wiresOf_append, getD_append_gt]
            · simp [b2z, evalPoly_zero]
            · rw [wiresOf_len]; omega
    · have hcnt2 : 2 * (gs ++ [g]).countP isNonlin = 2 * gs.countP isNonlin + 2 := by
        rw [hcnt, hnl]
        simp
        omega
      have hlen2 : g.inputs.length = 2 := by
        unfold isNonlin at hnl
        simpa using (Bool.and_eq_true _ _).mp hnl |>.1
      have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
        unfold isNonlin at hnl
        exact ((Bool.and_eq_true _ _).mp hnl).2
      rcases hgi : g.inputs with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩
      · simp [hgi] at hlen2
      · simp [hgi] at hlen2
      · obtain ⟨r1, c1, p1, hdeg1, heval1⟩ := hrep a1
        obtain ⟨r2, c2, p2, hdeg2, heval2⟩ := hrep a2
        let k0 := 2 * gs.countP isNonlin
        let c00 := b2z (g.op.eval [false, false])
        let c10 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
        let c01 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
        let R' : Fin (k0 + 2) → Fin n → ZMod 2 :=
          extTap R (fun i => r1 i + c01) (fun i => r2 i + c10)
        let C' : Fin (k0 + 2) → Fin m → ZMod 2 :=
          extTap C c1 c2
        rw [hcnt2]
        refine ⟨R', C', ?_⟩
        intro w
        by_cases hlt : w < n + m + gs.length
        · obtain ⟨r, c, p, hdeg, heval⟩ := hrep w
          refine ⟨r, c, liftPoly p, ?_, ?_⟩
          · rw [depthsOf_append, getD_append_lt]
            · exact degBound_liftPoly hdeg
            · rw [depthsOf_len]; exact hlt
          · intro i j
            rw [wiresOf_append, getD_append_lt]
            · rw [evalPoly_liftPoly R C R' C' (extTap_embed R _ _) (extTap_embed C _ _)]
              exact heval i j
            · rw [wiresOf_len]; exact hlt
        · by_cases heq : w = n + m + gs.length
          · subst heq
            let idx1 : Fin (k0 + 2) := ⟨k0, by omega⟩
            let idx2 : Fin (k0 + 2) := ⟨k0 + 1, by omega⟩
            let q1 : Finset (Fin (k0 + 2)) → ZMod 2 := singlePoly idx1 + liftPoly p1
            let q2 : Finset (Fin (k0 + 2)) → ZMod 2 := singlePoly idx2 + liftPoly p2
            refine ⟨fun _ => c00 + c10 * c01, 0, mulPoly q1 q2, ?_, ?_⟩
            · rw [depthsOf_append, ← depthsOf_len (n + m) gs, getD_append_eq, hgi, hnl]
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Nat.zero_le, max_eq_left, Bool.toNat_true]
              let d1 := (depthsOf (n + m) gs).getD a1 0
              let d2 := (depthsOf (n + m) gs).getD a2 0
              constructor
              · intro h0
                omega
              · have hq1 : ∀ S, q1 S ≠ 0 → S.card ≤ 2 ^ max d1 d2 := by
                  intro S hne
                  simp only [q1, Pi.add_apply] at hne
                  by_cases hs : singlePoly idx1 S = 0
                  · have hp1' : liftPoly p1 S ≠ 0 := by
                      intro hp1'
                      apply hne
                      simp [hs, hp1']
                    have hc := (degBound_liftPoly hdeg1).2 S hp1'
                    exact hc.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left d1 d2))
                  · have hS : S = {idx1} := by
                      by_contra hne'
                      apply hs
                      simp [singlePoly, hne']
                    rw [hS, Finset.card_singleton]
                    exact Nat.one_le_two_pow
                have hq2 : ∀ S, q2 S ≠ 0 → S.card ≤ 2 ^ max d1 d2 := by
                  intro S hne
                  simp only [q2, Pi.add_apply] at hne
                  by_cases hs : singlePoly idx2 S = 0
                  · have hp2' : liftPoly p2 S ≠ 0 := by
                      intro hp2'
                      apply hne
                      simp [hs, hp2']
                    have hc := (degBound_liftPoly hdeg2).2 S hp2'
                    exact hc.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right d1 d2))
                  · have hS : S = {idx2} := by
                      by_contra hne'
                      apply hs
                      simp [singlePoly, hne']
                    rw [hS, Finset.card_singleton]
                    exact Nat.one_le_two_pow
                have hm := deg_mulPoly hq1 hq2
                intro S hne
                have hc := hm S hne
                have hpow : 2 ^ max d1 d2 + 2 ^ max d1 d2 = 2 ^ (max d1 d2 + 1) := by
                  rw [Nat.pow_succ]
                  omega
                change S.card ≤ 2 ^ (max d1 d2 + 1)
                omega
            · intro i j
              rw [wiresOf_append, ← wiresOf_len gs i j, getD_append_eq, hgi]
              simp only [List.map_cons, List.map_nil, Pi.zero_apply, add_zero]
              rw [eval_two_nonlin g.op hxor, heval1 i j, heval2 i j]
              rw [evalPoly_mul]
              have hq1e : evalPoly R' C' q1 i j = r1 i + c1 j + evalPoly R C p1 i j + c01 := by
                simp only [q1]
                rw [evalPoly_add, evalPoly_single,
                  evalPoly_liftPoly R C R' C' (extTap_embed R _ _) (extTap_embed C _ _)]
                simp only [R', C', idx1, extTap_last1]
                ring
              have hq2e : evalPoly R' C' q2 i j = r2 i + c2 j + evalPoly R C p2 i j + c10 := by
                simp only [q2]
                rw [evalPoly_add, evalPoly_single,
                  evalPoly_liftPoly R C R' C' (extTap_embed R _ _) (extTap_embed C _ _)]
                simp only [R', C', idx2, extTap_last2]
                ring
              rw [hq1e, hq2e]
          · refine ⟨0, 0, 0, ?_, ?_⟩
            · rw [depthsOf_append, getD_append_gt]
              · exact ⟨fun _ => rfl, by simp⟩
              · rw [depthsOf_len]; omega
            · intro i j
              rw [wiresOf_append, getD_append_gt]
              · simp [b2z, evalPoly_zero]
              · rw [wiresOf_len]; omega
      · simp [hgi] at hlen2

private theorem rank_zero_mat {n m : ℕ} :
    (0 : Matrix (Fin n) (Fin m) (ZMod 2)).rank = 0 := by
  simp [Matrix.rank]

private theorem rank_add_le {n m : ℕ} (M1 M2 : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (M1 + M2).rank ≤ M1.rank + M2.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (M1 + M2).mulVecLin ≤
      LinearMap.range M1.mulVecLin ⊔ LinearMap.range M2.mulVecLin := by
    rintro y ⟨x, rfl⟩
    have hsum : (M1 + M2).mulVecLin x = M1.mulVecLin x + M2.mulVecLin x := by
      simp
    rw [hsum]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)
  have hmono := Submodule.finrank_mono hle
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range M1.mulVecLin) (LinearMap.range M2.mulVecLin)
  omega

private theorem rank_sum_le {n m : ℕ} {α : Type*} (s : Finset α)
    (f : α → Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ a ∈ s, f a).rank ≤ ∑ a ∈ s, (f a).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le (f a) (∑ x ∈ s, f x)).trans (Nat.add_le_add_left ih _)

private theorem rank_outer_le_one {n m : ℕ} (rv : Fin n → ZMod 2) (cv : Fin m → ZMod 2) :
    (Matrix.of (fun i j => rv i * cv j)).rank ≤ 1 := by
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.of (fun i j => rv i * cv j)).mulVecLin ≤
      Submodule.span (ZMod 2) ({rv} : Set (Fin n → ZMod 2)) := by
    rintro y ⟨x, rfl⟩
    have heq : (Matrix.of (fun i j => rv i * cv j)).mulVecLin x = (dotProduct cv x) • rv := by
      funext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton rv))
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({rv} : Set (Fin n → ZMod 2))) ≤ 1 := by
    have h1 := finrank_span_le_card (R := ZMod 2) ({rv} : Set (Fin n → ZMod 2))
    simpa using h1
  exact (Submodule.finrank_mono hle).trans hspan

private theorem card_nonempty_le (N k : ℕ) :
    (Finset.univ.filter (fun U : Finset (Fin N) => 1 ≤ U.card ∧ U.card ≤ k)).card =
      ∑ j ∈ Finset.range k, Nat.choose N (j + 1) := by
  induction k with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro U _
    omega
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hdisj : Disjoint
        (Finset.univ.filter (fun U : Finset (Fin N) => 1 ≤ U.card ∧ U.card ≤ k))
        (Finset.univ.filter (fun U : Finset (Fin N) => U.card = k + 1)) := by
      rw [Finset.disjoint_filter]
      intro U _ h1 h2
      omega
    have hunion : Finset.univ.filter (fun U : Finset (Fin N) => 1 ≤ U.card ∧ U.card ≤ k + 1) =
        Finset.univ.filter (fun U : Finset (Fin N) => 1 ≤ U.card ∧ U.card ≤ k) ∪
        Finset.univ.filter (fun U : Finset (Fin N) => U.card = k + 1) := by
      ext U
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hpc : Finset.univ.filter (fun U : Finset (Fin N) => U.card = k + 1) =
        Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin N)) := by
      ext U
      simp [Finset.mem_powersetCard]
    rw [hunion, Finset.card_union_of_disjoint hdisj, hpc, Finset.card_powersetCard, Finset.card_fin]

private theorem four_corner_rank_bound {n m k b : ℕ} (hb : 1 ≤ b)
    (u : Fin n) (v : Fin m)
    (R : Fin k → Fin n → ZMod 2) (C : Fin k → Fin m → ZMod 2)
    (r : Fin n → ZMod 2) (c : Fin m → ZMod 2)
    (p : Finset (Fin k) → ZMod 2)
    (hdeg : ∀ S : Finset (Fin k), p S ≠ 0 → S.card ≤ 2 * b) :
    let entry : Fin n → Fin m → ZMod 2 := fun i j => r i + c j + evalPoly R C p i j
    let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j =>
      entry i j + entry i v + entry u j + entry u v
    A.rank ≤
      (∑ j ∈ Finset.range b, Nat.choose k (j + 1)) +
      (∑ j ∈ Finset.range (b - 1), Nat.choose k (j + 1)) := by
  intro entry A
  let rowProd : Finset (Fin k) → Fin n → ZMod 2 := fun U i => ∏ a ∈ U, R a i
  let colProd : Finset (Fin k) → Fin m → ZMod 2 := fun V j => ∏ a ∈ V, C a j
  let rowDiff : Finset (Fin k) → Fin n → ZMod 2 := fun U i => rowProd U i + rowProd U u
  let colDiff : Finset (Fin k) → Fin m → ZMod 2 := fun V j => colProd V j + colProd V v
  have hrow0 : ∀ i, rowDiff ∅ i = 0 := by
    intro i
    simp [rowDiff, rowProd, zmod2_add_self]
  have hcol0 : ∀ j, colDiff ∅ j = 0 := by
    intro j
    simp [colDiff, colProd, zmod2_add_self]
  have h4prod : ∀ (S : Finset (Fin k)) (i : Fin n) (j : Fin m),
      (∏ a ∈ S, (R a i + C a j)) + (∏ a ∈ S, (R a i + C a v)) +
      (∏ a ∈ S, (R a u + C a j)) + (∏ a ∈ S, (R a u + C a v)) =
      ∑ U ∈ S.powerset, rowDiff U i * colDiff (S \ U) j := by
    intro S i j
    simp_rw [Finset.prod_add]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro U _
    simp only [rowDiff, colDiff, rowProd, colProd]
    ring
  let Lset := Finset.univ.filter (fun U : Finset (Fin k) => 1 ≤ U.card ∧ U.card ≤ b)
  let Rset := Finset.univ.filter (fun V : Finset (Fin k) => 1 ≤ V.card ∧ V.card ≤ b - 1)
  let H : Finset (Fin k) → Fin m → ZMod 2 := fun U j =>
    ∑ S : Finset (Fin k), if U ⊆ S then p S * colDiff (S \ U) j else 0
  let K : Finset (Fin k) → Fin n → ZMod 2 := fun V i =>
    ∑ S : Finset (Fin k), if V ⊆ S ∧ b < (S \ V).card then p S * rowDiff (S \ V) i else 0
  have hA : A =
      (∑ U ∈ Lset, Matrix.of (fun i j => rowDiff U i * H U j)) +
      (∑ V ∈ Rset, Matrix.of (fun i j => K V i * colDiff V j)) := by
    ext i j
    simp only [A, entry, evalPoly, Matrix.add_apply, Matrix.sum_apply, Matrix.of_apply]
    have hrc : (r i + c j + ∑ S, p S * ∏ a ∈ S, (R a i + C a j)) +
        (r i + c v + ∑ S, p S * ∏ a ∈ S, (R a i + C a v)) +
        (r u + c j + ∑ S, p S * ∏ a ∈ S, (R a u + C a j)) +
        (r u + c v + ∑ S, p S * ∏ a ∈ S, (R a u + C a v)) =
        ∑ S : Finset (Fin k), p S *
          ((∏ a ∈ S, (R a i + C a j)) + (∏ a ∈ S, (R a i + C a v)) +
           (∏ a ∈ S, (R a u + C a j)) + (∏ a ∈ S, (R a u + C a v))) := by
      have h1 := zmod2_add_self (r i)
      have h2 := zmod2_add_self (r u)
      have h3 := zmod2_add_self (c j)
      have h4 := zmod2_add_self (c v)
      simp_rw [mul_add, Finset.sum_add_distrib]
      linear_combination h1 + h2 + h3 + h4
    rw [hrc]
    simp_rw [h4prod, Finset.mul_sum]
    have hL : (∑ U ∈ Lset, rowDiff U i * H U j) =
        ∑ S : Finset (Fin k), ∑ U ∈ S.powerset,
          if U.card ≤ b then p S * (rowDiff U i * colDiff (S \ U) j) else 0 := by
      simp_rw [H, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro S _
      rw [Finset.sum_filter]
      have hsub : ∀ U : Finset (Fin k),
          (if 1 ≤ U.card ∧ U.card ≤ b then
            if U ⊆ S then rowDiff U i * (p S * colDiff (S \ U) j) else 0
          else 0) =
          if U ∈ S.powerset then
            if U.card ≤ b then p S * (rowDiff U i * colDiff (S \ U) j) else 0
          else 0 := by
        intro U
        by_cases hu : U ⊆ S
        · have hm : U ∈ S.powerset := Finset.mem_powerset.mpr hu
          by_cases hle : U.card ≤ b
          · by_cases h1 : 1 ≤ U.card
            · simp only [hm, hu, hle, h1, and_self, ↓reduceIte]
              ring
            · have he : U = ∅ := Finset.card_eq_zero.mp (by omega)
              simp [he, hrow0]
          · simp [hm, hle]
        · have hm : U ∉ S.powerset := fun h => hu (Finset.mem_powerset.mp h)
          simp [hm, hu]
      simp_rw [hsub]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hR : (∑ V ∈ Rset, K V i * colDiff V j) =
        ∑ S : Finset (Fin k), ∑ U ∈ S.powerset,
          if b < U.card then p S * (rowDiff U i * colDiff (S \ U) j) else 0 := by
      simp_rw [K, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro S _
      by_cases hpS : p S = 0
      · simp [hpS]
      · have hScard : S.card ≤ 2 * b := hdeg S hpS
        rw [Finset.sum_filter]
        have hsub : ∀ V : Finset (Fin k),
            (if 1 ≤ V.card ∧ V.card ≤ b - 1 then
              if V ⊆ S ∧ b < (S \ V).card then p S * rowDiff (S \ V) i * colDiff V j else 0
            else 0) =
            if V ∈ S.powerset then
              if b < (S \ V).card then p S * (rowDiff (S \ V) i * colDiff V j) else 0
            else 0 := by
          intro V
          by_cases hv : V ⊆ S
          · have hm : V ∈ S.powerset := Finset.mem_powerset.mpr hv
            by_cases hgt : b < (S \ V).card
            · have hcd : (S \ V).card + V.card = S.card := by
                have := Finset.card_sdiff_add_card_eq_card hv
                exact this
              have hvle : V.card ≤ b - 1 := by omega
              by_cases h1 : 1 ≤ V.card
              · simp only [hm, hv, hgt, h1, hvle, and_self, ↓reduceIte]
                ring
              · have he : V = ∅ := Finset.card_eq_zero.mp (by omega)
                simp [he, hcol0]
            · simp [hm, hv, hgt]
          · have hm : V ∉ S.powerset := fun h => hv (Finset.mem_powerset.mp h)
            simp [hm, hv]
        simp_rw [hsub]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        refine Finset.sum_bij' (fun V _ => S \ V) (fun U _ => S \ U) ?_ ?_ ?_ ?_ ?_
        · intro V hV
          exact Finset.mem_powerset.mpr Finset.sdiff_subset
        · intro U hU
          exact Finset.mem_powerset.mpr Finset.sdiff_subset
        · intro V hV
          exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hV)
        · intro U hU
          exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)
        · intro V hV
          rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hV)]
    rw [hL, hR, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro U _
    by_cases hle : U.card ≤ b
    · have hng : ¬ b < U.card := by omega
      simp [hle, hng]
    · have hg : b < U.card := by omega
      simp [hle, hg]
  rw [hA]
  have hr1 : (∑ U ∈ Lset, Matrix.of (fun i j => rowDiff U i * H U j)).rank ≤ Lset.card := by
    calc (∑ U ∈ Lset, Matrix.of (fun i j => rowDiff U i * H U j)).rank
        ≤ ∑ U ∈ Lset, (Matrix.of (fun i j => rowDiff U i * H U j)).rank := rank_sum_le _ _
      _ ≤ ∑ _ ∈ Lset, 1 := Finset.sum_le_sum (fun U _ => rank_outer_le_one (rowDiff U) (H U))
      _ = Lset.card := by simp
  have hr2 : (∑ V ∈ Rset, Matrix.of (fun i j => K V i * colDiff V j)).rank ≤ Rset.card := by
    calc (∑ V ∈ Rset, Matrix.of (fun i j => K V i * colDiff V j)).rank
        ≤ ∑ V ∈ Rset, (Matrix.of (fun i j => K V i * colDiff V j)).rank := rank_sum_le _ _
      _ ≤ ∑ _ ∈ Rset, 1 := Finset.sum_le_sum (fun V _ => rank_outer_le_one (K V) (colDiff V))
      _ = Rset.card := by simp
  have htot := (rank_add_le _ _).trans (Nat.add_le_add hr1 hr2)
  rw [card_nonempty_le, card_nonempty_le] at htot
  exact htot

theorem main_aux (n m : ℕ) (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (d : ℕ) (C : Circuit)
    (hrep : (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧
      PEqualNP.Represents.Represents G C)
    (hdep : (depthsOf (n + m) C.gates).getD C.output 0 ≤ d + 1) :
    let entry := fun (a : Fin n) (b : Fin m) => if G a b then (1 : ZMod 2) else 0
    let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j =>
      entry i j + entry i v + entry u j + entry u v
    A.rank ≤
      (∑ j ∈ Finset.range (2 ^ d), Nat.choose (2 * C.gates.countP isNonlin) (j + 1)) +
      (∑ j ∈ Finset.range (2 ^ d - 1), Nat.choose (2 * C.gates.countP isNonlin) (j + 1)) := by
  intro entry A
  obtain ⟨R, Co, hpoly⟩ := circuit_poly_rep (n := n) (m := m) C.gates hrep.1
  obtain ⟨r, c, p, hdeg, heval⟩ := hpoly C.output
  have hentry : ∀ (i : Fin n) (j : Fin m), entry i j = r i + c j + evalPoly R Co p i j := by
    intro i j
    have h1 := heval i j
    have h2 : (wiresOf C.gates i j).getD C.output false = C.eval (oneEach i j) := rfl
    rw [h2, hrep.2.2 i j] at h1
    exact h1
  have hAeq : A = fun i j =>
      (r i + c j + evalPoly R Co p i j) +
      (r i + c v + evalPoly R Co p i v) +
      (r u + c j + evalPoly R Co p u j) +
      (r u + c v + evalPoly R Co p u v) := by
    ext i j
    simp only [A, hentry]
  rw [hAeq]
  have hdeg2 : ∀ S, p S ≠ 0 → S.card ≤ 2 * (2 ^ d) := by
    intro S hne
    have h1 := hdeg.2 S hne
    have h2 : 2 ^ (depthsOf (n + m) C.gates).getD C.output 0 ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by norm_num) hdep
    have h3 : 2 ^ (d + 1) = 2 * 2 ^ d := by
      rw [Nat.pow_succ]
      ring
    omega
  exact four_corner_rank_bound (Nat.one_le_two_pow) u v R Co r c p hdeg2

end PEqualNP.Outside.L_meta_25648_aux

theorem PEqualNP.Outside.L_meta_25648 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let entry := fun (a : Fin n) (b : Fin m) => if G a b then (1 : ZMod 2) else 0
  let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j =>
    entry i j + entry i v + entry u j + entry u v
  let represents := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧
    PEqualNP.Represents.Represents G C
  let budget := fun (t b : ℕ) =>
    (∑ j ∈ Finset.range b, Nat.choose (2*t) (j+1)) +
    (∑ j ∈ Finset.range (b-1), Nat.choose (2*t) (j+1))
  ∀ (d : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    represents C → depth (n+m) C ≤ d+1 →
    A.rank ≤ budget (C.gates.countP nonlinear) (2^d) := by
  intro nonlinear depth n m G u v entry A represents budget d C hrep hdep
  exact PEqualNP.Outside.L_meta_25648_aux.main_aux n m G u v d C hrep hdep
