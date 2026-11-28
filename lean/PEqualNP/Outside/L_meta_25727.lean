import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25727_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open scoped BigOperators

/-- The field element represented by a Boolean input. -/
private def cnfBit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The posted test for a nonlinear gate. -/
private def cnfNonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def cnfWires (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem cnfWires_length (x : List Bool) (gs : List Gate) :
    (cnfWires x gs).length = x.length + gs.length := by
  unfold cnfWires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem cnfWires_append (x : List Bool) (gs hs : List Gate) :
    cnfWires x (gs ++ hs) = cnfWires (cnfWires x gs) hs := List.foldl_append

private theorem cnfWires_prefix (x : List Bool) (gs : List Gate) :
    ∃ ys, cnfWires x gs = x ++ ys := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [cnfWires]⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => x.getD i false)
    obtain ⟨ys, hys⟩ := ih (x ++ [b])
    exact ⟨b :: ys, by change cnfWires (x ++ [b]) gs = _; rw [hys]; simp⟩

private theorem cnfWires_append_getD (x : List Bool) (gs hs : List Gate) {w : ℕ}
    (hw : w < x.length + gs.length) :
    (cnfWires x (gs ++ hs)).getD w false = (cnfWires x gs).getD w false := by
  rw [cnfWires_append]
  obtain ⟨ys, hys⟩ := cnfWires_prefix (cnfWires x gs) hs
  rw [hys, List.getD_append _ _ _ _ (by rwa [cnfWires_length])]

private theorem cnfWires_gate (x : List Bool) (gs : List Gate) {j : ℕ} (hj : j < gs.length)
    (hrb : ∀ a ∈ (gs[j]).inputs, a < x.length + j) :
    (cnfWires x gs).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun a => (cnfWires x gs).getD a false) := by
  have hsplit : gs = (gs.take j ++ [gs[j]]) ++ gs.drop (j + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hlen' : (gs.take j ++ [gs[j]]).length = j + 1 := by
    rw [List.length_append, hlen]
    rfl
  conv_lhs => rw [hsplit]
  rw [cnfWires_append_getD x (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) (by omega)]
  rw [cnfWires_append]
  change ((cnfWires x (gs.take j)) ++
    [(gs[j]).op.eval ((gs[j]).inputs.map fun a => (cnfWires x (gs.take j)).getD a false)]).getD
      (x.length + j) false = _
  have hpre : (cnfWires x (gs.take j)).length = x.length + j := by simp [cnfWires_length, hlen]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hpre, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take j).length := by simpa [hlen] using hrb a ha
  conv_rhs => rw [hsplit]
  rw [cnfWires_append_getD x (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) (by omega)]
  rw [cnfWires_append_getD x (gs.take j) [gs[j]] halt]

private theorem cnfAnfOne (f : Bool → Bool) (x : Bool) :
    cnfBit (f x) = cnfBit (f false) + (cnfBit (f false) + cnfBit (f true)) * cnfBit x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

private theorem cnfAnfTwo (f : Bool → Bool → Bool) (x y : Bool) :
    cnfBit (f x y) =
      cnfBit (f false false) +
      (cnfBit (f false false) + cnfBit (f true false)) * cnfBit x +
      (cnfBit (f false false) + cnfBit (f false true)) * cnfBit y +
      cnfBit (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (cnfBit x * cnfBit y) := by
  cases x <;> cases y <;> cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

private theorem cnfCount {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun j : Fin l.length => p l[j.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun j : Fin (a :: l).length => p (a :: l)[j.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun j : Fin l.length => p l[j.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun j : Fin l.length => j.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      simpa using hsum (Finset.univ.filter (fun j : Fin (a :: l).length => p (a :: l)[j.val] = true))
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

private abbrev CnfFn (n : ℕ) := (Fin n → Bool) → ZMod 2

/-- The representation of a wire only uses products which have already been computed. -/
private def cnfSpan {n k : ℕ} (prodWire : Fin k → ℕ) (prod : Fin k → CnfFn n)
    (w : ℕ) (f : CnfFn n) : Prop :=
  ∃ (a : ZMod 2) (l : Fin n → ZMod 2) (d : Fin k → ZMod 2),
    (∀ j, w < prodWire j → d j = 0) ∧
    ∀ x, f x = a + (∑ q, l q * cnfBit (x q)) + ∑ j, d j * prod j x

private theorem cnfSpan_const {n k : ℕ} {p : Fin k → ℕ} {v : Fin k → CnfFn n}
    {w : ℕ} (a : ZMod 2) : cnfSpan p v w (fun _ => a) := by
  exact ⟨a, fun _ => 0, fun _ => 0, by simp, by simp⟩

private theorem cnfSpan_input {n k : ℕ} {p : Fin k → ℕ} {v : Fin k → CnfFn n}
    {w : ℕ} (q : Fin n) : cnfSpan p v w (fun x => cnfBit (x q)) := by
  classical
  refine ⟨0, fun r => if r = q then 1 else 0, fun _ => 0, by simp, fun x => ?_⟩
  simp

private theorem cnfSpan_prod {n k : ℕ} {p : Fin k → ℕ} {v : Fin k → CnfFn n}
    {w : ℕ} (j : Fin k) (hj : p j ≤ w) : cnfSpan p v w (v j) := by
  classical
  refine ⟨0, fun _ => 0, fun r => if r = j then 1 else 0, ?_, fun x => ?_⟩
  · intro r hr
    have hne : r ≠ j := by rintro rfl; omega
    simp [hne]
  · simp

private theorem cnfSpan_mono {n k : ℕ} {p : Fin k → ℕ} {v : Fin k → CnfFn n}
    {w z : ℕ} {f : CnfFn n} (h : cnfSpan p v w f) (hw : w ≤ z) : cnfSpan p v z f := by
  obtain ⟨a, l, d, hd, hf⟩ := h
  exact ⟨a, l, d, fun j hj => hd j (lt_of_le_of_lt hw hj), hf⟩

private theorem cnfSpan_add {n k : ℕ} {p : Fin k → ℕ} {v : Fin k → CnfFn n}
    {w : ℕ} {f g : CnfFn n} (hf : cnfSpan p v w f) (hg : cnfSpan p v w g) :
    cnfSpan p v w (fun x => f x + g x) := by
  obtain ⟨a, l, d, hd, hf⟩ := hf
  obtain ⟨a', l', d', hd', hg⟩ := hg
  refine ⟨a + a', fun q => l q + l' q, fun j => d j + d' j,
    fun j hj => by simp [hd j hj, hd' j hj], fun x => ?_⟩
  dsimp only
  rw [hf x, hg x]
  simp only [add_mul, Finset.sum_add_distrib]
  abel

private theorem cnfSpan_mul {n k : ℕ} {p : Fin k → ℕ} {v : Fin k → CnfFn n}
    {w : ℕ} {f : CnfFn n} (a : ZMod 2) (h : cnfSpan p v w f) :
    cnfSpan p v w (fun x => a * f x) := by
  obtain ⟨b, l, d, hd, hf⟩ := h
  refine ⟨a * b, fun q => a * l q, fun j => a * d j,
    fun j hj => by simp [hd j hj], fun x => ?_⟩
  dsimp only
  rw [hf x]
  simp only [mul_add, Finset.mul_sum, mul_assoc]

private theorem cnfBinary {g : Gate} (h : cnfNonlinear g = true) :
    ∃ a b, g.inputs = [a, b] := by
  have hl : g.inputs.length = 2 := by
    simpa only [beq_iff_eq] using (Bool.and_eq_true_iff.mp h).1
  rcases List.length_eq_two.mp hl with ⟨a, b, hab⟩
  exact ⟨a, b, hab⟩

/-- Affine wire labels and output, with one product for each nonlinear gate in evaluation order. -/
private theorem circuitNormalForm {n : ℕ} (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack n C) :
    let k := C.gates.countP cnfNonlinear
    ∃ (L : Fin k → Fin 2 → Fin k → ZMod 2) (c : Fin k → ZMod 2)
      (raw u : (Fin n → Bool) → Fin k → Fin 2 → ZMod 2) (lin : (Fin n → Bool) → ZMod 2),
      (∀ i b, ∃ (a : ZMod 2) (l : Fin n → ZMod 2),
        ∀ x, raw x i b = a + ∑ q, l q * cnfBit (x q)) ∧
      (∃ (a : ZMod 2) (l : Fin n → ZMod 2), ∀ x, lin x = a + ∑ q, l q * cnfBit (x q)) ∧
      (∀ i b j, i ≤ j → L i b j = 0) ∧
      (∀ x i b, u x i b = raw x i b + ∑ j, L i b j * (u x j 0 * u x j 1)) ∧
      (∀ x, cnfBit (C.eval (List.ofFn x)) = lin x + ∑ j, c j * (u x j 0 * u x j 1)) ∧
      ∀ g ∈ C.gates, cnfNonlinear g = true → ∀ w ∈ g.inputs,
        ∃ i b, ∀ x, cnfBit ((C.wires (List.ofFn x)).getD w false) = u x i b := by
  classical
  let k := C.gates.countP cnfNonlinear
  dsimp only
  let NL : Finset (Fin C.gates.length) := Finset.univ.filter (fun j => cnfNonlinear C.gates[j.val] = true)
  let e : Fin k ≃o NL := NL.orderIsoOfFin (cnfCount C.gates cnfNonlinear)
  let idx (i : Fin k) : Fin C.gates.length := (e i).val
  let opnd (i : Fin k) (b : Fin 2) : ℕ := C.gates[(idx i).val].inputs.getD b.val 0
  let val (w : ℕ) (x : Fin n → Bool) := cnfBit ((C.wires (List.ofFn x)).getD w false)
  let pw (i : Fin k) := n + (idx i).val
  let prod (i : Fin k) (x : Fin n → Bool) := val (opnd i 0) x * val (opnd i 1) x
  have hidx_nl (i : Fin k) : cnfNonlinear C.gates[(idx i).val] = true :=
    (Finset.mem_filter.mp (e i).property).2
  have hidx_of (j : Fin C.gates.length) (h : cnfNonlinear C.gates[j.val] = true) :
      ∃ i, idx i = j := by
    let a : NL := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    exact ⟨e.symm a, congrArg Subtype.val (e.apply_symm_apply a)⟩
  have hback (j : Fin C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j.val].inputs) :
      w < n + j.val := by
    have h := hrb j.val j.isLt w
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ j.isLt] at h
    exact h hw
  have hgate (j : Fin C.gates.length) (x : Fin n → Bool) :
      val (n + j.val) x = cnfBit (C.gates[j.val].op.eval
        (C.gates[j.val].inputs.map fun w => (C.wires (List.ofFn x)).getD w false)) := by
    have h := cnfWires_gate (List.ofFn x) C.gates j.isLt (by
      simpa only [List.length_ofFn] using hback j)
    rw [List.length_ofFn] at h
    exact congrArg cnfBit h
  have hspan (w : ℕ) : cnfSpan pw prod w (val w) := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hi : w < n
      · have hv : val w = fun x => cnfBit (x ⟨w, hi⟩) := by
          funext x
          obtain ⟨ys, hys⟩ := cnfWires_prefix (List.ofFn x) C.gates
          change cnfBit ((cnfWires (List.ofFn x) C.gates).getD w false) = _
          rw [hys, List.getD_append _ _ _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa),
            List.getElem_ofFn]
        rw [hv]
        exact cnfSpan_input ⟨w, hi⟩
      by_cases hg : w < n + C.gates.length
      · let j : Fin C.gates.length := ⟨w - n, by omega⟩
        have hj : w = n + j.val := by simp [j]; omega
        let g := C.gates[j.val]
        have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem j.isLt)
        have ha (a : ℕ) (hm : a ∈ g.inputs) : cnfSpan pw prod w (val a) := by
          have hab : a < w := hj.symm ▸ hback j a hm
          exact cnfSpan_mono (ih a hab) hab.le
        match hin : g.inputs with
        | [] =>
          have hv : val w = fun _ => cnfBit (g.op.eval []) := by
            funext x
            rw [hj, hgate]
            change cnfBit (g.op.eval (g.inputs.map _)) = _
            simp [hin]
          rw [hv]
          exact cnfSpan_const _
        | [a] =>
          let f (b : Bool) := g.op.eval [b]
          have hv : val w = fun x => cnfBit (f false) + (cnfBit (f false) + cnfBit (f true)) * val a x := by
            funext x
            rw [hj, hgate]
            change cnfBit (g.op.eval (g.inputs.map _)) = _
            simpa only [hin, List.map_cons, List.map_nil, val, f] using
              cnfAnfOne f ((C.wires (List.ofFn x)).getD a false)
          rw [hv]
          exact cnfSpan_add (cnfSpan_const _) (cnfSpan_mul _ (ha a (by simp [hin])))
        | [a, b] =>
          let f (z₁ z₂ : Bool) := g.op.eval [z₁, z₂]
          have hv : val w = fun x =>
              cnfBit (f false false) +
              (cnfBit (f false false) + cnfBit (f true false)) * val a x +
              (cnfBit (f false false) + cnfBit (f false true)) * val b x +
              cnfBit (cnfNonlinear g) * (val a x * val b x) := by
            funext x
            rw [hj, hgate]
            change cnfBit (g.op.eval (g.inputs.map _)) = _
            simpa [hin, val, f, cnfNonlinear] using cnfAnfTwo f
              ((C.wires (List.ofFn x)).getD a false) ((C.wires (List.ofFn x)).getD b false)
          rw [hv]
          refine cnfSpan_add (cnfSpan_add (cnfSpan_add (cnfSpan_const _) ?_) ?_) ?_
          · exact cnfSpan_mul _ (ha a (by simp [hin]))
          · exact cnfSpan_mul _ (ha b (by simp [hin]))
          · by_cases hn : cnfNonlinear g = true
            · obtain ⟨i, hi⟩ := hidx_of j hn
              have hwi : pw i = w := by simp [pw, hi, hj]
              have hop : C.gates[(idx i).val].inputs = [a, b] := by simpa only [hi] using hin
              have hvp : (fun x => cnfBit (cnfNonlinear g) * (val a x * val b x)) = prod i := by
                funext x
                simp [prod, opnd, hop, hn, cnfBit]
              rw [hvp]
              exact cnfSpan_prod i hwi.le
            · have hn' : cnfNonlinear g = false := Bool.eq_false_of_not_eq_true hn
              simpa [hn', cnfBit] using
                (cnfSpan_const (n := n) (p := pw) (v := prod) (w := w) 0)
        | _ :: _ :: _ :: _ => simp [hin] at hgl
      · have hv : val w = fun _ => 0 := by
          funext x
          have hw : (cnfWires (List.ofFn x) C.gates).length ≤ w := by
            rw [cnfWires_length, List.length_ofFn]; omega
          change cnfBit ((cnfWires (List.ofFn x) C.gates).getD w false) = _
          rw [List.getD_eq_default _ _ hw]
          rfl
        rw [hv]
        exact cnfSpan_const _
  have hoplt (i : Fin k) (b : Fin 2) : opnd i b < pw i := by
    obtain ⟨a, b', hab⟩ := cnfBinary (hidx_nl i)
    apply hback (idx i)
    fin_cases b <;> simp [opnd, hab]
  choose a l d hd hv using fun (i : Fin k) (b : Fin 2) => hspan (opnd i b)
  obtain ⟨ao, lo, co, _, ho⟩ := hspan C.output
  refine ⟨d, co, fun x i b => a i b + ∑ q, l i b q * cnfBit (x q),
    fun x i b => val (opnd i b) x, fun x => ao + ∑ q, lo q * cnfBit (x q),
    fun i b => ⟨a i b, l i b, fun _ => rfl⟩, ⟨ao, lo, fun _ => rfl⟩, ?_, ?_, ho, ?_⟩
  · intro i b j hij
    have hij' : pw i ≤ pw j := Nat.add_le_add_left (show (idx i).val ≤ (idx j).val from e.monotone hij) n
    exact hd i b j ((hoplt i b).trans_le hij')
  · intro x i b
    exact hv i b x
  · intro g hg hn w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨i, hi⟩ := hidx_of ⟨j, hj⟩ hn
    obtain ⟨a, b, hab⟩ := cnfBinary hn
    have hab' : C.gates[(idx i).val].inputs = [a, b] := by simpa only [hi] using hab
    simp [hab] at hw
    rcases hw with rfl | rfl
    · exact ⟨i, 0, fun x => by simp [opnd, hab', val]⟩
    · exact ⟨i, 1, fun x => by simp [opnd, hab', val]⟩

noncomputable section CorrelationBlocks

open scoped Classical

/-- The real sign of a Boolean value, with `true` represented by `-1`. -/
private def corrSign : Bool → ℝ
  | false => 1
  | true => -1

private theorem corrSign_sq (b : Bool) : corrSign b ^ 2 = 1 := by
  cases b <;> norm_num [corrSign]

private theorem corrSign_xor (b c : Bool) :
    corrSign (xor b c) = corrSign b * corrSign c := by
  cases b <;> cases c <;> norm_num [corrSign, xor, Bool.xor]

private theorem corrSign_dot {N : ℕ} (G : Fin N → Fin N → Bool)
    (hG : ∀ x z, x ≠ z →
      2 * (Finset.univ.filter fun y => G x y ≠ G z y).card = N)
    (x z : Fin N) :
    (∑ y, corrSign (G x y) * corrSign (G z y)) = if x = z then (N : ℝ) else 0 := by
  by_cases e : x = z
  · subst z
    simp [← pow_two, corrSign_sq]
  · rw [ite_eq_right e]
    have H (y : Fin N) : corrSign (G x y) * corrSign (G z y) =
        1 - 2 * (if G x y ≠ G z y then (1 : ℝ) else 0) := by
      cases G x y <;> cases G z y <;> norm_num [corrSign]
    rw [Finset.sum_congr rfl (fun y _ => H y), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
    exact sub_eq_zero.mpr (by exact_mod_cast (hG x z e).symm)

private theorem corrAggregate_dot {N : ℕ} (A : Fin N → Fin N → ℝ)
    (hA : ∀ x z, (∑ y, A x y * A z y) = if x = z then (N : ℝ) else 0)
    (u v : Fin N → ℝ) :
    (∑ y, (∑ x, u x * A x y) * (∑ z, v z * A z y)) =
      (N : ℝ) * ∑ x, u x * v x := by
  calc
    (∑ y, (∑ x, u x * A x y) * (∑ z, v z * A z y)) =
        ∑ y, ∑ x, ∑ z, u x * A x y * (v z * A z y) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
    _ =
        ∑ x, ∑ y, ∑ z, u x * A x y * (v z * A z y) := Finset.sum_comm
    _ = ∑ x, ∑ z, ∑ y, (u x * v z) * (A x y * A z y) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      calc
        (∑ y, ∑ z, u x * A x y * (v z * A z y)) =
            ∑ z, ∑ y, u x * A x y * (v z * A z y) := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ x, ∑ z, (u x * v z) * (if x = z then (N : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.mul_sum, hA]
    _ = (N : ℝ) * ∑ x, u x * v x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [mul_ite, mul_zero, Fintype.sum_ite_eq]
      ring

private theorem corrFiber_sum {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (f : Fin N → β) (L : β → ℝ) :
    (∑ y, L (f y)) = ∑ p : β, (Finset.univ.filter fun y => f y = p).card * L p := by
  rw [← Finset.sum_fiberwise' Finset.univ f L]
  simp [nsmul_eq_mul]

private theorem corrDecoder_balance {β : Type*} [Fintype β] {h N : ℕ}
    (hN : 0 < N) (hc : N = h ^ 2 * Fintype.card β)
    (D : β → β → ℝ) (w : β → ℕ) (hD : ∀ a p, D a p ^ 2 = 1)
    (hw : ∑ p, (w p : ℝ) = N)
    (horth : ∀ a b, a ≠ b → ∑ p, (w p : ℝ) * (D a p * D b p) = 0) :
    ∀ p, w p = h ^ 2 := by
  have nz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  let X : Matrix β β ℝ := fun a p => D a p
  let Y : Matrix β β ℝ := fun p a => (N : ℝ)⁻¹ * (w p : ℝ) * D a p
  have hXY : X * Y = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ p, D a p * ((N : ℝ)⁻¹ * (w p : ℝ) * D b p)) = _
    calc
      _ = (N : ℝ)⁻¹ * ∑ p, (w p : ℝ) * (D a p * D b p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
      _ = _ := by
        by_cases e : a = b
        · subst b
          simp [← pow_two, hD, hw, nz]
        · simp [e, horth a b e]
  have hYX : Y * X = 1 := mul_eq_one_comm.mp hXY
  intro p
  have H := congrArg (fun M : Matrix β β ℝ => M p p) hYX
  change (Y * X) p p = (1 : Matrix β β ℝ) p p at H
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at H
  change (∑ a, ((N : ℝ)⁻¹ * (w p : ℝ) * D a p) * D a p) = 1 at H
  have point (a : β) : ((N : ℝ)⁻¹ * (w p : ℝ) * D a p) * D a p =
      (N : ℝ)⁻¹ * (w p : ℝ) := by
    rw [mul_assoc, ← pow_two, hD, mul_one]
  simp only [point, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at H
  have H' : (Fintype.card β : ℝ) * (w p : ℝ) / N = 1 := by
    convert H using 1
    rw [div_eq_mul_inv]
    ring
  have H'' : Fintype.card β * w p = N := by
    have K := (div_eq_iff nz).mp H'
    rw [one_mul] at K
    exact_mod_cast K
  have cardPos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨p⟩
  rw [hc, mul_comm (h ^ 2)] at H''
  exact Nat.eq_of_mul_eq_mul_left cardPos H''

/-- Optimal agreement implies uniform fibers and unweighted decoder row orthogonality. -/
private theorem correlationBlocks {β : Type*} [Fintype β] [Nonempty β] [DecidableEq β] {N h : ℕ}
    (hh : 0 < h) (hc : N = h ^ 2 * Fintype.card β)
    (G F : Fin N → Fin N → Bool)
    (hG : ∀ x z, x ≠ z →
      2 * (Finset.univ.filter fun y => G x y ≠ G z y).card = N)
    (row col : Fin N → β) (Q R : Fin N → Bool) (d : β → β → Bool)
    (hF : ∀ x y, F x y = xor (xor (Q x) (R y)) (d (row x) (col y))) :
    let hits := ∑ x : Fin N, (Finset.univ.filter fun y => F x y = G x y).card
    2 * h * hits ≤ (h + 1) * N ^ 2 ∧
      (2 * h * hits = (h + 1) * N ^ 2 →
        (∀ p : β, (Finset.univ.filter fun x => row x = p).card = h ^ 2 ∧
                  (Finset.univ.filter fun y => col y = p).card = h ^ 2) ∧
        ∀ a b : β, a ≠ b → ∑ p : β, corrSign (d a p) * corrSign (d b p) = 0) := by
  let hits := ∑ x : Fin N, (Finset.univ.filter fun y => F x y = G x y).card
  change 2 * h * hits ≤ (h + 1) * N ^ 2 ∧ _
  let A (x y : Fin N) := corrSign (G x y)
  let D (a p : β) := corrSign (d a p)
  let U (a : β) (x : Fin N) := if row x = a then corrSign (Q x) else 0
  let V (a : β) (y : Fin N) := corrSign (R y) * D a (col y)
  let T (a : β) (y : Fin N) := ∑ x, U a x * A x y
  let nr (a : β) := (Finset.univ.filter fun x => row x = a).card
  let nc (p : β) := (Finset.univ.filter fun y => col y = p).card
  have hN : 0 < N := by rw [hc]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have nEq : (N : ℝ) = (h : ℝ)^2 * (Fintype.card β : ℝ) := by exact_mod_cast hc
  have tDot (a b : β) : (∑ y, T a y * T b y) =
      (N : ℝ) * ∑ x, U a x * U b x :=
    corrAggregate_dot A (corrSign_dot G hG) _ _
  have tNorm (a : β) : (∑ y, T a y ^ 2) = (N : ℝ) * (nr a : ℝ) := by
    calc
      (∑ y, T a y ^ 2) = ∑ y, T a y * T a y := by simp only [pow_two]
      _ = (N : ℝ) * ∑ x, U a x * U a x := tDot a a
      _ = _ := by
        have H (x : Fin N) : U a x * U a x = if row x = a then (1 : ℝ) else 0 := by
          by_cases hx : row x = a <;> simp [U, hx, ← pow_two, corrSign_sq]
        simp only [H, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, nr]
  have vNorm (a : β) (y : Fin N) : V a y ^ 2 = 1 := by
    simp [V, D, mul_pow, corrSign_sq]
  have tTotal : (∑ a, ∑ y, T a y ^ 2) = (N : ℝ)^2 := by
    simp only [tNorm, ← Finset.mul_sum]
    have hf := corrFiber_sum row (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hf
    change (N : ℝ) = ∑ a, (nr a : ℝ) at hf
    rw [← hf, pow_two]
  have vTotal : (∑ a, ∑ y, ((h : ℝ) * V a y)^2) = (N : ℝ)^2 := by
    simp only [mul_pow, vNorm, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [pow_two (N : ℝ), nEq]
    ring
  have matchSum : (∑ a, ∑ y, T a y * V a y) = 2 * (hits : ℝ) - (N : ℝ)^2 := by
    calc
      (∑ a, ∑ y, T a y * V a y) = ∑ x, ∑ y, corrSign (F x y) * A x y := by
        simp only [T, Finset.sum_mul]
        rw [Finset.sum_comm (f := fun a y => ∑ x, U a x * A x y * V a y)]
        simp only [Finset.sum_comm (f := fun a x => U a x * A x _ * V a _)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp only [U, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          hF, corrSign_xor, V, D]
        ring
      _ = 2 * (hits : ℝ) - (N : ℝ)^2 := by
        have H (x y : Fin N) : corrSign (F x y) * A x y =
            2 * (if F x y = G x y then (1 : ℝ) else 0) - 1 := by
          unfold A
          cases F x y <;> cases G x y <;> norm_num [corrSign]
        simp only [H, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          hits, Nat.cast_sum, pow_two]
  have energy : (∑ a, ∑ y, (T a y - (h : ℝ) * V a y)^2) =
      2 * ((h + 1 : ℝ) * (N : ℝ)^2 - 2 * (h : ℝ) * (hits : ℝ)) := by
    have H (a : β) (y : Fin N) : (T a y - (h : ℝ) * V a y)^2 =
        T a y ^ 2 + ((h : ℝ) * V a y)^2 - (2 * (h : ℝ)) * (T a y * V a y) := by ring
    simp only [H, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      tTotal, vTotal, matchSum]
    ring
  have enNonneg : 0 ≤ ∑ a, ∑ y, (T a y - (h : ℝ) * V a y)^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · rw [energy] at enNonneg
    have leR : 2 * (h : ℝ) * (hits : ℝ) ≤ (h + 1 : ℝ) * (N : ℝ)^2 := by linarith
    exact_mod_cast leR
  · intro he
    have heR : 2 * (h : ℝ) * (hits : ℝ) = (h + 1 : ℝ) * (N : ℝ)^2 := by exact_mod_cast he
    have enZero : (∑ a, ∑ y, (T a y - (h : ℝ) * V a y)^2) = 0 := by
      rw [energy, heR, sub_self, mul_zero]
    have tEq (a : β) (y : Fin N) : T a y = (h : ℝ) * V a y := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun (_ : β) _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp enZero a
          (Finset.mem_univ _)
      have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hz y
        (Finset.mem_univ _)
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hy)
    have rowSize (a : β) : nr a = h ^ 2 := by
      have H := tNorm a
      simp only [tEq, mul_pow, vNorm, mul_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at H
      have H' : (nr a : ℝ) = (h : ℝ)^2 := mul_left_cancel₀ (ne_of_gt hNr) H.symm
      exact_mod_cast H'
    have wOrth (a b : β) (hab : a ≠ b) :
        ∑ p, (nc p : ℝ) * (D a p * D b p) = 0 := by
      rw [← corrFiber_sum col (fun p => D a p * D b p)]
      have hz (x : Fin N) : U a x * U b x = 0 := by
        by_cases hx : row x = a
        · simp [U, hx, hab]
        · simp [U, hx]
      have id (y : Fin N) : T a y * T b y =
          (h : ℝ)^2 * (D a (col y) * D b (col y)) := by
        simp only [tEq, V]
        calc
          _ = (h : ℝ)^2 * corrSign (R y)^2 * (D a (col y) * D b (col y)) := by ring
          _ = _ := by rw [corrSign_sq, mul_one]
      have z := tDot a b
      simp only [hz, Finset.sum_const_zero, mul_zero, id, ← Finset.mul_sum] at z
      exact (mul_eq_zero.mp z).resolve_left (pow_ne_zero _ (ne_of_gt hhr))
    have sumW : ∑ p, (nc p : ℝ) = N := by
      have hf := corrFiber_sum col (fun _ => (1 : ℝ))
      simpa [nc, nsmul_eq_mul] using hf.symm
    have colSize := corrDecoder_balance hN hc D nc (fun _ _ => corrSign_sq _) sumW wOrth
    refine ⟨fun p => ⟨rowSize p, colSize p⟩, ?_⟩
    intro a b hab
    have K := wOrth a b hab
    simp only [colSize, Nat.cast_pow, ← Finset.mul_sum] at K
    exact (mul_eq_zero.mp K).resolve_left (pow_ne_zero _ (ne_of_gt hhr))

end CorrelationBlocks

open scoped BigOperators

private abbrev RBWord (k : ℕ) := Fin k → Fin 2 → ZMod 2
private abbrev RBFeedback (k : ℕ) := Fin k → Fin 2 → Fin k → ZMod 2

private def rbBit (b : Bool) : ZMod 2 := if b then 1 else 0
private def rbBool (z : ZMod 2) : Bool := decide (z = 1)
private def rbSign (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

private theorem rbBit_bool (z : ZMod 2) : rbBit (rbBool z) = z := by
  fin_cases z
  · change rbBit (rbBool 0) = 0
    decide
  · change rbBit (rbBool 1) = 1
    decide

private theorem rbBit_inj : Function.Injective rbBit := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; exact (by decide : ¬rbBit _ = rbBit _) h)

private theorem rbBit_xor (a b : Bool) : rbBit (xor a b) = rbBit a + rbBit b := by
  cases a <;> cases b <;> decide

private theorem rb_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

private theorem rbSign_mul (a b : ZMod 2) : rbSign (a + b) = rbSign a * rbSign b := by
  fin_cases a <;> fin_cases b
  · change rbSign (0 + 0) = rbSign 0 * rbSign 0
    simp [rbSign]
  · change rbSign (0 + 1) = rbSign 0 * rbSign 1
    simp [rbSign]
  · change rbSign (1 + 0) = rbSign 1 * rbSign 0
    simp [rbSign]
  · change rbSign (1 + 1) = rbSign 1 * rbSign 1
    simp [rbSign, rb_self]

private theorem rbSign_sq (a : ZMod 2) : rbSign a * rbSign a = 1 := by
  by_cases h : a = 0 <;> simp [rbSign, h]

private theorem rbSign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    rbSign (∑ i ∈ s, f i) = ∏ i ∈ s, rbSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rbSign]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, rbSign_mul, ih]

private def rbLin {k : ℕ} (a b : RBWord k) : ZMod 2 :=
  ∑ i, (a i 0 * b i 0 + a i 1 * b i 1)

private theorem rbLin_add {k : ℕ} (a b c : RBWord k) :
    rbLin a (b + c) = rbLin a b + rbLin a c := by
  rw [rbLin, rbLin, rbLin, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change a i 0 * (b i 0 + c i 0) + a i 1 * (b i 1 + c i 1) = _
  ring

private theorem rb_card (k : ℕ) : Fintype.card (RBWord k) = 2 ^ (2*k) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

private def rbProd {k : ℕ} (u : RBWord k) (i : Fin k) : ZMod 2 := u i 0 * u i 1

private def rbUnshift {k : ℕ} (L : RBFeedback k) (u : RBWord k) : RBWord k :=
  fun i b => u i b + ∑ j, L i b j * rbProd u j

private theorem rbUnshift_injective {k : ℕ} {L : RBFeedback k}
    (hL : ∀ i b j, i ≤ j → L i b j = 0) : Function.Injective (rbUnshift L) := by
  intro u v huv
  have h : ∀ m (i : Fin k), i.val = m → u i = v i := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro i hi
      funext b
      have e := congrFun (congrFun huv i) b
      change u i b + (∑ j, L i b j * rbProd u j) =
        v i b + (∑ j, L i b j * rbProd v j) at e
      have hs : (∑ j, L i b j * rbProd u j) = ∑ j, L i b j * rbProd v j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j < i
        · have hj' : j.val < m := by rw [← hi]; exact hj
          rw [rbProd, rbProd, ih j.val hj' j rfl]
        · rw [hL i b j (le_of_not_gt hj), zero_mul, zero_mul]
      rw [hs] at e
      exact add_right_cancel e
  funext i b
  exact congrFun (h i.val i rfl) b

private noncomputable def rbEquiv {k : ℕ} (L : RBFeedback k)
    (hL : ∀ i b j, i ≤ j → L i b j = 0) : RBWord k ≃ RBWord k :=
  Equiv.ofBijective (rbUnshift L)
    ⟨rbUnshift_injective hL, Finite.surjective_of_injective (rbUnshift_injective hL)⟩

private noncomputable def rbDecode {k : ℕ} (L : RBFeedback k)
    (hL : ∀ i b j, i ≤ j → L i b j = 0) (c : Fin k → ZMod 2) (z : RBWord k) : ZMod 2 :=
  ∑ j, c j * rbProd ((rbEquiv L hL).symm z) j

private theorem rbDecode_unshift {k : ℕ} (L : RBFeedback k)
    (hL : ∀ i b j, i ≤ j → L i b j = 0) (c : Fin k → ZMod 2) (u : RBWord k) :
    rbDecode L hL c (rbUnshift L u) = ∑ j, c j * rbProd u j := by
  unfold rbDecode
  change (∑ j, c j * rbProd ((rbEquiv L hL).symm (rbEquiv L hL u)) j) = _
  simp

private theorem rbWalsh_sq {k : ℕ} (D : RBWord k → ZMod 2)
    (hD : ∀ x, x ≠ 0 → ∑ z, rbSign (D z) * rbSign (D (x + z)) = 0)
    (a : RBWord k) :
    (∑ z, rbSign (D z + rbLin a z)) ^ 2 = (Fintype.card (RBWord k) : ℝ) := by
  classical
  let f := fun z => rbSign (D z + rbLin a z)
  have hg : ∀ x : RBWord k, ∑ z, f z * f (z + x) =
      rbSign (rbLin a x) * ∑ z, rbSign (D z) * rbSign (D (x + z)) := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp only [f, rbLin_add, rbSign_mul]
    rw [add_comm z x]
    calc
      _ = (rbSign (rbLin a z) * rbSign (rbLin a z)) *
          (rbSign (rbLin a x) * (rbSign (D z) * rbSign (D (x + z)))) := by ring
      _ = _ := by rw [rbSign_sq, one_mul]
  have he : ∀ z : RBWord k, (∑ w, f z * f w) = ∑ x, f z * f (z + x) := by
    intro z
    exact Fintype.sum_equiv (Equiv.addLeft z).symm _ _ (fun x => by
      exact congrArg (fun y => f z * f y) ((Equiv.addLeft z).apply_symm_apply x).symm)
  change (∑ z, f z) ^ 2 = _
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, he]
  rw [Finset.sum_comm, Finset.sum_eq_single (0 : RBWord k)]
  · simp only [add_zero, f, rbSign_sq, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  · intro x _ hx
    rw [hg, hD x hx, mul_zero]
  · simp

private theorem rbLin_unshift {k : ℕ} (L : RBFeedback k) (a u : RBWord k) :
    rbLin a (rbUnshift L u) = rbLin a u + ∑ j, rbLin a (fun i b => L i b j) * rbProd u j := by
  change rbLin a (u + fun i b => ∑ j, L i b j * rbProd u j) = _
  rw [rbLin_add]
  congr 1
  unfold rbLin
  calc
    _ = ∑ i : Fin k, ∑ j : Fin k,
        (a i 0 * L i 0 j + a i 1 * L i 1 j) * rbProd u j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]

private def rbPairSum (c : ZMod 2) (a : Fin 2 → ZMod 2) : ℝ :=
  ∑ v : Fin 2 → ZMod 2, rbSign (c * (v 0 * v 1) + (a 0 * v 0 + a 1 * v 1))

private theorem rbPairSum_sq (c : ZMod 2) (a : Fin 2 → ZMod 2) :
    rbPairSum c a ^ 2 = if c = 1 then 4 else if a 0 = 0 ∧ a 1 = 0 then 16 else 0 := by
  classical
  let e : (Fin 2 → ZMod 2) ≃ (ZMod 2 × ZMod 2) :=
    { toFun := fun v => (v 0, v 1)
      invFun := fun p i => if i = 0 then p.1 else p.2
      left_inv := fun v => funext fun i => by fin_cases i <;> rfl
      right_inv := fun p => by ext <;> rfl }
  unfold rbPairSum
  have hs : (∑ v : Fin 2 → ZMod 2, rbSign (c * (v 0 * v 1) + (a 0 * v 0 + a 1 * v 1))) =
      ∑ v : ZMod 2 × ZMod 2, rbSign (c * (v.1 * v.2) + (a 0 * v.1 + a 1 * v.2)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hs, Fintype.sum_prod_type]
  have hz : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have h01 (z : ZMod 2) : z = 0 ∨ z = 1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h01 c with hc | hc <;> rcases h01 (a 0) with ha | ha <;>
    rcases h01 (a 1) with hb | hb <;>
    simp [hz, rbSign, hc, ha, hb, rb_self] <;> norm_num

private theorem rbWalsh_prod {k : ℕ} (L : RBFeedback k)
    (hL : ∀ i b j, i ≤ j → L i b j = 0) (c : Fin k → ZMod 2) (a : RBWord k) :
    (∑ z, rbSign (rbDecode L hL c z + rbLin a z)) =
      ∏ j, rbPairSum (c j + rbLin a (fun i b => L i b j)) (a j) := by
  classical
  rw [Fintype.sum_equiv (rbEquiv L hL).symm _
      (fun u => rbSign (rbDecode L hL c (rbUnshift L u) + rbLin a (rbUnshift L u))) (fun z => by
        change _ = rbSign (rbDecode L hL c (rbEquiv L hL ((rbEquiv L hL).symm z)) +
          rbLin a (rbEquiv L hL ((rbEquiv L hL).symm z)))
        simp)]
  unfold rbPairSum
  rw [Finset.prod_univ_sum]
  have ht : (Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (Fin 2 → ZMod 2))) =
      (Finset.univ : Finset (RBWord k)) := by simp
  rw [ht]
  apply Finset.sum_congr rfl
  intro u _
  rw [rbDecode_unshift, rbLin_unshift, ← rbSign_sum]
  congr 1
  change (∑ j, c j * rbProd u j) +
    ((∑ j, (a j 0 * u j 0 + a j 1 * u j 1)) +
      ∑ j, rbLin a (fun i b => L i b j) * rbProd u j) = _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold rbProd
  ring

private theorem rbRigid {k : ℕ} (L : RBFeedback k)
    (hL : ∀ i b j, i ≤ j → L i b j = 0) (c : Fin k → ZMod 2)
    (hD : ∀ x, x ≠ 0 → ∑ z, rbSign (rbDecode L hL c z) * rbSign (rbDecode L hL c (x + z)) = 0) :
    (∀ j, c j = 1) ∧ (∀ i b j, L i b j = 0) := by
  classical
  have hall (a : RBWord k) (j : Fin k) : c j + rbLin a (fun i b => L i b j) = 1 := by
    let f := fun j => rbPairSum (c j + rbLin a (fun i b => L i b j)) (a j) ^ 2
    have hp : (∏ j, f j) = ∏ _j : Fin k, (4 : ℝ) := by
      have h := rbWalsh_sq _ hD a
      rw [rbWalsh_prod, rb_card] at h
      change (∏ j, rbPairSum (c j + rbLin a (fun i b => L i b j)) (a j)) ^ 2 = _ at h
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_mul] at h
      simpa [f, Finset.prod_pow, show (2 : ℝ)^2 = 4 by norm_num] using h
    have hn (i : Fin k) : f i ≠ 0 := by
      intro hi
      have hz : (∏ i, f i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hz] at hp
      have hpos : (0 : ℝ) < ∏ _j : Fin k, (4 : ℝ) := by positivity
      linarith
    have hvals (i : Fin k) : f i = 4 ∨ f i = 16 := by
      dsimp only [f] at *
      rw [rbPairSum_sq]
      split_ifs with hc hz
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hn i (by rw [rbPairSum_sq, ite_eq_right hc, ite_eq_right hz]))
    have hle : ∀ i : Fin k, i ∈ Finset.univ → (4 : ℝ) ≤ f i := by
      intro i _
      rcases hvals i with hi | hi
      · exact hi.ge
      · simpa only [hi] using (show (4 : ℝ) ≤ 16 by norm_num)
    by_contra hj
    have hj' : f j = 16 := by
      have hnj := hn j
      dsimp only [f] at hnj ⊢
      rw [rbPairSum_sq, ite_eq_right hj] at hnj ⊢
      by_cases hz : a j 0 = 0 ∧ a j 1 = 0
      · simp [hz]
      · exact False.elim (hnj (by simp [hz]))
    have hh := Finset.prod_lt_prod₀ (s := Finset.univ) (fun _ _ => (by norm_num : (0 : ℝ) < 4))
      hle ⟨j, Finset.mem_univ j, by rw [hj']; norm_num⟩
    exact (ne_of_lt hh) hp.symm
  have hc (j : Fin k) : c j = 1 := by simpa [rbLin] using hall 0 j
  refine ⟨hc, ?_⟩
  intro i b j
  let a : RBWord k := fun r s => if r = i ∧ s = b then 1 else 0
  have hd : rbLin a (fun r s => L r s j) = L i b j := by
    unfold rbLin
    rw [Finset.sum_eq_single i]
    · fin_cases b <;> simp [a]
    · intro r _ hr
      simp [a, hr]
    · simp
  have he := hall a j
  rw [hc, hd, ← add_zero (1 : ZMod 2)] at he
  exact add_left_cancel he

private def rbQuad {k : ℕ} (u : RBWord k) : ZMod 2 := ∑ j, rbProd u j

private theorem rbDecode_quad {k : ℕ} (L : RBFeedback k)
    (hL : ∀ i b j, i ≤ j → L i b j = 0) (c : Fin k → ZMod 2)
    (hc : ∀ j, c j = 1) (hz : ∀ i b j, L i b j = 0) (x : RBWord k) :
    rbDecode L hL c x = rbQuad x := by
  have hx : rbUnshift L x = x := by funext i b; simp [rbUnshift, hz]
  conv_lhs => rw [← hx]
  rw [rbDecode_unshift]
  simp [hc, rbQuad]

private def rbFlip {k : ℕ} (x : RBWord k) : RBWord k := fun i b => x i (1 - b)

private theorem rbFlip_inj {k : ℕ} : Function.Injective (@rbFlip k) := by
  intro u v h
  funext i b
  fin_cases b
  · exact congrFun (congrFun h i) 1
  · exact congrFun (congrFun h i) 0

private theorem rbQuad_add {k : ℕ} (u v : RBWord k) :
    rbQuad (u + v) = rbQuad u + rbQuad v + rbLin u (rbFlip v) := by
  unfold rbQuad rbLin
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (u i 0 + v i 0) * (u i 1 + v i 1) =
    u i 0 * u i 1 + v i 0 * v i 1 + (u i 0 * v i 1 + u i 1 * v i 0)
  ring

open scoped BigOperators

private def rbBitsBit (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem rbBitsBit_inj : Function.Injective rbBitsBit := by
  intro a b h
  cases a <;> cases b <;> simp_all [rbBitsBit]

private theorem rbBits_and (a b : Bool) : rbBitsBit (a && b) = rbBitsBit a * rbBitsBit b := by
  cases a <;> cases b <;> decide

private def rbCoord (k : ℕ) : Fin k × Fin 2 ≃ Fin (2*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))

private def rbTest (k : ℕ) (x : Fin (2^(2*k))) (i : Fin k) (b : Fin 2) : ZMod 2 :=
  rbBitsBit (x.val.testBit (rbCoord k (i,b)).val)

private theorem rbTest_inj (k : ℕ) : Function.Injective (rbTest k) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 2*k
  · let p := (rbCoord k).symm ⟨i, hi⟩
    have hp : rbCoord k p = ⟨i, hi⟩ := (rbCoord k).apply_symm_apply _
    have he := congrFun (congrFun h p.1) p.2
    change rbBitsBit (x.val.testBit (rbCoord k p).val) =
      rbBitsBit (y.val.testBit (rbCoord k p).val) at he
    rw [hp] at he
    exact rbBitsBit_inj he
  · have hp : 2^(2*k) ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le hp), Nat.testBit_lt_two_pow (y.isLt.trans_le hp)]

private noncomputable def rbEncode (k : ℕ) : (Fin k → Fin 2 → ZMod 2) ≃ Fin (2^(2*k)) :=
  (Equiv.ofBijective (rbTest k) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨rbTest_inj k, by simp only [Fintype.card_fin, Fintype.card_fun, ZMod.card]; rw [pow_mul]⟩)).symm

private theorem rbTest_encode (k : ℕ) (x : Fin k → Fin 2 → ZMod 2) : rbTest k (rbEncode k x) = x :=
  (rbEncode k).symm_apply_apply x

private theorem rbBits_parity (n : ℕ) : rbBitsBit (n % 2 == 1) = (n : ZMod 2) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h
  · have hh : rbBitsBit (n % 2 == 1) = 0 := by simp [h, rbBitsBit]
    rw [hh]
    apply ZMod.val_injective 2
    exact (ZMod.val_natCast 2 n).trans h |>.symm
  · have hh : rbBitsBit (n % 2 == 1) = 1 := by simp [h, rbBitsBit]
    rw [hh]
    apply ZMod.val_injective 2
    exact (ZMod.val_natCast 2 n).trans h |>.symm

private theorem rbDot_encode (k : ℕ) (x y : Fin k → Fin 2 → ZMod 2) :
    rbBitsBit (((Finset.univ : Finset (Fin (2*k))).filter (fun b =>
      (rbEncode k x).val.testBit b.val && (rbEncode k y).val.testBit b.val)).card % 2 == 1) =
      ∑ i, (x i 0 * y i 0 + x i 1 * y i 1) := by
  classical
  let p : Fin (2*k) → Bool := fun b =>
    (rbEncode k x).val.testBit b.val && (rbEncode k y).val.testBit b.val
  change rbBitsBit ((Finset.univ.filter (fun b => p b)).card % 2 == 1) = _
  rw [rbBits_parity]
  have hcount : ((Finset.univ.filter (fun b => p b)).card : ZMod 2) =
      ∑ b, rbBitsBit (p b) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    cases p b <;> simp [rbBitsBit]
  rw [hcount, Fintype.sum_equiv (rbCoord k).symm _
      (fun ij => x ij.1 ij.2 * y ij.1 ij.2) (fun b => by
        let ij := (rbCoord k).symm b
        have h := (rbCoord k).apply_symm_apply b
        change rbBitsBit (p b) = x ij.1 ij.2 * y ij.1 ij.2
        rw [← congrFun (congrFun (rbTest_encode k x) ij.1) ij.2,
          ← congrFun (congrFun (rbTest_encode k y) ij.1) ij.2]
        unfold rbTest
        change rbBitsBit (p b) = rbBitsBit ((rbEncode k x).val.testBit (rbCoord k ij).val) *
          rbBitsBit ((rbEncode k y).val.testBit (rbCoord k ij).val)
        rw [show rbCoord k ij = b from h]
        exact rbBits_and _ _), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_two _

open scoped BigOperators

private def rbExtend {k t : ℕ} {A : Type*} [Zero A] (f : Fin k → A) (i : Fin t) : A :=
  if hi : i.val < k then f ⟨i.val, hi⟩ else 0

private theorem rbExtend_sum {k t : ℕ} {A : Type*} [AddCommMonoid A]
    (hk : k ≤ t) (f : Fin k → A) : (∑ i : Fin t, rbExtend f i) = ∑ j, f j := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.map (Fin.castLEEmb hk), rbExtend f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hn : ¬ i.val < k := by
        intro h
        apply hi
        exact Finset.mem_map.mpr ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
      simp [rbExtend, hn]
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro j _
      simp [rbExtend, j.isLt]

private def rbExpandL {k t : ℕ} (L : Fin k → Fin 2 → Fin k → ZMod 2)
    (i : Fin t) (b : Fin 2) (j : Fin t) : ZMod 2 :=
  if hi : i.val < k then rbExtend (L ⟨i.val, hi⟩ b) j else 0

private theorem rbExpandL_tri {k t : ℕ} {L : Fin k → Fin 2 → Fin k → ZMod 2}
    (hL : ∀ i b j, i ≤ j → L i b j = 0) :
    ∀ (i : Fin t) b j, i ≤ j → rbExpandL L i b j = 0 := by
  intro i b j hij
  unfold rbExpandL rbExtend
  split_ifs with hi hj
  · exact hL _ _ _ hij
  · rfl
  · rfl

private theorem rbExpand_prod_sum {k t : ℕ} (hk : k ≤ t) (c : Fin k → ZMod 2)
    (u : Fin k → Fin 2 → ZMod 2) :
    (∑ j : Fin t, rbExtend c j * (rbExtend u j 0 * rbExtend u j 1)) =
      ∑ j, c j * (u j 0 * u j 1) := by
  rw [← rbExtend_sum (t := t) hk (fun j => c j * (u j 0 * u j 1))]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k <;> simp [rbExtend, hj]

private theorem rbExpand_operands {k t : ℕ} (hk : k ≤ t)
    (L : Fin k → Fin 2 → Fin k → ZMod 2) (u r : Fin k → Fin 2 → ZMod 2)
    (hu : ∀ i b, u i b = r i b + ∑ j, L i b j * (u j 0 * u j 1)) :
    ∀ (i : Fin t) b, rbExtend u i b = rbExtend r i b +
      ∑ j : Fin t, rbExpandL L i b j * (rbExtend u j 0 * rbExtend u j 1) := by
  intro i b
  by_cases hi : i.val < k
  · simpa only [rbExtend, rbExpandL, dite_eq_left hi] using
      (hu ⟨i.val, hi⟩ b).trans (congrArg (fun z => r ⟨i.val, hi⟩ b + z)
        (rbExpand_prod_sum hk (L ⟨i.val, hi⟩ b) u).symm)
  · simp [rbExtend, rbExpandL, hi]

private theorem rbExtend_full {k t : ℕ} (hkt : k ≤ t) (c : Fin k → ZMod 2)
    (hc : ∀ i : Fin t, rbExtend c i = 1) : k = t := by
  apply Nat.le_antisymm hkt
  by_contra h
  have hh := hc ⟨k, by omega⟩
  simp [rbExtend] at hh

private def rbInXor {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool := fun i => xor (x i) (y i)

private def rbAff {n : ℕ} (f : (Fin n → Bool) → ZMod 2) : Prop :=
  ∀ x y, f x + f y = f (rbInXor x y) + f (fun _ => false)

private theorem rbAff_extend {n k t : ℕ} {f : (Fin n → Bool) → Fin k → Fin 2 → ZMod 2}
    (hf : ∀ i b, rbAff (fun x => f x i b)) :
    ∀ (i : Fin t) b, rbAff (fun x => rbExtend (f x) i b) := by
  intro i b x y
  by_cases hi : i.val < k
  · simpa only [rbExtend, dite_eq_left hi] using hf ⟨i.val, hi⟩ b x y
  · simp [rbExtend, hi]

private def rbLeft {N : ℕ} (x : Fin N) : Fin (N+N) → Bool :=
  Fin.append (fun i => decide (i = x)) (fun _ => false)

private def rbRight {N : ℕ} (y : Fin N) : Fin (N+N) → Bool :=
  Fin.append (fun _ => false) (fun i => decide (i = y))

private theorem rbInXor_oneEach {N : ℕ} (x y : Fin N) :
    List.ofFn (rbInXor (rbLeft x) (rbRight y)) = PEqualNP.Represents.oneEach x y := by
  have h : rbInXor (rbLeft x) (rbRight y) = Fin.append (fun i => decide (i = x)) (fun i => decide (i = y)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [rbInXor, rbLeft, rbRight, Fin.append, Fin.addCases_left, Fin.addCases_right] <;>
      simp
  rw [h, List.ofFn_fin_append, PEqualNP.Represents.oneEach]

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

private def rbHits {N : ℕ} (F G : Fin N → Fin N → Bool) : ℕ :=
  ∑ x : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun y => F x y = G x y)).card

private def rbDot {k : ℕ} (x y : Fin (2^(2*k))) : Bool :=
  ((Finset.univ : Finset (Fin (2*k))).filter (fun b => x.val.testBit b.val && y.val.testBit b.val)).card % 2 == 1

private theorem rbDot_encoded {k : ℕ} (x y : RBWord k) :
    rbBit (rbDot (rbEncode k x) (rbEncode k y)) = rbLin x y := rbDot_encode k x y

private theorem rbFiber_push {α β : Type*} [DecidableEq α] [DecidableEq β]
    {N h : ℕ} (f : Fin N → α) (e : α → β)
    (he : Function.Bijective e)
    (hf : ∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => f x = p)).card = h^2) :
    ∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => e (f x) = p)).card = h^2 := by
  classical
  intro p
  obtain ⟨a, rfl⟩ := he.2 p
  convert hf a using 2
  ext x
  simp [he.1.eq_iff]

private theorem rbAff_coeffs {n : ℕ} {f : (Fin n → Bool) → ZMod 2}
    (hf : ∃ (a : ZMod 2) (l : Fin n → ZMod 2), ∀ x, f x = a + ∑ q, l q * cnfBit (x q)) :
    rbAff f := by
  obtain ⟨a, l, hf⟩ := hf
  intro x y
  simp only [hf, rbInXor]
  change (a + ∑ q, l q * rbBit (x q)) + (a + ∑ q, l q * rbBit (y q)) =
    (a + ∑ q, l q * rbBit (xor (x q) (y q))) + (a + ∑ q, l q * rbBit false)
  simp only [rbBit_xor, mul_add, Finset.sum_add_distrib, show rbBit false = 0 from rfl, mul_zero,
    Finset.sum_const_zero, add_zero]
  ring

private theorem rbCombine {N h k t : ℕ} (C : Circuit) (nonlinear : Gate → Bool)
    (hkt : k ≤ t) (hk : C.gates.countP nonlinear = k)
    (G : Fin N → Fin N → Bool)
    (L : RBFeedback k) (c : Fin k → ZMod 2)
    (u raw : (Fin (N+N) → Bool) → RBWord k) (lin : (Fin (N+N) → Bool) → ZMod 2)
    (hL : ∀ i b j, i ≤ j → L i b j = 0)
    (hu : ∀ a i b, u a i b = raw a i b + ∑ j, L i b j * (u a j 0 * u a j 1))
    (hraw : ∀ i b, rbAff (fun a => raw a i b)) (hlin : rbAff lin)
    (hval : ∀ a, rbBit (C.eval (List.ofFn a)) = lin a + ∑ j, c j * (u a j 0 * u a j 1))
    (hcovered : ∀ g ∈ C.gates, nonlinear g = true → ∀ w ∈ g.inputs,
      ∃ i b, ∀ a, rbBit ((C.wires (List.ofFn a)).getD w false) = u a i b)
    (hBlock : ∀ (row col : Fin N → RBWord t) (Q R : Fin N → Bool) (d : RBWord t → RBWord t → Bool),
      (∀ x y, C.eval (PEqualNP.Represents.oneEach x y) = xor (xor (Q x) (R y)) (d (row x) (col y))) →
      let hits := rbHits (fun x y => C.eval (PEqualNP.Represents.oneEach x y)) G
      2*h*hits ≤ (h+1)*N^2 ∧
      (2*h*hits = (h+1)*N^2 →
        (∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card = h^2 ∧
          ((Finset.univ : Finset (Fin N)).filter (fun y => col y = p)).card = h^2) ∧
        ∀ a b, a ≠ b → ∑ p, rbSign (rbBit (d a p)) * rbSign (rbBit (d b p)) = 0)) :
    let hits := rbHits (fun x y => C.eval (PEqualNP.Represents.oneEach x y)) G
    2*h*hits ≤ (h+1)*N^2 ∧
      (2*h*hits = (h+1)*N^2 → C.gates.countP nonlinear = t ∧
      (∃ (row col : Fin N → Fin (2^(2*t))) (Q R : Fin N → Bool),
        (∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card = h^2 ∧
          ((Finset.univ : Finset (Fin N)).filter (fun y => col y = p)).card = h^2) ∧
        ∀ x y, C.eval (PEqualNP.Represents.oneEach x y) = xor (xor (Q x) (R y)) (rbDot (row x) (col y))) ∧
      ∀ g ∈ C.gates, nonlinear g = true → ∀ w ∈ g.inputs,
        let W := fun (x : Fin (N+N) → Bool) => (C.wires (List.ofFn x)).getD w false
        ∀ x y, xor (W x) (W y) = xor (W (fun i => xor (x i) (y i))) (W (fun _ => false))) := by
  classical
  let L' : RBFeedback t := rbExpandL L
  let hL' : ∀ i b j, i ≤ j → L' i b j = 0 := rbExpandL_tri hL
  let c' : Fin t → ZMod 2 := rbExtend c
  let u' : (Fin (N+N) → Bool) → RBWord t := fun a => rbExtend (u a)
  let raw' : (Fin (N+N) → Bool) → RBWord t := fun a => rbExtend (raw a)
  let D := rbDecode L' hL' c'
  have hu' (a : Fin (N+N) → Bool) (i : Fin t) (b : Fin 2) :
      u' a i b = raw' a i b + ∑ j, L' i b j * rbProd (u' a) j :=
    rbExpand_operands hkt L (u a) (raw a) (hu a) i b
  have hraw' (i : Fin t) (b : Fin 2) : rbAff (fun a => raw' a i b) := rbAff_extend hraw i b
  have hD (a : Fin (N+N) → Bool) :
      rbBit (C.eval (List.ofFn a)) = lin a + D (raw' a) := by
    have he : rbUnshift L' (u' a) = raw' a := by
      funext i b
      change u' a i b + (∑ j, L' i b j * rbProd (u' a) j) = raw' a i b
      nth_rw 1 [hu' a i b]
      rw [add_assoc, rb_self, add_zero]
    rw [hval, ← he]
    change _ = lin a + rbDecode L' hL' c' (rbUnshift L' (u' a))
    rw [rbDecode_unshift]
    congr 1
    exact (rbExpand_prod_sum hkt c (u a)).symm
  let A : Fin N → RBWord t := fun x => raw' (rbLeft x)
  let B : Fin N → RBWord t := fun y => raw' (rbRight y) + raw' (fun _ => false)
  let q : Fin N → ZMod 2 := fun x => lin (rbLeft x)
  let r : Fin N → ZMod 2 := fun y => lin (rbRight y) + lin (fun _ => false)
  have hmodel (x y : Fin N) : rbBit (C.eval (PEqualNP.Represents.oneEach x y)) =
      q x + r y + D (A x + B y) := by
    rw [← rbInXor_oneEach, hD]
    have hl : lin (rbInXor (rbLeft x) (rbRight y)) = q x + r y := by
      have h := hlin (rbLeft x) (rbRight y)
      change _ = lin (rbLeft x) + (lin (rbRight y) + lin (fun _ => false))
      rw [← add_assoc, h, add_assoc, rb_self, add_zero]
    have hr : raw' (rbInXor (rbLeft x) (rbRight y)) = A x + B y := by
      funext i b
      have h := hraw' i b (rbLeft x) (rbRight y)
      change _ = raw' (rbLeft x) i b + (raw' (rbRight y) i b + raw' (fun _ => false) i b)
      rw [← add_assoc, h, add_assoc, rb_self, add_zero]
    rw [hl, hr]
  obtain ⟨hbound, heq⟩ := hBlock A B (fun x => rbBool (q x)) (fun y => rbBool (r y))
    (fun a b => rbBool (D (a+b))) (fun x y => by
      apply rbBit_inj
      simpa only [rbBit_xor, rbBit_bool] using hmodel x y)
  refine ⟨hbound, ?_⟩
  intro he
  obtain ⟨hfib, horth⟩ := heq he
  have hDorth (x : RBWord t) (hx : x ≠ 0) : ∑ z, rbSign (D z) * rbSign (D (x+z)) = 0 := by
    simpa [rbBit_bool] using horth 0 x (Ne.symm hx)
  obtain ⟨hc', hz⟩ := rbRigid L' hL' c' hDorth
  have hq (z) : D z = rbQuad z := rbDecode_quad L' hL' c' hc' hz z
  refine ⟨hk.trans (rbExtend_full hkt c hc'), ?_, ?_⟩
  · let flipE : RBWord t ≃ RBWord t := Equiv.ofBijective rbFlip
      ⟨rbFlip_inj, Finite.surjective_of_injective rbFlip_inj⟩
    refine ⟨fun x => rbEncode t (A x), fun y => (flipE.trans (rbEncode t)) (B y),
      fun x => rbBool (q x + rbQuad (A x)), fun y => rbBool (r y + rbQuad (B y)), ?_, ?_⟩
    · intro p
      exact ⟨rbFiber_push (h := h) A (rbEncode t) (rbEncode t).bijective (fun p => (hfib p).1) p,
        rbFiber_push (h := h) B (flipE.trans (rbEncode t)) (flipE.trans (rbEncode t)).bijective
          (fun p => (hfib p).2) p⟩
    · intro x y
      apply rbBit_inj
      rw [hmodel, hq, rbBit_xor, rbBit_xor, rbBit_bool, rbBit_bool]
      change _ = _ + rbBit (rbDot (rbEncode t (A x)) (rbEncode t (rbFlip (B y))))
      rw [rbDot_encoded, rbQuad_add]
      ring
  · intro g hg hnl w hw W x y
    obtain ⟨i, b, hwval⟩ := hcovered g hg hnl w hw
    let i' : Fin t := Fin.castLE hkt i
    have horig (a) : u' a i' b = u a i b := by simp [u', i', rbExtend, i.isLt]
    have hzero (a) : u' a i' b = raw' a i' b := by simp [hu' a i' b, hz]
    have hwire (a) : rbBit ((C.wires (List.ofFn a)).getD w false) = raw' a i' b :=
      (hwval a).trans ((horig a).symm.trans (hzero a))
    apply rbBit_inj
    simp only [W, rbBit_xor, hwire]
    exact hraw' i' b x y

end PEqualNP.Outside.L_meta_25727_aux

open PEqualNP.Outside.L_meta_25727_aux

theorem PEqualNP.Outside.L_meta_25727 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
∀ s t : ℕ, t ≤ s →
  let N := 2^(2*s)
  let h := 2^(s-t)
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.gates.countP nonlinear ≤ t
  let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin N) =>
    C.eval (PEqualNP.Represents.oneEach x y)
  let M := 2^(2*t)
  let dot := fun (i j : Fin M) =>
    ((Finset.univ : Finset (Fin (2*t))).filter (fun b =>
      i.val.testBit b.val && j.val.testBit b.val)).card % 2 == 1
  ∀ G : Fin N → Fin N → Bool,
  (∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun v => G a v ≠ G b v)).card = N) →
  ∀ C, valid C →
    let hits := ∑ x : Fin N, ((Finset.univ : Finset (Fin N)).filter
      (fun y => value C x y = G x y)).card
    2*h*hits ≤ (h+1)*N^2 ∧
    (2*h*hits = (h+1)*N^2 →
      C.gates.countP nonlinear = t ∧
      (∃ (row col : Fin N → Fin M) (Q R : Fin N → Bool),
        (∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card = h^2 ∧
              ((Finset.univ : Finset (Fin N)).filter (fun y => col y = p)).card = h^2) ∧
        ∀ x y, value C x y = xor (xor (Q x) (R y)) (dot (row x) (col y))) ∧
      ∀ g ∈ C.gates, nonlinear g = true → ∀ w ∈ g.inputs,
        let W := fun (x : Fin (N+N) → Bool) => (C.wires (List.ofFn x)).getD w false
        ∀ x y, xor (W x) (W y) =
          xor (W (fun i => xor (x i) (y i))) (W (fun _ => false)))
:= by
  classical
  intro nonlinear s t hst N h valid value M dot G hG C hC hits
  obtain ⟨hlen, hrb, hcount⟩ := hC
  have hh : 0 < h := by dsimp [h]; positivity
  have hsize : N = h^2 * Fintype.card (RBWord t) := by
    rw [rb_card]
    change 2^(2*s) = (2^(s-t))^2 * 2^(2*t)
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  obtain ⟨L, c, raw, u, lin, hraw, hlin, hL, hu, hv, hw⟩ := circuitNormalForm C hlen hrb
  refine rbCombine (h := h) (t := t) C cnfNonlinear hcount rfl G L c u raw lin hL hu
    (fun i b => rbAff_coeffs (hraw i b)) (rbAff_coeffs hlin) hv hw ?_
  intro row col Q R d hd
  have hs (b : Bool) : corrSign b = rbSign (rbBit b) := by cases b <;> simp [corrSign, rbSign, rbBit]
  simpa only [rbHits, value, hs] using correlationBlocks hh hsize G (value C) hG row col Q R d hd
