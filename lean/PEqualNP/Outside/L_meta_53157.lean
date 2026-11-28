import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53157

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma isNotOp_eq_true_iff (o : GateOp) : isNotOp o = true ↔ o = GateOp.not := by
  cases o <;> simp [isNotOp]

private lemma decide_eq_isNotOp (o : GateOp) (d : Decidable (o = GateOp.not)) :
    @decide (o = GateOp.not) d = isNotOp o := by
  cases o <;> simp [isNotOp]

private def cstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def evalW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl cstep x

private lemma evalW_nil (x : List Bool) : evalW [] x = x := rfl

private lemma evalW_append (gs1 gs2 : List Gate) (x : List Bool) :
    evalW (gs1 ++ gs2) x = evalW gs2 (evalW gs1 x) := by
  simp [evalW, List.foldl_append]

private lemma evalW_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    evalW (gs ++ [g]) x = cstep (evalW gs x) g := by
  rw [evalW_append]; rfl

private lemma evalW_len (gs : List Gate) :
    ∀ x : List Bool, (evalW gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [evalW]
  | cons g gs ih =>
    intro x
    change (evalW gs (cstep x g)).length = x.length + (g :: gs).length
    rw [ih, cstep]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_append_left (l1 l2 : List Bool) (i : Nat) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma evalW_pre (gs : List Gate) :
    ∀ (x : List Bool) (i : Nat), i < x.length → (evalW gs x).getD i false = x.getD i false := by
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    have h1 : i < (cstep x g).length := by simp [cstep]; omega
    change (evalW gs (cstep x g)).getD i false = _
    rw [ih (cstep x g) i h1]
    exact getD_append_left x _ i hi

private lemma evalW_append_pre (gs1 gs2 : List Gate) (x : List Bool) (i : Nat)
    (hi : i < x.length + gs1.length) :
    (evalW (gs1 ++ gs2) x).getD i false = (evalW gs1 x).getD i false := by
  rw [evalW_append]
  exact evalW_pre gs2 (evalW gs1 x) i (by rw [evalW_len]; exact hi)

private lemma evalW_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (evalW (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalW gs x).getD i false) := by
  rw [evalW_snoc]
  dsimp only [cstep]
  have hlen : (evalW gs x).length = x.length + gs.length := evalW_len gs x
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD]

private lemma wires_getD_pre (C : Circuit) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  evalW_pre C.gates x i hi

private lemma wires_getD_gate (C : Circuit) (x : List Bool) (u : Nat) (hu : u < C.size)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + u) false =
      (gateAt C u).op.eval ((gateAt C u).inputs.map fun i => (C.wires x).getD i false) := by
  have hu' : u < C.gates.length := hu
  have hsplit : C.gates = C.gates.take u ++ [C.gates[u]] ++ C.gates.drop (u + 1) := by
    have := List.take_append_drop u C.gates
    rw [List.drop_eq_getElem_cons hu'] at this
    simpa [List.append_assoc] using this.symm
  have hga : gateAt C u = C.gates[u] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu']
  rw [hga]
  change (evalW C.gates x).getD (x.length + u) false = _
  let pre := C.gates.take u
  let post := C.gates.drop (u + 1)
  have hpre_len : pre.length = u := List.length_take_of_le (Nat.le_of_lt hu')
  have h1 : (evalW C.gates x).getD (x.length + u) false =
      C.gates[u].op.eval (C.gates[u].inputs.map fun i => (evalW pre x).getD i false) := by
    conv_lhs => rw [hsplit]
    rw [evalW_append_pre (pre ++ [C.gates[u]]) post x (x.length + u) (by simp [hpre_len])]
    have := evalW_snoc_last pre C.gates[u] x
    rw [hpre_len] at this
    exact this
  rw [h1]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hilt : i < x.length + u := by
    have := hrb u hu' i; rw [hga] at this; exact this hi
  change (evalW pre x).getD i false = (evalW C.gates x).getD i false
  conv_rhs => rw [hsplit, List.append_assoc]
  exact (evalW_append_pre pre ([C.gates[u]] ++ post) x i (by rw [hpre_len]; exact hilt)).symm

private def posCount (gs : List Gate) : Nat :=
  (gs.filter (fun g => !isNotOp g.op)).length

private def notCountL (gs : List Gate) : Nat :=
  (gs.filter (fun g => isNotOp g.op)).length

private lemma notCount_eq_notCountL (C : Circuit) : notCount C = notCountL C.gates := by
  unfold notCount notCountL
  congr 1
  refine List.filter_congr fun g _ => decide_eq_isNotOp g.op _

private lemma posCount_add_notCountL (gs : List Gate) :
    posCount gs + notCountL gs = gs.length := by
  induction gs with
  | nil => simp [posCount, notCountL]
  | cons g gs ih =>
    simp only [posCount, notCountL, List.filter_cons, List.length_cons] at ih ⊢
    cases isNotOp g.op <;> simp <;> omega

private lemma posCount_append (gs1 gs2 : List Gate) :
    posCount (gs1 ++ gs2) = posCount gs1 + posCount gs2 := by
  simp [posCount, List.filter_append]

private lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

private lemma map_range_getD (L : List Gate) (d : Gate) :
    (List.range L.length).map (fun u => L.getD u d) = L := by
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]

private lemma range_filter_not_len (C : Circuit) :
    ((List.range C.size).filter (fun u => isNotOp (gateAt C u).op)).length = notCount C := by
  rw [notCount_eq_notCountL]
  have h := congrArg (fun L => (L.filter (fun g => isNotOp g.op)).length)
    (map_range_getD C.gates ⟨GateOp.or, []⟩)
  rw [List.filter_map, List.length_map] at h
  exact h

private def ValidGates (N : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < N + 2 + j)

private lemma validGates_nil (N : Nat) : ValidGates N [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

private lemma validGates_to_valid (N : Nat) (gs : List Gate) (h : ValidGates N gs) :
    FanInTwo ⟨gs, 0⟩ ∧ ReadsBack (N + 2) ⟨gs, 0⟩ ∧ (⟨gs, 0⟩ : Circuit).output < N + 2 + (⟨gs, 0⟩ : Circuit).size := by
  refine ⟨fun g hg => ?_, h.2, by simp [Circuit.size]⟩
  rcases h.1 g hg with ⟨hop, hlen⟩
  refine ⟨?_, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact hop

private lemma validGates_snoc (N : Nat) (gs : List Gate) (g : Gate)
    (hgs : ValidGates N gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < N + 2 + gs.length) :
    ValidGates N (gs ++ [g]) := by
  refine ⟨fun g' hg' => ?_, fun j hj i hi => ?_⟩
  · rcases List.mem_append.mp hg' with h1 | h2
    · exact hgs.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact ⟨hop, hlen⟩
  · simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi

private def bitsRank (f : Nat → Bool) (L : List Nat) (acc : Nat) : Nat :=
  L.foldl (fun v u => 2 * v + (if f u then 0 else 1)) acc

private lemma bitsRank_cons (f : Nat → Bool) (a : Nat) (L : List Nat) (acc : Nat) :
    bitsRank f (a :: L) acc = bitsRank f L (2 * acc + (if f a then 0 else 1)) := rfl

private lemma bitsRank_shift (f : Nat → Bool) (L : List Nat) :
    ∀ acc : Nat, bitsRank f L acc = acc * 2 ^ L.length + bitsRank f L 0 := by
  induction L with
  | nil => intro acc; simp [bitsRank]
  | cons a L ih =>
    intro acc
    rw [bitsRank_cons, bitsRank_cons, Nat.mul_zero, Nat.zero_add]
    rw [ih (2 * acc + (if f a then 0 else 1)), ih (if f a then 0 else 1)]
    have hp : 2 ^ (a :: L).length = 2 * 2 ^ L.length := by rw [List.length_cons, pow_succ, Nat.mul_comm]
    rw [hp]; ring

private lemma bitsRank_lt (f : Nat → Bool) (L : List Nat) :
    bitsRank f L 0 < 2 ^ L.length := by
  induction L with
  | nil => simp [bitsRank]
  | cons a L ih =>
    rw [bitsRank_cons, Nat.mul_zero, Nat.zero_add, bitsRank_shift]
    have hbit : (if f a then 0 else 1) ≤ 1 := by cases f a <;> decide
    have hp : 2 ^ (a :: L).length = 2 * 2 ^ L.length := by rw [List.length_cons, pow_succ, Nat.mul_comm]
    rw [hp]
    have := Nat.mul_le_mul_right (2 ^ L.length) hbit
    omega

private lemma bitsRank_testBit (f : Nat → Bool) (L : List Nat) :
    ∀ (s : Nat) (hs : s < L.length),
      (bitsRank f L 0).testBit (L.length - 1 - s) = !(f L[s]) := by
  induction L with
  | nil => intro s hs; simp at hs
  | cons a L ih =>
    intro s hs
    have hval : bitsRank f (a :: L) 0 = (if f a then 0 else 1) * 2 ^ L.length + bitsRank f L 0 := by
      rw [bitsRank_cons, Nat.mul_zero, Nat.zero_add]
      exact bitsRank_shift f L _
    have hrem : bitsRank f L 0 < 2 ^ L.length := bitsRank_lt f L
    rw [hval]
    cases s with
    | zero =>
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : ((if f a then 0 else 1) * 2 ^ L.length + bitsRank f L 0) / 2 ^ L.length =
          (if f a then 0 else 1) := by
        rw [Nat.mul_comm (if f a then 0 else 1) (2 ^ L.length),
          Nat.mul_add_div (Nat.two_pow_pos L.length), Nat.div_eq_of_lt hrem, Nat.add_zero]
      rw [hdiv]
      cases f a <;> decide
    | succ s =>
      simp only [List.length_cons, List.getElem_cons_succ]
      have hs' : s < L.length := Nat.lt_of_succ_lt_succ hs
      have hidx : L.length + 1 - 1 - (s + 1) = L.length - 1 - s := by omega
      rw [hidx, ← ih s hs']
      set r := L.length - 1 - s
      have hr : r < L.length := by omega
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ L.length = 2 ^ r * (2 * 2 ^ (L.length - r - 1)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have hdiv : ((if f a then 0 else 1) * 2 ^ L.length + bitsRank f L 0) / 2 ^ r =
          (if f a then 0 else 1) * (2 * 2 ^ (L.length - r - 1)) + bitsRank f L 0 / 2 ^ r := by
        rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (if f a then 0 else 1) (2 ^ r), Nat.mul_assoc,
          Nat.mul_add_div (Nat.two_pow_pos r)]
      rw [hdiv]
      have hmod : ((if f a then 0 else 1) * (2 * 2 ^ (L.length - r - 1)) + bitsRank f L 0 / 2 ^ r) % 2 =
          (bitsRank f L 0 / 2 ^ r) % 2 := by
        have hmul : (if f a then 0 else 1) * (2 * 2 ^ (L.length - r - 1)) =
            2 * ((if f a then 0 else 1) * 2 ^ (L.length - r - 1)) := by ring
        rw [hmul, Nat.mul_add_mod]
      rw [hmod]

private lemma nat_lt_two_iff (a : Nat) (h : a < 2) : a = 0 ∨ a = 1 := by omega

private lemma lt_iff_exists_msb_diff (b x y : Nat) (hx : x < 2 ^ b) (hy : y < 2 ^ b) :
    x < y ↔ ∃ s < b, (∀ j < s, x.testBit (b - 1 - j) = y.testBit (b - 1 - j)) ∧
      x.testBit (b - 1 - s) = false ∧ y.testBit (b - 1 - s) = true := by
  induction b generalizing x y with
  | zero => simp at hx hy; omega
  | succ b ih =>
    set P := 2 ^ b
    have hP : 0 < P := Nat.two_pow_pos b
    have hp : 2 ^ (b + 1) = 2 * P := by dsimp only [P]; rw [pow_succ, Nat.mul_comm]
    set qx := x / P
    set qy := y / P
    set rx := x % P
    set ry := y % P
    have hxhi : qx < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
    have hyhi : qy < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
    have hxlo : rx < P := Nat.mod_lt x hP
    have hylo : ry < P := Nat.mod_lt y hP
    have hx_bit_top : x.testBit b = decide (qx = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (qx % 2 = 1) = decide (qx = 1)
      rw [Nat.mod_eq_of_lt hxhi]
    have hy_bit_top : y.testBit b = decide (qy = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (qy % 2 = 1) = decide (qy = 1)
      rw [Nat.mod_eq_of_lt hyhi]
    have hx_bit_lo : ∀ r < b, rx.testBit r = x.testBit r := fun r hr => by
      dsimp only [rx, P]; rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]
    have hy_bit_lo : ∀ r < b, ry.testBit r = y.testBit r := fun r hr => by
      dsimp only [ry, P]; rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]
    have hx_dm : x = qx * P + rx := by
      have := Nat.div_add_mod x P; rw [Nat.mul_comm] at this; exact this.symm
    have hy_dm : y = qy * P + ry := by
      have := Nat.div_add_mod y P; rw [Nat.mul_comm] at this; exact this.symm
    constructor
    · intro hxy
      by_cases htop : qx = qy
      · have hmodlt : rx < ry := by rw [hx_dm, hy_dm, htop] at hxy; omega
        rcases (ih rx ry hxlo hylo).mp hmodlt with ⟨s, hs, hpre, hxf, hyt⟩
        refine ⟨s + 1, by omega, ?_, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero => simp only [Nat.add_sub_cancel, Nat.sub_zero, hx_bit_top, hy_bit_top, htop]
          | succ j =>
            have hidx : b + 1 - 1 - (j + 1) = b - 1 - j := by omega
            rw [hidx, ← hx_bit_lo (b - 1 - j) (by omega), ← hy_bit_lo (b - 1 - j) (by omega)]
            exact hpre j (by omega)
        · have hidx : b + 1 - 1 - (s + 1) = b - 1 - s := by omega
          rw [hidx, ← hx_bit_lo (b - 1 - s) (by omega)]; exact hxf
        · have hidx : b + 1 - 1 - (s + 1) = b - 1 - s := by omega
          rw [hidx, ← hy_bit_lo (b - 1 - s) (by omega)]; exact hyt
      · have hqx_qy : qx = 0 ∧ qy = 1 := by
          rcases nat_lt_two_iff qx hxhi with hqx0 | hqx1 <;>
          rcases nat_lt_two_iff qy hyhi with hqy0 | hqy1
          · exact absurd (hqx0.trans hqy0.symm) htop
          · exact ⟨hqx0, hqy1⟩
          · rw [hx_dm, hy_dm, hqx1, hqy0, Nat.one_mul, Nat.zero_mul, Nat.zero_add] at hxy; omega
          · exact absurd (hqx1.trans hqy1.symm) htop
        refine ⟨0, by omega, fun j hj => by omega, ?_, ?_⟩
        · simp [hx_bit_top, hqx_qy.1]
        · simp [hy_bit_top, hqx_qy.2]
    · rintro ⟨s, hs, hpre, hxf, hyt⟩
      cases s with
      | zero =>
        simp only [Nat.add_sub_cancel, Nat.sub_zero, hx_bit_top, hy_bit_top] at hxf hyt
        have hx0 : qx = 0 := (nat_lt_two_iff qx hxhi).resolve_right (of_decide_eq_false hxf)
        have hy1 : qy = 1 := of_decide_eq_true hyt
        rw [hx_dm, hy_dm, hx0, hy1, Nat.zero_mul, Nat.zero_add, Nat.one_mul]; omega
      | succ s =>
        have htop_bit := hpre 0 (by omega)
        simp only [Nat.add_sub_cancel, Nat.sub_zero, hx_bit_top, hy_bit_top] at htop_bit
        have htop : qx = qy := by
          by_cases h1 : qx = 1
          · rw [decide_eq_true h1] at htop_bit
            exact h1.trans (of_decide_eq_true htop_bit.symm).symm
          · rw [decide_eq_false h1] at htop_bit
            exact ((nat_lt_two_iff qx hxhi).resolve_right h1).trans
              ((nat_lt_two_iff qy hyhi).resolve_right (of_decide_eq_false htop_bit.symm)).symm
        have hmodlt : rx < ry := by
          apply (ih rx ry hxlo hylo).mpr
          refine ⟨s, by omega, ?_, ?_, ?_⟩
          · intro j hj
            rw [hx_bit_lo (b - 1 - j) (by omega), hy_bit_lo (b - 1 - j) (by omega)]
            have hidx : b - 1 - j = b + 1 - 1 - (j + 1) := by omega
            rw [hidx]; exact hpre (j + 1) (by omega)
          · rw [hx_bit_lo (b - 1 - s) (by omega)]
            have hidx : b - 1 - s = b + 1 - 1 - (s + 1) := by omega
            rw [hidx]; exact hxf
          · rw [hy_bit_lo (b - 1 - s) (by omega)]
            have hidx : b - 1 - s = b + 1 - 1 - (s + 1) := by omega
            rw [hidx]; exact hyt
        rw [hx_dm, hy_dm, htop]; omega

private lemma mono_pre_wires (L : Nat) (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack L C)
    (v1 v2 : List Bool) (hv1 : v1.length = L) (hv2 : v2.length = L)
    (hin : ∀ u < L, v1.getD u false = true → v2.getD u false = true)
    (lim : Nat) (hlim : lim ≤ C.size)
    (hnot_eq : ∀ u < lim, isNotOp (gateAt C u).op = true →
      (C.wires v1).getD (L + u) false = (C.wires v2).getD (L + u) false) :
    ∀ w < L + lim, (C.wires v1).getD w false = true → (C.wires v2).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw h1
    by_cases hwL : w < L
    · rw [wires_getD_pre C v1 w (by rw [hv1]; exact hwL)] at h1
      rw [wires_getD_pre C v2 w (by rw [hv2]; exact hwL)]
      exact hin w hwL h1
    · set u := w - L
      have hweq : w = L + u := by omega
      have hult : u < lim := by omega
      have husz : u < C.size := lt_of_lt_of_le hult hlim
      rw [hweq] at h1 ⊢
      by_cases hnotu : isNotOp (gateAt C u).op = true
      · rw [← hnot_eq u hult hnotu]; exact h1
      · have hgmem : gateAt C u ∈ C.gates := by
          have hu' : u < C.gates.length := husz
          have hga : gateAt C u = C.gates[u] := by
            simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu']
          rw [hga]; exact List.getElem_mem hu'
        have hop_ao : (gateAt C u).op = GateOp.and ∨ (gateAt C u).op = GateOp.or := by
          have := (hfan (gateAt C u) hgmem).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          rcases this with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd ((isNotOp_eq_true_iff _).mpr h) hnotu
        have hrb1 : ReadsBack v1.length C := by rw [hv1]; exact hrb
        have hrb2 : ReadsBack v2.length C := by rw [hv2]; exact hrb
        have hg1 := wires_getD_gate C v1 u husz hrb1
        have hg2 := wires_getD_gate C v2 u husz hrb2
        rw [hv1] at hg1; rw [hv2] at hg2
        rw [hg1] at h1; rw [hg2]
        rcases hop_ao with hand | hor
        · rw [hand] at h1 ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at h1 ⊢
          rintro _ ⟨a, ha, rfl⟩
          have halt : a < L + u := hrb u husz a ha
          exact ih a (by omega) (by omega) (h1 _ ⟨a, ha, rfl⟩)
        · rw [hor] at h1 ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at h1 ⊢
          rcases h1 with ⟨_, ⟨a, ha, rfl⟩, ha1⟩
          have halt : a < L + u := hrb u husz a ha
          exact ⟨_, ⟨a, ha, rfl⟩, ih a (by omega) (by omega) ha1⟩

private lemma rank_mono (L : Nat) (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack L C)
    (v1 v2 : List Bool) (hv1 : v1.length = L) (hv2 : v2.length = L)
    (hin : ∀ u < L, v1.getD u false = true → v2.getD u false = true) :
    let gates := (List.range C.size).filter (fun u => isNotOp (gateAt C u).op)
    bitsRank (fun u => (C.wires v1).getD (L + u) false) gates 0 ≤
      bitsRank (fun u => (C.wires v2).getD (L + u) false) gates 0 := by
  intro gates
  by_contra hnot
  have hlt : bitsRank (fun u => (C.wires v2).getD (L + u) false) gates 0 <
      bitsRank (fun u => (C.wires v1).getD (L + u) false) gates 0 := by omega
  have hr1_lt := bitsRank_lt (fun u => (C.wires v1).getD (L + u) false) gates
  have hr2_lt := bitsRank_lt (fun u => (C.wires v2).getD (L + u) false) gates
  rcases (lt_iff_exists_msb_diff gates.length _ _ hr2_lt hr1_lt).mp hlt with ⟨s, hs, hpre, h2f, h1t⟩
  have hgates_sorted : gates.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  set u0 := gates[s]
  have hu0_mem : u0 ∈ gates := List.getElem_mem hs
  have hu0_spec : u0 < C.size ∧ isNotOp (gateAt C u0).op = true := by
    have := List.mem_filter.mp hu0_mem
    exact ⟨List.mem_range.mp this.1, this.2⟩
  have hnot_pre : ∀ u' < u0, isNotOp (gateAt C u').op = true →
      (C.wires v1).getD (L + u') false = (C.wires v2).getD (L + u') false := by
    intro u' hu'lt hu'not
    have hu'mem : u' ∈ gates := List.mem_filter.mpr ⟨List.mem_range.mpr (lt_trans hu'lt hu0_spec.1), hu'not⟩
    have hidx_lt : gates.idxOf u' < gates.length := List.idxOf_lt_length_iff.mpr hu'mem
    have hidx_eq : gates[gates.idxOf u'] = u' := List.getElem_idxOf hidx_lt
    have hidx_lt_s : gates.idxOf u' < s := by
      by_contra hge
      have hsle : s ≤ gates.idxOf u' := by omega
      rcases eq_or_lt_of_le hsle with heq | hlt'
      · have : u0 = u' := by dsimp only [u0]; rw [← hidx_eq]; congr 1
        omega
      · have := List.pairwise_iff_getElem.mp hgates_sorted s (gates.idxOf u') hs hidx_lt hlt'
        rw [hidx_eq] at this; omega
    have hbit := hpre (gates.idxOf u') hidx_lt_s
    rw [bitsRank_testBit _ gates _ hidx_lt, bitsRank_testBit _ gates _ hidx_lt, hidx_eq] at hbit
    have h1 := congrArg Bool.not hbit
    simp only [Bool.not_not] at h1
    exact h1.symm
  have hmp := mono_pre_wires L C hfan hrb v1 v2 hv1 hv2 hin u0 (Nat.le_of_lt hu0_spec.1) hnot_pre
  rw [bitsRank_testBit _ gates s hs] at h2f h1t
  have hw2 : (C.wires v2).getD (L + u0) false = true := by
    cases h : (C.wires v2).getD (L + u0) false
    · rw [h] at h2f; simp at h2f
    · rfl
  have hw1 : (C.wires v1).getD (L + u0) false = false := by
    cases h : (C.wires v1).getD (L + u0) false
    · rfl
    · rw [h] at h1t; simp at h1t
  have hrb1 : ReadsBack v1.length C := by rw [hv1]; exact hrb
  have hrb2 : ReadsBack v2.length C := by rw [hv2]; exact hrb
  have hg1 := wires_getD_gate C v1 u0 hu0_spec.1 hrb1
  have hg2 := wires_getD_gate C v2 u0 hu0_spec.1 hrb2
  rw [hv1] at hg1; rw [hv2] at hg2
  have hu0_op : (gateAt C u0).op = GateOp.not := (isNotOp_eq_true_iff _).mp hu0_spec.2
  rw [hg1, hu0_op] at hw1
  rw [hg2, hu0_op] at hw2
  cases hlist : (gateAt C u0).inputs with
  | nil => rw [hlist] at hw1; simp [GateOp.eval] at hw1
  | cons a rest =>
    rw [hlist] at hw1 hw2
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_false', Bool.not_eq_true'] at hw1 hw2
    have halt : a < L + u0 := hrb u0 hu0_spec.1 a (by simp [hlist])
    have ha2 := hmp a halt hw1
    rw [ha2] at hw2
    exact Bool.noConfusion hw2

private def appendOrList (N : Nat) (gs : List Gate) : List Nat → List Gate × Nat
  | [] => (gs, N)
  | [w] => (gs, w)
  | w :: w2 :: rest =>
    let res := appendOrList N gs (w2 :: rest)
    (res.1 ++ [⟨GateOp.or, [w, res.2]⟩], N + 2 + res.1.length)

private lemma appendOrList_spec (N : Nat) (gs : List Gate) (ws : List Nat)
    (hgs : ValidGates N gs) (hws : ∀ w ∈ ws, w < N + 2 + gs.length) :
    let res := appendOrList N gs ws
    (∃ extra, res.1 = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra ≤ ws.length) ∧
    ValidGates N res.1 ∧ res.2 < N + 2 + res.1.length ∧
    ∀ x : List Bool, x.length = N + 2 → x.getD N false = false →
      (evalW res.1 x).getD res.2 false = ws.any (fun w => (evalW gs x).getD w false) := by
  induction ws with
  | nil =>
    dsimp only [appendOrList]
    refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hgs, by omega, fun x hx hxN => ?_⟩
    rw [evalW_pre gs x N (by omega), hxN]; rfl
  | cons w rest ih =>
    cases rest with
    | nil =>
      dsimp only [appendOrList]
      have hw : w < N + 2 + gs.length := hws w List.mem_cons_self
      refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hgs, hw, fun x _ _ => ?_⟩
      simp
    | cons w2 rest2 =>
      have hws' : ∀ u ∈ w2 :: rest2, u < N + 2 + gs.length :=
        fun u hu => hws u (List.mem_cons_of_mem w hu)
      rcases ih hws' with ⟨⟨extra, heq, hnot, hpos⟩, hval, hout, heval⟩
      set res := appendOrList N gs (w2 :: rest2)
      have hw : w < N + 2 + res.1.length := by
        have := hws w List.mem_cons_self
        rw [heq, List.length_append]; omega
      have hval' : ValidGates N (res.1 ++ [⟨GateOp.or, [w, res.2]⟩]) :=
        validGates_snoc N res.1 ⟨GateOp.or, [w, res.2]⟩ hval (Or.inr (Or.inl rfl)) (by simp) (by
          intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
      dsimp only [appendOrList]
      refine ⟨⟨extra ++ [⟨GateOp.or, [w, res.2]⟩], ?_, ?_, ?_⟩, hval', ?_, fun x hx hxN => ?_⟩
      · change res.1 ++ [⟨GateOp.or, [w, res.2]⟩] = gs ++ (extra ++ [⟨GateOp.or, [w, res.2]⟩])
        rw [heq, List.append_assoc]
      · rw [notCountL_append, hnot]; rfl
      · rw [posCount_append]
        have h1 : posCount [⟨GateOp.or, [w, res.2]⟩] = 1 := rfl
        simp only [List.length_cons] at hpos ⊢; omega
      · simp
      · have hlast := evalW_snoc_last res.1 ⟨GateOp.or, [w, res.2]⟩ x
        rw [hx] at hlast
        rw [hlast]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have hw_eq : (evalW res.1 x).getD w false = (evalW gs x).getD w false := by
          rw [heq]
          exact evalW_append_pre gs extra x w (by rw [hx]; exact hws w List.mem_cons_self)
        rw [hw_eq, heval x hx hxN]
        simp [List.any_cons]

private def appendAndList (N : Nat) (gs : List Gate) : List Nat → List Gate × Nat
  | [] => (gs, N + 1)
  | [w] => (gs, w)
  | w :: w2 :: rest =>
    let res := appendAndList N gs (w2 :: rest)
    (res.1 ++ [⟨GateOp.and, [w, res.2]⟩], N + 2 + res.1.length)

private lemma appendAndList_spec (N : Nat) (gs : List Gate) (ws : List Nat)
    (hgs : ValidGates N gs) (hws : ∀ w ∈ ws, w < N + 2 + gs.length) :
    let res := appendAndList N gs ws
    (∃ extra, res.1 = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra ≤ ws.length) ∧
    ValidGates N res.1 ∧ res.2 < N + 2 + res.1.length ∧
    ∀ x : List Bool, x.length = N + 2 → x.getD (N + 1) false = true →
      (evalW res.1 x).getD res.2 false = ws.all (fun w => (evalW gs x).getD w false) := by
  induction ws with
  | nil =>
    dsimp only [appendAndList]
    refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hgs, by omega, fun x hx hx1 => ?_⟩
    rw [evalW_pre gs x (N + 1) (by omega), hx1]; rfl
  | cons w rest ih =>
    cases rest with
    | nil =>
      dsimp only [appendAndList]
      have hw : w < N + 2 + gs.length := hws w List.mem_cons_self
      refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hgs, hw, fun x _ _ => ?_⟩
      simp
    | cons w2 rest2 =>
      have hws' : ∀ u ∈ w2 :: rest2, u < N + 2 + gs.length :=
        fun u hu => hws u (List.mem_cons_of_mem w hu)
      rcases ih hws' with ⟨⟨extra, heq, hnot, hpos⟩, hval, hout, heval⟩
      set res := appendAndList N gs (w2 :: rest2)
      have hw : w < N + 2 + res.1.length := by
        have := hws w List.mem_cons_self
        rw [heq, List.length_append]; omega
      have hval' : ValidGates N (res.1 ++ [⟨GateOp.and, [w, res.2]⟩]) :=
        validGates_snoc N res.1 ⟨GateOp.and, [w, res.2]⟩ hval (Or.inl rfl) (by simp) (by
          intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
      dsimp only [appendAndList]
      refine ⟨⟨extra ++ [⟨GateOp.and, [w, res.2]⟩], ?_, ?_, ?_⟩, hval', ?_, fun x hx hx1 => ?_⟩
      · change res.1 ++ [⟨GateOp.and, [w, res.2]⟩] = gs ++ (extra ++ [⟨GateOp.and, [w, res.2]⟩])
        rw [heq, List.append_assoc]
      · rw [notCountL_append, hnot]; rfl
      · rw [posCount_append]
        have h1 : posCount [⟨GateOp.and, [w, res.2]⟩] = 1 := rfl
        simp only [List.length_cons] at hpos ⊢; omega
      · simp
      · have hlast := evalW_snoc_last res.1 ⟨GateOp.and, [w, res.2]⟩ x
        rw [hx] at hlast
        rw [hlast]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hw_eq : (evalW res.1 x).getD w false = (evalW gs x).getD w false := by
          rw [heq]
          exact evalW_append_pre gs extra x w (by rw [hx]; exact hws w List.mem_cons_self)
        rw [hw_eq, heval x hx hx1]
        simp [List.all_cons]

private def buildDecoder (N : Nat) : Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat)
  | 0, gs, _ => (gs, fun _ => N + 1)
  | B + 1, gs, T =>
    let mid := 2 ^ B
    let nMidIdx := N + 2 + gs.length
    let gs1 := gs ++ [⟨GateOp.not, [T mid]⟩]
    let foldLoop : Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat) :=
      Nat.rec (fun g f => (g, f)) (fun j ih g f =>
        let prev := ih g f
        let j1 := j + 1
        let aIdx := N + 2 + prev.1.length
        let g1 := prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]
        let oIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]
        (g2, fun r => if r = j1 then oIdx else prev.2 r))
    let folded := foldLoop (mid - 1) gs1 (fun _ => N)
    let dec := buildDecoder N B folded.1 folded.2
    let unfoldLoop : Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat) :=
      Nat.rec (fun g f => (g, f)) (fun j ih g f =>
        let prev := ih g f
        let loIdx := N + 2 + prev.1.length
        let g1 := prev.1 ++ [⟨GateOp.and, [dec.2 j, nMidIdx]⟩]
        let hiIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.and, [dec.2 j, T mid]⟩]
        (g2, fun r => if r = j then loIdx else if r = mid + j then hiIdx else prev.2 r))
    unfoldLoop mid dec.1 (fun _ => N)

private lemma buildDecoder_spec (N : Nat) :
    ∀ (B : Nat) (gs : List Gate) (T : Nat → Nat),
      ValidGates N gs →
      (∀ j, 1 ≤ j → j < 2 ^ B → T j < N + 2 + gs.length) →
      let res := buildDecoder N B gs T
      (∃ extra, res.1 = gs ++ extra ∧ notCountL extra = B ∧ posCount extra ≤ 4 * (2 ^ B - 1)) ∧
      ValidGates N res.1 ∧
      (∀ j < 2 ^ B, res.2 j < N + 2 + res.1.length) ∧
      ∀ (x : List Bool) (v : Nat), x.length = N + 2 → x.getD (N + 1) false = true → v < 2 ^ B →
        (∀ j, 1 ≤ j → j < 2 ^ B → (evalW gs x).getD (T j) false = decide (j ≤ v)) →
        ∀ j < 2 ^ B, (evalW res.1 x).getD (res.2 j) false = decide (j = v) := by
  intro B
  induction B with
  | zero =>
    intro gs T hgs _
    dsimp only [buildDecoder]
    refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hgs, fun j _ => by omega, ?_⟩
    intro x v hx hx1 hv _ j hj
    have hv0 : v = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hv0; subst hj0
    rw [evalW_pre gs x (N + 1) (by omega), hx1]; rfl
  | succ B ih =>
    intro gs T hgs hT
    set mid := 2 ^ B
    have hmid_pos : 1 ≤ mid := Nat.one_le_two_pow
    have hpow2 : 2 ^ (B + 1) = 2 * mid := by rw [pow_succ, Nat.mul_comm]
    set nMidIdx := N + 2 + gs.length
    set gs1 := gs ++ [⟨GateOp.not, [T mid]⟩]
    have hTmid : T mid < N + 2 + gs.length := hT mid hmid_pos (by omega)
    have hval1 : ValidGates N gs1 :=
      validGates_snoc N gs ⟨GateOp.not, [T mid]⟩ hgs (Or.inr (Or.inr rfl)) (by simp) (by
        intro i hi; simp at hi; subst hi; exact hTmid)
    let foldLoop : Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat) :=
      Nat.rec (fun g f => (g, f)) (fun j ih g f =>
        let prev := ih g f
        let j1 := j + 1
        let aIdx := N + 2 + prev.1.length
        let g1 := prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]
        let oIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]
        (g2, fun r => if r = j1 then oIdx else prev.2 r))
    have hfold : ∀ m ≤ mid - 1,
        let f := foldLoop m gs1 (fun _ => N)
        (∃ e1, f.1 = gs1 ++ e1 ∧ notCountL e1 = 0 ∧ posCount e1 = 2 * m) ∧
        ValidGates N f.1 ∧
        (∀ j, 1 ≤ j → j ≤ m → f.2 j < N + 2 + f.1.length) ∧
        ∀ (x : List Bool) (v : Nat), x.length = N + 2 → v < 2 * mid →
          (∀ j, 1 ≤ j → j < 2 * mid → (evalW gs x).getD (T j) false = decide (j ≤ v)) →
          ∀ j, 1 ≤ j → j ≤ m → (evalW f.1 x).getD (f.2 j) false =
            decide (j ≤ (if v < mid then v else v - mid)) := by
      intro m
      induction m with
      | zero =>
        intro _
        dsimp only [foldLoop]
        refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hval1, fun j h1 h2 => by omega, fun _ _ _ _ _ j h1 h2 => by omega⟩
      | succ m ihm =>
        intro hm
        rcases ihm (by omega) with ⟨⟨e1, heq1, hnot1, hpos1⟩, hvalf, hbdf, hevalf⟩
        set prev := foldLoop m gs1 (fun _ => N)
        let j1 := m + 1
        let aIdx := N + 2 + prev.1.length
        let g1 := prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]
        let oIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]
        have hstep_eq : foldLoop (m + 1) gs1 (fun _ => N) =
            (g2, fun r => if r = j1 then oIdx else prev.2 r) := rfl
        rw [hstep_eq]
        have hgs_le_prev : gs.length + 1 ≤ prev.1.length := by
          rw [heq1, List.length_append]; simp [gs1]
        have hTj1 : T j1 < N + 2 + gs.length := hT j1 (by omega) (by omega)
        have hTmidj1 : T (mid + j1) < N + 2 + gs.length := hT (mid + j1) (by omega) (by omega)
        have hval_g1 : ValidGates N g1 :=
          validGates_snoc N prev.1 ⟨GateOp.and, [T j1, nMidIdx]⟩ hvalf (Or.inl rfl) (by simp) (by
            intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
        have hval_g2 : ValidGates N g2 :=
          validGates_snoc N g1 ⟨GateOp.or, [aIdx, T (mid + j1)]⟩ hval_g1 (Or.inr (Or.inl rfl)) (by simp) (by
            intro i hi; simp at hi; rcases hi with rfl | rfl
            · simp [g1, aIdx]
            · simp only [g1, List.length_append, List.length_singleton]; omega)
        refine ⟨⟨e1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩, ⟨GateOp.or, [aIdx, T (mid + j1)]⟩], ?_, ?_, ?_⟩,
          hval_g2, ?_, ?_⟩
        · simp [g2, g1, heq1, List.append_assoc]
        · rw [notCountL_append, hnot1]; rfl
        · rw [posCount_append, hpos1]
          have : posCount [⟨GateOp.and, [T j1, nMidIdx]⟩, ⟨GateOp.or, [aIdx, T (mid + j1)]⟩] = 2 := rfl
          omega
        · intro j hj1 hjm
          dsimp only
          by_cases heq : j = j1
          · rw [if_pos heq]; simp [g2, oIdx]
          · rw [if_neg heq]
            have := hbdf j hj1 (by omega)
            simp only [g2, g1, List.length_append, List.length_singleton]; omega
        · intro x v hx hv hTx j hj1 hjm
          dsimp only
          by_cases heq : j = j1
          · rw [if_pos heq, heq]
            have hlast2 := evalW_snoc_last g1 ⟨GateOp.or, [aIdx, T (mid + j1)]⟩ x
            rw [hx] at hlast2
            change (evalW (g1 ++ [⟨GateOp.or, [aIdx, T (mid + j1)]⟩]) x).getD (N + 2 + g1.length) false = _
            rw [hlast2]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            have ha_val : (evalW g1 x).getD aIdx false =
                ((evalW gs x).getD (T j1) false && !(evalW gs x).getD (T mid) false) := by
              have hlast1 := evalW_snoc_last prev.1 ⟨GateOp.and, [T j1, nMidIdx]⟩ x
              rw [hx] at hlast1
              change (evalW (prev.1 ++ [⟨GateOp.and, [T j1, nMidIdx]⟩]) x).getD (N + 2 + prev.1.length) false = _
              rw [hlast1]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              have h1 : (evalW prev.1 x).getD (T j1) false = (evalW gs x).getD (T j1) false := by
                rw [heq1]; dsimp only [gs1]; rw [List.append_assoc]
                exact evalW_append_pre gs ([⟨GateOp.not, [T mid]⟩] ++ e1) x (T j1) (by rw [hx]; exact hTj1)
              have h2 : (evalW prev.1 x).getD nMidIdx false = !(evalW gs x).getD (T mid) false := by
                rw [heq1, evalW_append_pre gs1 e1 x nMidIdx (by rw [hx]; simp [gs1, nMidIdx])]
                have hnotv := evalW_snoc_last gs ⟨GateOp.not, [T mid]⟩ x
                rw [hx] at hnotv
                change (evalW (gs ++ [⟨GateOp.not, [T mid]⟩]) x).getD (N + 2 + gs.length) false = _
                rw [hnotv]; simp [GateOp.eval]
              rw [h1, h2]
            have hT2_val : (evalW g1 x).getD (T (mid + j1)) false = (evalW gs x).getD (T (mid + j1)) false := by
              dsimp only [g1]; rw [heq1]; dsimp only [gs1]; rw [List.append_assoc, List.append_assoc]
              exact evalW_append_pre gs _ x (T (mid + j1)) (by rw [hx]; exact hTmidj1)
            rw [ha_val, hT2_val, hTx j1 (by omega) (by omega), hTx mid hmid_pos (by omega),
              hTx (mid + j1) (by omega) (by omega)]
            by_cases hvm : v < mid
            · rw [if_pos hvm, decide_eq_false (by omega : ¬ mid ≤ v), decide_eq_false (by omega : ¬ mid + j1 ≤ v)]
              simp
            · rw [if_neg hvm, decide_eq_true (by omega : mid ≤ v)]
              simp only [Bool.not_true, Bool.and_false, Bool.false_or]
              exact decide_eq_decide.mpr (by omega)
          · rw [if_neg heq]
            have hbdj := hbdf j hj1 (by omega)
            dsimp only [g2, g1]; rw [List.append_assoc]
            rw [evalW_append_pre prev.1 _ x (prev.2 j) (by rw [hx]; exact hbdj)]
            exact hevalf x v hx hv hTx j hj1 (by omega)
    rcases hfold (mid - 1) (le_refl _) with ⟨⟨e1, heq1, hnot1, hpos1⟩, hvalf, hbdf, hevalf⟩
    set folded := foldLoop (mid - 1) gs1 (fun _ => N)
    rcases ih folded.1 folded.2 hvalf (fun j hj1 hjm => hbdf j hj1 (by omega)) with
      ⟨⟨e2, heq2, hnot2, hpos2⟩, hvald, hbdd, hevald⟩
    set dec := buildDecoder N B folded.1 folded.2
    let unfoldLoop : Nat → List Gate → (Nat → Nat) → List Gate × (Nat → Nat) :=
      Nat.rec (fun g f => (g, f)) (fun j ih g f =>
        let prev := ih g f
        let loIdx := N + 2 + prev.1.length
        let g1 := prev.1 ++ [⟨GateOp.and, [dec.2 j, nMidIdx]⟩]
        let hiIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.and, [dec.2 j, T mid]⟩]
        (g2, fun r => if r = j then loIdx else if r = mid + j then hiIdx else prev.2 r))
    have hgs1_pre : dec.1 = gs1 ++ (e1 ++ e2) := by rw [heq2, heq1, List.append_assoc]
    have hgs_pre : dec.1 = gs ++ ([⟨GateOp.not, [T mid]⟩] ++ e1 ++ e2) := by
      rw [hgs1_pre]; simp [gs1, List.append_assoc]
    have hunfold : ∀ m ≤ mid,
        let u := unfoldLoop m dec.1 (fun _ => N)
        (∃ e3, u.1 = dec.1 ++ e3 ∧ notCountL e3 = 0 ∧ posCount e3 = 2 * m) ∧
        ValidGates N u.1 ∧
        (∀ j < m, u.2 j < N + 2 + u.1.length ∧ u.2 (mid + j) < N + 2 + u.1.length) ∧
        ∀ (x : List Bool) (v : Nat), x.length = N + 2 → x.getD (N + 1) false = true → v < 2 * mid →
          (∀ j, 1 ≤ j → j < 2 * mid → (evalW gs x).getD (T j) false = decide (j ≤ v)) →
          ∀ j < m, (evalW u.1 x).getD (u.2 j) false = decide (j = v) ∧
            (evalW u.1 x).getD (u.2 (mid + j)) false = decide (mid + j = v) := by
      intro m
      induction m with
      | zero =>
        intro _
        dsimp only [unfoldLoop]
        refine ⟨⟨[], by simp, rfl, by simp [posCount]⟩, hvald, fun j hj => by omega, fun _ _ _ _ _ _ j hj => by omega⟩
      | succ m ihm =>
        intro hm
        rcases ihm (by omega) with ⟨⟨e3, heq3, hnot3, hpos3⟩, hvalu, hbdu, hevalu⟩
        set prev := unfoldLoop m dec.1 (fun _ => N)
        let loIdx := N + 2 + prev.1.length
        let g1 := prev.1 ++ [⟨GateOp.and, [dec.2 m, nMidIdx]⟩]
        let hiIdx := N + 2 + g1.length
        let g2 := g1 ++ [⟨GateOp.and, [dec.2 m, T mid]⟩]
        have hstep_eq : unfoldLoop (m + 1) dec.1 (fun _ => N) =
            (g2, fun r => if r = m then loIdx else if r = mid + m then hiIdx else prev.2 r) := rfl
        rw [hstep_eq]
        have hdec_le_prev : dec.1.length ≤ prev.1.length := by rw [heq3, List.length_append]; omega
        have hgs_le_dec : gs.length + 1 ≤ dec.1.length := by rw [hgs_pre, List.length_append]; simp
        have hdm_lt : dec.2 m < N + 2 + dec.1.length := hbdd m (by omega)
        have hval_g1 : ValidGates N g1 :=
          validGates_snoc N prev.1 ⟨GateOp.and, [dec.2 m, nMidIdx]⟩ hvalu (Or.inl rfl) (by simp) (by
            intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
        have hval_g2 : ValidGates N g2 :=
          validGates_snoc N g1 ⟨GateOp.and, [dec.2 m, T mid]⟩ hval_g1 (Or.inl rfl) (by simp) (by
            intro i hi; simp at hi; rcases hi with rfl | rfl
            · simp only [g1, List.length_append, List.length_singleton]; omega
            · simp only [g1, List.length_append, List.length_singleton]; omega)
        refine ⟨⟨e3 ++ [⟨GateOp.and, [dec.2 m, nMidIdx]⟩, ⟨GateOp.and, [dec.2 m, T mid]⟩], ?_, ?_, ?_⟩,
          hval_g2, ?_, ?_⟩
        · simp [g2, g1, heq3, List.append_assoc]
        · rw [notCountL_append, hnot3]; rfl
        · rw [posCount_append, hpos3]
          have : posCount [⟨GateOp.and, [dec.2 m, nMidIdx]⟩, ⟨GateOp.and, [dec.2 m, T mid]⟩] = 2 := rfl
          omega
        · intro j hj
          dsimp only
          by_cases heq : j = m
          · rw [if_pos heq, if_neg (by omega : mid + j ≠ m), if_pos (by omega : mid + j = mid + m)]
            refine ⟨by simp only [g2, g1, loIdx, List.length_append, List.length_singleton]; omega,
                    by simp [g2, hiIdx]⟩
          · rw [if_neg heq, if_neg (by omega : j ≠ mid + m), if_neg (by omega : mid + j ≠ m),
              if_neg (by omega : mid + j ≠ mid + m)]
            rcases hbdu j (by omega) with ⟨h1, h2⟩
            simp only [g2, g1, List.length_append, List.length_singleton]
            exact ⟨by omega, by omega⟩
        · intro x v hx hx1 hv hTx j hj
          dsimp only
          by_cases heq : j = m
          · rw [if_pos heq, if_neg (by omega : mid + j ≠ m), if_pos (by omega : mid + j = mid + m)]
            subst heq
            have hdec_val : (evalW dec.1 x).getD (dec.2 j) false =
                decide (j = if v < mid then v else v - mid) := by
              have hv' : (if v < mid then v else v - mid) < mid := by split <;> omega
              exact hevald x (if v < mid then v else v - mid) hx hx1 hv'
                (fun r hr1 hrm => hevalf x v hx hv hTx r hr1 (by omega)) j (by omega)
            have hnMid_val : (evalW prev.1 x).getD nMidIdx false = !(evalW gs x).getD (T mid) false := by
              rw [heq3, hgs1_pre, List.append_assoc, evalW_append_pre gs1 _ x nMidIdx (by rw [hx]; simp [gs1, nMidIdx])]
              have hnotv := evalW_snoc_last gs ⟨GateOp.not, [T mid]⟩ x
              rw [hx] at hnotv
              change (evalW (gs ++ [⟨GateOp.not, [T mid]⟩]) x).getD (N + 2 + gs.length) false = _
              rw [hnotv]; simp [GateOp.eval]
            have hTmid_val : (evalW g1 x).getD (T mid) false = (evalW gs x).getD (T mid) false := by
              dsimp only [g1]; rw [heq3, hgs_pre]; simp only [List.append_assoc]
              exact evalW_append_pre gs _ x (T mid) (by rw [hx]; exact hTmid)
            constructor
            · rw [evalW_append_pre g1 _ x loIdx (by rw [hx]; simp [g1, loIdx])]
              have hlast1 := evalW_snoc_last prev.1 ⟨GateOp.and, [dec.2 j, nMidIdx]⟩ x
              rw [hx] at hlast1
              change (evalW (prev.1 ++ [⟨GateOp.and, [dec.2 j, nMidIdx]⟩]) x).getD (N + 2 + prev.1.length) false = _
              rw [hlast1]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [heq3, evalW_append_pre dec.1 e3 x (dec.2 j) (by rw [hx]; exact hdm_lt)]
              rw [← heq3, hnMid_val, hdec_val, hTx mid hmid_pos (by omega)]
              by_cases hvm : v < mid
              · rw [if_pos hvm, decide_eq_false (by omega : ¬ mid ≤ v)]; simp
              · rw [if_neg hvm, decide_eq_true (by omega : mid ≤ v), decide_eq_false (by omega : j ≠ v)]; simp
            · have hlast2 := evalW_snoc_last g1 ⟨GateOp.and, [dec.2 j, T mid]⟩ x
              rw [hx] at hlast2
              change (evalW (g1 ++ [⟨GateOp.and, [dec.2 j, T mid]⟩]) x).getD (N + 2 + g1.length) false = _
              rw [hlast2]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hTmid_val]
              have hdj_g1 : (evalW g1 x).getD (dec.2 j) false = (evalW dec.1 x).getD (dec.2 j) false := by
                dsimp only [g1]; rw [heq3, List.append_assoc]
                exact evalW_append_pre dec.1 _ x (dec.2 j) (by rw [hx]; exact hdm_lt)
              rw [hdj_g1, hdec_val, hTx mid hmid_pos (by omega)]
              by_cases hvm : v < mid
              · rw [if_pos hvm, decide_eq_false (by omega : ¬ mid ≤ v), decide_eq_false (by omega : mid + j ≠ v)]; simp
              · rw [if_neg hvm, decide_eq_true (by omega : mid ≤ v)]
                simp only [Bool.and_true]
                exact decide_eq_decide.mpr (by omega)
          · rw [if_neg heq, if_neg (by omega : j ≠ mid + m), if_neg (by omega : mid + j ≠ m),
              if_neg (by omega : mid + j ≠ mid + m)]
            rcases hbdu j (by omega) with ⟨hbd1, hbd2⟩
            rcases hevalu x v hx hx1 hv hTx j (by omega) with ⟨he1, he2⟩
            dsimp only [g2, g1]; rw [List.append_assoc]
            rw [evalW_append_pre prev.1 _ x (prev.2 j) (by rw [hx]; exact hbd1)]
            rw [evalW_append_pre prev.1 _ x (prev.2 (mid + j)) (by rw [hx]; exact hbd2)]
            exact ⟨he1, he2⟩
    rcases hunfold mid (le_refl mid) with ⟨⟨e3, heq3, hnot3, hpos3⟩, hvalu, hbdu, hevalu⟩
    have hbuild_eq : buildDecoder N (B + 1) gs T = unfoldLoop mid dec.1 (fun _ => N) := rfl
    rw [hbuild_eq]
    refine ⟨⟨[⟨GateOp.not, [T mid]⟩] ++ e1 ++ e2 ++ e3, ?_, ?_, ?_⟩, hvalu, ?_, ?_⟩
    · rw [heq3, hgs_pre, List.append_assoc, List.append_assoc]
    · rw [notCountL_append, notCountL_append, notCountL_append, hnot1, hnot2, hnot3]
      have : notCountL [⟨GateOp.not, [T mid]⟩] = 1 := rfl
      omega
    · rw [posCount_append, posCount_append, posCount_append, hpos1, hpos3]
      have : posCount [⟨GateOp.not, [T mid]⟩] = 0 := rfl
      omega
    · intro j hj
      by_cases hjm : j < mid
      · exact (hbdu j hjm).1
      · have hj' : j - mid < mid := by omega
        have heqj : j = mid + (j - mid) := by omega
        rw [heqj]; exact (hbdu (j - mid) hj').2
    · intro x v hx hx1 hv hTx j hj
      have hTx' : ∀ r, 1 ≤ r → r < 2 * mid → (evalW gs x).getD (T r) false = decide (r ≤ v) :=
        fun r hr1 hr2 => hTx r hr1 (by omega)
      by_cases hjm : j < mid
      · exact (hevalu x v hx hx1 (by omega) hTx' j hjm).1
      · have hj' : j - mid < mid := by omega
        have heqj : j = mid + (j - mid) := by omega
        rw [heqj]; exact (hevalu x v hx hx1 (by omega) hTx' (j - mid) hj').2

private def bitsVec (n : Nat) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

private lemma bitsVec_len (n : Nat) (x : Finset (Fin n)) : (bitsVec n x).length = n + 2 := by
  simp [bitsVec]

private lemma bitsVec_in (n : Nat) (x : Finset (Fin n)) (i : Fin n) :
    (bitsVec n x).getD i.val false = decide (i ∈ x) := by
  unfold bitsVec
  rw [getD_append_left _ _ i.val (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma bitsVec_c0 (n : Nat) (x : Finset (Fin n)) : (bitsVec n x).getD n false = false := by
  unfold bitsVec
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

private lemma bitsVec_c1 (n : Nat) (x : Finset (Fin n)) : (bitsVec n x).getD (n + 1) false = true := by
  unfold bitsVec
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

private lemma bitsVec_mono (n : Nat) (x y : Finset (Fin n)) (hxy : x ⊆ y) :
    ∀ u < n + 2, (bitsVec n x).getD u false = true → (bitsVec n y).getD u false = true := by
  intro u hu h1
  by_cases hun : u < n
  · have := bitsVec_in n x ⟨u, hun⟩
    have := bitsVec_in n y ⟨u, hun⟩
    rw [bitsVec_in n x ⟨u, hun⟩] at h1
    rw [bitsVec_in n y ⟨u, hun⟩]
    exact decide_eq_true (hxy (of_decide_eq_true h1))
  · by_cases hu0 : u = n
    · subst hu0; rw [bitsVec_c0] at h1; exact Bool.noConfusion h1
    · have hu1 : u = n + 1 := by omega
      subst hu1; rw [bitsVec_c1]

private lemma weak_duality (n m b : Nat) (S : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat)
    (C : Circuit) (a : Fin m → Fin (n + 2 + C.size))
    (P : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C) (hnot : notCount C ≤ b)
    (hchain : ∀ c ∈ P, c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
      ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧ f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false)
    (hcap : ∀ x ∈ S, ∀ j : Fin m, (P.flatten.filter (fun e =>
      decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length ≤ w x j) :
    let valC := fun (x : Finset (Fin n)) (j : Fin m) => (C.wires (bitsVec n x)).getD (a j).val false
    let lossC := S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j => if valC x j = f x j then 0 else w x j))
    P.flatten.length ≤ lossC + (2 ^ b - 1) * P.length := by
  intro valC lossC
  let gates := (List.range C.size).filter (fun u => isNotOp (gateAt C u).op)
  have hgates_len : gates.length = notCount C := range_filter_not_len C
  let rk : Finset (Fin n) → Nat := fun x =>
    bitsRank (fun u => (C.wires (bitsVec n x)).getD (n + 2 + u) false) gates 0
  have hrk_lt : ∀ x, rk x < 2 ^ b := by
    intro x
    have h1 : rk x < 2 ^ gates.length := bitsRank_lt _ _
    have h2 : 2 ^ gates.length ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hrk_mono : ∀ x y, x ⊆ y → rk x ≤ rk y := fun x y hxy =>
    rank_mono (n + 2) C hfan hrb (bitsVec n x) (bitsVec n y) (bitsVec_len n x) (bitsVec_len n y)
      (bitsVec_mono n x y hxy)
  have hrk_strict : ∀ x y j, x ⊆ y → valC x j = true → valC y j = false → rk x < rk y := by
    intro x y j hxy hx hy
    have hle := hrk_mono x y hxy
    by_contra hnotlt
    have heq : rk x = rk y := by omega
    have hnot_eq : ∀ u < C.size, isNotOp (gateAt C u).op = true →
        (C.wires (bitsVec n x)).getD (n + 2 + u) false = (C.wires (bitsVec n y)).getD (n + 2 + u) false := by
      intro u hu hnotu
      have humem : u ∈ gates := List.mem_filter.mpr ⟨List.mem_range.mpr hu, hnotu⟩
      rcases List.mem_iff_getElem.mp humem with ⟨idx, hidx, rfl⟩
      have htb := congrArg (fun v => v.testBit (gates.length - 1 - idx)) heq
      dsimp only [rk] at htb
      rw [bitsRank_testBit _ gates idx hidx, bitsRank_testBit _ gates idx hidx] at htb
      have h1 := congrArg Bool.not htb
      simp only [Bool.not_not] at h1
      exact h1
    have hmp := mono_pre_wires (n + 2) C hfan hrb (bitsVec n x) (bitsVec n y) (bitsVec_len n x) (bitsVec_len n y)
      (bitsVec_mono n x y hxy) C.size (le_refl _) hnot_eq (a j).val (a j).isLt hx
    dsimp only [valC] at hy
    rw [hmp] at hy
    exact Bool.noConfusion hy
  let good : Finset (Fin n) × Finset (Fin n) × Fin m → Bool :=
    fun e => decide (valC e.1 e.2.2 = true ∧ valC e.2.1 e.2.2 = false)
  have hchain_good : ∀ (c : List (Finset (Fin n) × Finset (Fin n) × Fin m)) (lo : Nat),
      lo ≤ 2 ^ b - 1 → c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) →
      (∀ e ∈ c, e.1 ⊆ e.2.1) → (∀ e ∈ c, lo ≤ rk e.1) →
      (c.filter good).length + lo ≤ 2 ^ b - 1 := by
    intro c
    induction c with
    | nil => intro lo hlo _ _ _; simp; omega
    | cons e rest ih =>
      intro lo hlo hpw hsub hlo_all
      rcases List.pairwise_cons.mp hpw with ⟨he_rest, hpw_rest⟩
      have he1 : lo ≤ rk e.1 := hlo_all e List.mem_cons_self
      have he12 : rk e.1 ≤ rk e.2.1 := hrk_mono e.1 e.2.1 (hsub e List.mem_cons_self)
      have hhi : rk e.2.1 ≤ 2 ^ b - 1 := by have := hrk_lt e.2.1; omega
      have hrest_lo : ∀ e' ∈ rest, rk e.2.1 ≤ rk e'.1 := fun e' he' => hrk_mono e.2.1 e'.1 (he_rest e' he')
      have hrec := ih (rk e.2.1) hhi hpw_rest (fun e' he' => hsub e' (List.mem_cons_of_mem e he')) hrest_lo
      simp only [List.filter_cons]
      cases hg : good e
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [↓reduceIte, List.length_cons]
        have hpair := of_decide_eq_true hg
        have hlt := hrk_strict e.1 e.2.1 e.2.2 (hsub e List.mem_cons_self) hpair.1 hpair.2
        omega
  have hgood_total : (P.flatten.filter good).length ≤ (2 ^ b - 1) * P.length := by
    clear hcap
    induction P with
    | nil => simp
    | cons c rest ih =>
      simp only [List.flatten_cons, List.filter_append, List.length_append, List.length_cons]
      have hc := hchain c List.mem_cons_self
      have h1 := hchain_good c 0 (Nat.zero_le _) hc.1 (fun e he => (hc.2 e he).2.2.1) (fun _ _ => Nat.zero_le _)
      have h2 := ih (fun c' hc' => hchain c' (List.mem_cons_of_mem c hc'))
      have hmul : (2 ^ b - 1) * (rest.length + 1) = (2 ^ b - 1) * rest.length + (2 ^ b - 1) := by ring
      omega
  have hbad_bound : ∀ (L : List (Finset (Fin n) × Finset (Fin n) × Fin m)),
      (∀ e ∈ L, e.1 ∈ S ∧ e.2.1 ∈ S ∧ f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) →
      (L.filter (fun e => !good e)).length ≤
        S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
          if valC x j = f x j then 0 else (L.filter (fun e => decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length)) := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons e rest ih =>
      intro hmem
      have he := hmem e List.mem_cons_self
      have hrec := ih (fun e' he' => hmem e' (List.mem_cons_of_mem e he'))
      have hsum_mono : S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
            if valC x j = f x j then 0 else (rest.filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x ∨ e'.2.1 = x)))).length)) ≤
          S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
            if valC x j = f x j then 0 else ((e :: rest).filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x ∨ e'.2.1 = x)))).length)) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun j _ => ?_
        split
        · exact le_refl 0
        · simp only [List.filter_cons]; split <;> simp
      conv_lhs => rw [List.filter_cons]
      cases hg : good e
      · simp only [Bool.not_false, ↓reduceIte, List.length_cons]
        have hbad_pair : valC e.1 e.2.2 ≠ f e.1 e.2.2 ∨ valC e.2.1 e.2.2 ≠ f e.2.1 e.2.2 := by
          have hnotg : ¬ (valC e.1 e.2.2 = true ∧ valC e.2.1 e.2.2 = false) := of_decide_eq_false hg
          by_cases h1 : valC e.1 e.2.2 = true
          · right; rw [he.2.2.2]; exact fun h2 => hnotg ⟨h1, h2⟩
          · left; rw [he.2.2.1]; exact h1
        have hinc : ∀ (x0 : Finset (Fin n)), x0 ∈ S → (e.1 = x0 ∨ e.2.1 = x0) → valC x0 e.2.2 ≠ f x0 e.2.2 →
            S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
              if valC x j = f x j then 0 else (rest.filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x ∨ e'.2.1 = x)))).length)) + 1 ≤
            S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
              if valC x j = f x j then 0 else ((e :: rest).filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x ∨ e'.2.1 = x)))).length)) := by
          intro x0 hx0 htouch hne
          let G1 : Finset (Fin n) → Nat := fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
            if valC x j = f x j then 0 else (rest.filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x ∨ e'.2.1 = x)))).length)
          let G2 : Finset (Fin n) → Nat := fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
            if valC x j = f x j then 0 else ((e :: rest).filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x ∨ e'.2.1 = x)))).length)
          have hle_all : ∀ x ∈ S, G1 x ≤ G2 x := fun x _ => Finset.sum_le_sum fun j _ => by
            split
            · exact le_refl 0
            · simp only [List.filter_cons]; split <;> simp
          have hstrict_x0 : G1 x0 + 1 ≤ G2 x0 := by
            let F1 : Fin m → Nat := fun j => if valC x0 j = f x0 j then 0 else (rest.filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x0 ∨ e'.2.1 = x0)))).length
            let F2 : Fin m → Nat := fun j => if valC x0 j = f x0 j then 0 else ((e :: rest).filter (fun e' => decide (e'.2.2 = j ∧ (e'.1 = x0 ∨ e'.2.1 = x0)))).length
            have hle_j : ∀ j ∈ (Finset.univ : Finset (Fin m)), F1 j ≤ F2 j := fun j _ => by
              dsimp only [F1, F2]; split
              · exact le_refl 0
              · simp only [List.filter_cons]; split <;> simp
            have hstrict_j : F1 e.2.2 + 1 ≤ F2 e.2.2 := by
              dsimp only [F1, F2]
              rw [if_neg hne, if_neg hne]
              have htr : e.2.2 = e.2.2 ∧ (e.1 = x0 ∨ e.2.1 = x0) := ⟨rfl, htouch⟩
              rw [List.filter_cons, decide_eq_true htr]
              simp only [↓reduceIte, List.length_cons]
              omega
            have h1 : F1 e.2.2 + (Finset.univ.erase e.2.2).sum F1 = G1 x0 :=
              Finset.add_sum_erase (Finset.univ : Finset (Fin m)) F1 (Finset.mem_univ e.2.2)
            have h2 : F2 e.2.2 + (Finset.univ.erase e.2.2).sum F2 = G2 x0 :=
              Finset.add_sum_erase (Finset.univ : Finset (Fin m)) F2 (Finset.mem_univ e.2.2)
            have h3 : (Finset.univ.erase e.2.2).sum F1 ≤ (Finset.univ.erase e.2.2).sum F2 :=
              Finset.sum_le_sum fun j _ => hle_j j (Finset.mem_univ j)
            omega
          have h1 : G1 x0 + (S.erase x0).sum G1 = S.sum G1 := Finset.add_sum_erase S G1 hx0
          have h2 : G2 x0 + (S.erase x0).sum G2 = S.sum G2 := Finset.add_sum_erase S G2 hx0
          have h3 : (S.erase x0).sum G1 ≤ (S.erase x0).sum G2 :=
            Finset.sum_le_sum fun x hx => hle_all x (Finset.mem_of_mem_erase hx)
          change S.sum G1 + 1 ≤ S.sum G2
          omega
        rcases hbad_pair with h1 | h2
        · exact (Nat.add_le_add_right hrec 1).trans (hinc e.1 he.1 (Or.inl rfl) h1)
        · exact (Nat.add_le_add_right hrec 1).trans (hinc e.2.1 he.2.1 (Or.inr rfl) h2)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hrec.trans hsum_mono
  have hP_mem : ∀ e ∈ P.flatten, e.1 ∈ S ∧ e.2.1 ∈ S ∧ f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false := by
    intro e he
    rcases List.mem_flatten.mp he with ⟨c, hc, hec⟩
    rcases (hchain c hc).2 e hec with ⟨h1, h2, _, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  have hbad_le_loss : (P.flatten.filter (fun e => !good e)).length ≤ lossC := by
    refine (hbad_bound P.flatten hP_mem).trans ?_
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => ?_
    split
    · exact le_refl 0
    · exact hcap x hx j
  have hsplit_len : ∀ (L : List (Finset (Fin n) × Finset (Fin n) × Fin m)),
      (L.filter good).length + (L.filter (fun e => !good e)).length = L.length := by
    intro L
    induction L with
    | nil => simp
    | cons e rest ih =>
      simp only [List.filter_cons, List.length_cons] at ih ⊢
      cases good e <;> simp <;> omega
  have hsp := hsplit_len P.flatten
  omega

private inductive IsWalk {V : Type} (R : List (V × V × Int)) : V → V → List (V × V × Int) → Prop
  | nil (u : V) : IsWalk R u u []
  | cons {u v : V} (e : V × V × Int) {rest : List (V × V × Int)} :
      e ∈ R → e.1 = u → IsWalk R e.2.1 v rest → IsWalk R u v (e :: rest)

private def walkGain {V : Type} (p : List (V × V × Int)) : Int :=
  (p.map (fun e => e.2.2)).sum

private lemma walkGain_nil {V : Type} : walkGain ([] : List (V × V × Int)) = 0 := rfl

private lemma walkGain_cons {V : Type} (e : V × V × Int) (p : List (V × V × Int)) :
    walkGain (e :: p) = e.2.2 + walkGain p := rfl

private lemma walkGain_append {V : Type} (p q : List (V × V × Int)) :
    walkGain (p ++ q) = walkGain p + walkGain q := by
  simp [walkGain]

private lemma isWalk_append {V : Type} {R : List (V × V × Int)} {u v w : V}
    {p q : List (V × V × Int)} (hp : IsWalk R u v p) (hq : IsWalk R v w q) :
    IsWalk R u w (p ++ q) := by
  induction hp with
  | nil _ => exact hq
  | cons e he hsrc _ ih => exact IsWalk.cons e he hsrc (ih hq)

private def walkVerts {V : Type} : V → List (V × V × Int) → List V
  | u, [] => [u]
  | u, e :: rest => u :: walkVerts e.2.1 rest

private lemma walkVerts_len {V : Type} (u : V) (p : List (V × V × Int)) :
    (walkVerts u p).length = p.length + 1 := by
  induction p generalizing u with
  | nil => rfl
  | cons e rest ih => simp [walkVerts, ih]

private lemma isWalk_split {V : Type} {R : List (V × V × Int)} :
    ∀ {u v : V} (p : List (V × V × Int)), IsWalk R u v p →
      ∀ (i : Nat) (hi : i < p.length + 1),
        let mid := (walkVerts u p)[i]'(by rw [walkVerts_len]; exact hi)
        IsWalk R u mid (p.take i) ∧ IsWalk R mid v (p.drop i) := by
  intro u v p hp
  induction hp with
  | nil u =>
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨IsWalk.nil u, IsWalk.nil u⟩
  | cons e he hsrc hrest ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [walkVerts, List.getElem_cons_zero, List.take_zero, List.drop_zero]
      exact ⟨IsWalk.nil _, IsWalk.cons e he hsrc hrest⟩
    | succ i =>
      simp only [walkVerts, List.getElem_cons_succ, List.take_succ_cons, List.drop_succ_cons]
      have hi' := Nat.lt_of_succ_lt_succ hi
      rcases ih i hi' with ⟨h1, h2⟩
      exact ⟨IsWalk.cons e he hsrc h1, h2⟩

private lemma walkVerts_drop {V : Type} {R : List (V × V × Int)} :
    ∀ {u v : V} (p : List (V × V × Int)), IsWalk R u v p →
      ∀ (i j : Nat) (hi : i ≤ j) (hj : j < p.length + 1),
        let mid := (walkVerts u p)[i]'(by rw [walkVerts_len]; omega)
        (walkVerts mid (p.drop i))[j - i]'(by rw [walkVerts_len, List.length_drop]; omega) =
          (walkVerts u p)[j]'(by rw [walkVerts_len]; exact hj) := by
  intro u v p hp
  induction hp with
  | nil u =>
    intro i j hi hj
    have hi0 : i = 0 := by simp at hj; omega
    have hj0 : j = 0 := by simp at hj; omega
    subst hi0; subst hj0; rfl
  | cons e he hsrc hrest ih =>
    intro i j hi hj
    cases i with
    | zero => simp [walkVerts]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [walkVerts, List.getElem_cons_succ, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
        exact ih i j (by omega) (by simp at hj; omega)

private lemma exists_dup_of_card_lt {V : Type} [Fintype V] [DecidableEq V] (L : List V)
    (hlt : Fintype.card V < L.length) :
    ∃ (i j : Nat) (hi : i < j) (hj : j < L.length), L[i]'(lt_trans hi hj) = L[j]'hj := by
  by_contra hno
  have hnd : L.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    apply Fin.ext
    rcases lt_trichotomy i j with h1 | h2 | h3
    · exact False.elim (hno ⟨i, j, h1, hj, heq⟩)
    · exact h2
    · exact False.elim (hno ⟨j, i, h3, hi, heq.symm⟩)
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
  have hle : L.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  omega

private lemma no_pos_cycle_shorten {V : Type} [Fintype V] [DecidableEq V]
    (R : List (V × V × Int)) (hnopos : ∀ u cyc, IsWalk R u u cyc → walkGain cyc ≤ 0) :
    ∀ {u v : V} (p : List (V × V × Int)), IsWalk R u v p →
      ∃ p', IsWalk R u v p' ∧ p'.length < Fintype.card V ∧ walkGain p ≤ walkGain p' := by
  intro u v p
  induction hlen : p.length using Nat.strong_induction_on generalizing p with
  | ind L ih =>
    intro hp
    by_cases hlt : p.length < Fintype.card V
    · exact ⟨p, hp, hlt, le_refl _⟩
    · have hcard_lt : Fintype.card V < (walkVerts u p).length := by rw [walkVerts_len]; omega
      rcases exists_dup_of_card_lt (walkVerts u p) hcard_lt with ⟨i, j, hij, hj_len, heq⟩
      have hj : j < p.length + 1 := by rw [walkVerts_len] at hj_len; exact hj_len
      rcases isWalk_split p hp i (by omega) with ⟨hp1, hdrop⟩
      set mid := (walkVerts u p)[i]'(by rw [walkVerts_len]; omega)
      have hj' : j - i < (p.drop i).length + 1 := by rw [List.length_drop]; omega
      rcases isWalk_split (p.drop i) hdrop (j - i) hj' with ⟨hcyc, hp2⟩
      have hmid2 : (walkVerts mid (p.drop i))[j - i]'(by rw [walkVerts_len]; exact hj') = mid := by
        rw [walkVerts_drop p hp i j (le_of_lt hij) hj]
        exact heq.symm
      rw [hmid2] at hcyc hp2
      have hshort : IsWalk R u v (p.take i ++ (p.drop i).drop (j - i)) := isWalk_append hp1 hp2
      have hpeq : p = p.take i ++ (p.drop i).take (j - i) ++ (p.drop i).drop (j - i) := by
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
      have hgain : walkGain p = walkGain (p.take i ++ (p.drop i).drop (j - i)) +
          walkGain ((p.drop i).take (j - i)) := by
        conv_lhs => rw [hpeq]
        rw [walkGain_append, walkGain_append, walkGain_append]
        omega
      have hcyc_le : walkGain ((p.drop i).take (j - i)) ≤ 0 := hnopos mid _ hcyc
      have hlen_lt : (p.take i ++ (p.drop i).drop (j - i)).length < L := by
        rw [List.length_append, List.length_take, List.length_drop, List.length_drop]
        omega
      rcases ih _ hlen_lt _ rfl hshort with ⟨p', hp', hlen', hgain'⟩
      exact ⟨p', hp', hlen', by omega⟩

private def optMax : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some x, some y => some (max x y)

private def optAdd (o : Option Int) (g : Int) : Option Int :=
  o.map (fun x => x + g)

private lemma optMax_eq_some_cases (a b : Option Int) (val : Int) (h : optMax a b = some val) :
    a = some val ∨ b = some val := by
  cases a with
  | none => right; exact h
  | some x =>
    cases b with
    | none => left; exact h
    | some y =>
      simp only [optMax, Option.some.injEq] at h
      rcases max_choice x y with hm | hm
      · left; rw [hm] at h; exact congrArg some h
      · right; rw [hm] at h; exact congrArg some h

private lemma optMax_ge_left (a b : Option Int) (x : Int) (ha : a = some x) :
    ∃ val, optMax a b = some val ∧ x ≤ val := by
  subst ha
  cases b with
  | none => exact ⟨x, rfl, le_refl _⟩
  | some y => exact ⟨max x y, rfl, le_max_left _ _⟩

private lemma optMax_ge_right (a b : Option Int) (y : Int) (hb : b = some y) :
    ∃ val, optMax a b = some val ∧ y ≤ val := by
  subst hb
  cases a with
  | none => exact ⟨y, rfl, le_refl _⟩
  | some x => exact ⟨max x y, rfl, le_max_right _ _⟩

private def bfDP {V : Type} [DecidableEq V] (R : List (V × V × Int)) (s0 : V) : Nat → V → Option Int
  | 0, v => if v = s0 then some 0 else none
  | k + 1, v =>
    R.foldl (fun acc e => if e.2.1 = v then optMax acc (optAdd (bfDP R s0 k e.1) e.2.2) else acc)
      (bfDP R s0 k v)

private lemma bfDP_fold_sound {V : Type} [DecidableEq V] (R : List (V × V × Int)) (s0 v : V)
    (k : Nat) (ih : ∀ u val, bfDP R s0 k u = some val → ∃ p, IsWalk R s0 u p ∧ p.length ≤ k ∧ walkGain p = val) :
    ∀ (E : List (V × V × Int)), (∀ e ∈ E, e ∈ R) →
      ∀ (acc : Option Int),
        (∀ val, acc = some val → ∃ p, IsWalk R s0 v p ∧ p.length ≤ k + 1 ∧ walkGain p = val) →
        ∀ val, E.foldl (fun a e => if e.2.1 = v then optMax a (optAdd (bfDP R s0 k e.1) e.2.2) else a) acc = some val →
          ∃ p, IsWalk R s0 v p ∧ p.length ≤ k + 1 ∧ walkGain p = val := by
  intro E
  induction E with
  | nil => intro _ acc hacc val h; exact hacc val h
  | cons e rest ihE =>
    intro hsub acc hacc val hfold
    simp only [List.foldl_cons] at hfold
    refine ihE (fun e' he' => hsub e' (List.mem_cons_of_mem e he')) _ ?_ val hfold
    intro val' hstep
    by_cases hdst : e.2.1 = v
    · rw [if_pos hdst] at hstep
      rcases optMax_eq_some_cases _ _ _ hstep with h1 | h2
      · exact hacc val' h1
      · cases hu : bfDP R s0 k e.1 with
        | none => simp [optAdd, hu] at h2
        | some x =>
          simp only [optAdd, hu, Option.map_some, Option.some.injEq] at h2
          rcases ih e.1 x hu with ⟨p, hp, hplen, hpgain⟩
          have heR : e ∈ R := hsub e List.mem_cons_self
          have hw1 : IsWalk R e.1 v [e] := IsWalk.cons e heR rfl (by rw [hdst]; exact IsWalk.nil v)
          refine ⟨p ++ [e], isWalk_append hp hw1, by simp; omega, ?_⟩
          rw [walkGain_append, hpgain, walkGain_cons, walkGain_nil, add_zero, h2]
    · rw [if_neg hdst] at hstep
      exact hacc val' hstep

private lemma bfDP_sound {V : Type} [DecidableEq V] (R : List (V × V × Int)) (s0 : V) :
    ∀ (k : Nat) (v : V) (val : Int), bfDP R s0 k v = some val →
      ∃ p, IsWalk R s0 v p ∧ p.length ≤ k ∧ walkGain p = val := by
  intro k
  induction k with
  | zero =>
    intro v val h
    dsimp only [bfDP] at h
    by_cases hv : v = s0
    · rw [if_pos hv] at h; cases h; subst hv; exact ⟨[], IsWalk.nil _, le_refl _, rfl⟩
    · rw [if_neg hv] at h; cases h
  | succ k ih =>
    intro v val h
    refine bfDP_fold_sound R s0 v k ih R (fun _ he => he) (bfDP R s0 k v) ?_ val h
    intro val' h'
    rcases ih v val' h' with ⟨p, hp, hlen, hgain⟩
    exact ⟨p, hp, by omega, hgain⟩

private lemma bfDP_fold_mono {V : Type} [DecidableEq V] (R : List (V × V × Int)) (s0 v : V) (k : Nat) :
    ∀ (E : List (V × V × Int)) (acc : Option Int) (x : Int), acc = some x →
      ∃ val, E.foldl (fun a e => if e.2.1 = v then optMax a (optAdd (bfDP R s0 k e.1) e.2.2) else a) acc = some val ∧ x ≤ val := by
  intro E
  induction E with
  | nil => intro acc x h; exact ⟨x, h, le_refl _⟩
  | cons e rest ih =>
    intro acc x h
    simp only [List.foldl_cons]
    by_cases hdst : e.2.1 = v
    · rw [if_pos hdst]
      rcases optMax_ge_left acc (optAdd (bfDP R s0 k e.1) e.2.2) x h with ⟨y, hy, hxy⟩
      rcases ih _ y hy with ⟨val, hval, hyv⟩
      exact ⟨val, hval, le_trans hxy hyv⟩
    · rw [if_neg hdst]
      exact ih acc x h

private lemma bfDP_fold_mem {V : Type} [DecidableEq V] (R : List (V × V × Int)) (s0 v : V) (k : Nat) :
    ∀ (E : List (V × V × Int)) (e : V × V × Int), e ∈ E → e.2.1 = v →
      ∀ (x : Int), bfDP R s0 k e.1 = some x →
      ∀ (acc : Option Int),
        ∃ val, E.foldl (fun a e' => if e'.2.1 = v then optMax a (optAdd (bfDP R s0 k e'.1) e'.2.2) else a) acc = some val ∧
          x + e.2.2 ≤ val := by
  intro E
  induction E with
  | nil => intro e he; simp at he
  | cons e0 rest ih =>
    intro e he hdst x hx acc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | hmem
    · rw [if_pos hdst]
      have hopt : optAdd (bfDP R s0 k e.1) e.2.2 = some (x + e.2.2) := by simp [optAdd, hx]
      rcases optMax_ge_right acc _ (x + e.2.2) hopt with ⟨y, hy, hle⟩
      rcases bfDP_fold_mono R s0 v k rest _ y hy with ⟨val, hval, hyv⟩
      exact ⟨val, hval, le_trans hle hyv⟩
    · exact ih e hmem hdst x hx _

private lemma isWalk_snoc_inv {V : Type} {R : List (V × V × Int)} :
    ∀ {u v : V} (p : List (V × V × Int)) (e : V × V × Int),
      IsWalk R u v (p ++ [e]) → e ∈ R ∧ e.2.1 = v ∧ IsWalk R u e.1 p := by
  intro u v p
  induction p generalizing u with
  | nil =>
    intro e h
    cases h with
    | cons _ he hsrc hrest =>
      cases hrest with
      | nil => exact ⟨he, rfl, by rw [← hsrc]; exact IsWalk.nil _⟩
  | cons e0 rest ih =>
    intro e h
    cases h with
    | cons _ he0 hsrc0 hrest =>
      rcases ih e hrest with ⟨heR, hdst, hpre⟩
      exact ⟨heR, hdst, IsWalk.cons e0 he0 hsrc0 hpre⟩

private lemma list_snoc_of_ne_nil {α : Type} {L : List α} (h : L ≠ []) :
    ∃ pre a, L = pre ++ [a] :=
  ⟨L.dropLast, L.getLast h, (List.dropLast_append_getLast h).symm⟩

private lemma bfDP_complete {V : Type} [DecidableEq V] (R : List (V × V × Int)) (s0 : V) :
    ∀ (k : Nat) (v : V) (p : List (V × V × Int)), IsWalk R s0 v p → p.length ≤ k →
      ∃ val, bfDP R s0 k v = some val ∧ walkGain p ≤ val := by
  intro k
  induction k with
  | zero =>
    intro v p hp hlen
    have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp0
    cases hp with
    | nil => exact ⟨0, by simp [bfDP], le_refl 0⟩
  | succ k ih =>
    intro v p hp hlen
    by_cases hlek : p.length ≤ k
    · rcases ih v p hp hlek with ⟨x, hx, hgx⟩
      rcases bfDP_fold_mono R s0 v k R (bfDP R s0 k v) x hx with ⟨val, hval, hxv⟩
      exact ⟨val, hval, le_trans hgx hxv⟩
    · have hne : p ≠ [] := fun h => by subst h; simp at hlek
      rcases list_snoc_of_ne_nil hne with ⟨pre, e, rfl⟩
      rcases isWalk_snoc_inv pre e hp with ⟨heR, hdst, hpre⟩
      have hpre_len : pre.length ≤ k := by simp at hlen; omega
      rcases ih e.1 pre hpre hpre_len with ⟨x, hx, hgx⟩
      rcases bfDP_fold_mem R s0 v k R e heR hdst x hx (bfDP R s0 k v) with ⟨val, hval, hle⟩
      refine ⟨val, hval, ?_⟩
      rw [walkGain_append, walkGain_cons, walkGain_nil, add_zero]
      omega

private lemma bellman_ford_potential {V : Type} [Fintype V] [DecidableEq V]
    (R : List (V × V × Int)) (s0 : V)
    (hreach : ∀ v : V, ∃ p, IsWalk R s0 v p)
    (hnopos : ∀ u cyc, IsWalk R u u cyc → walkGain cyc ≤ 0) :
    ∃ π : V → Int, π s0 = 0 ∧ ∀ e ∈ R, π e.1 + e.2.2 ≤ π e.2.1 := by
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s0⟩
  let K := Fintype.card V - 1
  have hsome : ∀ v : V, ∃ val, bfDP R s0 K v = some val := by
    intro v
    rcases hreach v with ⟨p, hp⟩
    rcases no_pos_cycle_shorten R hnopos p hp with ⟨p', hp', hlen', _⟩
    rcases bfDP_complete R s0 K v p' hp' (by omega) with ⟨val, hval, _⟩
    exact ⟨val, hval⟩
  let π : V → Int := fun v => (bfDP R s0 K v).getD 0
  have hπ_eq : ∀ v : V, bfDP R s0 K v = some (π v) := by
    intro v
    rcases hsome v with ⟨val, hval⟩
    have : π v = val := by simp [π, hval]
    rw [this]; exact hval
  refine ⟨π, ?_, ?_⟩
  · rcases bfDP_complete R s0 K s0 [] (IsWalk.nil s0) (Nat.zero_le _) with ⟨v1, hv1, hge0⟩
    rw [hπ_eq s0] at hv1; cases hv1
    rcases bfDP_sound R s0 K s0 (π s0) (hπ_eq s0) with ⟨p, hp, _, hgp⟩
    have hle0 := hnopos s0 p hp
    rw [hgp] at hle0
    dsimp only [walkGain] at hge0; simp at hge0
    omega
  · intro e heR
    rcases bfDP_sound R s0 K e.1 (π e.1) (hπ_eq e.1) with ⟨p, hp, _, hgp⟩
    have hw : IsWalk R s0 e.2.1 (p ++ [e]) :=
      isWalk_append hp (IsWalk.cons e heR rfl (IsWalk.nil e.2.1))
    rcases no_pos_cycle_shorten R hnopos (p ++ [e]) hw with ⟨p', hp', hlen', hgain'⟩
    rcases bfDP_complete R s0 K e.2.1 p' hp' (by omega) with ⟨val, hval, hle⟩
    rw [hπ_eq e.2.1] at hval; cases hval
    rw [walkGain_append, walkGain_cons, walkGain_nil, add_zero, hgp] at hgain'
    omega


private inductive SVert (n : Nat) (S : Finset (Finset (Fin n))) (m : Nat)
  | src
  | snk
  | vB (x : {x : Finset (Fin n) // x ∈ S})
  | vT (x : {x : Finset (Fin n) // x ∈ S}) (j : Fin m)
  deriving DecidableEq

private def svertEquiv (n : Nat) (S : Finset (Finset (Fin n))) (m : Nat) :
    SVert n S m ≃ Unit ⊕ Unit ⊕ {x : Finset (Fin n) // x ∈ S} ⊕ ({x : Finset (Fin n) // x ∈ S} × Fin m) where
  toFun
    | .src => Sum.inl ()
    | .snk => Sum.inr (Sum.inl ())
    | .vB x => Sum.inr (Sum.inr (Sum.inl x))
    | .vT x j => Sum.inr (Sum.inr (Sum.inr (x, j)))
  invFun
    | Sum.inl () => .src
    | Sum.inr (Sum.inl ()) => .snk
    | Sum.inr (Sum.inr (Sum.inl x)) => .vB x
    | Sum.inr (Sum.inr (Sum.inr (x, j))) => .vT x j
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with ⟨⟩ | ⟨⟩ | x | ⟨x, j⟩ <;> rfl

private instance svertFintype (n : Nat) (S : Finset (Finset (Fin n))) (m : Nat) :
    Fintype (SVert n S m) :=
  Fintype.ofEquiv _ (svertEquiv n S m).symm

private inductive SArc (n : Nat) (S : Finset (Finset (Fin n))) (m : Nat)
  | srcB (x : {x : Finset (Fin n) // x ∈ S})
  | bSnk (x : {x : Finset (Fin n) // x ∈ S})
  | ret
  | bb (x y : {x : Finset (Fin n) // x ∈ S})
  | tt (x y : {x : Finset (Fin n) // x ∈ S}) (j : Fin m)
  | ent0 (x : {x : Finset (Fin n) // x ∈ S}) (j : Fin m)
  | extM1 (x : {x : Finset (Fin n) // x ∈ S}) (j : Fin m)
  | entHi (x : {x : Finset (Fin n) // x ∈ S}) (j : Fin m)
  | extLo (x : {x : Finset (Fin n) // x ∈ S}) (j : Fin m)
  deriving DecidableEq

private def sarcEquiv (n : Nat) (S : Finset (Finset (Fin n))) (m : Nat) :
    SArc n S m ≃
      {x : Finset (Fin n) // x ∈ S} ⊕
      {x : Finset (Fin n) // x ∈ S} ⊕
      Unit ⊕
      ({x : Finset (Fin n) // x ∈ S} × {x : Finset (Fin n) // x ∈ S}) ⊕
      ({x : Finset (Fin n) // x ∈ S} × {x : Finset (Fin n) // x ∈ S} × Fin m) ⊕
      ({x : Finset (Fin n) // x ∈ S} × Fin m) ⊕
      ({x : Finset (Fin n) // x ∈ S} × Fin m) ⊕
      ({x : Finset (Fin n) // x ∈ S} × Fin m) ⊕
      ({x : Finset (Fin n) // x ∈ S} × Fin m) where
  toFun
    | .srcB x => Sum.inl x
    | .bSnk x => Sum.inr (Sum.inl x)
    | .ret => Sum.inr (Sum.inr (Sum.inl ()))
    | .bb x y => Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, y))))
    | .tt x y j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, y, j)))))
    | .ent0 x j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, j))))))
    | .extM1 x j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, j)))))))
    | .entHi x j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, j))))))))
    | .extLo x j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (x, j))))))))
  invFun
    | Sum.inl x => .srcB x
    | Sum.inr (Sum.inl x) => .bSnk x
    | Sum.inr (Sum.inr (Sum.inl ())) => .ret
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, y)))) => .bb x y
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, y, j))))) => .tt x y j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, j)))))) => .ent0 x j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, j))))))) => .extM1 x j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, j)))))))) => .entHi x j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (x, j)))))))) => .extLo x j
  left_inv a := by cases a <;> rfl
  right_inv a := by
    rcases a with x | x | ⟨⟩ | ⟨x, y⟩ | ⟨x, y, j⟩ | ⟨x, j⟩ | ⟨x, j⟩ | ⟨x, j⟩ | ⟨x, j⟩ <;> rfl

private instance sarcFintype (n : Nat) (S : Finset (Finset (Fin n))) (m : Nat) :
    Fintype (SArc n S m) :=
  Fintype.ofEquiv _ (sarcEquiv n S m).symm

private lemma sarc_sum {n m : Nat} {S : Finset (Finset (Fin n))} {M : Type} [AddCommMonoid M]
    (g : SArc n S m → M) :
    (Finset.univ : Finset (SArc n S m)).sum g =
      (Finset.univ.sum fun x => g (.srcB x)) +
      ((Finset.univ.sum fun x => g (.bSnk x)) +
      (g .ret +
      ((Finset.univ.sum fun p : {x // x ∈ S} × {x // x ∈ S} => g (.bb p.1 p.2)) +
      ((Finset.univ.sum fun p : {x // x ∈ S} × {x // x ∈ S} × Fin m => g (.tt p.1 p.2.1 p.2.2)) +
      ((Finset.univ.sum fun p : {x // x ∈ S} × Fin m => g (.ent0 p.1 p.2)) +
      ((Finset.univ.sum fun p : {x // x ∈ S} × Fin m => g (.extM1 p.1 p.2)) +
      ((Finset.univ.sum fun p : {x // x ∈ S} × Fin m => g (.entHi p.1 p.2)) +
      (Finset.univ.sum fun p : {x // x ∈ S} × Fin m => g (.extLo p.1 p.2))))))))) := by
  have heq := Fintype.sum_equiv (sarcEquiv n S m) g (fun y => g ((sarcEquiv n S m).symm y))
    (fun a => by simp)
  rw [heq]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  rfl

private def arcSrc {n m : Nat} {S : Finset (Finset (Fin n))} : SArc n S m → SVert n S m
  | .srcB _ => .src
  | .bSnk x => .vB x
  | .ret => .snk
  | .bb x _ => .vB x
  | .tt x _ j => .vT x j
  | .ent0 x j => .vB x
  | .extM1 x j => .vT x j
  | .entHi x j => .vB x
  | .extLo x j => .vT x j

private def arcDst {n m : Nat} {S : Finset (Finset (Fin n))} : SArc n S m → SVert n S m
  | .srcB x => .vB x
  | .bSnk _ => .snk
  | .ret => .src
  | .bb _ y => .vB y
  | .tt _ y j => .vT y j
  | .ent0 x j => .vT x j
  | .extM1 x j => .vB x
  | .entHi x j => .vT x j
  | .extLo x j => .vB x

private def arcGain {n m : Nat} {S : Finset (Finset (Fin n))} (d : Nat) : SArc n S m → Int
  | .srcB _ => 0
  | .bSnk _ => 0
  | .ret => -(d : Int)
  | .bb _ _ => 0
  | .tt _ _ _ => 0
  | .ent0 _ _ => 0
  | .extM1 _ _ => -1
  | .entHi _ _ => 1
  | .extLo _ _ => 0

private def arcValid {n m : Nat} {S : Finset (Finset (Fin n))} : SArc n S m → Bool
  | .bb x y => decide (x.1 ⊆ y.1 ∧ x.1 ≠ y.1)
  | .tt x y _ => decide (x.1 ⊆ y.1 ∧ x.1 ≠ y.1)
  | _ => true

private def arcCap {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) : SArc n S m → Option Nat
  | .entHi x j => some (if f x.1 j = true then w x.1 j else 0)
  | .extLo x j => some (if f x.1 j = false then w x.1 j else 0)
  | _ => none

private lemma arcValid_no_self_loop {n m : Nat} {S : Finset (Finset (Fin n))} (a : SArc n S m)
    (hv : arcValid a = true) : arcSrc a ≠ arcDst a := by
  cases a with
  | bb x y =>
    simp only [arcValid] at hv
    have hxy := of_decide_eq_true hv
    intro h; cases h; exact hxy.2 rfl
  | tt x y j =>
    simp only [arcValid] at hv
    have hxy := of_decide_eq_true hv
    intro h; cases h; exact hxy.2 rfl
  | _ => intro h; cases h

private def outFlow {n m : Nat} {S : Finset (Finset (Fin n))} (φ : SArc n S m → Nat) (v : SVert n S m) : Nat :=
  (Finset.univ : Finset (SArc n S m)).sum (fun a => if arcSrc a = v then φ a else 0)

private def inFlow {n m : Nat} {S : Finset (Finset (Fin n))} (φ : SArc n S m → Nat) (v : SVert n S m) : Nat :=
  (Finset.univ : Finset (SArc n S m)).sum (fun a => if arcDst a = v then φ a else 0)

private def IsCirc {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat)
    (φ : SArc n S m → Nat) : Prop :=
  (∀ a, arcValid a = false → φ a = 0) ∧
  (∀ a cap, arcCap f w a = some cap → φ a ≤ cap) ∧
  (∀ v, outFlow φ v = inFlow φ v)

private def circGain {n m : Nat} {S : Finset (Finset (Fin n))} (d : Nat) (φ : SArc n S m → Nat) : Int :=
  (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * arcGain d a)

private def totalFlow {n m : Nat} {S : Finset (Finset (Fin n))} (φ : SArc n S m → Nat) : Nat :=
  (Finset.univ : Finset (SArc n S m)).sum φ

private inductive IsGenWalk {V A : Type} (src dst : A → V) (P : A → Prop) : V → V → List A → Prop
  | nil (u : V) : IsGenWalk src dst P u u []
  | cons {u v : V} (a : A) {rest : List A} :
      P a → src a = u → IsGenWalk src dst P (dst a) v rest → IsGenWalk src dst P u v (a :: rest)

private def genWalkVerts {V A : Type} (dst : A → V) : V → List A → List V
  | u, [] => [u]
  | u, a :: rest => u :: genWalkVerts dst (dst a) rest

private lemma genWalkVerts_len {V A : Type} (dst : A → V) (u : V) (p : List A) :
    (genWalkVerts dst u p).length = p.length + 1 := by
  induction p generalizing u with
  | nil => rfl
  | cons a rest ih => simp [genWalkVerts, ih]

private lemma isGenWalk_append {V A : Type} {src dst : A → V} {P : A → Prop} {u v w : V}
    {p q : List A} (hp : IsGenWalk src dst P u v p) (hq : IsGenWalk src dst P v w q) :
    IsGenWalk src dst P u w (p ++ q) := by
  induction hp with
  | nil _ => exact hq
  | cons a ha hs _ ih => exact IsGenWalk.cons a ha hs (ih hq)

private lemma isGenWalk_mem {V A : Type} {src dst : A → V} {P : A → Prop} {u v : V} {p : List A}
    (hp : IsGenWalk src dst P u v p) : ∀ a ∈ p, P a := by
  induction hp with
  | nil _ => intro a ha; simp at ha
  | cons a ha _ _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ha
    · exact ih b hb'

private lemma isGenWalk_split {V A : Type} {src dst : A → V} {P : A → Prop} :
    ∀ {u v : V} (p : List A), IsGenWalk src dst P u v p →
      ∀ (i : Nat) (hi : i < p.length + 1),
        let mid := (genWalkVerts dst u p)[i]'(by rw [genWalkVerts_len]; exact hi)
        IsGenWalk src dst P u mid (p.take i) ∧ IsGenWalk src dst P mid v (p.drop i) := by
  intro u v p hp
  induction hp with
  | nil u =>
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; exact ⟨IsGenWalk.nil u, IsGenWalk.nil u⟩
  | cons a ha hs hrest ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [genWalkVerts, List.getElem_cons_zero, List.take_zero, List.drop_zero]
      exact ⟨IsGenWalk.nil _, IsGenWalk.cons a ha hs hrest⟩
    | succ i =>
      simp only [genWalkVerts, List.getElem_cons_succ, List.take_succ_cons, List.drop_succ_cons]
      rcases ih i (by simp at hi; omega) with ⟨h1, h2⟩
      exact ⟨IsGenWalk.cons a ha hs h1, h2⟩

private lemma genWalkVerts_drop {V A : Type} {src dst : A → V} {P : A → Prop} :
    ∀ {u v : V} (p : List A), IsGenWalk src dst P u v p →
      ∀ (i j : Nat) (hi : i ≤ j) (hj : j < p.length + 1),
        let mid := (genWalkVerts dst u p)[i]'(by rw [genWalkVerts_len]; omega)
        (genWalkVerts dst mid (p.drop i))[j - i]'(by rw [genWalkVerts_len, List.length_drop]; omega) =
          (genWalkVerts dst u p)[j]'(by rw [genWalkVerts_len]; exact hj) := by
  intro u v p hp
  induction hp with
  | nil u =>
    intro i j hi hj
    have hi0 : i = 0 := by simp at hj; omega
    have hj0 : j = 0 := by simp at hj; omega
    subst hi0; subst hj0; rfl
  | cons a ha hs hrest ih =>
    intro i j hi hj
    cases i with
    | zero => simp [genWalkVerts]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [genWalkVerts, List.getElem_cons_succ, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
        exact ih i j (by omega) (by simp at hj; omega)

private lemma genWalkVerts_take_eq_map_src {V A : Type} {src dst : A → V} {P : A → Prop} :
    ∀ {u v : V} (p : List A), IsGenWalk src dst P u v p →
      (genWalkVerts dst u p).take p.length = p.map src := by
  intro u v p hp
  induction hp with
  | nil _ => rfl
  | cons a _ hs _ ih =>
    simp only [genWalkVerts, List.length_cons, List.take_succ_cons, List.map_cons, hs, ih]

private lemma isGenWalk_balance {V A : Type} [DecidableEq V] {src dst : A → V} {P : A → Prop} :
    ∀ {u v : V} (p : List A), IsGenWalk src dst P u v p →
      ∀ (w : V),
        ((p.filter (fun a => decide (src a = w))).length : Int) -
        ((p.filter (fun a => decide (dst a = w))).length : Int) =
          (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  intro u v p hp
  induction hp with
  | nil u => intro w; simp
  | cons a _ hs hrest ih =>
    intro w
    have hrec := ih w
    simp only [List.filter_cons]
    by_cases h1 : src a = w <;> by_cases h2 : dst a = w
    · rw [decide_eq_true h1, decide_eq_true h2]
      simp only [↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [← hs, if_pos h1]; rw [if_pos h2] at hrec; omega
    · rw [decide_eq_true h1, decide_eq_false h2]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [← hs, if_pos h1]; rw [if_neg h2] at hrec; omega
    · rw [decide_eq_false h1, decide_eq_true h2]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [← hs, if_neg h1]; rw [if_pos h2] at hrec; omega
    · rw [decide_eq_false h1, decide_eq_false h2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hs, if_neg h1]; rw [if_neg h2] at hrec; omega

private lemma isGenWalk_closed_balance {V A : Type} [DecidableEq V] {src dst : A → V} {P : A → Prop}
    {u : V} {p : List A} (hp : IsGenWalk src dst P u u p) (w : V) :
    (p.filter (fun a => decide (src a = w))).length =
      (p.filter (fun a => decide (dst a = w))).length := by
  have hb := isGenWalk_balance p hp w
  omega

private lemma isGenWalk_sum_count {A : Type} [Fintype A] [DecidableEq A] {M : Type} [AddCommMonoid M]
    (g : A → M) (p : List A) :
    (Finset.univ : Finset A).sum (fun a => p.count a • g a) = (p.map g).sum := by
  induction p with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    have h1 : ∀ a : A, (x :: rest).count a • g a = (if a = x then g a else 0) + rest.count a • g a := by
      intro a
      by_cases hax : a = x
      · subst hax; simp [List.count_cons_self, add_nsmul, add_comm]
      · simp [List.count_cons_of_ne (Ne.symm hax), hax]
    calc (Finset.univ : Finset A).sum (fun a => (x :: rest).count a • g a)
        = (Finset.univ : Finset A).sum (fun a => (if a = x then g a else 0) + rest.count a • g a) :=
          Finset.sum_congr rfl fun a _ => h1 a
      _ = (Finset.univ : Finset A).sum (fun a => if a = x then g a else 0) +
          (Finset.univ : Finset A).sum (fun a => rest.count a • g a) := Finset.sum_add_distrib
      _ = g x + (Finset.univ : Finset A).sum (fun a => rest.count a • g a) := by simp

private lemma sum_count_int {A : Type} [Fintype A] [DecidableEq A] (g : A → Int) (p : List A) :
    (Finset.univ : Finset A).sum (fun a => (p.count a : Int) * g a) = (p.map g).sum := by
  have h := isGenWalk_sum_count g p
  simpa [zsmul_eq_mul] using h

private lemma sum_count_filter {A : Type} [Fintype A] [DecidableEq A] (q : A → Bool) (p : List A) :
    (Finset.univ : Finset A).sum (fun a => if q a = true then p.count a else 0) = (p.filter q).length := by
  induction p with
  | nil => simp
  | cons x rest ih =>
    simp only [List.filter_cons]
    have h1 : ∀ a : A, (if q a = true then (x :: rest).count a else 0) =
        (if a = x then (if q a = true then 1 else 0) else 0) + (if q a = true then rest.count a else 0) := by
      intro a
      by_cases hax : a = x
      · subst hax
        cases hq : q a <;> simp [List.count_cons_self, Nat.add_comm]
      · simp [List.count_cons_of_ne (Ne.symm hax), hax]
    calc (Finset.univ : Finset A).sum (fun a => if q a = true then (x :: rest).count a else 0)
        = (Finset.univ : Finset A).sum (fun a => (if a = x then (if q a = true then 1 else 0) else 0) +
            (if q a = true then rest.count a else 0)) := Finset.sum_congr rfl fun a _ => h1 a
      _ = (Finset.univ : Finset A).sum (fun a => if a = x then (if q a = true then 1 else 0) else 0) +
          (Finset.univ : Finset A).sum (fun a => if q a = true then rest.count a else 0) := Finset.sum_add_distrib
      _ = (if q x = true then 1 else 0) + (rest.filter q).length := by rw [ih]; simp
      _ = (if q x = true then x :: rest.filter q else rest.filter q).length := by
          cases q x <;> simp [Nat.add_comm]

private lemma isGenWalk_telescope {V A : Type} {src dst : A → V} {P : A → Prop}
    (g : A → Int) (ψ : V → Int) :
    ∀ {u v : V} (p : List A), IsGenWalk src dst P u v p →
      (∀ a ∈ p, g a ≤ ψ (dst a) - ψ (src a)) →
      (p.map g).sum ≤ ψ v - ψ u := by
  intro u v p hp
  induction hp with
  | nil u => intro _; simp
  | cons a _ hs hrest ih =>
    intro hle
    have ha := hle a List.mem_cons_self
    have hrec := ih (fun b hb => hle b (List.mem_cons_of_mem a hb))
    rw [hs] at ha
    simp only [List.map_cons, List.sum_cons]
    omega

private lemma isGenWalk_rotate {V A : Type} {src dst : A → V} {P : A → Prop}
    {u : V} {p : List A} (hp : IsGenWalk src dst P u u p) (i : Nat) (hi : i < p.length) :
    let mid := (genWalkVerts dst u p)[i]'(by rw [genWalkVerts_len]; omega)
    IsGenWalk src dst P mid mid (p.drop i ++ p.take i) := by
  rcases isGenWalk_split p hp i (by omega) with ⟨h1, h2⟩
  exact isGenWalk_append h2 h1

private lemma nodup_rotate {α : Type} (L : List α) (i : Nat) (hnd : L.Nodup) :
    (L.drop i ++ L.take i).Nodup := by
  have hperm : (L.drop i ++ L.take i).Perm L := by
    refine List.perm_append_comm.trans ?_
    rw [List.take_append_drop]
  exact hperm.nodup_iff.mpr hnd

private lemma mem_iff_rotate_head {V A : Type} {src dst : A → V} {P : A → Prop}
    {u : V} {p : List A} (hp : IsGenWalk src dst P u u p) (a : A) (ha : a ∈ p) :
    ∃ (q : List A), IsGenWalk src dst P (src a) (src a) (a :: q) ∧ (a :: q).Perm p := by
  rcases List.mem_iff_getElem.mp ha with ⟨i, hi, hget⟩
  have hrot := isGenWalk_rotate hp i hi
  have hdrop_eq : p.drop i = a :: p.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have hmid : (genWalkVerts dst u p)[i]'(by rw [genWalkVerts_len]; omega) = src a := by
    have htake := genWalkVerts_take_eq_map_src p hp
    have h1 : ((genWalkVerts dst u p).take p.length)[i]'(by rw [List.length_take, genWalkVerts_len]; omega) =
        (p.map src)[i]'(by simp [hi]) := by congr 1
    simp only [List.getElem_take, List.getElem_map, hget] at h1
    exact h1
  rw [hmid, hdrop_eq, List.cons_append] at hrot
  refine ⟨p.drop (i + 1) ++ p.take i, hrot, ?_⟩
  rw [← List.cons_append, ← hdrop_eq]
  refine List.perm_append_comm.trans ?_
  rw [List.take_append_drop]

private lemma exists_simple_pos_cycle {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat)
    (φ : SArc n S m → Nat) (hcirc : IsCirc f w φ) (hpos : 0 < totalFlow φ) :
    ∃ (u : SVert n S m) (C : List (SArc n S m)),
      IsGenWalk arcSrc arcDst (fun a => 0 < φ a) u u C ∧
      0 < C.length ∧ (C.map arcSrc).Nodup := by
  have hex_arc : ∃ a : SArc n S m, 0 < φ a := by
    by_contra hno
    push_neg at hno
    have h0 : totalFlow φ = 0 := Finset.sum_eq_zero fun a _ => Nat.le_zero.mp (hno a)
    omega
  rcases hex_arc with ⟨a0, ha0⟩
  have hstep : ∀ (v : SVert n S m), 0 < inFlow φ v → ∃ a : SArc n S m, 0 < φ a ∧ arcSrc a = v := by
    intro v hin
    have hout : 0 < outFlow φ v := by rw [hcirc.2.2 v]; exact hin
    by_contra hno
    push_neg at hno
    have h0 : outFlow φ v = 0 := Finset.sum_eq_zero fun a _ => by
      by_cases hs : arcSrc a = v
      · rw [if_pos hs]
        by_cases hpa : 0 < φ a
        · exact False.elim (hno a hpa hs)
        · omega
      · rw [if_neg hs]
    omega
  have hwalk_len : ∀ k : Nat, ∃ (v : SVert n S m) (p : List (SArc n S m)),
      IsGenWalk arcSrc arcDst (fun a => 0 < φ a) (arcSrc a0) v p ∧ p.length = k + 1 := by
    intro k
    induction k with
    | zero =>
      exact ⟨arcDst a0, [a0], IsGenWalk.cons a0 ha0 rfl (IsGenWalk.nil _), rfl⟩
    | succ k ih =>
      rcases ih with ⟨v, p, hp, hplen⟩
      have hne : p ≠ [] := fun h => by subst h; simp at hplen
      rcases list_snoc_of_ne_nil hne with ⟨pre, aLast, rfl⟩
      have haLast : 0 < φ aLast ∧ arcDst aLast = v := by
        have hmem := isGenWalk_mem hp aLast (by simp)
        have hlast_dst : ∀ {u1 v1 : SVert n S m} (q : List (SArc n S m)) (e : SArc n S m),
            IsGenWalk arcSrc arcDst (fun a => 0 < φ a) u1 v1 (q ++ [e]) → arcDst e = v1 := by
          intro u1 v1 q
          induction q generalizing u1 with
          | nil =>
            intro e h; cases h with
            | cons _ _ _ hr => cases hr; rfl
          | cons e0 r ihq =>
            intro e h; cases h with
            | cons _ _ _ hr => exact ihq e hr
        exact ⟨hmem, hlast_dst pre aLast hp⟩
      have hin : 0 < inFlow φ v := by
        have hle : (if arcDst aLast = v then φ aLast else 0) ≤ inFlow φ v :=
          Finset.single_le_sum (f := fun a => if arcDst a = v then φ a else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ aLast)
        rw [if_pos haLast.2] at hle
        omega
      rcases hstep v hin with ⟨aNext, haNext, hsNext⟩
      refine ⟨arcDst aNext, (pre ++ [aLast]) ++ [aNext],
        isGenWalk_append hp (IsGenWalk.cons aNext haNext hsNext (IsGenWalk.nil _)), ?_⟩
      rw [List.length_append, hplen]; rfl
  have hex_cyc : ∃ L : Nat, 0 < L ∧ ∃ (u : SVert n S m) (C : List (SArc n S m)),
      IsGenWalk arcSrc arcDst (fun a => 0 < φ a) u u C ∧ C.length = L := by
    rcases hwalk_len (Fintype.card (SVert n S m)) with ⟨v, p, hp, hplen⟩
    have hlt : Fintype.card (SVert n S m) < (genWalkVerts arcDst (arcSrc a0) p).length := by
      rw [genWalkVerts_len, hplen]; omega
    rcases exists_dup_of_card_lt (genWalkVerts arcDst (arcSrc a0) p) hlt with ⟨i, j, hij, hjlen, heq⟩
    have hj : j < p.length + 1 := by rw [genWalkVerts_len] at hjlen; exact hjlen
    rcases isGenWalk_split p hp i (by omega) with ⟨_, hdrop⟩
    set mid := (genWalkVerts arcDst (arcSrc a0) p)[i]'(by rw [genWalkVerts_len]; omega)
    have hj' : j - i < (p.drop i).length + 1 := by rw [List.length_drop]; omega
    rcases isGenWalk_split (p.drop i) hdrop (j - i) hj' with ⟨hcyc, _⟩
    have hmid2 : (genWalkVerts arcDst mid (p.drop i))[j - i]'(by rw [genWalkVerts_len]; exact hj') = mid := by
      rw [genWalkVerts_drop p hp i j (le_of_lt hij) hj]; exact heq.symm
    rw [hmid2] at hcyc
    refine ⟨j - i, by omega, mid, (p.drop i).take (j - i), hcyc, ?_⟩
    rw [List.length_take, List.length_drop]; omega
  classical
  let Lmin := Nat.find hex_cyc
  have hmin_spec := Nat.find_spec hex_cyc
  rcases hmin_spec with ⟨hLpos, u, C, hC, hClen⟩
  refine ⟨u, C, hC, by omega, ?_⟩
  rw [← genWalkVerts_take_eq_map_src C hC]
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  apply Fin.ext
  have hiC : i < C.length := by rw [List.length_take, genWalkVerts_len] at hi; omega
  have hjC : j < C.length := by rw [List.length_take, genWalkVerts_len] at hj; omega
  simp only [List.getElem_take] at heq
  rcases lt_trichotomy i j with hlt | hEq | hgt
  · rcases isGenWalk_split C hC i (by omega) with ⟨_, hdrop⟩
    set mid := (genWalkVerts arcDst u C)[i]'(by rw [genWalkVerts_len]; omega)
    have hj' : j - i < (C.drop i).length + 1 := by rw [List.length_drop]; omega
    rcases isGenWalk_split (C.drop i) hdrop (j - i) hj' with ⟨hcyc, _⟩
    have hmid2 : (genWalkVerts arcDst mid (C.drop i))[j - i]'(by rw [genWalkVerts_len]; exact hj') = mid := by
      rw [genWalkVerts_drop C hC i j (le_of_lt hlt) (by omega)]; exact heq.symm
    rw [hmid2] at hcyc
    have hsub_len : ((C.drop i).take (j - i)).length = j - i := by
      rw [List.length_take, List.length_drop]; omega
    exact False.elim (Nat.find_min hex_cyc (by omega : j - i < Lmin) ⟨by omega, mid, _, hcyc, hsub_len⟩)
  · exact hEq
  · rcases isGenWalk_split C hC j (by omega) with ⟨_, hdrop⟩
    set mid := (genWalkVerts arcDst u C)[j]'(by rw [genWalkVerts_len]; omega)
    have hi' : i - j < (C.drop j).length + 1 := by rw [List.length_drop]; omega
    rcases isGenWalk_split (C.drop j) hdrop (i - j) hi' with ⟨hcyc, _⟩
    have hmid2 : (genWalkVerts arcDst mid (C.drop j))[i - j]'(by rw [genWalkVerts_len]; exact hi') = mid := by
      rw [genWalkVerts_drop C hC j i (le_of_lt hgt) (by omega)]; exact heq
    rw [hmid2] at hcyc
    have hsub_len : ((C.drop j).take (i - j)).length = i - j := by
      rw [List.length_take, List.length_drop]; omega
    exact False.elim (Nat.find_min hex_cyc (by omega : i - j < Lmin) ⟨by omega, mid, _, hcyc, hsub_len⟩)

private lemma consume_tap {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (φ : SArc n S m → Nat) (hcirc : IsCirc f w φ) :
    ∀ (W : List (SArc n S m)) (x xEnd : {x : Finset (Fin n) // x ∈ S}) (j : Fin m),
      IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) (.vT x j) (.vB xEnd) W →
      ∃ (y : {x : Finset (Fin n) // x ∈ S}) (isLo : Bool) (rest : List (SArc n S m)),
        x.1 ⊆ y.1 ∧
        rest.length < W.length ∧
        IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) (.vB y) (.vB xEnd) rest ∧
        (W.map (arcGain d)).sum = (if isLo = true then 0 else -1) + (rest.map (arcGain d)).sum ∧
        (isLo = true → f y.1 j = false) ∧
        (∀ z k, W.count (.entHi z k) = rest.count (.entHi z k)) ∧
        (∀ z k, W.count (.extLo z k) = (if isLo = true ∧ z = y ∧ k = j then 1 else 0) + rest.count (.extLo z k)) := by
  intro W
  induction W with
  | nil =>
    intro x xEnd j hW
    cases hW
  | cons a rest ih =>
    intro x xEnd j hW
    cases hW with
    | cons _ ha hs hrest =>
      have hval : arcValid a = true := by
        cases hv : arcValid a
        · have := hcirc.1 a hv; omega
        · rfl
      cases a with
      | tt x1 y1 j1 =>
        simp only [arcSrc] at hs
        cases hs
        simp only [arcValid] at hval
        have hxy : x.1 ⊆ y1.1 := (of_decide_eq_true hval).1
        rcases ih y1 xEnd j hrest with ⟨y, isLo, rest2, hy_sub, hlen, hrest2, hgain, hlo, hent, hext⟩
        refine ⟨y, isLo, rest2, hxy.trans hy_sub, by simp; omega, hrest2, ?_, hlo, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, arcGain, zero_add]; exact hgain
        · intro z k
          have hne : SArc.tt x y1 j ≠ SArc.entHi z k := by intro h; cases h
          rw [List.count_cons_of_ne hne]; exact hent z k
        · intro z k
          have hne : SArc.tt x y1 j ≠ SArc.extLo z k := by intro h; cases h
          rw [List.count_cons_of_ne hne]; exact hext z k
      | extM1 x1 j1 =>
        simp only [arcSrc] at hs; cases hs
        refine ⟨x, false, rest, le_refl _, by simp, hrest, ?_, fun h => Bool.noConfusion h, ?_, ?_⟩
        · simp [arcGain]
        · intro z k
          have hne : SArc.extM1 x j ≠ SArc.entHi z k := by intro h; cases h
          rw [List.count_cons_of_ne hne]
        · intro z k
          have hne : SArc.extM1 x j ≠ SArc.extLo z k := by intro h; cases h
          rw [List.count_cons_of_ne hne]; simp
      | extLo x1 j1 =>
        simp only [arcSrc] at hs; cases hs
        have hf : f x.1 j = false := by
          have hcap := hcirc.2.1 (.extLo x j) _ rfl
          cases hfv : f x.1 j
          · rfl
          · simp [hfv] at hcap; omega
        refine ⟨x, true, rest, le_refl _, by simp, hrest, ?_, fun _ => hf, ?_, ?_⟩
        · simp [arcGain]
        · intro z k
          have hne : SArc.extLo x j ≠ SArc.entHi z k := by intro h; cases h
          rw [List.count_cons_of_ne hne]
        · intro z k
          by_cases hzk : z = x ∧ k = j
          · rcases hzk with ⟨rfl, rfl⟩
            simp [List.count_cons_self, Nat.add_comm]
          · have hne : SArc.extLo x j ≠ SArc.extLo z k := by
              intro h; cases h; exact hzk ⟨rfl, rfl⟩
            rw [List.count_cons_of_ne hne, if_neg (by tauto)]; simp
      | srcB _ => simp [arcSrc] at hs
      | bSnk _ => simp [arcSrc] at hs
      | ret => simp [arcSrc] at hs
      | bb _ _ => simp [arcSrc] at hs
      | ent0 _ _ => simp [arcSrc] at hs
      | entHi _ _ => simp [arcSrc] at hs

private lemma extract_base_chain {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (φ : SArc n S m → Nat) (hcirc : IsCirc f w φ) :
    ∀ (M : List (SArc n S m)) (x0 xEnd : {x : Finset (Fin n) // x ∈ S}),
      IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) (.vB x0) (.vB xEnd) M →
      ∃ c : List (Finset (Fin n) × Finset (Fin n) × Fin m),
        c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
        (∀ e ∈ c, x0.1 ⊆ e.1 ∧ e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
          f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
        (M.map (arcGain d)).sum ≤ (c.length : Int) ∧
        (∀ (z : {x : Finset (Fin n) // x ∈ S}) (k : Fin m),
          (c.filter (fun e => decide (e.2.2 = k ∧ (e.1 = z.1 ∨ e.2.1 = z.1)))).length ≤
            (if f z.1 k = true then M.count (.entHi z k) else M.count (.extLo z k))) := by
  intro M
  induction hlen : M.length using Nat.strong_induction_on generalizing M with
  | ind L ih =>
    intro x0 xEnd hM
    cases M with
    | nil =>
      refine ⟨[], List.Pairwise.nil, fun e he => by simp at he, by simp, fun z k => by simp⟩
    | cons a rest =>
      cases hM with
      | cons _ ha hs hrest =>
        have hval : arcValid a = true := by
          cases hv : arcValid a
          · have := hcirc.1 a hv; omega
          · rfl
        cases a with
        | bb x1 y1 =>
          simp only [arcSrc] at hs; cases hs
          simp only [arcValid] at hval
          have hxy : x0.1 ⊆ y1.1 := (of_decide_eq_true hval).1
          rcases ih rest.length (by simp at hlen; omega) rest rfl y1 xEnd hrest with
            ⟨c, hpw, hmem, hgain, hcnt⟩
          refine ⟨c, hpw, fun e he => ?_, ?_, fun z k => ?_⟩
          · rcases hmem e he with ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨hxy.trans h1, h2, h3, h4, h5, h6⟩
          · simp only [List.map_cons, List.sum_cons, arcGain, zero_add]; exact hgain
          · have hrec := hcnt z k
            have hne1 : SArc.bb x0 y1 ≠ SArc.entHi z k := by intro h; cases h
            have hne2 : SArc.bb x0 y1 ≠ SArc.extLo z k := by intro h; cases h
            rw [List.count_cons_of_ne hne1, List.count_cons_of_ne hne2]
            exact hrec
        | ent0 x1 j1 =>
          simp only [arcSrc] at hs; cases hs
          rcases consume_tap f w d φ hcirc rest x0 xEnd j1 hrest with
            ⟨y, isLo, rest2, hxy, hlt2, hrest2, hgain2, _, hent2, hext2⟩
          rcases ih rest2.length (by simp at hlen; omega) rest2 rfl y xEnd hrest2 with
            ⟨c, hpw, hmem, hgain, hcnt⟩
          refine ⟨c, hpw, fun e he => ?_, ?_, fun z k => ?_⟩
          · rcases hmem e he with ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨hxy.trans h1, h2, h3, h4, h5, h6⟩
          · simp only [List.map_cons, List.sum_cons, arcGain, zero_add, hgain2]
            cases isLo <;> simp <;> omega
          · have hrec := hcnt z k
            have hne1 : SArc.ent0 x0 j1 ≠ SArc.entHi z k := by intro h; cases h
            have hne2 : SArc.ent0 x0 j1 ≠ SArc.extLo z k := by intro h; cases h
            rw [List.count_cons_of_ne hne1, List.count_cons_of_ne hne2, hent2 z k, hext2 z k]
            by_cases hfz : f z.1 k = true
            · rw [if_pos hfz] at hrec ⊢; omega
            · rw [if_neg hfz] at hrec ⊢; omega
        | entHi x1 j1 =>
          simp only [arcSrc] at hs; cases hs
          have hf1 : f x0.1 j1 = true := by
            have hcap := hcirc.2.1 (.entHi x0 j1) _ rfl
            cases hfv : f x0.1 j1
            · simp [hfv] at hcap; omega
            · rfl
          rcases consume_tap f w d φ hcirc rest x0 xEnd j1 hrest with
            ⟨y, isLo, rest2, hxy, hlt2, hrest2, hgain2, hlo, hent2, hext2⟩
          rcases ih rest2.length (by simp at hlen; omega) rest2 rfl y xEnd hrest2 with
            ⟨c, hpw, hmem, hgain, hcnt⟩
          cases hisLo : isLo
          · refine ⟨c, hpw, fun e he => ?_, ?_, fun z k => ?_⟩
            · rcases hmem e he with ⟨h1, h2, h3, h4, h5, h6⟩
              exact ⟨hxy.trans h1, h2, h3, h4, h5, h6⟩
            · simp only [List.map_cons, List.sum_cons, arcGain, hgain2, hisLo, Bool.false_eq_true, ↓reduceIte]
              omega
            · have hrec := hcnt z k
              have hne2 : SArc.entHi x0 j1 ≠ SArc.extLo z k := by intro h; cases h
              rw [List.count_cons_of_ne hne2, hext2 z k]
              by_cases hfz : f z.1 k = true
              · rw [if_pos hfz] at hrec ⊢
                rw [List.count_cons, hent2 z k]
                omega
              · rw [if_neg hfz] at hrec ⊢; omega
          · have hfy : f y.1 j1 = false := hlo hisLo
            refine ⟨(x0.1, y.1, j1) :: c, ?_, ?_, ?_, fun z k => ?_⟩
            · refine List.pairwise_cons.mpr ⟨fun e he => (hmem e he).1, hpw⟩
            · intro e he
              rcases List.mem_cons.mp he with rfl | he'
              · exact ⟨le_refl _, x0.2, y.2, hxy, hf1, hfy⟩
              · rcases hmem e he' with ⟨h1, h2, h3, h4, h5, h6⟩
                exact ⟨hxy.trans h1, h2, h3, h4, h5, h6⟩
            · simp only [List.map_cons, List.sum_cons, arcGain, hgain2, hisLo, ↓reduceIte, zero_add,
                List.length_cons, Nat.cast_add, Nat.cast_one]
              omega
            · have hrec := hcnt z k
              have hne2 : SArc.entHi x0 j1 ≠ SArc.extLo z k := by intro h; cases h
              simp only [List.filter_cons]
              by_cases hfz : f z.1 k = true
              · rw [if_pos hfz] at hrec ⊢
                rw [List.count_cons, hent2 z k]
                by_cases hmatch : j1 = k ∧ (x0.1 = z.1 ∨ y.1 = z.1)
                · rw [decide_eq_true hmatch, if_pos rfl, List.length_cons]
                  rcases hmatch with ⟨rfl, hx | hy⟩
                  · have hzx : z = x0 := Subtype.ext hx.symm
                    subst hzx
                    simp [Nat.add_comm]; omega
                  · rw [← hy] at hfz; rw [hfy] at hfz; exact Bool.noConfusion hfz
                · rw [decide_eq_false hmatch]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · rw [if_neg hfz] at hrec ⊢
                rw [List.count_cons_of_ne hne2, hext2 z k]
                by_cases hmatch : j1 = k ∧ (x0.1 = z.1 ∨ y.1 = z.1)
                · rw [decide_eq_true hmatch, if_pos rfl, List.length_cons]
                  rcases hmatch with ⟨rfl, hx | hy⟩
                  · rw [← hx] at hfz; exact False.elim (hfz hf1)
                  · have hzy : z = y := Subtype.ext hy.symm
                    subst hzy
                    rw [if_pos ⟨hisLo, rfl, rfl⟩]; omega
                · rw [decide_eq_false hmatch]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
        | bSnk _ =>
          have hno_snk : ∀ {v1 : SVert n S m} (q : List (SArc n S m)),
              IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) .snk v1 q → v1 = .snk := by
            intro v1 q hq
            cases hq with
            | nil => rfl
            | cons a2 ha2 hs2 _ =>
              cases a2 with
              | ret => exact False.elim (ha2.2 rfl)
              | _ => simp [arcSrc] at hs2
          have hsnk := hno_snk rest hrest
          cases hsnk
        | srcB _ => simp [arcSrc] at hs
        | ret => simp [arcSrc] at hs
        | tt _ _ _ => simp [arcSrc] at hs
        | extM1 _ _ => simp [arcSrc] at hs
        | extLo _ _ => simp [arcSrc] at hs

private lemma cycle_no_ret_gain_le_zero {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (φ : SArc n S m → Nat) (hcirc : IsCirc f w φ)
    {u : SVert n S m} {C : List (SArc n S m)}
    (hC : IsGenWalk arcSrc arcDst (fun a => 0 < φ a) u u C) (hnoret : SArc.ret ∉ C) :
    (C.map (arcGain d)).sum ≤ 0 := by
  have hno_srcB : ∀ x, SArc.srcB x ∉ C := by
    intro x hmem
    have hbal := isGenWalk_closed_balance hC .src
    have hpos : 0 < (C.filter (fun a => decide (arcSrc a = .src))).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, decide_eq_true rfl⟩)
    rw [hbal] at hpos
    rcases List.length_pos_iff_exists_mem.mp hpos with ⟨a, ha⟩
    rcases List.mem_filter.mp ha with ⟨haC, hdst⟩
    have hdst' := of_decide_eq_true hdst
    cases a with
    | ret => exact hnoret haC
    | _ => simp [arcDst] at hdst'
  have hno_bSnk : ∀ x, SArc.bSnk x ∉ C := by
    intro x hmem
    have hbal := isGenWalk_closed_balance hC .snk
    have hpos : 0 < (C.filter (fun a => decide (arcDst a = .snk))).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, decide_eq_true rfl⟩)
    rw [← hbal] at hpos
    rcases List.length_pos_iff_exists_mem.mp hpos with ⟨a, ha⟩
    rcases List.mem_filter.mp ha with ⟨haC, hsrc⟩
    have hsrc' := of_decide_eq_true hsrc
    cases a with
    | ret => exact hnoret haC
    | _ => simp [arcSrc] at hsrc'
  let ψ1 : SVert n S m → Int := fun v => match v with
    | .vB x => (x.1.card : Int)
    | .vT x _ => (x.1.card : Int)
    | _ => 0
  have hstrict_le : ∀ a ∈ C, (match a with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0) ≤
      ψ1 (arcDst a) - ψ1 (arcSrc a) := by
    intro a haC
    have hposa := isGenWalk_mem hC a haC
    have hval : arcValid a = true := by
      cases hv : arcValid a
      · have := hcirc.1 a hv; omega
      · rfl
    cases a with
    | srcB x => exact False.elim (hno_srcB x haC)
    | bSnk x => exact False.elim (hno_bSnk x haC)
    | ret => exact False.elim (hnoret haC)
    | bb x y =>
      simp only [arcValid] at hval
      rcases of_decide_eq_true hval with ⟨hsub, hne⟩
      have hlt : x.1.card < y.1.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      simp only [arcDst, arcSrc, ψ1]; omega
    | tt x y j =>
      simp only [arcValid] at hval
      rcases of_decide_eq_true hval with ⟨hsub, hne⟩
      have hlt : x.1.card < y.1.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      simp only [arcDst, arcSrc, ψ1]; omega
    | ent0 x j => simp [arcDst, arcSrc, ψ1]
    | extM1 x j => simp [arcDst, arcSrc, ψ1]
    | entHi x j => simp [arcDst, arcSrc, ψ1]
    | extLo x j => simp [arcDst, arcSrc, ψ1]
  have htel1 := isGenWalk_telescope (fun a => match a with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0)
    ψ1 C hC hstrict_le
  have hno_strict : ∀ a ∈ C, (match a with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0) = 0 := by
    have hsum_nn : ∀ L : List Int, (∀ z ∈ L, 0 ≤ z) → 0 ≤ L.sum := by
      intro L
      induction L with
      | nil => intro _; simp
      | cons z r ihr =>
        intro h
        have h1 := h z List.mem_cons_self
        have h2 := ihr (fun y hy => h y (List.mem_cons_of_mem z hy))
        simp only [List.sum_cons]; omega
    have hnonneg : ∀ L : List (SArc n S m), (∀ a ∈ L, (0 : Int) ≤ match a with | .bb _ _ => 1 | .tt _ _ _ => 1 | _ => 0) →
        (L.map (fun a => match a with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0)).sum ≤ 0 →
        ∀ a ∈ L, (match a with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0) = 0 := by
      intro L
      induction L with
      | nil => intro _ _ a ha; simp at ha
      | cons b rest ih =>
        intro hnn hsum a ha
        simp only [List.map_cons, List.sum_cons] at hsum
        have hb0 : 0 ≤ (match b with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0) :=
          hnn b List.mem_cons_self
        have hrest_nn : 0 ≤ (rest.map (fun a => match a with | .bb _ _ => (1 : Int) | .tt _ _ _ => 1 | _ => 0)).sum :=
          hsum_nn _ (fun z hz => by
            rcases List.mem_map.mp hz with ⟨a', ha', rfl⟩
            exact hnn a' (List.mem_cons_of_mem b ha'))
        rcases List.mem_cons.mp ha with rfl | ha'
        · omega
        · exact ih (fun z hz => hnn z (List.mem_cons_of_mem b hz)) (by omega) a ha'
    exact hnonneg C (fun a _ => by cases a <;> simp) (by omega)
  let ψ2 : SVert n S m → Int := fun v => match v with
    | .vT x j => if f x.1 j = true then 1 else 0
    | _ => 0
  have htel2 := isGenWalk_telescope (arcGain d) ψ2 C hC (fun a haC => by
    have hposa := isGenWalk_mem hC a haC
    cases a with
    | srcB x => exact False.elim (hno_srcB x haC)
    | bSnk x => exact False.elim (hno_bSnk x haC)
    | ret => exact False.elim (hnoret haC)
    | bb x y => have := hno_strict (.bb x y) haC; simp at this
    | tt x y j => have := hno_strict (.tt x y j) haC; simp at this
    | ent0 x j =>
      simp only [arcGain, arcDst, arcSrc, ψ2]; split <;> omega
    | extM1 x j =>
      simp only [arcGain, arcDst, arcSrc, ψ2]; split <;> omega
    | entHi x j =>
      have hcap := hcirc.2.1 (.entHi x j) _ rfl
      have hft : f x.1 j = true := by
        cases hfv : f x.1 j
        · simp [hfv] at hcap; omega
        · rfl
      simp [arcGain, arcDst, arcSrc, ψ2, hft]
    | extLo x j =>
      have hcap := hcirc.2.1 (.extLo x j) _ rfl
      have hff : f x.1 j = false := by
        cases hfv : f x.1 j
        · rfl
        · simp [hfv] at hcap; omega
      simp [arcGain, arcDst, arcSrc, ψ2, hff])
  omega

private lemma cycle_with_ret_extract {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (φ : SArc n S m → Nat) (hcirc : IsCirc f w φ)
    {u : SVert n S m} {C : List (SArc n S m)}
    (hC : IsGenWalk arcSrc arcDst (fun a => 0 < φ a) u u C)
    (hnd : (C.map arcSrc).Nodup) (hret : SArc.ret ∈ C) :
    ∃ c : List (Finset (Fin n) × Finset (Fin n) × Fin m),
      c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
      (∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
        f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
      (C.map (arcGain d)).sum ≤ (c.length : Int) - (d : Int) ∧
      (∀ (z : {x : Finset (Fin n) // x ∈ S}) (k : Fin m),
        (c.filter (fun e => decide (e.2.2 = k ∧ (e.1 = z.1 ∨ e.2.1 = z.1)))).length ≤
          (if f z.1 k = true then (if SArc.entHi z k ∈ C then 1 else 0)
           else (if SArc.extLo z k ∈ C then 1 else 0))) := by
  rcases mem_iff_rotate_head hC .ret hret with ⟨W, hW, hperm⟩
  have hndW : ((SArc.ret :: W).map arcSrc).Nodup := (hperm.map arcSrc).nodup_iff.mpr hnd
  have hC_nd : C.Nodup := List.Nodup.of_map arcSrc hnd
  cases hW with
  | cons _ _ _ hW_body =>
    have hnoret_W : SArc.ret ∉ W := by
      intro hmem
      simp only [List.map_cons, List.nodup_cons] at hndW
      exact hndW.1 (List.mem_map.mpr ⟨.ret, hmem, rfl⟩)
    have hW_body' : IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) .src .snk W := by
      have hlift : ∀ {u1 v1 : SVert n S m} (p : List (SArc n S m)),
          IsGenWalk arcSrc arcDst (fun a => 0 < φ a) u1 v1 p → SArc.ret ∉ p →
          IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) u1 v1 p := by
        intro u1 v1 p hp hn
        induction hp with
        | nil _ => exact IsGenWalk.nil _
        | cons a ha hs _ ih =>
          exact IsGenWalk.cons a ⟨ha, fun heq => hn (heq ▸ List.mem_cons_self)⟩ hs
            (ih (fun hm => hn (List.mem_cons_of_mem a hm)))
      exact hlift W hW_body hnoret_W
    cases hW_body' with
    | @cons _ _ a0 rest0 ha0 hs0 hrest0 =>
      cases a0 with
      | srcB x0 =>
        have hne_rest0 : rest0 ≠ [] := by
          intro heq; rw [heq] at hrest0; cases hrest0
        rcases list_snoc_of_ne_nil hne_rest0 with ⟨M, aLast, hrest0_eq⟩
        rw [hrest0_eq] at hrest0
        have hsnoc : ∀ {u1 v1 : SVert n S m} (q : List (SArc n S m)) (e : SArc n S m),
            IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) u1 v1 (q ++ [e]) →
            (0 < φ e ∧ e ≠ .ret) ∧ arcDst e = v1 ∧
              IsGenWalk arcSrc arcDst (fun a => 0 < φ a ∧ a ≠ .ret) u1 (arcSrc e) q := by
          intro u1 v1 q
          induction q generalizing u1 with
          | nil =>
            intro e h; cases h with
            | cons _ he hs hr => cases hr; exact ⟨he, rfl, by rw [← hs]; exact IsGenWalk.nil _⟩
          | cons e0 r ihq =>
            intro e h; cases h with
            | cons _ he0 hs0 hr =>
              rcases ihq e hr with ⟨he, hd, hpre⟩
              exact ⟨he, hd, IsGenWalk.cons e0 he0 hs0 hpre⟩
        rcases hsnoc M aLast hrest0 with ⟨haLast, hdstLast, hM⟩
        cases aLast with
        | bSnk xEnd =>
          rcases extract_base_chain f w d φ hcirc M x0 xEnd hM with ⟨c, hpw, hmem, hgain, hcnt⟩
          refine ⟨c, hpw, fun e he => (hmem e he).2, ?_, fun z k => ?_⟩
          · have hsum_perm : (C.map (arcGain d)).sum = ((SArc.ret :: SArc.srcB x0 :: (M ++ [SArc.bSnk xEnd])).map (arcGain d)).sum := by
              have h1 := hperm.symm.map (arcGain d)
              rw [hrest0_eq] at h1
              exact h1.sum_eq
            rw [hsum_perm]
            simp only [List.map_cons, List.map_append, List.map_nil, List.sum_cons, List.sum_append,
              List.sum_nil, arcGain]
            omega
          · have hsub_cnt : ∀ a : SArc n S m, M.count a ≤ if a ∈ C then 1 else 0 := by
              intro a
              have hle1 : M.count a ≤ (SArc.ret :: SArc.srcB x0 :: (M ++ [SArc.bSnk xEnd])).count a := by
                simp only [List.count_cons, List.count_append]; omega
              have hpc : (SArc.ret :: SArc.srcB x0 :: (M ++ [SArc.bSnk xEnd])).count a = C.count a := by
                have hp2 : (SArc.ret :: SArc.srcB x0 :: (M ++ [SArc.bSnk xEnd])).Perm C := by
                  rw [← hrest0_eq]; exact hperm
                exact hp2.count_eq a
              have hnd_cnt : C.count a ≤ if a ∈ C then 1 else 0 := by
                rw [List.Nodup.count hC_nd]
              omega
            have hrec := hcnt z k
            by_cases hfz : f z.1 k = true
            · rw [if_pos hfz] at hrec ⊢
              exact hrec.trans (hsub_cnt (.entHi z k))
            · rw [if_neg hfz] at hrec ⊢
              exact hrec.trans (hsub_cnt (.extLo z k))
        | _ => simp [arcDst] at hdstLast
      | _ => simp [arcSrc] at hs0

private lemma cycle_decomp_cert {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat) :
    ∀ (φ : SArc n S m → Nat), IsCirc f w φ →
      ∃ P : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)),
        (∀ c ∈ P, d < c.length) ∧
        (∀ c ∈ P, c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
          ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
            f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
        (∀ (z : {x : Finset (Fin n) // x ∈ S}) (k : Fin m),
          (P.flatten.filter (fun e => decide (e.2.2 = k ∧ (e.1 = z.1 ∨ e.2.1 = z.1)))).length ≤
            (if f z.1 k = true then φ (.entHi z k) else φ (.extLo z k))) ∧
        circGain d φ ≤ (P.flatten.length : Int) - (d : Int) * (P.length : Int) := by
  intro φ
  induction htf : totalFlow φ using Nat.strong_induction_on generalizing φ with
  | ind T ih =>
    intro hcirc
    by_cases hT0 : T = 0
    · have hφ0 : ∀ a, φ a = 0 := fun a => by
        have hle : φ a ≤ totalFlow φ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        omega
      refine ⟨[], fun c hc => by simp at hc, fun c hc => by simp at hc, fun z k => by simp, ?_⟩
      have hg0 : circGain d φ = 0 := Finset.sum_eq_zero fun a _ => by rw [hφ0 a]; simp
      simp [hg0]
    · rcases exists_simple_pos_cycle f w φ hcirc (by omega) with ⟨u, C, hC, hClen, hCnd⟩
      have hC_nodup : C.Nodup := List.Nodup.of_map arcSrc hCnd
      have hC_pos : ∀ a ∈ C, 0 < φ a := isGenWalk_mem hC
      let indC : SArc n S m → Nat := fun a => if a ∈ C then 1 else 0
      have hind_eq_cnt : ∀ a, indC a = C.count a := fun a => by
        dsimp only [indC]
        rw [List.Nodup.count hC_nodup]
      let φ' : SArc n S m → Nat := fun a => φ a - indC a
      have hφ_split : ∀ a, φ a = φ' a + indC a := fun a => by
        dsimp only [φ', indC]
        by_cases hm : a ∈ C
        · rw [if_pos hm]; have := hC_pos a hm; omega
        · rw [if_neg hm]; omega
      have hcirc' : IsCirc f w φ' := by
        refine ⟨fun a hv => by have := hcirc.1 a hv; dsimp only [φ']; omega,
          fun a cap hc => by have := hcirc.2.1 a cap hc; dsimp only [φ']; omega, fun v => ?_⟩
        have hout_split : outFlow φ v = outFlow φ' v + outFlow indC v := by
          dsimp only [outFlow]; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          split
          · exact hφ_split a
          · rfl
        have hin_split : inFlow φ v = inFlow φ' v + inFlow indC v := by
          dsimp only [inFlow]; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          split
          · exact hφ_split a
          · rfl
        have hind_bal : outFlow indC v = inFlow indC v := by
          have ho : outFlow indC v = (C.filter (fun a => decide (arcSrc a = v))).length := by
            rw [← sum_count_filter]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← hind_eq_cnt a]; by_cases h : arcSrc a = v <;> simp [h]
          have hi : inFlow indC v = (C.filter (fun a => decide (arcDst a = v))).length := by
            rw [← sum_count_filter]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← hind_eq_cnt a]; by_cases h : arcDst a = v <;> simp [h]
          rw [ho, hi]
          exact isGenWalk_closed_balance hC v
        have hbal := hcirc.2.2 v
        omega
      have htf_split : totalFlow φ = totalFlow φ' + C.length := by
        have h1 : totalFlow φ = totalFlow φ' + totalFlow indC := by
          dsimp only [totalFlow]; rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun a _ => hφ_split a
        have h2 : totalFlow indC = C.length := by
          have := sum_count_filter (fun _ : SArc n S m => true) C
          simp only [↓reduceIte, List.filter_true] at this
          rw [← this]
          exact Finset.sum_congr rfl fun a _ => hind_eq_cnt a
        omega
      have hgain_split : circGain d φ = circGain d φ' + (C.map (arcGain d)).sum := by
        have h1 : circGain d φ = circGain d φ' + (Finset.univ : Finset (SArc n S m)).sum (fun a => (indC a : Int) * arcGain d a) := by
          dsimp only [circGain]; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          have := hφ_split a
          push_cast [this]; ring
        rw [h1, ← sum_count_int (arcGain d) C]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by rw [hind_eq_cnt a]
      rcases ih (totalFlow φ') (by omega) φ' rfl hcirc' with ⟨P', hP'len, hP'ch, hP'cnt, hP'gain⟩
      by_cases hret : SArc.ret ∈ C
      · rcases cycle_with_ret_extract f w d φ hcirc hC hCnd hret with ⟨c, hcpw, hcmem, hcgain, hccnt⟩
        by_cases hclen : d < c.length
        · refine ⟨c :: P', ?_, ?_, fun z k => ?_, ?_⟩
          · intro c' hc'; rcases List.mem_cons.mp hc' with rfl | hc''; exact hclen; exact hP'len c' hc''
          · intro c' hc'; rcases List.mem_cons.mp hc' with rfl | hc''; exact ⟨hcpw, hcmem⟩; exact hP'ch c' hc''
          · simp only [List.flatten_cons, List.filter_append, List.length_append]
            have h1 := hccnt z k
            have h2 := hP'cnt z k
            have hsp1 := hφ_split (.entHi z k)
            have hsp2 := hφ_split (.extLo z k)
            dsimp only [indC] at hsp1 hsp2
            by_cases hfz : f z.1 k = true
            · rw [if_pos hfz] at h1 h2 ⊢; omega
            · rw [if_neg hfz] at h1 h2 ⊢; omega
          · simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
            rw [mul_add, mul_one]
            omega
        · refine ⟨P', hP'len, hP'ch, fun z k => ?_, ?_⟩
          · have h2 := hP'cnt z k
            have hsp1 := hφ_split (.entHi z k)
            have hsp2 := hφ_split (.extLo z k)
            by_cases hfz : f z.1 k = true
            · rw [if_pos hfz] at h2 ⊢; omega
            · rw [if_neg hfz] at h2 ⊢; omega
          · omega
      · have hle0 := cycle_no_ret_gain_le_zero f w d φ hcirc hC hret
        refine ⟨P', hP'len, hP'ch, fun z k => ?_, ?_⟩
        · have h2 := hP'cnt z k
          have hsp1 := hφ_split (.entHi z k)
          have hsp2 := hφ_split (.extLo z k)
          by_cases hfz : f z.1 k = true
          · rw [if_pos hfz] at h2 ⊢; omega
          · rw [if_neg hfz] at h2 ⊢; omega
        · omega

private def LegalStrict {n m : Nat} (S : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (P : List (List (Finset (Fin n) × Finset (Fin n) × Fin m))) : Prop :=
  (∀ c ∈ P, d < c.length) ∧
  (∀ c ∈ P, c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
    ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
      f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
  (∀ x ∈ S, ∀ j : Fin m, (P.flatten.filter (fun e =>
    decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length ≤ w x j)

private def chainArcsAux {n m : Nat} {S : Finset (Finset (Fin n))}
    (cur : {x : Finset (Fin n) // x ∈ S}) :
    (c : List (Finset (Fin n) × Finset (Fin n) × Fin m)) →
    (∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S) → List (SArc n S m)
  | [], _ => [.bSnk cur, .ret]
  | e :: rest, hc =>
    let x : {x // x ∈ S} := ⟨e.1, (hc e List.mem_cons_self).1⟩
    let y : {x // x ∈ S} := ⟨e.2.1, (hc e List.mem_cons_self).2⟩
    (if cur = x then [] else [.bb cur x]) ++
      [.entHi x e.2.2, .tt x y e.2.2, .extLo y e.2.2] ++
      chainArcsAux y rest (fun e' he' => hc e' (List.mem_cons_of_mem e he'))

private lemma chainArcsAux_spec {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (d : Nat) :
    ∀ (c : List (Finset (Fin n) × Finset (Fin n) × Fin m))
      (cur : {x : Finset (Fin n) // x ∈ S})
      (hc : ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S)
      (hcur : ∀ e ∈ c, cur.1 ⊆ e.1)
      (hpw : c.Pairwise (fun e e' => e.2.1 ⊆ e'.1))
      (hval : ∀ e ∈ c, e.1 ⊆ e.2.1 ∧ f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false),
      let L := chainArcsAux cur c hc
      IsGenWalk arcSrc arcDst (fun a => arcValid a = true) (.vB cur) .src L ∧
      (L.map (arcGain d)).sum = (c.length : Int) - (d : Int) ∧
      (∀ z k, L.count (.entHi z k) = (c.filter (fun e => decide (e.1 = z.1 ∧ e.2.2 = k))).length) ∧
      (∀ z k, L.count (.extLo z k) = (c.filter (fun e => decide (e.2.1 = z.1 ∧ e.2.2 = k))).length) := by
  intro c
  induction c with
  | nil =>
    intro cur hc _ _ _
    dsimp only [chainArcsAux]
    refine ⟨IsGenWalk.cons (SArc.bSnk cur) rfl rfl (IsGenWalk.cons SArc.ret rfl rfl (IsGenWalk.nil SVert.src)),
      by simp [arcGain], fun z k => ?_, fun z k => ?_⟩
    · simp only [List.count_cons, List.count_nil, List.filter_nil, List.length_nil]
      have h1 : SArc.bSnk cur ≠ SArc.entHi z k := by intro h; cases h
      have h2 : SArc.ret ≠ SArc.entHi z k := by intro h; cases h
      simp [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2]
    · simp only [List.count_cons, List.count_nil, List.filter_nil, List.length_nil]
      have h1 : SArc.bSnk cur ≠ SArc.extLo z k := by intro h; cases h
      have h2 : SArc.ret ≠ SArc.extLo z k := by intro h; cases h
      simp [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2]
  | cons e rest ih =>
    intro cur hc hcur hpw hval
    rcases List.pairwise_cons.mp hpw with ⟨he_rest, hpw_rest⟩
    rcases hval e List.mem_cons_self with ⟨hsub_e, hft, hff⟩
    let x : {x // x ∈ S} := ⟨e.1, (hc e List.mem_cons_self).1⟩
    let y : {x // x ∈ S} := ⟨e.2.1, (hc e List.mem_cons_self).2⟩
    have hxy_ne : x.1 ≠ y.1 := fun heq => by
      change e.1 = e.2.1 at heq; rw [heq] at hft; rw [hff] at hft; exact Bool.noConfusion hft
    have hrec := ih y (fun e' he' => hc e' (List.mem_cons_of_mem e he'))
      (fun e' he' => he_rest e' he') hpw_rest (fun e' he' => hval e' (List.mem_cons_of_mem e he'))
    rcases hrec with ⟨hw_rec, hg_rec, hent_rec, hext_rec⟩
    dsimp only [x, y] at hg_rec hent_rec hext_rec
    dsimp only [chainArcsAux]
    have hw_pre : IsGenWalk (@arcSrc n m S) (@arcDst n m S) (fun a => arcValid a = true) (.vB cur) (.vB x)
        (if cur = x then [] else [SArc.bb cur x]) := by
      by_cases hcx : cur = x
      · rw [if_pos hcx, hcx]; exact IsGenWalk.nil _
      · rw [if_neg hcx]
        have hsub_cx : cur.1 ⊆ x.1 := hcur e List.mem_cons_self
        have hne_cx : cur.1 ≠ x.1 := fun h => hcx (Subtype.ext h)
        exact IsGenWalk.cons (SArc.bb cur x) (decide_eq_true (show cur.1 ⊆ x.1 ∧ cur.1 ≠ x.1 from ⟨hsub_cx, hne_cx⟩)) rfl (IsGenWalk.nil _)
    have hw_mid : IsGenWalk (@arcSrc n m S) (@arcDst n m S) (fun a => arcValid a = true) (.vB x) (.vB y)
        [SArc.entHi x e.2.2, SArc.tt x y e.2.2, SArc.extLo y e.2.2] :=
      IsGenWalk.cons (SArc.entHi x e.2.2) rfl rfl
        (IsGenWalk.cons (SArc.tt x y e.2.2) (decide_eq_true (show x.1 ⊆ y.1 ∧ x.1 ≠ y.1 from ⟨hsub_e, hxy_ne⟩)) rfl
          (IsGenWalk.cons (SArc.extLo y e.2.2) rfl rfl (IsGenWalk.nil _)))
    refine ⟨isGenWalk_append (isGenWalk_append hw_pre hw_mid) hw_rec, ?_, fun z k => ?_, fun z k => ?_⟩
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        arcGain, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hg_rec]
      by_cases hcx : cur = x
      · rw [if_pos hcx]; simp; omega
      · rw [if_neg hcx]; simp [arcGain]; omega
    · simp only [List.count_append, List.filter_cons]
      rw [hent_rec z k]
      have hpre0 : (if cur = x then ([] : List (SArc n S m)) else [.bb cur x]).count (.entHi z k) = 0 := by
        split
        · rfl
        · have hne : SArc.bb cur x ≠ SArc.entHi z k := by intro h; cases h
          simp [List.count_cons_of_ne hne]
      have hmid : ([SArc.entHi x e.2.2, .tt x y e.2.2, .extLo y e.2.2]).count (.entHi z k) =
          if e.1 = z.1 ∧ e.2.2 = k then 1 else 0 := by
        have hne1 : SArc.tt x y e.2.2 ≠ SArc.entHi z k := by intro h; cases h
        have hne2 : SArc.extLo y e.2.2 ≠ SArc.entHi z k := by intro h; cases h
        simp only [List.count_cons, List.count_nil, beq_eq_false_iff_ne.mpr hne1, beq_eq_false_iff_ne.mpr hne2]
        by_cases hzk : e.1 = z.1 ∧ e.2.2 = k
        · have hxz : x = z := Subtype.ext hzk.1
          rw [if_pos hzk, hxz, hzk.2]; simp
        · have hne0 : SArc.entHi x e.2.2 ≠ SArc.entHi z k := by
            intro h; cases h; exact hzk ⟨rfl, rfl⟩
          rw [if_neg hzk, beq_eq_false_iff_ne.mpr hne0]; simp
      rw [hpre0, hmid]
      by_cases hzk : e.1 = z.1 ∧ e.2.2 = k
      · rw [if_pos hzk, decide_eq_true hzk, if_pos rfl, List.length_cons]; omega
      · rw [if_neg hzk, decide_eq_false hzk]; simp
    · simp only [List.count_append, List.filter_cons]
      rw [hext_rec z k]
      have hpre0 : (if cur = x then ([] : List (SArc n S m)) else [.bb cur x]).count (.extLo z k) = 0 := by
        split
        · rfl
        · have hne : SArc.bb cur x ≠ SArc.extLo z k := by intro h; cases h
          simp [List.count_cons_of_ne hne]
      have hmid : ([SArc.entHi x e.2.2, .tt x y e.2.2, .extLo y e.2.2]).count (.extLo z k) =
          if e.2.1 = z.1 ∧ e.2.2 = k then 1 else 0 := by
        have hne1 : SArc.entHi x e.2.2 ≠ SArc.extLo z k := by intro h; cases h
        have hne2 : SArc.tt x y e.2.2 ≠ SArc.extLo z k := by intro h; cases h
        simp only [List.count_cons, List.count_nil, beq_eq_false_iff_ne.mpr hne1, beq_eq_false_iff_ne.mpr hne2]
        by_cases hzk : e.2.1 = z.1 ∧ e.2.2 = k
        · have hyz : y = z := Subtype.ext hzk.1
          rw [if_pos hzk, hyz, hzk.2]; simp
        · have hne0 : SArc.extLo y e.2.2 ≠ SArc.extLo z k := by
            intro h; cases h; exact hzk ⟨rfl, rfl⟩
          rw [if_neg hzk, beq_eq_false_iff_ne.mpr hne0]; simp
      rw [hpre0, hmid]
      by_cases hzk : e.2.1 = z.1 ∧ e.2.2 = k
      · rw [if_pos hzk, decide_eq_true hzk, if_pos rfl, List.length_cons]; omega
      · rw [if_neg hzk, decide_eq_false hzk]; simp

private lemma cert_to_circ {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (P : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)))
    (hP : LegalStrict S f w d P) :
    ∃ φ : SArc n S m → Nat,
      IsCirc f w φ ∧
      circGain d φ = (P.flatten.length : Int) - (d : Int) * (P.length : Int) ∧
      (∀ z k, φ (.entHi z k) = (P.flatten.filter (fun e => decide (e.1 = z.1 ∧ e.2.2 = k))).length) ∧
      (∀ z k, φ (.extLo z k) = (P.flatten.filter (fun e => decide (e.2.1 = z.1 ∧ e.2.2 = k))).length) := by
  have hex_raw : ∀ (Q : List (List (Finset (Fin n) × Finset (Fin n) × Fin m))),
      (∀ c ∈ Q, 0 < c.length) →
      (∀ c ∈ Q, c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
        ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
          f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) →
      ∃ φ : SArc n S m → Nat,
        (∀ a, arcValid a = false → φ a = 0) ∧
        (∀ v, outFlow φ v = inFlow φ v) ∧
        circGain d φ = (Q.flatten.length : Int) - (d : Int) * (Q.length : Int) ∧
        (∀ z k, φ (.entHi z k) = (Q.flatten.filter (fun e => decide (e.1 = z.1 ∧ e.2.2 = k))).length) ∧
        (∀ z k, φ (.extLo z k) = (Q.flatten.filter (fun e => decide (e.2.1 = z.1 ∧ e.2.2 = k))).length) := by
    intro Q
    induction Q with
    | nil =>
      intro _ _
      refine ⟨fun _ => 0, fun _ _ => rfl, fun v => by simp [outFlow, inFlow], by simp [circGain],
        fun _ _ => rfl, fun _ _ => rfl⟩
    | cons c rest ih =>
      intro hpos hch
      rcases ih (fun c' hc' => hpos c' (List.mem_cons_of_mem c hc'))
        (fun c' hc' => hch c' (List.mem_cons_of_mem c hc')) with ⟨φr, hvr, hbr, hgr, hentr, hextr⟩
      have hcpos := hpos c List.mem_cons_self
      rcases hch c List.mem_cons_self with ⟨hcpw, hcmem⟩
      cases c with
      | nil => simp at hcpos
      | cons e0 erest =>
        let x0 : {x // x ∈ S} := ⟨e0.1, (hcmem e0 List.mem_cons_self).1⟩
        let hc_sub : ∀ e ∈ e0 :: erest, e.1 ∈ S ∧ e.2.1 ∈ S := fun e he => ⟨(hcmem e he).1, (hcmem e he).2.1⟩
        have hcur : ∀ e ∈ e0 :: erest, x0.1 ⊆ e.1 := by
          intro e he
          rcases List.mem_cons.mp he with rfl | he'
          · exact le_refl _
          · exact (hcmem e0 List.mem_cons_self).2.2.1.trans ((List.pairwise_cons.mp hcpw).1 e he')
        let L := SArc.srcB x0 :: chainArcsAux x0 (e0 :: erest) hc_sub
        rcases chainArcsAux_spec f d (e0 :: erest) x0 hc_sub hcur hcpw
          (fun e he => (hcmem e he).2.2) with ⟨hw0, hg0, hent0, hext0⟩
        have hw : IsGenWalk arcSrc arcDst (fun a => arcValid a = true) .src .src L :=
          IsGenWalk.cons (SArc.srcB x0) rfl rfl hw0
        let φ : SArc n S m → Nat := fun a => L.count a + φr a
        refine ⟨φ, fun a hva => ?_, fun v => ?_, ?_, fun z k => ?_, fun z k => ?_⟩
        · have hnot : a ∉ L := fun hm => by
            have := isGenWalk_mem hw a hm; rw [hva] at this; exact Bool.noConfusion this
          dsimp only [φ]; rw [List.count_eq_zero.mpr hnot, hvr a hva]
        · have hout : outFlow φ v = (L.filter (fun a => decide (arcSrc a = v))).length + outFlow φr v := by
            dsimp only [outFlow, φ]
            rw [← sum_count_filter, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases h : arcSrc a = v <;> simp [h]
          have hin : inFlow φ v = (L.filter (fun a => decide (arcDst a = v))).length + inFlow φr v := by
            dsimp only [inFlow, φ]
            rw [← sum_count_filter, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases h : arcDst a = v <;> simp [h]
          rw [hout, hin, isGenWalk_closed_balance hw v, hbr v]
        · have hgs : circGain d φ = (L.map (arcGain d)).sum + circGain d φr := by
            dsimp only [circGain, φ]
            rw [← sum_count_int (arcGain d) L, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            push_cast; ring
          rw [hgs, hgr]
          simp only [L, List.map_cons, List.sum_cons, arcGain, zero_add, hg0,
            List.flatten_cons, List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
        · dsimp only [φ, L]
          have hne : SArc.srcB x0 ≠ SArc.entHi z k := by intro h; cases h
          rw [List.count_cons_of_ne hne, hent0 z k, hentr z k]
          simp only [List.flatten_cons, List.filter_append, List.length_append]
        · dsimp only [φ, L]
          have hne : SArc.srcB x0 ≠ SArc.extLo z k := by intro h; cases h
          rw [List.count_cons_of_ne hne, hext0 z k, hextr z k]
          simp only [List.flatten_cons, List.filter_append, List.length_append]
  rcases hex_raw P (fun c hc => by have := hP.1 c hc; omega) hP.2.1 with ⟨φ, hv, hb, hg, hent, hext⟩
  refine ⟨φ, ⟨hv, fun a cap hcap => ?_, hb⟩, hg, hent, hext⟩
  have hfilter_le : ∀ {α : Type} (L : List α) (p q : α → Bool),
      (∀ e, p e = true → q e = true) → (L.filter p).length ≤ (L.filter q).length := by
    intro α L p q himp
    induction L with
    | nil => simp
    | cons e r ihr =>
      simp only [List.filter_cons]
      cases hp : p e
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases q e <;> simp <;> omega
      · rw [himp e hp]; simp; omega
  cases a with
  | entHi z k =>
    simp only [arcCap, Option.some.injEq] at hcap; subst hcap
    rw [hent z k]
    by_cases hfz : f z.1 k = true
    · rw [if_pos hfz]
      have hle : (P.flatten.filter (fun e => decide (e.1 = z.1 ∧ e.2.2 = k))).length ≤
          (P.flatten.filter (fun e => decide (e.2.2 = k ∧ (e.1 = z.1 ∨ e.2.1 = z.1)))).length :=
        hfilter_le P.flatten _ _ fun e he => by
          rcases of_decide_eq_true he with ⟨h1, h2⟩
          exact decide_eq_true ⟨h2, Or.inl h1⟩
      exact hle.trans (hP.2.2 z.1 z.2 k)
    · rw [if_neg hfz]
      have h0 : P.flatten.filter (fun e => decide (e.1 = z.1 ∧ e.2.2 = k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        cases hdec : decide (e.1 = z.1 ∧ e.2.2 = k)
        · simp
        · exfalso
          rcases of_decide_eq_true hdec with ⟨h1, h2⟩
          rcases List.mem_flatten.mp he with ⟨c, hc, hec⟩
          have hft := (hP.2.1 c hc).2 e hec
          rw [h1, h2] at hft
          exact hfz hft.2.2.2.1
      rw [h0]; simp
  | extLo z k =>
    simp only [arcCap, Option.some.injEq] at hcap; subst hcap
    rw [hext z k]
    by_cases hfz : f z.1 k = false
    · rw [if_pos hfz]
      have hle : (P.flatten.filter (fun e => decide (e.2.1 = z.1 ∧ e.2.2 = k))).length ≤
          (P.flatten.filter (fun e => decide (e.2.2 = k ∧ (e.1 = z.1 ∨ e.2.1 = z.1)))).length :=
        hfilter_le P.flatten _ _ fun e he => by
          rcases of_decide_eq_true he with ⟨h1, h2⟩
          exact decide_eq_true ⟨h2, Or.inr h1⟩
      exact hle.trans (hP.2.2 z.1 z.2 k)
    · rw [if_neg hfz]
      have h0 : P.flatten.filter (fun e => decide (e.2.1 = z.1 ∧ e.2.2 = k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        cases hdec : decide (e.2.1 = z.1 ∧ e.2.2 = k)
        · simp
        · exfalso
          rcases of_decide_eq_true hdec with ⟨h1, h2⟩
          rcases List.mem_flatten.mp he with ⟨c, hc, hec⟩
          have hff := (hP.2.1 c hc).2 e hec
          rw [h1, h2] at hff
          exact hfz hff.2.2.2.2
      rw [h0]; simp
  | _ => simp [arcCap] at hcap

private def resStepValid {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat)
    (φ : SArc n S m → Nat) : SArc n S m × Bool → Bool
  | (a, true) => arcValid a && match arcCap f w a with | none => true | some c => decide (φ a < c)
  | (a, false) => arcValid a && decide (0 < φ a)

private def resStepSrc {n m : Nat} {S : Finset (Finset (Fin n))} : SArc n S m × Bool → SVert n S m
  | (a, true) => arcSrc a
  | (a, false) => arcDst a

private def resStepDst {n m : Nat} {S : Finset (Finset (Fin n))} : SArc n S m × Bool → SVert n S m
  | (a, true) => arcDst a
  | (a, false) => arcSrc a

private def resStepGain {n m : Nat} {S : Finset (Finset (Fin n))} (d : Nat) : SArc n S m × Bool → Int
  | (a, true) => arcGain d a
  | (a, false) => -(arcGain d a)

private noncomputable def resEdges {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (φ : SArc n S m → Nat) : List (SVert n S m × SVert n S m × Int) :=
  ((Finset.univ : Finset (SArc n S m × Bool)).toList.filter (resStepValid f w φ)).map
    (fun s => (resStepSrc s, resStepDst s, resStepGain d s))

private lemma mem_resEdges_iff {n m : Nat} {S : Finset (Finset (Fin n))}
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (φ : SArc n S m → Nat) (e : SVert n S m × SVert n S m × Int) :
    e ∈ resEdges f w d φ ↔
      ∃ s : SArc n S m × Bool, resStepValid f w φ s = true ∧
        (resStepSrc s, resStepDst s, resStepGain d s) = e := by
  unfold resEdges
  simp only [List.mem_map, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and]

private lemma exists_max_cert {n m : Nat} (S : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat) :
    ∃ P : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)),
      LegalStrict S f w d P ∧
      ∀ P', LegalStrict S f w d P' →
        (P'.flatten.length : Int) - (d : Int) * (P'.length : Int) ≤
        (P.flatten.length : Int) - (d : Int) * (P.length : Int) := by
  let W : Nat := S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j => w x j))
  have hbound : ∀ P, LegalStrict S f w d P →
      d * P.length ≤ P.flatten.length ∧ P.flatten.length ≤ W := by
    intro P hP
    constructor
    · have hlen : ∀ Q : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)),
          (∀ c ∈ Q, d < c.length) → d * Q.length ≤ Q.flatten.length := by
        intro Q
        induction Q with
        | nil => intro _; simp
        | cons c r ih =>
          intro h
          have hc := h c List.mem_cons_self
          have hr := ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))
          simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
      exact hlen P hP.1
    · rcases cert_to_circ f w d P hP with ⟨φ, hcirc, _, hent, _⟩
      have hsum_ent_aux : ∀ (L : List (Finset (Fin n) × Finset (Fin n) × Fin m)),
          (∀ e ∈ L, e.1 ∈ S) →
          L.length = S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
            (L.filter (fun e => decide (e.1 = x ∧ e.2.2 = j))).length)) := by
        intro L
        induction L with
        | nil => intro _; simp
        | cons e r ih =>
          intro hmem
          have he1 : e.1 ∈ S := hmem e List.mem_cons_self
          have hrec := ih (fun e' he' => hmem e' (List.mem_cons_of_mem e he'))
          simp only [List.length_cons, hrec]
          have hstep : ∀ x, (Finset.univ : Finset (Fin m)).sum (fun j =>
              ((e :: r).filter (fun e' => decide (e'.1 = x ∧ e'.2.2 = j))).length) =
              (if e.1 = x then 1 else 0) + (Finset.univ : Finset (Fin m)).sum (fun j =>
                (r.filter (fun e' => decide (e'.1 = x ∧ e'.2.2 = j))).length) := by
            intro x
            have h1 : ∀ j : Fin m, ((e :: r).filter (fun e' => decide (e'.1 = x ∧ e'.2.2 = j))).length =
                (if e.1 = x ∧ e.2.2 = j then 1 else 0) +
                (r.filter (fun e' => decide (e'.1 = x ∧ e'.2.2 = j))).length := by
              intro j
              simp only [List.filter_cons]
              by_cases h : e.1 = x ∧ e.2.2 = j
              · rw [decide_eq_true h, if_pos rfl, if_pos h, List.length_cons]; omega
              · rw [decide_eq_false h, if_neg h]; simp
            rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib]
            congr 1
            by_cases hx : e.1 = x
            · rw [if_pos hx]
              have : (Finset.univ : Finset (Fin m)).sum (fun j => if e.1 = x ∧ e.2.2 = j then 1 else 0) =
                  (Finset.univ : Finset (Fin m)).sum (fun j => if j = e.2.2 then 1 else 0) :=
                Finset.sum_congr rfl fun j _ => by
                  by_cases hj : j = e.2.2
                  · rw [if_pos hj, if_pos ⟨hx, hj.symm⟩]
                  · rw [if_neg hj, if_neg (fun h => hj h.2.symm)]
              rw [this]; simp
            · rw [if_neg hx]
              exact Finset.sum_eq_zero fun j _ => by rw [if_neg (fun h => hx h.1)]
          rw [Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_add_distrib]
          have h1 : S.sum (fun x => if e.1 = x then 1 else 0) = 1 := by
            have : S.sum (fun x => if e.1 = x then 1 else 0) = S.sum (fun x => if x = e.1 then 1 else 0) :=
              Finset.sum_congr rfl fun x _ => by by_cases h : x = e.1 <;> simp [h, eq_comm]
            rw [this, Finset.sum_ite_eq' S e.1, if_pos he1]
          rw [h1]; omega
      have hsum_ent : P.flatten.length =
          S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
            (P.flatten.filter (fun e => decide (e.1 = x ∧ e.2.2 = j))).length)) :=
        hsum_ent_aux P.flatten fun e he => by
          rcases List.mem_flatten.mp he with ⟨c, hc, hec⟩
          exact (hP.2.1 c hc).2 e hec |>.1
      rw [hsum_ent]
      refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => ?_
      rw [← hent ⟨x, hx⟩ j]
      have hcap := hcirc.2.1 (.entHi ⟨x, hx⟩ j) _ rfl
      split at hcap <;> omega
  classical
  have hex_gap : ∃ g : Nat, ∃ P, LegalStrict S f w d P ∧ P.flatten.length - d * P.length + g = W :=
    ⟨W, [], ⟨fun _ hc => by simp at hc, fun _ hc => by simp at hc, fun _ _ _ => by simp⟩, by simp⟩
  let gmin := Nat.find hex_gap
  rcases Nat.find_spec hex_gap with ⟨Popt, hPopt, hPopt_eq⟩
  refine ⟨Popt, hPopt, fun P' hP' => ?_⟩
  rcases hbound Popt hPopt with ⟨h1, h2⟩
  rcases hbound P' hP' with ⟨h1', h2'⟩
  have hle_nat : P'.flatten.length - d * P'.length ≤ Popt.flatten.length - d * Popt.length := by
    by_contra hgt
    have hg' : W - (P'.flatten.length - d * P'.length) < gmin := by omega
    exact Nat.find_min hex_gap hg' ⟨P', hP', by omega⟩
  omega

private lemma no_pos_res_cycle {n m : Nat} (S : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) (d : Nat)
    (Popt : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)))
    (hPopt : LegalStrict S f w d Popt)
    (hmax : ∀ P', LegalStrict S f w d P' →
      (P'.flatten.length : Int) - (d : Int) * (P'.length : Int) ≤
      (Popt.flatten.length : Int) - (d : Int) * (Popt.length : Int))
    (φ : SArc n S m → Nat) (hcirc : IsCirc f w φ)
    (hgain : circGain d φ = (Popt.flatten.length : Int) - (d : Int) * (Popt.length : Int)) :
    ∀ u cyc, IsWalk (resEdges f w d φ) u u cyc → walkGain cyc ≤ 0 := by
  intro u cyc hcyc
  by_contra hpos
  push_neg at hpos
  have hlift : ∀ {u1 v1 : SVert n S m} (p : List (SVert n S m × SVert n S m × Int)),
      IsWalk (resEdges f w d φ) u1 v1 p →
      ∃ γ : List (SArc n S m × Bool),
        IsGenWalk resStepSrc resStepDst (fun s => resStepValid f w φ s = true) u1 v1 γ ∧
        (γ.map (resStepGain d)).sum = walkGain p := by
    intro u1 v1 p hp
    induction hp with
    | nil u1 => exact ⟨[], IsGenWalk.nil u1, rfl⟩
    | cons e he hsrc _ ih =>
      rcases (mem_resEdges_iff f w d φ e).mp he with ⟨s, hs_val, hs_eq⟩
      rcases ih with ⟨γr, hγr, hgr⟩
      have hs1 : resStepSrc s = e.1 := by rw [← hs_eq]
      have hs2 : resStepDst s = e.2.1 := by rw [← hs_eq]
      have hs3 : resStepGain d s = e.2.2 := by rw [← hs_eq]
      refine ⟨s :: γr, IsGenWalk.cons s hs_val (by rw [hs1, hsrc]) (by rw [hs2]; exact hγr), ?_⟩
      simp only [List.map_cons, List.sum_cons, walkGain_cons, hs3, hgr]
  rcases hlift cyc hcyc with ⟨γ0, hγ0, hg0⟩
  have hex_pos : ∃ L : Nat, ∃ (u1 : SVert n S m) (γ : List (SArc n S m × Bool)),
      IsGenWalk resStepSrc resStepDst (fun s => resStepValid f w φ s = true) u1 u1 γ ∧
      0 < (γ.map (resStepGain d)).sum ∧ γ.length = L :=
    ⟨γ0.length, u, γ0, hγ0, by omega, rfl⟩
  classical
  let Lmin := Nat.find hex_pos
  rcases Nat.find_spec hex_pos with ⟨u1, γ, hγ, hγpos, hγlen⟩
  have hγ_ne : 0 < γ.length := by
    cases γ with
    | nil => simp at hγpos
    | cons _ _ => simp
  have hγ_vsimple : (γ.map resStepSrc).Nodup := by
    rw [← genWalkVerts_take_eq_map_src γ hγ]
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    apply Fin.ext
    have hiγ : i < γ.length := by rw [List.length_take, genWalkVerts_len] at hi; omega
    have hjγ : j < γ.length := by rw [List.length_take, genWalkVerts_len] at hj; omega
    simp only [List.getElem_take] at heq
    have hcontra : ∀ i0 j0 (hij : i0 < j0) (hj0 : j0 < γ.length),
        (genWalkVerts resStepDst u1 γ)[i0]'(by rw [genWalkVerts_len]; omega) =
        (genWalkVerts resStepDst u1 γ)[j0]'(by rw [genWalkVerts_len]; omega) → False := by
      intro i0 j0 hij hj0 heq0
      rcases isGenWalk_split γ hγ i0 (by omega) with ⟨h1, hdrop⟩
      set mid := (genWalkVerts resStepDst u1 γ)[i0]'(by rw [genWalkVerts_len]; omega)
      have hj' : j0 - i0 < (γ.drop i0).length + 1 := by rw [List.length_drop]; omega
      rcases isGenWalk_split (γ.drop i0) hdrop (j0 - i0) hj' with ⟨hmid, h2⟩
      have hmid2 : (genWalkVerts resStepDst mid (γ.drop i0))[j0 - i0]'(by rw [genWalkVerts_len]; exact hj') = mid := by
        rw [genWalkVerts_drop γ hγ i0 j0 (le_of_lt hij) (by omega)]; exact heq0.symm
      rw [hmid2] at hmid h2
      have houter := isGenWalk_append h1 h2
      have hsplit : γ = γ.take i0 ++ (γ.drop i0).take (j0 - i0) ++ (γ.drop i0).drop (j0 - i0) := by
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
      have hg_split : (γ.map (resStepGain d)).sum =
          (((γ.drop i0).take (j0 - i0)).map (resStepGain d)).sum +
          ((γ.take i0 ++ (γ.drop i0).drop (j0 - i0)).map (resStepGain d)).sum := by
        conv_lhs => rw [hsplit]
        simp only [List.map_append, List.sum_append]; omega
      have hlen_mid : ((γ.drop i0).take (j0 - i0)).length < Lmin := by
        rw [List.length_take, List.length_drop]; omega
      have hlen_out : (γ.take i0 ++ (γ.drop i0).drop (j0 - i0)).length < Lmin := by
        rw [List.length_append, List.length_take, List.length_drop, List.length_drop]; omega
      by_cases hgm : 0 < (((γ.drop i0).take (j0 - i0)).map (resStepGain d)).sum
      · exact Nat.find_min hex_pos hlen_mid ⟨mid, _, hmid, hgm, rfl⟩
      · exact Nat.find_min hex_pos hlen_out ⟨u1, _, houter, by omega, rfl⟩
    rcases lt_trichotomy i j with hlt | hEq | hgt
    · exact False.elim (hcontra i j hlt hjγ heq)
    · exact hEq
    · exact False.elim (hcontra j i hgt hiγ heq.symm)
  have hγ_nodup : γ.Nodup := List.Nodup.of_map resStepSrc hγ_vsimple
  have hwalk_cons : ∀ {u0 v0 : SVert n S m} {s0 : SArc n S m × Bool} {r0 : List (SArc n S m × Bool)},
      IsGenWalk resStepSrc resStepDst (fun s => resStepValid f w φ s = true) u0 v0 (s0 :: r0) →
      resStepValid f w φ s0 = true ∧ resStepSrc s0 = u0 ∧
        IsGenWalk resStepSrc resStepDst (fun s => resStepValid f w φ s = true) (resStepDst s0) v0 r0 := by
    intro u0 v0 s0 r0 h
    cases h with
    | cons _ hv hs hr => exact ⟨hv, hs, hr⟩
  have hno_both : ∀ a : SArc n S m, ¬ ((a, true) ∈ γ ∧ (a, false) ∈ γ) := by
    intro a ⟨ht, hf⟩
    rcases mem_iff_rotate_head hγ (a, true) ht with ⟨rest, hrot, hperm⟩
    have hnd_rot : (((a, true) :: rest).map resStepSrc).Nodup := (hperm.map resStepSrc).nodup_iff.mpr hγ_vsimple
    have hf_rot : (a, false) ∈ (a, true) :: rest := hperm.symm.subset hf
    have hf_rest : (a, false) ∈ rest := by
      rcases List.mem_cons.mp hf_rot with h | h
      · cases h
      · exact h
    rcases hwalk_cons hrot with ⟨_, _, hrest⟩
    cases rest with
    | nil => simp at hf_rest
    | cons s2 rest2 =>
      rcases hwalk_cons hrest with ⟨_, hs2, hrest2⟩
      simp only [List.map_cons, List.nodup_cons] at hnd_rot
      rcases hnd_rot with ⟨hu_not, hv_not, _⟩
      have hs2_eq : s2 = (a, false) := by
        rcases List.mem_cons.mp hf_rest with h | h
        · exact h.symm
        · exact False.elim (hv_not (List.mem_map.mpr ⟨(a, false), h, by dsimp only [resStepSrc, resStepDst] at hs2 ⊢; exact hs2.symm⟩))
      subst hs2_eq
      cases rest2 with
      | nil =>
        have hg_rot : (((a, true) :: [(a, false)]).map (resStepGain d)).sum = (γ.map (resStepGain d)).sum :=
          (hperm.map (resStepGain d)).sum_eq
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, resStepGain] at hg_rot
        omega
      | cons s3 rest3 =>
        rcases hwalk_cons hrest2 with ⟨_, hs3, _⟩
        exact hu_not (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨s3, List.mem_cons_self, by dsimp only [resStepSrc, resStepDst] at hs3 ⊢; exact hs3⟩))
  let φ' : SArc n S m → Nat := fun a =>
    if (a, true) ∈ γ then φ a + 1 else if (a, false) ∈ γ then φ a - 1 else φ a
  have hφ'_int : ∀ a : SArc n S m, (φ' a : Int) = (φ a : Int) +
      (if (a, true) ∈ γ then 1 else 0) - (if (a, false) ∈ γ then 1 else 0) := by
    intro a
    dsimp only [φ']
    by_cases ht : (a, true) ∈ γ
    · have hf : (a, false) ∉ γ := fun h => hno_both a ⟨ht, h⟩
      rw [if_pos ht, if_pos ht, if_neg hf]; push_cast; omega
    · rw [if_neg ht, if_neg ht]
      by_cases hf : (a, false) ∈ γ
      · rw [if_pos hf, if_pos hf]
        have hv := isGenWalk_mem hγ (a, false) hf
        simp only [resStepValid, Bool.and_eq_true] at hv
        have hposa : 0 < φ a := of_decide_eq_true hv.2
        omega
      · rw [if_neg hf, if_neg hf]; omega
  have hcirc' : IsCirc f w φ' := by
    refine ⟨fun a hva => ?_, fun a cap hcap => ?_, fun v => ?_⟩
    · have ht : (a, true) ∉ γ := fun hm => by
        have hv := isGenWalk_mem hγ (a, true) hm
        simp [resStepValid, hva] at hv
      have hf : (a, false) ∉ γ := fun hm => by
        have hv := isGenWalk_mem hγ (a, false) hm
        simp [resStepValid, hva] at hv
      dsimp only [φ']; rw [if_neg ht, if_neg hf]; exact hcirc.1 a hva
    · dsimp only [φ']
      by_cases ht : (a, true) ∈ γ
      · rw [if_pos ht]
        have hv := isGenWalk_mem hγ (a, true) ht
        simp only [resStepValid, hcap, Bool.and_eq_true] at hv
        have hlt : φ a < cap := of_decide_eq_true hv.2
        omega
      · rw [if_neg ht]
        have hle := hcirc.2.1 a cap hcap
        split <;> omega
    · suffices h : ((outFlow φ' v : Int) - (inFlow φ' v : Int)) = 0 by omega
      have hbal0 : (outFlow φ v : Int) = (inFlow φ v : Int) := by exact_mod_cast hcirc.2.2 v
      have hcnt_step : ∀ s : SArc n S m × Bool, γ.count s = if s ∈ γ then 1 else 0 := fun _ =>
        List.Nodup.count hγ_nodup
      have hsrc_cnt : ((γ.filter (fun s => decide (resStepSrc s = v))).length : Int) =
          (Finset.univ : Finset (SArc n S m)).sum (fun a =>
            (if arcSrc a = v then (if (a, true) ∈ γ then (1 : Int) else 0) else 0) +
            (if arcDst a = v then (if (a, false) ∈ γ then (1 : Int) else 0) else 0)) := by
        rw [← sum_count_filter]
        have h1 : (Finset.univ : Finset (SArc n S m × Bool)).sum
            (fun s => if decide (resStepSrc s = v) = true then γ.count s else 0) =
            (Finset.univ : Finset (SArc n S m)).sum (fun a =>
              (if arcSrc a = v then (if (a, true) ∈ γ then 1 else 0) else 0) +
              (if arcDst a = v then (if (a, false) ∈ γ then 1 else 0) else 0)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Fintype.sum_bool]
          by_cases h1 : arcSrc a = v <;> by_cases h2 : arcDst a = v <;> simp [resStepSrc, hcnt_step, h1, h2]
        exact_mod_cast h1
      have hdst_cnt : ((γ.filter (fun s => decide (resStepDst s = v))).length : Int) =
          (Finset.univ : Finset (SArc n S m)).sum (fun a =>
            (if arcDst a = v then (if (a, true) ∈ γ then (1 : Int) else 0) else 0) +
            (if arcSrc a = v then (if (a, false) ∈ γ then (1 : Int) else 0) else 0)) := by
        rw [← sum_count_filter]
        have h1 : (Finset.univ : Finset (SArc n S m × Bool)).sum
            (fun s => if decide (resStepDst s = v) = true then γ.count s else 0) =
            (Finset.univ : Finset (SArc n S m)).sum (fun a =>
              (if arcDst a = v then (if (a, true) ∈ γ then 1 else 0) else 0) +
              (if arcSrc a = v then (if (a, false) ∈ γ then 1 else 0) else 0)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Fintype.sum_bool]
          by_cases h1 : arcDst a = v <;> by_cases h2 : arcSrc a = v <;> simp [resStepDst, hcnt_step, h1, h2]
        exact_mod_cast h1
      have hdiff : (outFlow φ' v : Int) - (inFlow φ' v : Int) =
          ((outFlow φ v : Int) - (inFlow φ v : Int)) +
          (((γ.filter (fun s => decide (resStepSrc s = v))).length : Int) -
           ((γ.filter (fun s => decide (resStepDst s = v))).length : Int)) := by
        rw [hsrc_cnt, hdst_cnt]
        dsimp only [outFlow, inFlow]
        push_cast
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hφa := hφ'_int a
        by_cases h1 : arcSrc a = v <;> by_cases h2 : arcDst a = v <;> simp [h1, h2] <;> omega
      rw [hdiff, hbal0, isGenWalk_closed_balance hγ v]; omega
  have hgain' : circGain d φ' = circGain d φ + (γ.map (resStepGain d)).sum := by
    have hcnt_step : ∀ s : SArc n S m × Bool, γ.count s = if s ∈ γ then 1 else 0 := fun _ =>
      List.Nodup.count hγ_nodup
    rw [← sum_count_int (resStepGain d) γ, Fintype.sum_prod_type]
    dsimp only [circGain]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_bool]
    simp only [hcnt_step, resStepGain, hφ'_int a]
    split <;> split <;> ring
  rcases cycle_decomp_cert f w d φ' hcirc' with ⟨P', hP'len, hP'ch, hP'cnt, hP'gain⟩
  have hP'_legal : LegalStrict S f w d P' := by
    refine ⟨hP'len, hP'ch, fun x hx j => ?_⟩
    have h1 := hP'cnt ⟨x, hx⟩ j
    dsimp only at h1
    by_cases hfx : f x j = true
    · rw [if_pos hfx] at h1
      have hcap := hcirc'.2.1 (.entHi ⟨x, hx⟩ j) _ rfl
      rw [if_pos hfx] at hcap
      exact h1.trans hcap
    · rw [if_neg hfx] at h1
      have hff : f x j = false := Bool.eq_false_iff.mpr hfx
      have hcap := hcirc'.2.1 (.extLo ⟨x, hx⟩ j) _ rfl
      rw [if_pos hff] at hcap
      exact h1.trans hcap
  have hle := hmax P' hP'_legal
  omega

private lemma strong_duality_stage {n m b : Nat} (S : Finset (Finset (Fin n)))
    (hS : S.Nonempty) (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) :
    let d := 2 ^ b - 1
    ∃ (P : List (List (Finset (Fin n) × Finset (Fin n) × Fin m)))
      (base : Finset (Fin n) → Nat) (g : Finset (Fin n) → Fin m → Bool),
      LegalStrict S f w d P ∧
      (∀ x ∈ S, base x < 2 ^ b) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ⊆ y → base x ≤ base y) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ⊆ y → base x = base y → ∀ j, g x j = true → g y j = true) ∧
      P.flatten.length =
        S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j => if g x j = f x j then 0 else w x j)) +
        d * P.length := by
  intro d
  rcases exists_max_cert S f w d with ⟨Popt, hPopt, hmax⟩
  rcases cert_to_circ f w d Popt hPopt with ⟨φ, hcirc, hgain, _, _⟩
  let R := resEdges f w d φ
  have hnopos : ∀ u cyc, IsWalk R u u cyc → walkGain cyc ≤ 0 :=
    no_pos_res_cycle S f w d Popt hPopt hmax φ hcirc hgain
  rcases hS with ⟨x0, hx0⟩
  have hreach : ∀ v : SVert n S m, ∃ p, IsWalk R .src v p := by
    intro v
    cases v with
    | src => exact ⟨[], IsWalk.nil SVert.src⟩
    | vB x =>
      have he : (.src, .vB x, (0 : Int)) ∈ R :=
        (mem_resEdges_iff f w d φ _).mpr ⟨(.srcB x, true), rfl, rfl⟩
      exact ⟨[(.src, .vB x, 0)], IsWalk.cons _ he rfl (IsWalk.nil _)⟩
    | vT x j =>
      have he1 : (.src, .vB x, (0 : Int)) ∈ R :=
        (mem_resEdges_iff f w d φ _).mpr ⟨(.srcB x, true), rfl, rfl⟩
      have he2 : (.vB x, .vT x j, (0 : Int)) ∈ R :=
        (mem_resEdges_iff f w d φ _).mpr ⟨(.ent0 x j, true), rfl, rfl⟩
      exact ⟨[(.src, .vB x, 0), (.vB x, .vT x j, 0)],
        IsWalk.cons _ he1 rfl (IsWalk.cons _ he2 rfl (IsWalk.nil _))⟩
    | snk =>
      have he1 : (.src, .vB ⟨x0, hx0⟩, (0 : Int)) ∈ R :=
        (mem_resEdges_iff f w d φ _).mpr ⟨(.srcB ⟨x0, hx0⟩, true), rfl, rfl⟩
      have he2 : (.vB ⟨x0, hx0⟩, .snk, (0 : Int)) ∈ R :=
        (mem_resEdges_iff f w d φ _).mpr ⟨(.bSnk ⟨x0, hx0⟩, true), rfl, rfl⟩
      exact ⟨[(.src, .vB ⟨x0, hx0⟩, 0), (.vB ⟨x0, hx0⟩, .snk, 0)],
        IsWalk.cons _ he1 rfl (IsWalk.cons _ he2 rfl (IsWalk.nil _))⟩
  rcases bellman_ford_potential R .src hreach hnopos with ⟨π, hπ0, hπ_edge⟩
  have hfwd : ∀ a : SArc n S m, arcValid a = true →
      (match arcCap f w a with | none => True | some c => φ a < c) →
      π (arcSrc a) + arcGain d a ≤ π (arcDst a) := by
    intro a hva hcap
    have hv : resStepValid f w φ (a, true) = true := by
      simp only [resStepValid, hva, Bool.true_and]
      cases hc : arcCap f w a with
      | none => rfl
      | some c => rw [hc] at hcap; exact decide_eq_true hcap
    exact hπ_edge _ ((mem_resEdges_iff f w d φ _).mpr ⟨(a, true), hv, rfl⟩)
  have hbwd : ∀ a : SArc n S m, arcValid a = true → 0 < φ a →
      π (arcDst a) - arcGain d a ≤ π (arcSrc a) := by
    intro a hva hpos
    have hv : resStepValid f w φ (a, false) = true := by
      simp only [resStepValid, hva, Bool.true_and]; exact decide_eq_true hpos
    have h := hπ_edge _ ((mem_resEdges_iff f w d φ _).mpr ⟨(a, false), hv, rfl⟩)
    simp only [resStepSrc, resStepDst, resStepGain] at h
    omega
  have hB_ge0 : ∀ x : {x // x ∈ S}, 0 ≤ π (.vB x) := fun x => by
    have := hfwd (.srcB x) rfl trivial
    simp only [arcSrc, arcDst, arcGain, hπ0] at this; omega
  have hB_le_snk : ∀ x : {x // x ∈ S}, π (.vB x) ≤ π .snk := fun x => by
    have := hfwd (.bSnk x) rfl trivial
    simp only [arcSrc, arcDst, arcGain] at this; omega
  have hsnk_le_d : π .snk ≤ (d : Int) := by
    have := hfwd .ret rfl trivial
    simp only [arcSrc, arcDst, arcGain, hπ0] at this; omega
  have hB_mono : ∀ x y : {x // x ∈ S}, x.1 ⊆ y.1 → π (.vB x) ≤ π (.vB y) := by
    intro x y hxy
    by_cases heq : x.1 = y.1
    · have : x = y := Subtype.ext heq
      rw [this]
    · have := hfwd (.bb x y) (decide_eq_true ⟨hxy, heq⟩) trivial
      simp only [arcSrc, arcDst, arcGain] at this; omega
  have hT_mono : ∀ (x y : {x // x ∈ S}) (j : Fin m), x.1 ⊆ y.1 → π (.vT x j) ≤ π (.vT y j) := by
    intro x y j hxy
    by_cases heq : x.1 = y.1
    · have : x = y := Subtype.ext heq
      rw [this]
    · have := hfwd (.tt x y j) (decide_eq_true ⟨hxy, heq⟩) trivial
      simp only [arcSrc, arcDst, arcGain] at this; omega
  have hT_lo : ∀ (x : {x // x ∈ S}) (j : Fin m), π (.vB x) ≤ π (.vT x j) := fun x j => by
    have := hfwd (.ent0 x j) rfl trivial
    simp only [arcSrc, arcDst, arcGain] at this; omega
  have hT_hi : ∀ (x : {x // x ∈ S}) (j : Fin m), π (.vT x j) ≤ π (.vB x) + 1 := fun x j => by
    have := hfwd (.extM1 x j) rfl trivial
    simp only [arcSrc, arcDst, arcGain] at this; omega
  let base : Finset (Fin n) → Nat := fun x => if hx : x ∈ S then (π (.vB ⟨x, hx⟩)).toNat else 0
  let g : Finset (Fin n) → Fin m → Bool := fun x j =>
    if hx : x ∈ S then decide (π (.vT ⟨x, hx⟩ j) = π (.vB ⟨x, hx⟩) + 1) else false
  have hpot_zero : (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * (π (arcDst a) - π (arcSrc a))) = 0 := by
    have h1 : (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * π (arcDst a)) =
        (Finset.univ : Finset (SVert n S m)).sum (fun v => (inFlow φ v : Int) * π v) := by
      symm
      calc (Finset.univ : Finset (SVert n S m)).sum (fun v => (inFlow φ v : Int) * π v)
          = (Finset.univ : Finset (SVert n S m)).sum (fun v =>
              (Finset.univ : Finset (SArc n S m)).sum (fun a => if arcDst a = v then (φ a : Int) * π v else 0)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            dsimp only [inFlow]; push_cast; rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => by split <;> simp
        _ = (Finset.univ : Finset (SArc n S m)).sum (fun a =>
              (Finset.univ : Finset (SVert n S m)).sum (fun v => if arcDst a = v then (φ a : Int) * π v else 0)) :=
            Finset.sum_comm
        _ = (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * π (arcDst a)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have : (Finset.univ : Finset (SVert n S m)).sum (fun v => if arcDst a = v then (φ a : Int) * π v else 0) =
                (Finset.univ : Finset (SVert n S m)).sum (fun v => if v = arcDst a then (φ a : Int) * π v else 0) :=
              Finset.sum_congr rfl fun v _ => by by_cases h : v = arcDst a <;> simp [h, eq_comm]
            rw [this]; simp
    have h2 : (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * π (arcSrc a)) =
        (Finset.univ : Finset (SVert n S m)).sum (fun v => (outFlow φ v : Int) * π v) := by
      symm
      calc (Finset.univ : Finset (SVert n S m)).sum (fun v => (outFlow φ v : Int) * π v)
          = (Finset.univ : Finset (SVert n S m)).sum (fun v =>
              (Finset.univ : Finset (SArc n S m)).sum (fun a => if arcSrc a = v then (φ a : Int) * π v else 0)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            dsimp only [outFlow]; push_cast; rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => by split <;> simp
        _ = (Finset.univ : Finset (SArc n S m)).sum (fun a =>
              (Finset.univ : Finset (SVert n S m)).sum (fun v => if arcSrc a = v then (φ a : Int) * π v else 0)) :=
            Finset.sum_comm
        _ = (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * π (arcSrc a)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have : (Finset.univ : Finset (SVert n S m)).sum (fun v => if arcSrc a = v then (φ a : Int) * π v else 0) =
                (Finset.univ : Finset (SVert n S m)).sum (fun v => if v = arcSrc a then (φ a : Int) * π v else 0) :=
              Finset.sum_congr rfl fun v _ => by by_cases h : v = arcSrc a <;> simp [h, eq_comm]
            rw [this]; simp
    have h3 : (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * (π (arcDst a) - π (arcSrc a))) =
        (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * π (arcDst a)) -
        (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * π (arcSrc a)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h3, h1, h2]
    have h4 : (Finset.univ : Finset (SVert n S m)).sum (fun v => (inFlow φ v : Int) * π v) =
        (Finset.univ : Finset (SVert n S m)).sum (fun v => (outFlow φ v : Int) * π v) :=
      Finset.sum_congr rfl fun v _ => by rw [hcirc.2.2 v]
    omega
  have hcs_inf : ∀ a : SArc n S m, arcCap f w a = none →
      (φ a : Int) * (arcGain d a - (π (arcDst a) - π (arcSrc a))) = 0 := by
    intro a hcap
    by_cases hφ0 : φ a = 0
    · rw [hφ0]; simp
    · have hva : arcValid a = true := by
        cases hv : arcValid a
        · exact False.elim (hφ0 (hcirc.1 a hv))
        · rfl
      have h1 := hfwd a hva (by rw [hcap]; trivial)
      have h2 := hbwd a hva (by omega)
      have heq : arcGain d a - (π (arcDst a) - π (arcSrc a)) = 0 := by omega
      rw [heq, mul_zero]
  have hcs_pair : ∀ (x : {x // x ∈ S}) (j : Fin m),
      (φ (.entHi x j) : Int) * (arcGain d (.entHi x j) - (π (arcDst (.entHi x j)) - π (arcSrc (.entHi x j)))) +
      (φ (.extLo x j) : Int) * (arcGain d (.extLo x j) - (π (arcDst (.extLo x j)) - π (arcSrc (.extLo x j)))) =
      (if g x.1 j = f x.1 j then (0 : Int) else (w x.1 j : Int)) := by
    intro x j
    have hlo := hT_lo x j
    have hhi := hT_hi x j
    simp only [arcGain, arcDst, arcSrc, g, dif_pos x.2]
    cases hfx : f x.1 j
    · have hent0 : φ (.entHi x j) = 0 := by
        have hcap := hcirc.2.1 (.entHi x j) _ rfl; simp [hfx] at hcap; omega
      rw [hent0]; simp only [Nat.cast_zero, zero_mul, zero_add]
      by_cases hT : π (.vT x j) = π (.vB x) + 1
      · rw [decide_eq_true hT, if_neg (by decide)]
        have hsat : φ (.extLo x j) = w x.1 j := by
          have hle := hcirc.2.1 (.extLo x j) _ rfl; simp [hfx] at hle
          by_contra hne
          have hlt : φ (.extLo x j) < w x.1 j := by omega
          have h1 := hfwd (.extLo x j) rfl (by simp [arcCap, hfx, hlt])
          simp only [arcSrc, arcDst, arcGain] at h1; omega
        rw [hsat, hT]; ring
      · rw [decide_eq_false hT, if_pos rfl]
        have hTeq : π (.vT x j) = π (.vB x) := by omega
        rw [hTeq]; ring
    · have hext0 : φ (.extLo x j) = 0 := by
        have hcap := hcirc.2.1 (.extLo x j) _ rfl; simp [hfx] at hcap; omega
      rw [hext0]; simp only [Nat.cast_zero, zero_mul, add_zero]
      by_cases hT : π (.vT x j) = π (.vB x) + 1
      · rw [decide_eq_true hT, if_pos rfl, hT]; ring
      · rw [decide_eq_false hT, if_neg (by decide)]
        have hTeq : π (.vT x j) = π (.vB x) := by omega
        have hsat : φ (.entHi x j) = w x.1 j := by
          have hle := hcirc.2.1 (.entHi x j) _ rfl; simp [hfx] at hle
          by_contra hne
          have hlt : φ (.entHi x j) < w x.1 j := by omega
          have h1 := hfwd (.entHi x j) rfl (by simp [arcCap, hfx, hlt])
          simp only [arcSrc, arcDst, arcGain] at h1; omega
        rw [hsat, hTeq]; ring
  let lossNat : Nat := S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j => if g x j = f x j then 0 else w x j))
  have hgain_eq_loss : circGain d φ = (lossNat : Int) := by
    have h1 : circGain d φ = (Finset.univ : Finset (SArc n S m)).sum
        (fun a => (φ a : Int) * (arcGain d a - (π (arcDst a) - π (arcSrc a)))) := by
      dsimp only [circGain]
      have hsub : (Finset.univ : Finset (SArc n S m)).sum
          (fun a => (φ a : Int) * (arcGain d a - (π (arcDst a) - π (arcSrc a)))) =
          (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * arcGain d a) -
          (Finset.univ : Finset (SArc n S m)).sum (fun a => (φ a : Int) * (π (arcDst a) - π (arcSrc a))) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hsub, hpot_zero, sub_zero]
    rw [h1, sarc_sum]
    have hz1 : (Finset.univ.sum fun x => (φ (.srcB x) : Int) * (arcGain d (.srcB x) - (π (arcDst (.srcB x)) - π (arcSrc (.srcB x))))) = 0 :=
      Finset.sum_eq_zero fun x _ => hcs_inf (.srcB x) rfl
    have hz2 : (Finset.univ.sum fun x => (φ (.bSnk x) : Int) * (arcGain d (.bSnk x) - (π (arcDst (.bSnk x)) - π (arcSrc (.bSnk x))))) = 0 :=
      Finset.sum_eq_zero fun x _ => hcs_inf (.bSnk x) rfl
    have hz3 : (φ .ret : Int) * (arcGain d .ret - (π (arcDst .ret) - π (arcSrc .ret))) = 0 := hcs_inf .ret rfl
    have hz4 : (Finset.univ.sum fun p : {x // x ∈ S} × {x // x ∈ S} => (φ (.bb p.1 p.2) : Int) * (arcGain d (.bb p.1 p.2) - (π (arcDst (.bb p.1 p.2)) - π (arcSrc (.bb p.1 p.2))))) = 0 :=
      Finset.sum_eq_zero fun p _ => hcs_inf (.bb p.1 p.2) rfl
    have hz5 : (Finset.univ.sum fun p : {x // x ∈ S} × {x // x ∈ S} × Fin m => (φ (.tt p.1 p.2.1 p.2.2) : Int) * (arcGain d (.tt p.1 p.2.1 p.2.2) - (π (arcDst (.tt p.1 p.2.1 p.2.2)) - π (arcSrc (.tt p.1 p.2.1 p.2.2))))) = 0 :=
      Finset.sum_eq_zero fun p _ => hcs_inf (.tt p.1 p.2.1 p.2.2) rfl
    have hz6 : (Finset.univ.sum fun p : {x // x ∈ S} × Fin m => (φ (.ent0 p.1 p.2) : Int) * (arcGain d (.ent0 p.1 p.2) - (π (arcDst (.ent0 p.1 p.2)) - π (arcSrc (.ent0 p.1 p.2))))) = 0 :=
      Finset.sum_eq_zero fun p _ => hcs_inf (.ent0 p.1 p.2) rfl
    have hz7 : (Finset.univ.sum fun p : {x // x ∈ S} × Fin m => (φ (.extM1 p.1 p.2) : Int) * (arcGain d (.extM1 p.1 p.2) - (π (arcDst (.extM1 p.1 p.2)) - π (arcSrc (.extM1 p.1 p.2))))) = 0 :=
      Finset.sum_eq_zero fun p _ => hcs_inf (.extM1 p.1 p.2) rfl
    rw [hz1, hz2, hz3, hz4, hz5, hz6, hz7]
    simp only [zero_add]
    rw [← Finset.sum_add_distrib]
    have hpair_sum : (Finset.univ : Finset ({x // x ∈ S} × Fin m)).sum
        (fun p => (φ (.entHi p.1 p.2) : Int) * (arcGain d (.entHi p.1 p.2) - (π (arcDst (.entHi p.1 p.2)) - π (arcSrc (.entHi p.1 p.2)))) +
          (φ (.extLo p.1 p.2) : Int) * (arcGain d (.extLo p.1 p.2) - (π (arcDst (.extLo p.1 p.2)) - π (arcSrc (.extLo p.1 p.2))))) =
        (Finset.univ : Finset ({x // x ∈ S} × Fin m)).sum (fun p => if g p.1.1 p.2 = f p.1.1 p.2 then (0 : Int) else (w p.1.1 p.2 : Int)) :=
      Finset.sum_congr rfl fun p _ => hcs_pair p.1 p.2
    rw [hpair_sum, Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort S (fun x => (Finset.univ : Finset (Fin m)).sum (fun j => if g x j = f x j then (0 : Int) else (w x j : Int)))]
    symm
    dsimp only [lossNat]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split <;> simp
  refine ⟨Popt, base, g, hPopt, ?_, ?_, ?_, ?_⟩
  · intro x hx
    dsimp only [base]; rw [dif_pos hx]
    have h1 := hB_ge0 ⟨x, hx⟩
    have h2 := hB_le_snk ⟨x, hx⟩
    have hpow : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    omega
  · intro x hx y hy hxy
    dsimp only [base]; rw [dif_pos hx, dif_pos hy]
    have h1 := hB_ge0 ⟨x, hx⟩
    have h2 := hB_ge0 ⟨y, hy⟩
    have h3 := hB_mono ⟨x, hx⟩ ⟨y, hy⟩ hxy
    omega
  · intro x hx y hy hxy heq j hgx
    dsimp only [base] at heq; rw [dif_pos hx, dif_pos hy] at heq
    dsimp only [g] at hgx ⊢; rw [dif_pos hx] at hgx; rw [dif_pos hy]
    have h1 := hB_ge0 ⟨x, hx⟩
    have h2 := hB_ge0 ⟨y, hy⟩
    have hBeq : π (.vB ⟨x, hx⟩) = π (.vB ⟨y, hy⟩) := by omega
    have hTx := of_decide_eq_true hgx
    have hTm := hT_mono ⟨x, hx⟩ ⟨y, hy⟩ j hxy
    have hThi := hT_hi ⟨y, hy⟩ j
    exact decide_eq_true (by omega)
  · change Popt.flatten.length = lossNat + d * Popt.length
    omega


private lemma exists_min_pow2 (L b : Nat) (hL1 : 1 ≤ L) (hLb : L ≤ 2 ^ b) :
    ∃ b' : Nat, b' ≤ b ∧ L ≤ 2 ^ b' ∧ 2 ^ b' ≤ 2 * L := by
  have hex : ∃ k : Nat, L ≤ 2 ^ k := ⟨b, hLb⟩
  classical
  let b' := Nat.find hex
  have hb'_ge : L ≤ 2 ^ b' := Nat.find_spec hex
  have hb'_le : b' ≤ b := Nat.find_min' hex hLb
  refine ⟨b', hb'_le, hb'_ge, ?_⟩
  cases hb' : b' with
  | zero => simp; omega
  | succ k =>
    have hlt : ¬ (L ≤ 2 ^ k) := Nat.find_min hex (by omega : k < b')
    rw [pow_succ]; omega

private lemma nat_le_two_pow (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

private lemma sum_filter_disjoint {α : Type} (xs : List α) (K : Nat) (pred : Nat → α → Bool)
    (hdisj : ∀ x ∈ xs, ∀ r1 r2, r1 < K → r2 < K → pred r1 x = true → pred r2 x = true → r1 = r2) :
    (Finset.range K).sum (fun r => (xs.filter (pred r)).length) ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hrec := ih (fun y hy => hdisj y (List.mem_cons_of_mem x hy))
    have hstep : ∀ r ∈ Finset.range K,
        ((x :: rest).filter (pred r)).length = (if pred r x = true then 1 else 0) + (rest.filter (pred r)).length := by
      intro r _
      simp only [List.filter_cons]
      cases pred r x <;> simp [Nat.add_comm]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    have hone : (Finset.range K).sum (fun r => if pred r x = true then 1 else 0) ≤ 1 := by
      by_cases hex : ∃ r0 ∈ Finset.range K, pred r0 x = true
      · rcases hex with ⟨r0, hr0, hpr0⟩
        have huniq : ∀ r ∈ Finset.range K, (if pred r x = true then 1 else 0) = if r = r0 then 1 else 0 := by
          intro r hr
          by_cases heq : r = r0
          · rw [if_pos heq, heq, if_pos hpr0]
          · rw [if_neg heq]
            by_cases hpr : pred r x = true
            · exact False.elim (heq (hdisj x List.mem_cons_self r r0 (Finset.mem_range.mp hr) (Finset.mem_range.mp hr0) hpr hpr0))
            · rw [if_neg hpr]
        rw [Finset.sum_congr rfl huniq, Finset.sum_ite_eq' (Finset.range K) r0, if_pos hr0]
      · push_neg at hex
        have hz : (Finset.range K).sum (fun r => if pred r x = true then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun r hr => by rw [if_neg (hex r hr)]
        omega
    simp only [List.length_cons]
    omega

private lemma build_up_wires (n : Nat) :
    ∀ (xs : List (Finset (Fin n))) (gs : List Gate),
      ValidGates n gs →
      ∃ (gs' : List Gate) (upW : Finset (Fin n) → Nat),
        (∃ extra, gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra ≤ n * xs.length) ∧
        ValidGates n gs' ∧
        (∀ x ∈ xs, upW x < n + 2 + gs'.length) ∧
        (∀ x ∈ xs, ∀ y : Finset (Fin n),
          (evalW gs' (bitsVec n y)).getD (upW x) false = decide (x ⊆ y)) := by
  intro xs
  induction xs with
  | nil =>
    intro gs hgs
    refine ⟨gs, fun _ => n, ⟨[], by simp, rfl, by simp [posCount]⟩, hgs,
      fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons x rest ih =>
    intro gs hgs
    let ws : List Nat := x.toList.map (fun i : Fin n => i.val)
    have hws_len : ws.length ≤ n := by
      dsimp only [ws]; rw [List.length_map, Finset.length_toList]
      have := Finset.card_le_univ x
      simpa using this
    have hws_bd : ∀ w ∈ ws, w < n + 2 + gs.length := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
      have := i.isLt; omega
    rcases appendAndList_spec n gs ws hgs hws_bd with ⟨⟨e1, heq1, hnot1, hpos1⟩, hval1, hout1, heval1⟩
    set res := appendAndList n gs ws
    rcases ih res.1 hval1 with ⟨gs2, up2, ⟨e2, heq2, hnot2, hpos2⟩, hval2, hbd2, heval2⟩
    let up' : Finset (Fin n) → Nat := fun z => if z = x then res.2 else up2 z
    refine ⟨gs2, up', ⟨e1 ++ e2, ?_, ?_, ?_⟩, hval2, ?_, ?_⟩
    · rw [heq2, heq1, List.append_assoc]
    · rw [notCountL_append, hnot1, hnot2]
    · rw [posCount_append, List.length_cons, Nat.mul_add, Nat.mul_one]; omega
    · intro z hz
      dsimp only [up']
      by_cases hzx : z = x
      · rw [if_pos hzx, heq2, List.length_append]; omega
      · rw [if_neg hzx]
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact False.elim (hzx rfl)
        · exact hbd2 z hz'
    · intro z hz y
      dsimp only [up']
      by_cases hzx : z = x
      · rw [if_pos hzx, hzx, heq2]
        rw [evalW_append_pre res.1 e2 (bitsVec n y) res.2 (by rw [bitsVec_len]; exact hout1)]
        rw [heval1 (bitsVec n y) (bitsVec_len n y) (bitsVec_c1 n y)]
        by_cases hsub : x ⊆ y
        · rw [decide_eq_true hsub]
          rw [List.all_eq_true]
          intro w hw
          rcases List.mem_map.mp hw with ⟨i, hi, rfl⟩
          rw [evalW_pre gs (bitsVec n y) i.val (by rw [bitsVec_len]; have := i.isLt; omega)]
          rw [bitsVec_in]
          exact decide_eq_true (hsub (Finset.mem_toList.mp hi))
        · rw [decide_eq_false hsub]
          cases hall : ws.all (fun w => (evalW gs (bitsVec n y)).getD w false)
          · rfl
          · exfalso; apply hsub; intro i hi
            have hw : i.val ∈ ws := List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩
            have h1 := List.all_eq_true.mp hall i.val hw
            rw [evalW_pre gs (bitsVec n y) i.val (by rw [bitsVec_len]; have := i.isLt; omega), bitsVec_in] at h1
            exact of_decide_eq_true h1
      · rw [if_neg hzx]
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact False.elim (hzx rfl)
        · exact heval2 z hz' y

private lemma build_bucket_ors (n : Nat) (upW : Finset (Fin n) → Nat) (xs : List (Finset (Fin n)))
    (pred : Nat → Finset (Fin n) → Bool) :
    ∀ (K : Nat) (gs : List Gate),
      ValidGates n gs →
      (∀ x ∈ xs, upW x < n + 2 + gs.length) →
      (∀ x ∈ xs, ∀ y : Finset (Fin n), (evalW gs (bitsVec n y)).getD (upW x) false = decide (x ⊆ y)) →
      ∃ (gs' : List Gate) (bW : Nat → Nat),
        (∃ extra, gs' = gs ++ extra ∧ notCountL extra = 0 ∧
          posCount extra ≤ (Finset.range K).sum (fun r => (xs.filter (pred r)).length)) ∧
        ValidGates n gs' ∧
        (∀ r < K, bW r < n + 2 + gs'.length) ∧
        (∀ r < K, ∀ y : Finset (Fin n),
          (evalW gs' (bitsVec n y)).getD (bW r) false = decide (∃ x ∈ xs, pred r x = true ∧ x ⊆ y)) := by
  intro K
  induction K with
  | zero =>
    intro gs hgs _ _
    refine ⟨gs, fun _ => n, ⟨[], by simp, rfl, by simp [posCount]⟩, hgs,
      fun _ h => by omega, fun _ h => by omega⟩
  | succ K ih =>
    intro gs hgs hbd hev
    rcases ih gs hgs hbd hev with ⟨gs1, bW1, ⟨e1, heq1, hnot1, hpos1⟩, hval1, hbd1, hev1⟩
    let ws : List Nat := (xs.filter (pred K)).map upW
    have hws_bd : ∀ w ∈ ws, w < n + 2 + gs1.length := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
      have hx' := (List.mem_filter.mp hx).1
      have := hbd x hx'
      rw [heq1, List.length_append]; omega
    rcases appendOrList_spec n gs1 ws hval1 hws_bd with ⟨⟨e2, heq2, hnot2, hpos2⟩, hval2, hout2, heval2⟩
    set res := appendOrList n gs1 ws
    let bW' : Nat → Nat := fun r => if r = K then res.2 else bW1 r
    refine ⟨res.1, bW', ⟨e1 ++ e2, ?_, ?_, ?_⟩, hval2, ?_, ?_⟩
    · rw [heq2, heq1, List.append_assoc]
    · rw [notCountL_append, hnot1, hnot2]
    · rw [posCount_append, Finset.sum_range_succ]
      have hlen : ws.length = (xs.filter (pred K)).length := by simp [ws]
      omega
    · intro r hr
      dsimp only [bW']
      by_cases hrK : r = K
      · rw [if_pos hrK]; exact hout2
      · rw [if_neg hrK, heq2, List.length_append]
        have := hbd1 r (by omega); omega
    · intro r hr y
      dsimp only [bW']
      by_cases hrK : r = K
      · rw [if_pos hrK, hrK, heval2 (bitsVec n y) (bitsVec_len n y) (bitsVec_c0 n y)]
        by_cases hex : ∃ x ∈ xs, pred K x = true ∧ x ⊆ y
        · rw [decide_eq_true hex]
          rcases hex with ⟨x, hxs, hpx, hxy⟩
          rw [List.any_eq_true]
          refine ⟨upW x, List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hxs, hpx⟩, rfl⟩, ?_⟩
          rw [heq1, evalW_append_pre gs e1 (bitsVec n y) (upW x) (by rw [bitsVec_len]; exact hbd x hxs)]
          rw [hev x hxs y, decide_eq_true hxy]
        · rw [decide_eq_false hex]
          cases hany : ws.any (fun w => (evalW gs1 (bitsVec n y)).getD w false)
          · rfl
          · exfalso; apply hex
            rcases List.any_eq_true.mp hany with ⟨w, hw, hw1⟩
            rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
            rcases List.mem_filter.mp hx with ⟨hxs, hpx⟩
            rw [heq1, evalW_append_pre gs e1 (bitsVec n y) (upW x) (by rw [bitsVec_len]; exact hbd x hxs),
              hev x hxs y] at hw1
            exact ⟨x, hxs, hpx, of_decide_eq_true hw1⟩
      · rw [if_neg hrK, heq2]
        have hbdr := hbd1 r (by omega)
        rw [evalW_append_pre gs1 e2 (bitsVec n y) (bW1 r) (by rw [bitsVec_len]; exact hbdr)]
        exact hev1 r (by omega) y

private lemma build_suffix_ors (n L : Nat) (bW : Nat → Nat) :
    ∀ (k : Nat), k ≤ L →
      ∀ (gs : List Gate),
        ValidGates n gs →
        (∀ r < L, bW r < n + 2 + gs.length) →
        ∃ (gs' : List Gate) (T : Nat → Nat),
          (∃ extra, gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra = k) ∧
          ValidGates n gs' ∧
          (∀ r, T r < n + 2 + gs'.length) ∧
          (∀ y : Finset (Fin n),
            (∀ r ≥ L, (evalW gs' (bitsVec n y)).getD (T r) false = false) ∧
            (∀ r, L - k ≤ r → r < L →
              (evalW gs' (bitsVec n y)).getD (T r) false =
                decide (∃ s ∈ Finset.range L, r ≤ s ∧ (evalW gs (bitsVec n y)).getD (bW s) false = true))) := by
  intro k
  induction k with
  | zero =>
    intro _ gs hgs _
    refine ⟨gs, fun _ => n, ⟨[], by simp, rfl, rfl⟩, hgs, fun _ => by dsimp only; omega, fun y => ⟨?_, ?_⟩⟩
    · intro r _; rw [evalW_pre gs (bitsVec n y) n (by rw [bitsVec_len]; omega), bitsVec_c0]
    · intro r h1 h2; omega
  | succ k ih =>
    intro hk gs hgs hbd
    rcases ih (by omega) gs hgs hbd with ⟨gs1, T1, ⟨e1, heq1, hnot1, hpos1⟩, hval1, hbd1, hev1⟩
    let r0 := L - (k + 1)
    have hr0_lt : r0 < L := by omega
    have hb_r0 : bW r0 < n + 2 + gs1.length := by
      have := hbd r0 hr0_lt; rw [heq1, List.length_append]; omega
    have hT_next : T1 (r0 + 1) < n + 2 + gs1.length := hbd1 (r0 + 1)
    let oIdx := n + 2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.or, [bW r0, T1 (r0 + 1)]⟩]
    have hval2 : ValidGates n gs2 :=
      validGates_snoc n gs1 ⟨GateOp.or, [bW r0, T1 (r0 + 1)]⟩ hval1 (Or.inr (Or.inl rfl)) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
    let T2 : Nat → Nat := fun r => if r = r0 then oIdx else T1 r
    refine ⟨gs2, T2, ⟨e1 ++ [⟨GateOp.or, [bW r0, T1 (r0 + 1)]⟩], ?_, ?_, ?_⟩, hval2, ?_, fun y => ⟨?_, ?_⟩⟩
    · dsimp only [gs2]; rw [heq1, List.append_assoc]
    · rw [notCountL_append, hnot1]; rfl
    · rw [posCount_append, hpos1]; rfl
    · intro r; dsimp only [T2]
      by_cases hrr0 : r = r0
      · rw [if_pos hrr0]; simp [gs2, oIdx]
      · rw [if_neg hrr0]; have := hbd1 r; simp only [gs2, List.length_append, List.length_singleton]; omega
    · intro r hrL
      dsimp only [T2]
      rw [if_neg (by omega : r ≠ r0)]
      dsimp only [gs2]
      rw [evalW_append_pre gs1 _ (bitsVec n y) (T1 r) (by rw [bitsVec_len]; exact hbd1 r)]
      exact (hev1 y).1 r hrL
    · intro r hrlo hrhi
      dsimp only [T2]
      by_cases hrr0 : r = r0
      · rw [if_pos hrr0, hrr0]
        have hlast := evalW_snoc_last gs1 ⟨GateOp.or, [bW r0, T1 (r0 + 1)]⟩ (bitsVec n y)
        rw [bitsVec_len] at hlast
        change (evalW (gs1 ++ [⟨GateOp.or, [bW r0, T1 (r0 + 1)]⟩]) (bitsVec n y)).getD (n + 2 + gs1.length) false = _
        rw [hlast]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have hb_eq : (evalW gs1 (bitsVec n y)).getD (bW r0) false = (evalW gs (bitsVec n y)).getD (bW r0) false := by
          rw [heq1]
          exact evalW_append_pre gs e1 (bitsVec n y) (bW r0) (by rw [bitsVec_len]; exact hbd r0 hr0_lt)
        rw [hb_eq]
        have hT1_val : (evalW gs1 (bitsVec n y)).getD (T1 (r0 + 1)) false =
            decide (∃ s ∈ Finset.range L, r0 + 1 ≤ s ∧ (evalW gs (bitsVec n y)).getD (bW s) false = true) := by
          by_cases hnext : r0 + 1 < L
          · exact (hev1 y).2 (r0 + 1) (by omega) hnext
          · rw [(hev1 y).1 (r0 + 1) (by omega)]
            symm; exact decide_eq_false (by rintro ⟨s, hs, h1, _⟩; have := Finset.mem_range.mp hs; omega)
        rw [hT1_val]
        by_cases hnow : (evalW gs (bitsVec n y)).getD (bW r0) false = true
        · rw [hnow, Bool.true_or]
          symm; exact decide_eq_true ⟨r0, Finset.mem_range.mpr hr0_lt, le_refl _, hnow⟩
        · have hnowf : (evalW gs (bitsVec n y)).getD (bW r0) false = false := Bool.eq_false_iff.mpr hnow
          rw [hnowf, Bool.false_or]
          apply decide_eq_decide.mpr
          constructor
          · rintro ⟨s, hs, h1, h3⟩; exact ⟨s, hs, by omega, h3⟩
          · rintro ⟨s, hs, h1, h3⟩
            by_cases hsr0 : s = r0
            · rw [hsr0] at h3; exact False.elim (hnow h3)
            · exact ⟨s, hs, by omega, h3⟩
      · rw [if_neg hrr0]
        dsimp only [gs2]
        rw [evalW_append_pre gs1 _ (bitsVec n y) (T1 r) (by rw [bitsVec_len]; exact hbd1 r)]
        exact (hev1 y).2 r (by omega) hrhi

private lemma build_masked_ands (n : Nat) (dec hW : Nat → Nat) :
    ∀ (K : Nat) (gs : List Gate),
      ValidGates n gs →
      (∀ r < K, dec r < n + 2 + gs.length ∧ hW r < n + 2 + gs.length) →
      ∃ (gs' : List Gate) (mW : Nat → Nat),
        (∃ extra, gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra = K) ∧
        ValidGates n gs' ∧
        (∀ r < K, mW r < n + 2 + gs'.length) ∧
        (∀ r < K, ∀ y : Finset (Fin n),
          (evalW gs' (bitsVec n y)).getD (mW r) false =
            ((evalW gs (bitsVec n y)).getD (dec r) false && (evalW gs (bitsVec n y)).getD (hW r) false)) := by
  intro K
  induction K with
  | zero =>
    intro gs hgs _
    refine ⟨gs, fun _ => n, ⟨[], by simp, rfl, rfl⟩, hgs, fun _ h => by omega, fun _ h => by omega⟩
  | succ K ih =>
    intro gs hgs hbd
    rcases ih gs hgs (fun r hr => hbd r (by omega)) with ⟨gs1, mW1, ⟨e1, heq1, hnot1, hpos1⟩, hval1, hbd1, hev1⟩
    rcases hbd K (by omega) with ⟨hdecK, hhWK⟩
    have hdecK1 : dec K < n + 2 + gs1.length := by rw [heq1, List.length_append]; omega
    have hhWK1 : hW K < n + 2 + gs1.length := by rw [heq1, List.length_append]; omega
    let aIdx := n + 2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [dec K, hW K]⟩]
    have hval2 : ValidGates n gs2 :=
      validGates_snoc n gs1 ⟨GateOp.and, [dec K, hW K]⟩ hval1 (Or.inl rfl) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
    let mW2 : Nat → Nat := fun r => if r = K then aIdx else mW1 r
    refine ⟨gs2, mW2, ⟨e1 ++ [⟨GateOp.and, [dec K, hW K]⟩], ?_, ?_, ?_⟩, hval2, ?_, ?_⟩
    · dsimp only [gs2]; rw [heq1, List.append_assoc]
    · rw [notCountL_append, hnot1]; rfl
    · rw [posCount_append, hpos1]; rfl
    · intro r hr; dsimp only [mW2]
      by_cases hrK : r = K
      · rw [if_pos hrK]; simp [gs2, aIdx]
      · rw [if_neg hrK]; have := hbd1 r (by omega); simp only [gs2, List.length_append, List.length_singleton]; omega
    · intro r hr y; dsimp only [mW2]
      by_cases hrK : r = K
      · rw [if_pos hrK, hrK]
        have hlast := evalW_snoc_last gs1 ⟨GateOp.and, [dec K, hW K]⟩ (bitsVec n y)
        rw [bitsVec_len] at hlast
        change (evalW (gs1 ++ [⟨GateOp.and, [dec K, hW K]⟩]) (bitsVec n y)).getD (n + 2 + gs1.length) false = _
        rw [hlast]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [heq1, evalW_append_pre gs e1 (bitsVec n y) (dec K) (by rw [bitsVec_len]; exact hdecK)]
        rw [evalW_append_pre gs e1 (bitsVec n y) (hW K) (by rw [bitsVec_len]; exact hhWK)]
      · rw [if_neg hrK]
        dsimp only [gs2]
        rw [evalW_append_pre gs1 _ (bitsVec n y) (mW1 r) (by rw [bitsVec_len]; exact hbd1 r (by omega))]
        exact hev1 r (by omega) y

private lemma realize_stage_circuit {n m b : Nat} (S : Finset (Finset (Fin n)))
    (hS : S.Nonempty) (base : Finset (Fin n) → Nat) (g : Finset (Fin n) → Fin m → Bool)
    (hbase_lt : ∀ x ∈ S, base x < 2 ^ b)
    (hbase_mono : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → base x ≤ base y)
    (hg_mono : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → base x = base y → ∀ j, g x j = true → g y j = true) :
    ∃ (C : Circuit) (a : Fin m → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
      C.size ≤ 32 * (n + 1) * (m + 1) * (S.card + 1) ∧
      ∀ x ∈ S, ∀ j : Fin m, (C.wires (bitsVec n x)).getD (a j).val false = g x j := by
  let vals : List Nat := (S.image base).sort (· ≤ ·)
  have hvals_nd : vals.Nodup := Finset.sort_nodup (S.image base) (· ≤ ·)
  have hvals_pw : vals.Pairwise (· ≤ ·) := Finset.pairwise_sort (S.image base) (· ≤ ·)
  let L := vals.length
  have hL_eq : L = (S.image base).card := Finset.length_sort (· ≤ ·)
  have hL_ge1 : 1 ≤ L := by
    rcases hS with ⟨x0, hx0⟩
    have : 0 < (S.image base).card := Finset.card_pos.mpr ⟨base x0, Finset.mem_image_of_mem base hx0⟩
    omega
  have hL_le_S : L ≤ S.card := by rw [hL_eq]; exact Finset.card_image_le
  have hL_le_pow : L ≤ 2 ^ b := by
    rw [hL_eq]
    have hsub : S.image base ⊆ Finset.range (2 ^ b) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
      exact Finset.mem_range.mpr (hbase_lt x hx)
    exact (Finset.card_le_card hsub).trans (by simp)
  rcases exists_min_pow2 L b hL_ge1 hL_le_pow with ⟨b', hb'_le, hL_le_2b', h2b'_le⟩
  let cbase : Finset (Fin n) → Nat := fun x => vals.idxOf (base x)
  have hmem_vals : ∀ x ∈ S, base x ∈ vals := fun x hx =>
    (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_image_of_mem base hx)
  have hcbase_lt : ∀ x ∈ S, cbase x < L := fun x hx => List.idxOf_lt_length_iff.mpr (hmem_vals x hx)
  have hvals_get : ∀ x (hx : x ∈ S), vals[cbase x]'(hcbase_lt x hx) = base x := fun x hx =>
    List.getElem_idxOf (hcbase_lt x hx)
  have hvals_strict : ∀ i j (hi : i < L) (hj : j < L), i < j → vals[i]'hi < vals[j]'hj := by
    intro i j hi hj hij
    have hle := List.pairwise_iff_getElem.mp hvals_pw i j hi hj hij
    have hne := List.pairwise_iff_getElem.mp hvals_nd i j hi hj hij
    omega
  have hcbase_mono : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → cbase x ≤ cbase y := by
    intro x hx y hy hxy
    have hb := hbase_mono x hx y hy hxy
    by_contra hgt
    have hlt := hvals_strict (cbase y) (cbase x) (hcbase_lt y hy) (hcbase_lt x hx) (by omega)
    rw [hvals_get y hy, hvals_get x hx] at hlt
    omega
  have hcbase_eq_iff : ∀ x ∈ S, ∀ y ∈ S, cbase x = cbase y → base x = base y := by
    intro x hx y hy heq
    have h1 := hvals_get x hx
    have h2 := hvals_get y hy
    rw [← h1, ← h2]
    simp only [heq]
  let xs : List (Finset (Fin n)) := S.toList
  have hxs_len : xs.length = S.card := Finset.length_toList S
  have hxs_mem : ∀ x, x ∈ xs ↔ x ∈ S := fun x => Finset.mem_toList
  rcases build_up_wires n xs [] (validGates_nil n) with ⟨gsA, upW, ⟨eA, heqA, hnotA, hposA⟩, hvalA, hbdA, hevA⟩
  rw [hxs_len] at hposA
  let predB : Nat → Finset (Fin n) → Bool := fun r x => decide (cbase x = r)
  rcases build_bucket_ors n upW xs predB L gsA hvalA hbdA hevA with
    ⟨gsB1, bW, ⟨eB1, heqB1, hnotB1, hposB1⟩, hvalB1, hbdB1, hevB1⟩
  have hposB1_le : posCount eB1 ≤ S.card := by
    have hd := sum_filter_disjoint xs L predB (fun x _ r1 r2 _ _ h1 h2 => by
      have e1 := of_decide_eq_true h1; have e2 := of_decide_eq_true h2; omega)
    omega
  rcases build_suffix_ors n L bW L (le_refl L) gsB1 hvalB1 hbdB1 with
    ⟨gsB2, T, ⟨eB2, heqB2, hnotB2, hposB2⟩, hvalB2, hbdB2, hevB2⟩
  have hT_eval : ∀ y ∈ S, ∀ r, 1 ≤ r → r < 2 ^ b' →
      (evalW gsB2 (bitsVec n y)).getD (T r) false = decide (r ≤ cbase y) := by
    intro y hy r hr1 hr2
    by_cases hrL : r < L
    · rw [(hevB2 y).2 r (by omega) hrL]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨s, hs, hrs, hbs⟩
        have hsL := Finset.mem_range.mp hs
        rw [hevB1 s hsL y] at hbs
        rcases of_decide_eq_true hbs with ⟨x, hxs, hpx, hxy⟩
        have hxS : x ∈ S := (hxs_mem x).mp hxs
        have hcx : cbase x = s := of_decide_eq_true hpx
        have hcm := hcbase_mono x hxS y hy hxy
        omega
      · intro hle
        refine ⟨cbase y, Finset.mem_range.mpr (hcbase_lt y hy), hle, ?_⟩
        rw [hevB1 (cbase y) (hcbase_lt y hy) y]
        exact decide_eq_true ⟨y, (hxs_mem y).mpr hy, decide_eq_true rfl, le_refl _⟩
    · rw [(hevB2 y).1 r (by omega)]
      have hcy := hcbase_lt y hy
      symm; exact decide_eq_false (by omega)
  rcases buildDecoder_spec n b' gsB2 T hvalB2 (fun r _ _ => hbdB2 r) with
    ⟨⟨eC, heqC, hnotC, hposC⟩, hvalC, hbdC, hevC⟩
  set decRes := buildDecoder n b' gsB2 T
  have hdec_eval : ∀ y ∈ S, ∀ r < 2 ^ b',
      (evalW decRes.1 (bitsVec n y)).getD (decRes.2 r) false = decide (r = cbase y) :=
    fun y hy r hr => hevC (bitsVec n y) (cbase y) (bitsVec_len n y) (bitsVec_c1 n y)
      (lt_of_lt_of_le (hcbase_lt y hy) hL_le_2b') (hT_eval y hy) r hr
  have hup_at_C : ∀ x ∈ xs, upW x < n + 2 + decRes.1.length := fun x hx => by
    have := hbdA x hx
    rw [heqC, heqB2, heqB1, List.length_append, List.length_append, List.length_append]; omega
  have hup_ev_C : ∀ x ∈ xs, ∀ y : Finset (Fin n),
      (evalW decRes.1 (bitsVec n y)).getD (upW x) false = decide (x ⊆ y) := fun x hx y => by
    have hpre : decRes.1 = gsA ++ (eB1 ++ eB2 ++ eC) := by
      rw [heqC, heqB2, heqB1]; simp only [List.append_assoc]
    rw [hpre, evalW_append_pre gsA _ (bitsVec n y) (upW x) (by rw [bitsVec_len]; exact hbdA x hx)]
    exact hevA x hx y
  have build_one_tap : ∀ (j : Fin m) (gs : List Gate),
      ValidGates n gs →
      (∃ extra0, gs = decRes.1 ++ extra0) →
      ∃ (gs' : List Gate) (outW : Nat),
        (∃ extra, gs' = gs ++ extra ∧ notCountL extra = 0 ∧ posCount extra ≤ 3 * S.card) ∧
        ValidGates n gs' ∧
        outW < n + 2 + gs'.length ∧
        ∀ y ∈ S, (evalW gs' (bitsVec n y)).getD outW false = g y j := by
    intro j gs hgs ⟨extra0, hgs_eq⟩
    have hup_bd : ∀ x ∈ xs, upW x < n + 2 + gs.length := fun x hx => by
      have := hup_at_C x hx; rw [hgs_eq, List.length_append]; omega
    have hup_ev : ∀ x ∈ xs, ∀ y : Finset (Fin n), (evalW gs (bitsVec n y)).getD (upW x) false = decide (x ⊆ y) :=
      fun x hx y => by
        rw [hgs_eq, evalW_append_pre decRes.1 extra0 (bitsVec n y) (upW x) (by rw [bitsVec_len]; exact hup_at_C x hx)]
        exact hup_ev_C x hx y
    let predJ : Nat → Finset (Fin n) → Bool := fun r x => decide (cbase x = r ∧ g x j = true)
    rcases build_bucket_ors n upW xs predJ L gs hgs hup_bd hup_ev with
      ⟨gs1, hW, ⟨e1, heq1, hnot1, hpos1⟩, hval1, hbd1, hev1⟩
    have hpos1_le : posCount e1 ≤ S.card := by
      have hd := sum_filter_disjoint xs L predJ (fun x _ r1 r2 _ _ h1 h2 => by
        have p1 := of_decide_eq_true h1; have p2 := of_decide_eq_true h2; omega)
      omega
    have hbd_dec_hW : ∀ r < L, decRes.2 r < n + 2 + gs1.length ∧ hW r < n + 2 + gs1.length := fun r hr => by
      have h1 := hbdC r (lt_of_lt_of_le hr hL_le_2b')
      have h2 := hbd1 r hr
      exact ⟨by rw [heq1, hgs_eq, List.length_append, List.length_append]; omega, h2⟩
    rcases build_masked_ands n decRes.2 hW L gs1 hval1 hbd_dec_hW with
      ⟨gs2, mW, ⟨e2, heq2, hnot2, hpos2⟩, hval2, hbd2, hev2⟩
    let mList : List Nat := (List.range L).map mW
    have hmList_bd : ∀ w ∈ mList, w < n + 2 + gs2.length := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨r, hr, rfl⟩
      exact hbd2 r (List.mem_range.mp hr)
    rcases appendOrList_spec n gs2 mList hval2 hmList_bd with
      ⟨⟨e3, heq3, hnot3, hpos3⟩, hval3, hout3, heval3⟩
    set res3 := appendOrList n gs2 mList
    refine ⟨res3.1, res3.2, ⟨e1 ++ e2 ++ e3, ?_, ?_, ?_⟩, hval3, hout3, fun y hy => ?_⟩
    · rw [heq3, heq2, heq1]; simp only [List.append_assoc]
    · rw [notCountL_append, notCountL_append, hnot1, hnot2, hnot3]
    · rw [posCount_append, posCount_append]
      have hlen : mList.length = L := by simp [mList]
      omega
    · rw [heval3 (bitsVec n y) (bitsVec_len n y) (bitsVec_c0 n y)]
      have hdec_gs1 : ∀ r < L, (evalW gs1 (bitsVec n y)).getD (decRes.2 r) false = decide (r = cbase y) := by
        intro r hr
        have hpre : gs1 = decRes.1 ++ (extra0 ++ e1) := by rw [heq1, hgs_eq, List.append_assoc]
        rw [hpre, evalW_append_pre decRes.1 _ (bitsVec n y) (decRes.2 r)
          (by rw [bitsVec_len]; exact hbdC r (lt_of_lt_of_le hr hL_le_2b'))]
        exact hdec_eval y hy r (lt_of_lt_of_le hr hL_le_2b')
      cases hgy : g y j
      · cases hany : mList.any (fun w => (evalW gs2 (bitsVec n y)).getD w false)
        · rfl
        · exfalso
          rcases List.any_eq_true.mp hany with ⟨w, hw, hw1⟩
          rcases List.mem_map.mp hw with ⟨r, hr, rfl⟩
          have hrL : r < L := List.mem_range.mp hr
          rw [hev2 r hrL y, Bool.and_eq_true, hdec_gs1 r hrL, hev1 r hrL y] at hw1
          have hreq : r = cbase y := of_decide_eq_true hw1.1
          rcases of_decide_eq_true hw1.2 with ⟨x, hxs, hpx, hxy⟩
          rcases of_decide_eq_true hpx with ⟨hcx, hgx⟩
          have hxS : x ∈ S := (hxs_mem x).mp hxs
          have hbe : base x = base y := hcbase_eq_iff x hxS y hy (by omega)
          have hgy_t := hg_mono x hxS y hy hxy hbe j hgx
          rw [hgy] at hgy_t; exact Bool.noConfusion hgy_t
      · rw [List.any_eq_true]
        refine ⟨mW (cbase y), List.mem_map.mpr ⟨cbase y, List.mem_range.mpr (hcbase_lt y hy), rfl⟩, ?_⟩
        rw [hev2 (cbase y) (hcbase_lt y hy) y, Bool.and_eq_true, hdec_gs1 (cbase y) (hcbase_lt y hy),
          hev1 (cbase y) (hcbase_lt y hy) y]
        exact ⟨decide_eq_true rfl, decide_eq_true ⟨y, (hxs_mem y).mpr hy, decide_eq_true ⟨rfl, hgy⟩, le_refl _⟩⟩
  have build_all_taps : ∀ (k : Nat) (hk : k ≤ m),
      ∃ (gs' : List Gate) (outW : Nat → Nat),
        (∃ extra, gs' = decRes.1 ++ extra ∧ notCountL extra = 0 ∧ posCount extra ≤ 3 * k * S.card) ∧
        ValidGates n gs' ∧
        (∀ r < k, outW r < n + 2 + gs'.length) ∧
        (∀ r (hr : r < k), ∀ y ∈ S, (evalW gs' (bitsVec n y)).getD (outW r) false = g y ⟨r, lt_of_lt_of_le hr hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨decRes.1, fun _ => n, ⟨[], by simp, rfl, by simp [posCount]⟩, hvalC,
        fun _ h => by omega, fun _ h => by omega⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs1, out1, ⟨e1, heq1, hnot1, hpos1⟩, hval1, hbd1, hev1⟩
      rcases build_one_tap ⟨k, hk⟩ gs1 hval1 ⟨e1, heq1⟩ with ⟨gs2, owK, ⟨e2, heq2, hnot2, hpos2⟩, hval2, hbdK, hevK⟩
      let out2 : Nat → Nat := fun r => if r = k then owK else out1 r
      refine ⟨gs2, out2, ⟨e1 ++ e2, ?_, ?_, ?_⟩, hval2, ?_, ?_⟩
      · rw [heq2, heq1, List.append_assoc]
      · rw [notCountL_append, hnot1, hnot2]
      · rw [posCount_append]
        have : 3 * (k + 1) * S.card = 3 * k * S.card + 3 * S.card := by ring
        omega
      · intro r hr; dsimp only [out2]
        by_cases hrk : r = k
        · rw [if_pos hrk]; exact hbdK
        · rw [if_neg hrk, heq2, List.length_append]; have := hbd1 r (by omega); omega
      · intro r hr y hy; dsimp only [out2]
        by_cases hrk : r = k
        · rw [if_pos hrk]
          have hfin : (⟨r, lt_of_lt_of_le hr hk⟩ : Fin m) = ⟨k, hk⟩ := Fin.ext hrk
          rw [hfin]; exact hevK y hy
        · rw [if_neg hrk, heq2, evalW_append_pre gs1 e2 (bitsVec n y) (out1 r)
            (by rw [bitsVec_len]; exact hbd1 r (by omega))]
          exact hev1 r (by omega) y hy
  rcases build_all_taps m (le_refl m) with ⟨gsF, outF, ⟨eD, heqD, hnotD, hposD⟩, hvalF, hbdF, hevF⟩
  let C : Circuit := ⟨gsF, 0⟩
  have hC_valid := validGates_to_valid n gsF hvalF
  have hgsF_eq : gsF = eA ++ eB1 ++ eB2 ++ eC ++ eD := by
    rw [heqD, heqC, heqB2, heqB1, heqA, List.nil_append]
  have hnotF : notCount C ≤ b := by
    rw [notCount_eq_notCountL]
    change notCountL gsF ≤ b
    rw [hgsF_eq, notCountL_append, notCountL_append, notCountL_append, notCountL_append,
      hnotA, hnotB1, hnotB2, hnotC, hnotD]
    omega
  have hposF : posCount gsF ≤ (n + 3 * m + 10) * S.card := by
    rw [hgsF_eq, posCount_append, posCount_append, posCount_append, posCount_append]
    have hmul_eq : (n + 3 * m + 10) * S.card = n * S.card + 3 * m * S.card + 10 * S.card := by ring
    omega
  have hC_size : C.size ≤ 32 * (n + 1) * (m + 1) * (S.card + 1) := by
    change gsF.length ≤ _
    have hlen := posCount_add_notCountL gsF
    have hnot_le : notCountL gsF ≤ 2 * S.card := by
      rw [hgsF_eq, notCountL_append, notCountL_append, notCountL_append, notCountL_append,
        hnotA, hnotB1, hnotB2, hnotC, hnotD]
      have := nat_le_two_pow b'
      omega
    have hlin : (n + 3 * m + 12) * S.card ≤ 32 * (n + 1) * (m + 1) * (S.card + 1) := by
      have hcoef : n + 3 * m + 12 ≤ 32 * (n + 1) * (m + 1) := by nlinarith
      have h1 := Nat.mul_le_mul_right S.card hcoef
      have h2 := Nat.mul_le_mul_left (32 * (n + 1) * (m + 1)) (Nat.le_succ S.card)
      exact h1.trans h2
    have hsum_eq : (n + 3 * m + 10) * S.card + 2 * S.card = (n + 3 * m + 12) * S.card := by ring
    omega
  refine ⟨C, fun j => ⟨outF j.val, hbdF j.val j.isLt⟩, hC_valid.1, hC_valid.2.1, hC_valid.2.2,
    hnotF, hC_size, fun x hx j => ?_⟩
  exact hevF j.val j.isLt x hx

private lemma main_body (n m b : Nat) (S : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Fin m → Bool) (w : Finset (Fin n) → Fin m → Nat) :
    let X := Finset (Fin n)
    let val := fun (C : Circuit) (a : Fin m → Fin (n + 2 + C.size)) (x : X) (j : Fin m) =>
      (C.wires (bitsVec n x)).getD (a j).val false
    let valid := fun (C : Circuit) => FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b
    let E := X × X × Fin m
    let legal := fun (P : List (List E)) =>
      (∀ c ∈ P, c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
        ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
          f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
      ∀ x ∈ S, ∀ j : Fin m, (P.flatten.filter (fun e =>
        decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length ≤ w x j
    let loss := fun (C : Circuit) (a : Fin m → Fin (n + 2 + C.size)) => S.sum (fun x =>
      (Finset.univ : Finset (Fin m)).sum (fun j => if val C a x j = f x j then 0 else w x j))
    let d := 2 ^ b - 1
    (∀ C a P, valid C → legal P → P.flatten.length ≤ loss C a + d * P.length) ∧
    ∃ C a P, valid C ∧ C.size ≤ 32 * (n + 1) * (m + 1) * (S.card + 1) ∧
      legal P ∧ (∀ c ∈ P, d < c.length) ∧ P.flatten.length = loss C a + d * P.length := by
  intro X val valid E legal loss d
  constructor
  · intro C a P hval hleg
    exact weak_duality n m b S f w C a P hval.1 hval.2.1 hval.2.2.2 hleg.1 hleg.2
  · by_cases hSe : S = ∅
    · subst hSe
      let C : Circuit := ⟨[], 0⟩
      let a : Fin m → Fin (n + 2 + C.size) := fun _ => ⟨n, by simp [C, Circuit.size]⟩
      refine ⟨C, a, [], ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩,
        fun _ h => by simp at h, ?_⟩
      · intro g hg; simp [C] at hg
      · intro j hj; simp [C, Circuit.size] at hj
      · simp [C, Circuit.size]
      · simp [C, notCount]
      · simp [C, Circuit.size]
      · simp [loss]
    · have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      rcases strong_duality_stage (b := b) S hS f w with ⟨P, base, g, hP, hblt, hbmono, hgmono, hPeq⟩
      rcases realize_stage_circuit (b := b) S hS base g hblt hbmono hgmono with
        ⟨C, a, hfan, hrb, hout, hnot, hsize, hvalC⟩
      refine ⟨C, a, P, ⟨hfan, hrb, hout, hnot⟩, hsize, ⟨hP.2.1, hP.2.2⟩, hP.1, ?_⟩
      have hloss_eq : loss C a =
          S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j => if g x j = f x j then 0 else w x j)) :=
        Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun j _ => by
          simp only [val, hvalC x hx j]
      rw [hloss_eq]
      exact hPeq

private lemma decide_eq_of_dec (p : Prop) (d1 d2 : Decidable p) :
    @decide p d1 = @decide p d2 := by
  by_cases h : p <;> simp [h]

private lemma ite_eq_of_dec {α : Type} (p : Prop) (d1 d2 : Decidable p) (a b : α) :
    @ite α p d1 a b = @ite α p d2 a b := by
  by_cases h : p <;> simp [h]

private lemma main_bridge :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (n m b : Nat) (S : Finset (Finset (Fin n))) (f : Finset (Fin n) → Fin m → Bool)
      (w : Finset (Fin n) → Fin m → Nat),
      let X := Finset (Fin n)
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
      let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
      let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin m) =>
        (C.wires (input x)).getD (a j).val false
      let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
        PEqualNP.NotBracket.notCount C ≤ b
      let E := X × X × Fin m
      let Cert := List (List E)
      let legal := fun (P : Cert) =>
        (∀ c ∈ P, c.Pairwise (fun (e e' : E) => e.2.1 ⊆ e'.1) ∧
          ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
            f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
        ∀ x ∈ S, ∀ j : Fin m, (P.flatten.filter (fun e =>
          decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length ≤ w x j
      let loss := fun (C : Circ) (a : taps C) => S.sum (fun x =>
        (Finset.univ : Finset (Fin m)).sum (fun j => if val C a x j = f x j then 0 else w x j))
      let d := 2^b-1
      (∀ (C : Circ) (a : taps C) (P : Cert), valid C → legal P →
          P.flatten.length ≤ loss C a + d*P.length) ∧
      ∃ (C : Circ) (a : taps C) (P : Cert), valid C ∧
        C.size ≤ 32*(n+1)*(m+1)*(S.card+1) ∧ legal P ∧ (∀ c ∈ P, d < c.length) ∧
        P.flatten.length = loss C a + d*P.length := by
  intro n m b S f w
  have hbody := main_body n m b S f w
  dsimp only at hbody ⊢
  have hinput : ∀ x : Finset (Fin n),
      List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) ++ [false, true] =
      bitsVec n x := by
    intro x
    unfold bitsVec
    congr 1
    apply List.ofFn_inj.mpr
    funext i
    exact decide_eq_of_dec _ _ _
  have hfilter_len : ∀ (L : List (Finset (Fin n) × Finset (Fin n) × Fin m)) (x : Finset (Fin n)) (j : Fin m)
      (d1 d2 : ∀ e : Finset (Fin n) × Finset (Fin n) × Fin m, Decidable (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x))),
      (L.filter (fun e => @decide _ (d1 e))).length = (L.filter (fun e => @decide _ (d2 e))).length := by
    intro L x j d1 d2
    exact congrArg List.length (List.filter_congr fun e _ => decide_eq_of_dec _ _ _)
  have hloss : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin m → Fin (n + 2 + C.size)),
      S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
        @ite Nat ((C.wires (List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) ++ [false, true])).getD (a j).val false = f x j)
          (Classical.propDecidable _) 0 (w x j))) =
      S.sum (fun x => (Finset.univ : Finset (Fin m)).sum (fun j =>
        if (C.wires (bitsVec n x)).getD (a j).val false = f x j then 0 else w x j)) := by
    intro C a
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hinput x]
  constructor
  · intro C a P hval hleg
    have hleg' : (∀ c ∈ P, c.Pairwise (fun e e' => e.2.1 ⊆ e'.1) ∧
        ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
          f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
        ∀ x ∈ S, ∀ j : Fin m, (P.flatten.filter (fun e =>
          decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length ≤ w x j := by
      refine ⟨hleg.1, fun x hx j => ?_⟩
      exact (hfilter_len P.flatten x j _ _).trans_le (hleg.2 x hx j)
    have h1 := hbody.1 C a P hval hleg'
    rw [hloss C a]
    exact h1
  · rcases hbody.2 with ⟨C, a, P, hval, hsize, hleg, hlen, heq⟩
    refine ⟨C, a, P, hval, hsize, ⟨hleg.1, fun x hx j => ?_⟩, hlen, ?_⟩
    · exact (hfilter_len P.flatten x j _ _).trans_le (hleg.2 x hx j)
    · rw [hloss C a]; exact heq

end PEqualNP.Outside.L_meta_53157

theorem PEqualNP.Outside.L_meta_53157 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m b : Nat) (S : Finset (Finset (Fin n))) (f : Finset (Fin n) → Fin m → Bool)
  (w : Finset (Fin n) → Fin m → Nat),
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin m) =>
    (C.wires (input x)).getD (a j).val false
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let E := X × X × Fin m
  let Cert := List (List E)
  let legal := fun (P : Cert) =>
    (∀ c ∈ P, c.Pairwise (fun (e e' : E) => e.2.1 ⊆ e'.1) ∧
      ∀ e ∈ c, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.1 ⊆ e.2.1 ∧
        f e.1 e.2.2 = true ∧ f e.2.1 e.2.2 = false) ∧
    ∀ x ∈ S, ∀ j : Fin m, (P.flatten.filter (fun e =>
      decide (e.2.2 = j ∧ (e.1 = x ∨ e.2.1 = x)))).length ≤ w x j
  let loss := fun (C : Circ) (a : taps C) => S.sum (fun x =>
    (Finset.univ : Finset (Fin m)).sum (fun j => if val C a x j = f x j then 0 else w x j))
  let d := 2^b-1
  (∀ (C : Circ) (a : taps C) (P : Cert), valid C → legal P →
      P.flatten.length ≤ loss C a + d*P.length) ∧
  ∃ (C : Circ) (a : taps C) (P : Cert), valid C ∧
    C.size ≤ 32*(n+1)*(m+1)*(S.card+1) ∧ legal P ∧ (∀ c ∈ P, d < c.length) ∧
    P.flatten.length = loss C a + d*P.length :=
  PEqualNP.Outside.L_meta_53157.main_bridge
