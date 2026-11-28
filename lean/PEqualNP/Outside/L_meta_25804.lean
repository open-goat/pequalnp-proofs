import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25804

open Finset

def z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem z_true : z true = 1 := rfl
theorem z_false : z false = 0 := rfl

theorem z_xor (a b : Bool) : z (xor a b) = z a + z b := by
  cases a <;> cases b <;> decide

theorem z_dec (q : ZMod 2) : z (decide (q = 1)) = q := by
  revert q; decide

theorem z_inj {a b : Bool} (h : z a = z b) : a = b := by
  revert h; cases a <;> cases b <;> decide

def sg (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  revert a b; decide

theorem sg_zero : sg 0 = 1 := rfl

theorem sg_sum {ι : Type} (S : Finset ι) (f : ι → ZMod 2) :
    sg (∑ i ∈ S, f i) = ∏ i ∈ S, sg (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sg_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sg_add, ih]

def dot {s : ℕ} (u v : Fin s → ZMod 2) : ZMod 2 := ∑ i, u i * v i

theorem dot_add_right {s : ℕ} (u v w : Fin s → ZMod 2) :
    dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem univ_zmod2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

theorem sum_zmod2 (f : ZMod 2 → ℤ) : ∑ a, f a = f 0 + f 1 := by
  rw [univ_zmod2, Finset.sum_pair (by decide)]

theorem charsum {s : ℕ} (u : Fin s → ZMod 2) :
    ∑ p : Fin s → ZMod 2, sg (dot p u) = if u = 0 then 2 ^ s else 0 := by
  have h1 : ∀ p : Fin s → ZMod 2, sg (dot p u) = ∏ i, sg (p i * u i) := fun p => sg_sum _ _
  simp_rw [h1]
  have h3 := Finset.prod_univ_sum (fun _ : Fin s => (Finset.univ : Finset (ZMod 2)))
    (fun i a => sg (a * u i))
  rw [Fintype.piFinset_univ] at h3
  rw [← h3]
  have h2 : ∀ i, ∑ a : ZMod 2, sg (a * u i) = if u i = 0 then 2 else 0 := by
    intro i; rw [sum_zmod2]; generalize u i = q; revert q; decide
  simp_rw [h2]
  split_ifs with hu
  · subst hu; simp
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push Not at h; exact hu (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem add_eq_zero_iff2 {s : ℕ} (x w : Fin s → ZMod 2) : x + w = 0 ↔ x = w := by
  have h : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h]

theorem inversion {s : ℕ} (F : (Fin s → ZMod 2) → (Fin s → ZMod 2) → ZMod 2)
    (w1 w2 : Fin s → ZMod 2) :
    ∑ p, ∑ q, (∑ x, ∑ y, sg (F x y + dot p x + dot q y)) * sg (dot p w1 + dot q w2) =
      4 ^ s * sg (F w1 w2) := by
  have key : ∀ p q x y, sg (F x y + dot p x + dot q y) * sg (dot p w1 + dot q w2) =
      sg (F x y) * (sg (dot p (x + w1)) * sg (dot q (y + w2))) := by
    intros; simp only [dot_add_right, sg_add]; ring
  calc _ = ∑ p, ∑ q, ∑ x, ∑ y, sg (F x y) * (sg (dot p (x + w1)) * sg (dot q (y + w2))) := by
        simp_rw [Finset.sum_mul, key]
    _ = ∑ pq : (Fin s → ZMod 2) × (Fin s → ZMod 2), ∑ xy : (Fin s → ZMod 2) × (Fin s → ZMod 2),
          sg (F xy.1 xy.2) * (sg (dot pq.1 (xy.1 + w1)) * sg (dot pq.2 (xy.2 + w2))) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ xy : (Fin s → ZMod 2) × (Fin s → ZMod 2), ∑ pq : (Fin s → ZMod 2) × (Fin s → ZMod 2),
          sg (F xy.1 xy.2) * (sg (dot pq.1 (xy.1 + w1)) * sg (dot pq.2 (xy.2 + w2))) :=
        Finset.sum_comm
    _ = ∑ x, ∑ y, sg (F x y) * ((∑ p, sg (dot p (x + w1))) * (∑ q, sg (dot q (y + w2)))) := by
        simp only [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, sg (F x y) * ((if x = w1 then 2 ^ s else 0) * (if y = w2 then 2 ^ s else 0)) := by
        simp only [charsum, add_eq_zero_iff2]
    _ = 4 ^ s * sg (F w1 w2) := by
        simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        rw [show (4 : ℤ) ^ s = 2 ^ s * 2 ^ s by rw [← mul_pow]; norm_num]; ring

def zr {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (x y : Fin s → ZMod 2) (i : Fin s) : ZMod 2 :=
  (x i + ∑ j ∈ (Finset.Iio i).attach, A i j.1 * zr A B x y j.1) *
    (y i + ∑ j ∈ (Finset.Iio i).attach, B i j.1 * zr A B x y j.1)
termination_by i.val
decreasing_by all_goals (have h := Finset.mem_Iio.mp j.2; exact h)

theorem zr_eq {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (x y : Fin s → ZMod 2) (i : Fin s) :
    zr A B x y i = (x i + ∑ j ∈ Finset.Iio i, A i j * zr A B x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * zr A B x y j) := by
  rw [zr, Finset.sum_attach (Finset.Iio i) (fun j => A i j * zr A B x y j),
    Finset.sum_attach (Finset.Iio i) (fun j => B i j * zr A B x y j)]

theorem zr_unique {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (x y : Fin s → ZMod 2)
    (G : Fin s → ZMod 2)
    (hG : ∀ i, G i = (x i + ∑ j ∈ Finset.Iio i, A i j * G j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * G j)) :
    ∀ k, ∀ i : Fin s, i.val = k → G i = zr A B x y i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    rw [hG i, zr_eq]
    have hs : ∀ j ∈ Finset.Iio i, G j = zr A B x y j := fun j hj =>
      ih j.val (by have h := Finset.mem_Iio.mp hj; rw [← hi]; exact h) j rfl
    congr 1 <;> congr 1 <;> exact Finset.sum_congr rfl (fun j hj => by rw [hs j hj])

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepf x := rfl

theorem stepf_len (w : List Bool) (g : Gate) : (stepf w g).length = w.length + 1 := by
  simp [stepf]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepf w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, stepf_len, List.length_cons]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepf w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepf w g) (by rw [stepf_len]; omega), stepf,
      List.getD_append _ _ _ _ hi]

theorem fold_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j) :
    (gs.foldl stepf w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map
        fun i => (gs.foldl stepf w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have h0 : ∀ i ∈ g.inputs, i < w.length := fun i hi => by simpa using hrb 0 (by simp) i hi
      rw [List.foldl_cons, fold_pre gs (stepf w g) _ (by rw [stepf_len]; omega)]
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [stepf, List.getD_append_right _ _ _ _ le_rfl]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [fold_pre gs _ i (by simp; have := h0 i hi; omega), List.getD_append _ _ _ _ (h0 i hi)]
    | succ j =>
      have hl : (stepf w g).length = w.length + 1 := stepf_len w g
      rw [List.foldl_cons, show w.length + (j + 1) = (stepf w g).length + j by omega]
      simp only [List.getD_cons_succ]
      apply ih (stepf w g) j (by simpa using hj)
      intro j' hj' i hi
      have := hrb (j' + 1) (by simpa using hj') i (by simpa using hi)
      omega

def WW (N : ℕ) (C : Circuit) (w : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem WW_in {N : ℕ} (C : Circuit) (w : ℕ) (hw : w < N) (x : Fin N → Bool) :
    WW N C w x = x ⟨w, hw⟩ := by
  unfold WW
  rw [wires_eq, fold_pre _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw),
    List.getElem_ofFn]

theorem WW_out {N : ℕ} (C : Circuit) (w : ℕ) (hw : N + C.gates.length ≤ w) (x : Fin N → Bool) :
    WW N C w x = false := by
  unfold WW
  rw [wires_eq]
  apply List.getD_eq_default
  rw [fold_len]; simpa using hw

theorem WW_gate {N : ℕ} (C : Circuit) (hrb : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin N → Bool) :
    WW N C (N + j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => WW N C i x) := by
  unfold WW
  rw [wires_eq]
  have := fold_gate C.gates (List.ofFn x) j hj
    (fun j hj i hi => by rw [List.length_ofFn]; exact hrb j hj i hi)
  rw [List.length_ofFn] at this
  exact this

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

def nl (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def SS (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => nl (gateAt C j) = true)

def pos (C : Circuit) (k : Fin (SS C).card) : ℕ := (SS C).orderEmbOfFin rfl k

theorem pos_mem (C : Circuit) (k : Fin (SS C).card) : pos C k ∈ SS C :=
  Finset.orderEmbOfFin_mem _ _ _

theorem pos_lt_iff (C : Circuit) (k k' : Fin (SS C).card) : pos C k < pos C k' ↔ k < k' :=
  ((SS C).orderEmbOfFin rfl).lt_iff_lt

theorem pos_surj (C : Circuit) (j : ℕ) (hj : j ∈ SS C) : ∃ k, pos C k = j := by
  have : j ∈ Set.range ((SS C).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hj
  obtain ⟨k, hk⟩ := this
  exact ⟨k, hk⟩

theorem card_SS (C : Circuit) : (SS C).card = C.gates.countP nl := by
  unfold SS gateAt
  generalize C.gates = l
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [Finset.card_filter] at ih ⊢
    rw [List.length_cons, Finset.sum_range_succ', List.countP_cons, ← ih]
    simp [List.getD_cons_succ, List.getD_cons_zero]

theorem exp2 (f : List Bool → Bool) (a b : Bool) :
    z (f [a, b]) = z (f [false, false]) + (z (f [true, false]) + z (f [false, false])) * z a +
      (z (f [false, true]) + z (f [false, false])) * z b +
      (z (f [false, false]) + z (f [false, true]) + z (f [true, false]) + z (f [true, true])) *
        (z a * z b) := by
  cases h1 : f [false, false] <;> cases h2 : f [false, true] <;> cases h3 : f [true, false] <;>
    cases h4 : f [true, true] <;> cases a <;> cases b <;> simp only [h1, h2, h3, h4] <;> decide

theorem exp1 (f : List Bool → Bool) (a : Bool) :
    z (f [a]) = z (f [false]) + (z (f [true]) + z (f [false])) * z a := by
  cases h1 : f [false] <;> cases h2 : f [true] <;> cases a <;> simp only [h1, h2] <;> decide

theorem coef_nl (g : Gate) (h : nl g = true) :
    z (g.op.eval [false,false]) + z (g.op.eval [false,true]) + z (g.op.eval [true,false]) +
      z (g.op.eval [true,true]) = 1 := by
  unfold nl at h
  rw [Bool.and_eq_true] at h
  have h2 := congrArg z h.2
  rw [z_xor, z_xor, z_xor, z_true] at h2
  rw [← h2]; ring

theorem coef_lin (g : Gate) (h : nl g = false) (hl : g.inputs.length = 2) :
    z (g.op.eval [false,false]) + z (g.op.eval [false,true]) + z (g.op.eval [true,false]) +
      z (g.op.eval [true,true]) = 0 := by
  unfold nl at h
  rw [show (g.inputs.length == 2) = true by simp [hl], Bool.true_and] at h
  have h2 := congrArg z h
  rw [z_xor, z_xor, z_xor, z_false] at h2
  rw [← h2]; ring

def i1 (C : Circuit) (k : Fin (SS C).card) : ℕ := (gateAt C (pos C k)).inputs.getD 0 0
def i2 (C : Circuit) (k : Fin (SS C).card) : ℕ := (gateAt C (pos C k)).inputs.getD 1 0
def ev (C : Circuit) (k : Fin (SS C).card) (a b : Bool) : ZMod 2 :=
  z ((gateAt C (pos C k)).op.eval [a, b])
def bet (C : Circuit) (k : Fin (SS C).card) : ZMod 2 := ev C k false true + ev C k false false
def alp (C : Circuit) (k : Fin (SS C).card) : ZMod 2 := ev C k true false + ev C k false false
def GG (N : ℕ) (C : Circuit) (k : Fin (SS C).card) (x : Fin N → Bool) : ZMod 2 :=
  (z (WW N C (i1 C k) x) + bet C k) * (z (WW N C (i2 C k) x) + alp C k)

theorem nl_pos (C : Circuit) (k : Fin (SS C).card) : nl (gateAt C (pos C k)) = true := by
  have := pos_mem C k
  simp only [SS, Finset.mem_filter] at this
  exact this.2

theorem pos_lt_len (C : Circuit) (k : Fin (SS C).card) : pos C k < C.gates.length := by
  have := pos_mem C k
  simp only [SS, Finset.mem_filter, Finset.mem_range] at this
  exact this.1

theorem inputs_eq (C : Circuit) (k : Fin (SS C).card) :
    (gateAt C (pos C k)).inputs = [i1 C k, i2 C k] := by
  have h := nl_pos C k
  unfold nl at h
  rw [Bool.and_eq_true] at h
  have hl : (gateAt C (pos C k)).inputs.length = 2 := by simpa using h.1
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  simp only [i1, i2, hab, List.getD_cons_zero, List.getD_cons_succ]

theorem comb {N s : ℕ} (c1 c2 e α β : ZMod 2) (l1 l2 : Fin N → ZMod 2) (μ1 μ2 : Fin s → ZMod 2)
    (G : Fin s → (Fin N → Bool) → ZMod 2) (Wp Wq Ww : (Fin N → Bool) → ZMod 2)
    (h1 : ∀ x, Wp x = c1 + ∑ r, l1 r * z (x r) + ∑ k, μ1 k * G k x)
    (h2 : ∀ x, Wq x = c2 + ∑ r, l2 r * z (x r) + ∑ k, μ2 k * G k x)
    (h : ∀ x, Ww x = e + α * Wp x + β * Wq x) :
    ∀ x, Ww x = (e + α * c1 + β * c2) + ∑ r, (α * l1 r + β * l2 r) * z (x r) +
      ∑ k, (α * μ1 k + β * μ2 k) * G k x := by
  intro x
  rw [h, h1, h2]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem form_exists (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ w, ∃ (c : ZMod 2) (l : Fin N → ZMod 2) (μ : Fin (SS C).card → ZMod 2),
      (∀ x, z (WW N C w x) = c + ∑ r, l r * z (x r) + ∑ k, μ k * GG N C k x) ∧
      ∀ k, μ k ≠ 0 → N + pos C k ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hw : w < N
  · refine ⟨0, fun r => if r = ⟨w, hw⟩ then 1 else 0, 0, fun x => ?_, fun k hk => absurd rfl hk⟩
    rw [WW_in C w hw]
    simp [Finset.sum_ite_eq']
  by_cases hw2 : w < N + C.gates.length
  · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    have hg := WW_gate C hrb j hj
    have hlen := hfan _ (gateAt_mem C j hj)
    have hrj : ∀ i ∈ (gateAt C j).inputs, i < N + j := hrb j hj
    by_cases hnl : nl (gateAt C j) = true
    · obtain ⟨k, hk⟩ := pos_surj C j (by simp [SS, hj, hnl])
      subst hk
      have hin := inputs_eq C k
      refine ⟨ev C k false false + bet C k * alp C k, 0, Pi.single k 1, fun x => ?_,
        fun k' hk' => ?_⟩
      · rw [hg, hin]
        simp only [List.map_cons, List.map_nil]
        rw [exp2 (gateAt C (pos C k)).op.eval, coef_nl _ hnl]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Pi.single_apply,
          ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        unfold GG bet alp ev
        generalize z (WW N C (i1 C k) x) = a
        generalize z (WW N C (i2 C k) x) = b
        generalize z ((gateAt C (pos C k)).op.eval [false, false]) = p
        generalize z ((gateAt C (pos C k)).op.eval [false, true]) = q
        generalize z ((gateAt C (pos C k)).op.eval [true, false]) = r
        revert a b p q r; decide
      · have : k' = k := by
          by_contra hne; exact hk' (by simp [Pi.single_apply, hne])
        subst this; exact le_rfl
    · have hnl' : nl (gateAt C j) = false := by simpa using hnl
      rcases hL : (gateAt C j).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
      · refine ⟨z ((gateAt C j).op.eval []), 0, 0, fun x => ?_, fun k hk => absurd rfl hk⟩
        rw [hg, hL]; simp
      · have hp : p < N + j := hrj p (by simp [hL])
        obtain ⟨c1, l1, μ1, h1, s1⟩ := ih p hp
        have hh : ∀ x, z (WW N C (N + j) x) = z ((gateAt C j).op.eval [false]) +
            (z ((gateAt C j).op.eval [true]) + z ((gateAt C j).op.eval [false])) *
              z (WW N C p x) + 0 * z (WW N C p x) := by
          intro x; rw [hg, hL]; simp only [List.map_cons, List.map_nil]
          rw [exp1 (gateAt C j).op.eval]; ring
        refine ⟨_, _, _, comb c1 c1 _ _ 0 l1 l1 μ1 μ1 (GG N C) (fun x => z (WW N C p x))
          (fun x => z (WW N C p x)) (fun x => z (WW N C (N + j) x)) h1 h1 hh, fun k hk => ?_⟩
        have : μ1 k ≠ 0 := by
          intro h0; apply hk; simp [h0]
        have := s1 k this; omega
      · have hp : p < N + j := hrj p (by simp [hL])
        have hq : q < N + j := hrj q (by simp [hL])
        obtain ⟨c1, l1, μ1, h1, s1⟩ := ih p hp
        obtain ⟨c2, l2, μ2, h2, s2⟩ := ih q hq
        have h0 := coef_lin _ hnl' (by simp [hL])
        have hh : ∀ x, z (WW N C (N + j) x) = z ((gateAt C j).op.eval [false, false]) +
            (z ((gateAt C j).op.eval [true, false]) + z ((gateAt C j).op.eval [false, false])) *
              z (WW N C p x) +
            (z ((gateAt C j).op.eval [false, true]) + z ((gateAt C j).op.eval [false, false])) *
              z (WW N C q x) := by
          intro x; rw [hg, hL]; simp only [List.map_cons, List.map_nil]
          rw [exp2 (gateAt C j).op.eval, h0]; ring
        refine ⟨_, _, _, comb c1 c2 _ _ _ l1 l2 μ1 μ2 (GG N C) (fun x => z (WW N C p x))
          (fun x => z (WW N C q x)) (fun x => z (WW N C (N + j) x)) h1 h2 hh, fun k hk => ?_⟩
        by_cases hk1 : μ1 k = 0
        · have : μ2 k ≠ 0 := by
            intro h0; apply hk; simp [h0, hk1]
          have := s2 k this; omega
        · have := s1 k hk1; omega
      · exfalso; rw [hL] at hlen; simp at hlen
  · refine ⟨0, 0, 0, fun x => ?_, fun k hk => absurd rfl hk⟩
    rw [WW_out C w (by omega)]; simp [z]

theorem pad {K : Type} [Field K] {ι : Type} [Fintype ι] {α β : Type} (d : ℕ)
    (hd : Fintype.card ι ≤ d) (a : α → ι → K) (b : β → ι → K) :
    ∃ (A : α → Fin d → K) (B : β → Fin d → K),
      ∀ p q, ∑ σ, a p σ * b q σ = ∑ j : Fin d, A p j * B q j := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin d) (by simpa using hd)
  refine ⟨fun p => Function.extend e (a p) 0, fun q => Function.extend e (b q) 0, fun p q => ?_⟩
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    have hj' : ¬∃ x, e x = j := by simpa [Set.mem_range] using hj
    dsimp only
    rw [Function.extend_apply' _ _ _ hj']
    simp
  · intro σ
    simp [e.injective.extend_apply]

def fh {s : ℕ} (F : (Fin s → ZMod 2) → (Fin s → ZMod 2) → ZMod 2) (p q : Fin s → ZMod 2) : ℤ :=
  ∑ x, ∑ y, sg (F x y + dot p x + dot q y)

def srcs {s : ℕ} (A B : Fin s → Fin s → ZMod 2) : Finset (Fin s) :=
  (Finset.univ : Finset (Fin s)).filter (fun j => ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))

def cc {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (γ : Fin s → ZMod 2) (j : Fin s)
    (w : (Fin s → ZMod 2) × (Fin s → ZMod 2)) : ZMod 2 :=
  γ j + ∑ i ∈ Finset.Ioi j, (w.1 i * A i j + w.2 i * B i j)

def liveS {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (γ : Fin s → ZMod 2) :
    Finset ((Fin s → ZMod 2) × (Fin s → ZMod 2)) :=
  (Finset.univ : Finset ((Fin s → ZMod 2) × (Fin s → ZMod 2))).filter (fun w =>
    ∀ j, cc A B γ j w ≠ 0 ∨ (w.1 j = 0 ∧ w.2 j = 0))

def vl (n m : ℕ) (C : Circuit) (a : Fin n) (b : Fin m) : Bool :=
  C.eval (PEqualNP.Represents.oneEach a b)

def Km (n m : ℕ) (C : Circuit) : Matrix (Fin n) (Fin m) ℚ := fun i j =>
  if vl n m C i j then -1 else 1

def Dm (n m : ℕ) (C : Circuit) :
    Matrix (Fin (n + m + C.gates.length)) ((Fin (n + m) → Bool) × (Fin (n + m) → Bool)) (ZMod 2) :=
  fun w v =>
    if (∃ g ∈ C.gates, nl g = true ∧ w.val ∈ g.inputs) ∧
      xor (xor (WW (n + m) C w.val v.1) (WW (n + m) C w.val v.2))
        (xor (WW (n + m) C w.val (fun i => xor (v.1 i) (v.2 i)))
          (WW (n + m) C w.val (fun _ => false))) = true
    then 1 else 0

theorem core (n m : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (tri : ∀ (s : ℕ) (A B : Fin s → Fin s → ZMod 2) (γ : Fin s → ZMod 2),
      2 * 4 ^ (srcs A B).card * (liveS A B γ).card ≤ (4 ^ (srcs A B).card + 1) * 4 ^ s)
    (cp : ∀ (s : ℕ) (A B : Fin s → Fin s → ZMod 2) (γ p q : Fin s → ZMod 2),
      (p, q) ∉ liveS A B γ → fh (fun x y => dot γ (zr A B x y)) p q = 0) :
    2 * 4 ^ (Dm n m C).rank * (Km n m C).rank ≤
        (4 ^ (Dm n m C).rank + 1) * 4 ^ (C.gates.countP nl) ∧
      (5 * 4 ^ (C.gates.countP nl) < 8 * (Km n m C).rank → (Dm n m C).rank = 0 ∧
        ∃ (row : Fin n → Fin (2 * C.gates.countP nl) → ZMod 2)
          (col : Fin m → Fin (2 * C.gates.countP nl) → ZMod 2) (Q : Fin n → Bool)
          (R : Fin m → Bool),
          ∀ i j, vl n m C i j = xor (xor (Q i) (R j))
            (decide ((∑ b : Fin (2 * C.gates.countP nl), row i b * col j b) = 1))) := by
  choose fc fl fμ hf hs using form_exists (n + m) C hrb hfan
  have hst : (SS C).card = C.gates.countP nl := card_SS C
  let A : Fin (SS C).card → Fin (SS C).card → ZMod 2 := fun i k => fμ (i1 C i) k
  let B : Fin (SS C).card → Fin (SS C).card → ZMod 2 := fun i k => fμ (i2 C i) k
  let γ : Fin (SS C).card → ZMod 2 := fμ C.output
  have hA_lt : ∀ i k, A i k ≠ 0 → k < i := by
    intro i k h
    have h1 := hs (i1 C i) k h
    have h2 : i1 C i < n + m + pos C i :=
      hrb (pos C i) (pos_lt_len C i) (i1 C i) (by rw [inputs_eq]; simp)
    exact (pos_lt_iff C k i).mp (by omega)
  have hB_lt : ∀ i k, B i k ≠ 0 → k < i := by
    intro i k h
    have h1 := hs (i2 C i) k h
    have h2 : i2 C i < n + m + pos C i :=
      hrb (pos C i) (pos_lt_len C i) (i2 C i) (by rw [inputs_eq]; simp)
    exact (pos_lt_iff C k i).mp (by omega)
  let X : (Fin (n + m) → Bool) → Fin (SS C).card → ZMod 2 := fun x k =>
    fc (i1 C k) + ∑ r, fl (i1 C k) r * z (x r) + bet C k
  let Y : (Fin (n + m) → Bool) → Fin (SS C).card → ZMod 2 := fun x k =>
    fc (i2 C k) + ∑ r, fl (i2 C k) r * z (x r) + alp C k
  have hGrec : ∀ x k, GG (n + m) C k x =
      (X x k + ∑ j ∈ Finset.Iio k, A k j * GG (n + m) C j x) *
        (Y x k + ∑ j ∈ Finset.Iio k, B k j * GG (n + m) C j x) := by
    intro x k
    have e1 : ∑ j ∈ Finset.Iio k, A k j * GG (n + m) C j x =
        ∑ j, fμ (i1 C k) j * GG (n + m) C j x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have : A k j = 0 := by
        by_contra h; exact hj (Finset.mem_Iio.mpr (hA_lt k j h))
      rw [this, zero_mul]
    have e2 : ∑ j ∈ Finset.Iio k, B k j * GG (n + m) C j x =
        ∑ j, fμ (i2 C k) j * GG (n + m) C j x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have : B k j = 0 := by
        by_contra h; exact hj (Finset.mem_Iio.mpr (hB_lt k j h))
      rw [this, zero_mul]
    rw [e1, e2]
    show (z (WW (n + m) C (i1 C k) x) + bet C k) * (z (WW (n + m) C (i2 C k) x) + alp C k) = _
    rw [hf, hf]
    simp only [X, Y]; ring
  have hGz : ∀ x k, GG (n + m) C k x = zr A B (X x) (Y x) k := fun x k =>
    zr_unique A B (X x) (Y x) (fun k => GG (n + m) C k x) (hGrec x) k.val k rfl
  let e : Fin n → Fin m → Fin (n + m) → Bool := fun a b r =>
    if r.val < n then decide (r.val = a.val) else decide (r.val = n + b.val)
  have hone : ∀ a b, PEqualNP.Represents.oneEach a b = List.ofFn (e a b) := by
    intro a b
    unfold PEqualNP.Represents.oneEach
    rw [List.ofFn_add]
    congr 1 <;> congr 1 <;> funext i <;> simp [e, Fin.ext_iff]
  have haff : ∀ (l : Fin (n + m) → ZMod 2) a b,
      ∑ r, l r * z (e a b r) = l (Fin.castAdd m a) + l (Fin.natAdd n b) := by
    intro l a b
    rw [Fin.sum_univ_add]
    simp [e, z, Fin.val_inj]
  let P1 : Fin n → Fin (SS C).card → ZMod 2 := fun a k =>
    fc (i1 C k) + fl (i1 C k) (Fin.castAdd m a) + bet C k
  let P2 : Fin n → Fin (SS C).card → ZMod 2 := fun a k =>
    fc (i2 C k) + fl (i2 C k) (Fin.castAdd m a) + alp C k
  let Q1 : Fin m → Fin (SS C).card → ZMod 2 := fun b k => fl (i1 C k) (Fin.natAdd n b)
  let Q2 : Fin m → Fin (SS C).card → ZMod 2 := fun b k => fl (i2 C k) (Fin.natAdd n b)
  let u : Fin n → ZMod 2 := fun a => fc C.output + fl C.output (Fin.castAdd m a)
  let v : Fin m → ZMod 2 := fun b => fl C.output (Fin.natAdd n b)
  let F : (Fin (SS C).card → ZMod 2) → (Fin (SS C).card → ZMod 2) → ZMod 2 :=
    fun x y => dot γ (zr A B x y)
  have hval : ∀ a b, z (vl n m C a b) = u a + v b + F (P1 a + Q1 b) (P2 a + Q2 b) := by
    intro a b
    have h1 : vl n m C a b = WW (n + m) C C.output (e a b) := by
      simp only [vl, Circuit.eval, WW, hone]
    have hX : X (e a b) = P1 a + Q1 b := by
      funext k; simp only [X, haff, P1, Q1, Pi.add_apply]; ring
    have hY : Y (e a b) = P2 a + Q2 b := by
      funext k; simp only [Y, haff, P2, Q2, Pi.add_apply]; ring
    rw [h1, hf, haff]
    simp only [hGz]
    rw [hX, hY]
    simp only [F, dot, γ, u, v]
    ring
  -- Walsh expansion of the sign table
  let live := liveS A B γ
  have hZ : ∀ a b, (4 : ℤ) ^ (SS C).card * sg (z (vl n m C a b)) =
      ∑ χ ∈ live, (sg (u a) * fh F χ.1 χ.2 * sg (dot χ.1 (P1 a) + dot χ.2 (P2 a))) *
        (sg (v b) * sg (dot χ.1 (Q1 b) + dot χ.2 (Q2 b))) := by
    intro a b
    rw [hval, sg_add, sg_add]
    rw [show (4 : ℤ) ^ (SS C).card * (sg (u a) * sg (v b) * sg (F (P1 a + Q1 b) (P2 a + Q2 b))) =
      sg (u a) * sg (v b) * (4 ^ (SS C).card * sg (F (P1 a + Q1 b) (P2 a + Q2 b))) by ring]
    rw [← inversion F]
    rw [← Fintype.sum_prod_type' (fun p q => (∑ x, ∑ y, sg (F x y + dot p x + dot q y)) *
      sg (dot p (P1 a + Q1 b) + dot q (P2 a + Q2 b)))]
    rw [← Finset.sum_subset (Finset.subset_univ live) (fun χ _ hχ => by
      have h0 := cp _ A B γ χ.1 χ.2 hχ
      simp only [fh] at h0
      rw [h0, zero_mul])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    have hs : sg (dot χ.1 (P1 a + Q1 b) + dot χ.2 (P2 a + Q2 b)) =
        sg (dot χ.1 (P1 a) + dot χ.2 (P2 a)) * sg (dot χ.1 (Q1 b) + dot χ.2 (Q2 b)) := by
      rw [dot_add_right, dot_add_right, ← sg_add]; congr 1; ring
    rw [hs]
    simp only [fh]
    ring
  let U : Matrix (Fin n) {χ // χ ∈ live} ℚ := fun a χ => ((4 : ℚ) ^ (SS C).card)⁻¹ *
    ((sg (u a) * fh F χ.1.1 χ.1.2 * sg (dot χ.1.1 (P1 a) + dot χ.1.2 (P2 a)) : ℤ) : ℚ)
  let W' : Matrix {χ // χ ∈ live} (Fin m) ℚ := fun χ b =>
    ((sg (v b) * sg (dot χ.1.1 (Q1 b) + dot χ.1.2 (Q2 b)) : ℤ) : ℚ)
  have hK : Km n m C = U * W' := by
    ext a b
    have k1 : Km n m C a b = ((sg (z (vl n m C a b)) : ℤ) : ℚ) := by
      unfold Km
      cases vl n m C a b <;> simp [sg, z]
    have k2 : ((sg (z (vl n m C a b)) : ℤ) : ℚ) = ((4 : ℚ) ^ (SS C).card)⁻¹ *
        (((4 : ℤ) ^ (SS C).card * sg (z (vl n m C a b)) : ℤ) : ℚ) := by
      push_cast; field_simp
    rw [k1, k2, hZ a b, Matrix.mul_apply]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_coe_sort live]
    apply Finset.sum_congr rfl
    intro χ _
    simp only [U, W']
    push_cast
    ring
  have hRk : (Km n m C).rank ≤ live.card := by
    rw [hK]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  -- the defect matrix
  have hsrc : ∀ (w : ℕ), (∃ g ∈ C.gates, nl g = true ∧ w ∈ g.inputs) →
      ∀ k, fμ w k ≠ 0 → k ∈ srcs A B := by
    rintro w ⟨g, hg, hnl, hw⟩ k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hga : gateAt C j = C.gates[j] := by
      unfold gateAt; exact List.getD_eq_getElem _ _ hj
    obtain ⟨k0, hk0⟩ := pos_surj C j (by
      simp only [SS, Finset.mem_filter, Finset.mem_range]; rw [hga]; exact ⟨hj, hnl⟩)
    have hin := inputs_eq C k0
    rw [hk0, hga] at hin
    rw [hin] at hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    simp only [srcs, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨k0, hA_lt k0 k hk, Or.inl hk⟩
    · exact ⟨k0, hB_lt k0 k hk, Or.inr hk⟩
  let M1 : Matrix (Fin (n + m + C.gates.length)) {k // k ∈ srcs A B} (ZMod 2) := fun w k =>
    if (∃ g ∈ C.gates, nl g = true ∧ w.val ∈ g.inputs) then fμ w.val k.1 else 0
  let M2 : Matrix {k // k ∈ srcs A B} ((Fin (n + m) → Bool) × (Fin (n + m) → Bool)) (ZMod 2) :=
    fun k v => GG (n + m) C k.1 v.1 + GG (n + m) C k.1 v.2 +
      GG (n + m) C k.1 (fun i => xor (v.1 i) (v.2 i)) + GG (n + m) C k.1 (fun _ => false)
  have hDM : Dm n m C = M1 * M2 := by
    ext w v
    rw [Matrix.mul_apply]
    by_cases hc : ∃ g ∈ C.gates, nl g = true ∧ w.val ∈ g.inputs
    · unfold Dm
      simp only [hc, true_and]
      change z (xor (xor _ _) (xor _ _)) = _
      rw [z_xor, z_xor, z_xor, hf, hf, hf, hf]
      simp only [M1, M2, hc, ite_true]
      have hsum : ∑ k ∈ srcs A B, fμ w.val k * (GG (n + m) C k v.1 +
          GG (n + m) C k v.2 + GG (n + m) C k (fun i => xor (v.1 i) (v.2 i)) +
          GG (n + m) C k (fun _ => false)) = ∑ k, fμ w.val k * (GG (n + m) C k v.1 +
          GG (n + m) C k v.2 + GG (n + m) C k (fun i => xor (v.1 i) (v.2 i)) +
          GG (n + m) C k (fun _ => false)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        have : fμ w.val k = 0 := by
          by_contra h; exact hk (hsrc _ hc k h)
        rw [this, zero_mul]
      rw [Finset.sum_coe_sort (srcs A B) (fun k => fμ w.val k * (GG (n + m) C k v.1 +
        GG (n + m) C k v.2 + GG (n + m) C k (fun i => xor (v.1 i) (v.2 i)) +
        GG (n + m) C k (fun _ => false))), hsum]
      simp only [z_xor, z_false, mul_add, mul_zero, Finset.sum_add_distrib, Finset.sum_const_zero]
      have q0 : ∀ q : ZMod 2, q + q = 0 := by decide
      have h2a := q0 (fc w.val)
      have h2b := q0 (∑ r, fl w.val r * z (v.1 r))
      have h2c := q0 (∑ r, fl w.val r * z (v.2 r))
      linear_combination 2 * h2a + h2b + h2c
    · unfold Dm
      simp [hc, M1]
  have hD : (Dm n m C).rank ≤ (srcs A B).card := by
    rw [hDM]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  have htri := tri _ A B γ
  have hT' : 4 ^ (SS C).card = 4 ^ C.gates.countP nl := by rw [hst]
  rw [hT'] at htri
  have hpow : 4 ^ (Dm n m C).rank ≤ 4 ^ (srcs A B).card := Nat.pow_le_pow_right (by norm_num) hD
  have hapos : 0 < 4 ^ (Dm n m C).rank := by positivity
  have hbpos : 0 < 4 ^ (srcs A B).card := by positivity
  set a := 4 ^ (Dm n m C).rank with ha
  set bb := 4 ^ (srcs A B).card with hbb
  set T := 4 ^ (C.gates.countP nl) with hT
  set R := (Km n m C).rank with hR
  set L := live.card with hL
  have hmain : 2 * a * R ≤ (a + 1) * T := by
    have h1 : bb * (2 * a * R) ≤ bb * ((a + 1) * T) := by
      calc bb * (2 * a * R) ≤ a * (2 * bb * L) := by
            have := Nat.mul_le_mul_left (2 * a * bb) hRk
            nlinarith [this]
        _ ≤ a * ((bb + 1) * T) := Nat.mul_le_mul_left a htri
        _ = a * bb * T + a * T := by ring
        _ ≤ a * bb * T + bb * T := by nlinarith [Nat.mul_le_mul_right T hpow]
        _ = bb * ((a + 1) * T) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hbpos
  refine ⟨hmain, fun hbig => ?_⟩
  have hsc : (srcs A B).card = 0 := by
    by_contra hne
    have h4 : 4 ≤ bb := by
      rw [hbb]
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (srcs A B).card := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 8 * bb * R ≤ 4 * ((bb + 1) * T) := by
      have := Nat.mul_le_mul_left (8 * bb) hRk
      nlinarith [this, htri]
    nlinarith [Nat.mul_le_mul_right T h4, Nat.mul_le_mul_left bb hbig]
  have hr0 : (Dm n m C).rank = 0 := by omega
  refine ⟨hr0, ?_⟩
  have hsE : srcs A B = ∅ := Finset.card_eq_zero.mp hsc
  have hA0 : ∀ i k, A i k = 0 := by
    intro i k
    by_contra h
    have : k ∈ srcs A B := by
      simp only [srcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hA_lt i k h, Or.inl h⟩
    rw [hsE] at this; simp at this
  have hB0 : ∀ i k, B i k = 0 := by
    intro i k
    by_contra h
    have : k ∈ srcs A B := by
      simp only [srcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hB_lt i k h, Or.inr h⟩
    rw [hsE] at this; simp at this
  have hzr : ∀ x y i, zr A B x y i = x i * y i := by
    intro x y i
    rw [zr_eq]
    simp [hA0, hB0]
  have hval' : ∀ a b, z (vl n m C a b) = (u a + ∑ i, γ i * (P1 a i * P2 a i)) +
      (v b + ∑ i, γ i * (Q1 b i * Q2 b i)) +
      ∑ σ : Fin (SS C).card ⊕ Fin (SS C).card,
        (Sum.elim (fun i => γ i * P1 a i) (fun i => γ i * P2 a i) σ) *
          (Sum.elim (fun i => Q2 b i) (fun i => Q1 b i) σ) := by
    intro a b
    rw [hval, Fintype.sum_sum_type]
    simp only [F, dot, hzr, Pi.add_apply, Sum.elim_inl, Sum.elim_inr]
    rw [show ∑ i, γ i * ((P1 a i + Q1 b i) * (P2 a i + Q2 b i)) =
        ∑ i, γ i * (P1 a i * P2 a i) + ∑ i, γ i * (Q1 b i * Q2 b i) +
          (∑ i, γ i * P1 a i * Q2 b i + ∑ i, γ i * P2 a i * Q1 b i) by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    ring
  obtain ⟨row, col, hrc⟩ := pad (K := ZMod 2) (ι := Fin (SS C).card ⊕ Fin (SS C).card)
    (2 * C.gates.countP nl) (by simp [hst]; omega)
    (fun a σ => Sum.elim (fun i => γ i * P1 a i) (fun i => γ i * P2 a i) σ)
    (fun b σ => Sum.elim (fun i => Q2 b i) (fun i => Q1 b i) σ)
  refine ⟨row, col, fun a => decide ((u a + ∑ i, γ i * (P1 a i * P2 a i)) = 1),
    fun b => decide ((v b + ∑ i, γ i * (Q1 b i * Q2 b i)) = 1), fun a b => ?_⟩
  apply z_inj
  rw [z_xor, z_xor, z_dec, z_dec, z_dec, hval', hrc]

end PEqualNP.Outside.L_meta_25804

open PEqualNP.Outside.L_meta_25804 in
theorem PEqualNP.Outside.L_meta_25804 :
let triangularSupport : Prop :=
  ∀ t : ℕ,
    let V := Fin t → ZMod 2
    ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
      let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
        ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
      let c := fun (j : Fin t) (z : V × V) =>
        γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
      let live := (Finset.univ : Finset (V × V)).filter (fun z =>
        ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
      let lhs := 2 * 4^sources.card * live.card
      let rhs := (4^sources.card + 1) * 4^t
      lhs ≤ rhs ∧
        (lhs = rhs ↔
          (∀ j, j ∉ sources → γ j = 1) ∧
          ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z)
let coefficientProduct : Prop :=
  ∀ s : ℕ,
    let V := Fin s → ZMod 2
    let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
    let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
    ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
    (∀ x y i, Z x y i =
      (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
    ∀ p q : V,
      let c := fun (j : Fin s) =>
        γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
      (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
        ∏ j : Fin s,
          if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
          else 2 * sign (p j * q j)
let conclusion : Prop :=
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
    let t := C.gates.countP nonlinear
    let raw := Fin (n+m) → Bool
    let W := fun (w : ℕ) (x : raw) => (C.wires (List.ofFn x)).getD w false
    let defect : Matrix (Fin (n+m+C.gates.length)) (raw × raw) (ZMod 2) := fun w v =>
      if (∃ g ∈ C.gates, nonlinear g = true ∧ w.val ∈ g.inputs) ∧
        xor (xor (W w.val v.1) (W w.val v.2))
            (xor (W w.val (fun i => xor (v.1 i) (v.2 i))) (W w.val (fun _ => false))) = true
      then 1 else 0
    let value := fun (a : Fin n) (b : Fin m) => C.eval (PEqualNP.Represents.oneEach a b)
    let K : Matrix (Fin n) (Fin m) ℚ := fun i j => if value i j then -1 else 1
    let V := Fin (2*t) → ZMod 2
    2 * 4^defect.rank * K.rank ≤ (4^defect.rank + 1) * 4^t ∧
    (5 * 4^t < 8 * K.rank → defect.rank = 0 ∧
      ∃ (row : Fin n → V) (col : Fin m → V) (Q : Fin n → Bool) (R : Fin m → Bool),
        ∀ i j, value i j = xor (xor (Q i) (R j))
          (decide ((∑ b : Fin (2*t), row i b * col j b) = 1)))
triangularSupport → coefficientProduct → conclusion := by
  dsimp only
  intro tri cp n m C hfan hrb
  have tri' : ∀ (s : ℕ) (A B : Fin s → Fin s → ZMod 2) (γ : Fin s → ZMod 2),
      2 * 4 ^ (srcs A B).card * (liveS A B γ).card ≤ (4 ^ (srcs A B).card + 1) * 4 ^ s :=
    fun s A B γ => (tri s A B γ).1
  have cp' : ∀ (s : ℕ) (A B : Fin s → Fin s → ZMod 2) (γ p q : Fin s → ZMod 2),
      (p, q) ∉ liveS A B γ → fh (fun x y => dot γ (zr A B x y)) p q = 0 := by
    intro s A B γ p q hpq
    have h := cp s A B γ (zr A B) (fun x y i => zr_eq A B x y i) p q
    have h' : fh (fun x y => dot γ (zr A B x y)) p q = _ := h
    rw [h']
    have hpq' : ¬ ∀ j, cc A B γ j (p, q) ≠ 0 ∨ (p j = 0 ∧ q j = 0) := fun hall =>
      hpq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
    push Not at hpq'
    obtain ⟨j, hj1, hj2⟩ := hpq'
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [cc] at hj1
    simp only [hj1, ite_true]
    split_ifs with h3
    · exact absurd h3.2 (hj2 h3.1)
    · rfl
  exact core n m C hfan hrb tri' cp'
