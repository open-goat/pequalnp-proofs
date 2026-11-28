import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25887_aux

open Finset

def sg (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  revert a b; decide

lemma sg_add_one (a : ZMod 2) : sg (a + 1) = - sg a := by
  revert a; decide

lemma zz (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma z01 (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

abbrev V (k : ℕ) := Fin k → ZMod 2

lemma vv {k : ℕ} (x : V k) : x + x = 0 := by funext j; exact zz (x j)

lemma cardPow {k : ℕ} (H : Finset (V k)) (h0 : (0 : V k) ∈ H)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) : ∃ m, H.card = 2 ^ m := by
  classical
  let S : Submodule (ZMod 2) (V k) :=
    { carrier := (H : Set (V k)), add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := by
        intro c x hx
        rcases z01 c with rfl | rfl
        · simpa using h0
        · simpa using hx }
  refine ⟨Module.finrank (ZMod 2) S, ?_⟩
  have e := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [Nat.card_zmod] at e
  rw [← e]
  have : Nat.card S = Nat.card (H : Set (V k)) := rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem gauss {k : ℕ} (A : Finset (V k))
    (hA : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z ∈ A)
    (f : V k → ZMod 2)
    (hf : ∀ h x y z, f (x+y+z+h) + f (x+y+z) =
      (f (x+h) + f x) + (f (y+h) + f y) + (f (z+h) + f z)) :
    (∑ x ∈ A, sg (f x)) = 0 ∨ ∃ e, (∑ x ∈ A, sg (f x)).natAbs = 2 ^ e := by
  classical
  rcases A.eq_empty_or_nonempty with hE | ⟨a, ha⟩
  · left; simp [hE]
  let Vs : Finset (V k) := A.image (fun x => x + a)
  have memV : ∀ h, h ∈ Vs ↔ a + h ∈ A := by
    intro h
    simp only [Vs, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : a + (x + a) = x := by
        rw [add_comm x a, ← add_assoc, vv, zero_add]
      rw [this]; exact hx
    · intro h'
      refine ⟨a + h, h', ?_⟩
      rw [add_comm a h, add_assoc, vv, add_zero]
  have shift : ∀ x ∈ A, ∀ h ∈ Vs, x + h ∈ A := by
    intro x hx h hh
    have := hA x hx (a + h) ((memV h).1 hh) a ha
    have e : x + (a + h) + a = x + h := by
      calc x + (a + h) + a = x + h + (a + a) := by abel
        _ = x + h := by rw [vv, add_zero]
    rwa [e] at this
  have Vadd : ∀ h1 ∈ Vs, ∀ h2 ∈ Vs, h1 + h2 ∈ Vs := by
    intro h1 g1 h2 g2
    rw [memV]
    have := hA (a + h1) ((memV h1).1 g1) (a + h2) ((memV h2).1 g2) a ha
    have e : a + h1 + (a + h2) + a = a + (h1 + h2) := by
      calc a + h1 + (a + h2) + a = a + (h1 + h2) + (a + a) := by abel
        _ = _ := by rw [vv, add_zero]
    rwa [e] at this
  have V0 : (0 : V k) ∈ Vs := by rw [memV, add_zero]; exact ha
  let g : V k → V k → ZMod 2 := fun h x => f (x + h) + f x
  have gaff : ∀ h x y z, g h (x + y + z) = g h x + g h y + g h z := fun h x y z => hf h x y z
  set S := ∑ x ∈ A, sg (f x) with hS
  have sq : S * S = ∑ h ∈ Vs, ∑ x ∈ A, sg (g h x) := by
    rw [hS, Finset.sum_mul_sum, Finset.sum_comm (s := Vs)]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    apply Finset.sum_nbij' (fun y => x + y) (fun h => x + h)
    · intro y hy
      rw [memV, ← add_assoc]; exact hA a ha x hx y hy
    · intro h hh; exact shift x hx h hh
    · intro y _; rw [← add_assoc, vv, zero_add]
    · intro y _; rw [← add_assoc, vv, zero_add]
    · intro y _
      simp only [g]
      rw [← add_assoc, vv, zero_add, sg_add, mul_comm]
  let R := Vs.filter (fun h => ∀ x ∈ A, g h x = g h a)
  have Dzero : ∀ h ∈ Vs, h ∉ R → ∑ x ∈ A, sg (g h x) = 0 := by
    intro h hh hR
    simp only [R, Finset.mem_filter, not_and, not_forall] at hR
    obtain ⟨u, hu, hne⟩ := hR hh
    have h1 : g h u + g h a = 1 := by
      rcases z01 (g h u) with e1 | e1 <;> rcases z01 (g h a) with e2 | e2 <;>
        simp_all
    have key : ∑ x ∈ A, sg (g h x) = ∑ x ∈ A, sg (g h (x + u + a)) := by
      apply Finset.sum_nbij' (fun x => x + u + a) (fun x => x + u + a)
      · intro x hx; exact hA x hx u hu a ha
      · intro x hx; exact hA x hx u hu a ha
      · intro x _
        calc x + u + a + u + a = x + (u + u) + (a + a) := by abel
          _ = x := by rw [vv, vv, add_zero, add_zero]
      · intro x _
        calc x + u + a + u + a = x + (u + u) + (a + a) := by abel
          _ = x := by rw [vv, vv, add_zero, add_zero]
      · intro x _
        congr 2
        calc x = x + (u + u) + (a + a) := by rw [vv, vv, add_zero, add_zero]
          _ = x + u + a + u + a := by abel
    have flip : ∀ x ∈ A, sg (g h (x + u + a)) = - sg (g h x) := by
      intro x _
      rw [gaff, add_assoc, h1, sg_add_one]
    rw [Finset.sum_congr rfl flip, Finset.sum_neg_distrib] at key
    linarith
  have Dconst : ∀ h ∈ R, ∑ x ∈ A, sg (g h x) = A.card * sg (g h a) := by
    intro h hR
    simp only [R, Finset.mem_filter] at hR
    rw [Finset.sum_congr rfl (fun x hx => by rw [hR.2 x hx])]
    simp
  have sq2 : S * S = A.card * ∑ h ∈ R, sg (g h a) := by
    rw [sq, ← Finset.sum_filter_add_sum_filter_not Vs (fun h => ∀ x ∈ A, g h x = g h a)]
    have z : ∑ h ∈ Vs.filter (fun h => ¬ ∀ x ∈ A, g h x = g h a), ∑ x ∈ A, sg (g h x) = 0 :=
      Finset.sum_eq_zero (fun h hh => by
        simp only [Finset.mem_filter] at hh
        exact Dzero h hh.1 (by simp only [R, Finset.mem_filter]; exact fun hc => hh.2 hc.2))
    rw [z, add_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h hh => Dconst h hh)
  have R0 : (0 : V k) ∈ R := by
    simp only [R, Finset.mem_filter]; refine ⟨V0, fun x _ => ?_⟩; simp [g, zz]
  have Radd : ∀ h1 ∈ R, ∀ h2 ∈ R, h1 + h2 ∈ R ∧ g (h1 + h2) a = g h1 a + g h2 a := by
    intro h1 r1 h2 r2
    simp only [R, Finset.mem_filter] at r1 r2
    have split : ∀ x ∈ A, g (h1 + h2) x = g h1 a + g h2 a := by
      intro x hx
      have hx1 : x + h1 ∈ A := shift x hx h1 r1.1
      have : g (h1 + h2) x = g h2 (x + h1) + g h1 x := by
        simp only [g]
        rw [show x + (h1 + h2) = x + h1 + h2 by abel]
        linear_combination (-1 : ZMod 2) * zz (f (x + h1))
      rw [this, r2.2 _ hx1, r1.2 _ hx, add_comm]
    refine ⟨?_, split a ha⟩
    simp only [R, Finset.mem_filter]
    exact ⟨Vadd _ r1.1 _ r2.1, fun x hx => by rw [split x hx, split a ha]⟩
  have Tval : (∑ h ∈ R, sg (g h a)) = 0 ∨ (∑ h ∈ R, sg (g h a)) = R.card := by
    by_cases hall : ∀ h ∈ R, g h a = 0
    · right; rw [Finset.sum_congr rfl (fun h hh => by rw [hall h hh])]; simp [sg]
    · left
      push Not at hall
      obtain ⟨h0, r0, ne⟩ := hall
      have one : g h0 a = 1 := by
        rcases z01 (g h0 a) with e | e
        · exact absurd e ne
        · exact e
      have key : ∑ h ∈ R, sg (g h a) = ∑ h ∈ R, sg (g (h + h0) a) := by
        apply Finset.sum_nbij' (fun h => h + h0) (fun h => h + h0)
        · intro h hh; exact (Radd h hh h0 r0).1
        · intro h hh; exact (Radd h hh h0 r0).1
        · intro h _; rw [add_assoc, vv, add_zero]
        · intro h _; rw [add_assoc, vv, add_zero]
        · intro h _; rw [add_assoc, vv, add_zero]
      have flip : ∀ h ∈ R, sg (g (h + h0) a) = - sg (g h a) := by
        intro h hh; rw [(Radd h hh h0 r0).2, one, sg_add_one]
      rw [Finset.sum_congr rfl flip, Finset.sum_neg_distrib] at key
      linarith
  obtain ⟨m1, hm1⟩ := cardPow Vs V0 Vadd
  obtain ⟨m2, hm2⟩ := cardPow R R0 (fun x hx y hy => (Radd x hx y hy).1)
  have cardA : A.card = Vs.card :=
    (Finset.card_image_of_injective _ (add_left_injective a)).symm
  rcases Tval with h | h
  · left; rw [h, mul_zero] at sq2; exact mul_self_eq_zero.mp sq2
  · right
    rw [h, cardA, hm1, hm2] at sq2
    have h3 : ((S.natAbs * S.natAbs : ℕ) : ℤ) = ((2 ^ (m1 + m2) : ℕ) : ℤ) := by
      push_cast; rw [abs_mul_abs_self, sq2]; push_cast; ring
    have h4 : S.natAbs * S.natAbs = 2 ^ (m1 + m2) := by exact_mod_cast h3
    have hd : S.natAbs ∣ 2 ^ (m1+m2) := ⟨S.natAbs, h4.symm⟩
    obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨e, he⟩

/-! Quadratic functions -/

def Q2 {k : ℕ} (f : V k → ZMod 2) : Prop :=
  ∀ h x y z, f (x+y+z+h) + f (x+y+z) = (f (x+h) + f x) + (f (y+h) + f y) + (f (z+h) + f z)

def Lin {k : ℕ} (f : V k → ZMod 2) : Prop := ∀ x y, f (x + y) = f x + f y

lemma q2_add {k : ℕ} {f g : V k → ZMod 2} (hf : Q2 f) (hg : Q2 g) : Q2 (fun x => f x + g x) := by
  intro h x y z; linear_combination hf h x y z + hg h x y z

lemma q2_const {k : ℕ} (c : ZMod 2) : Q2 (fun _ : V k => c) := by
  intro h x y z; linear_combination (-2 : ZMod 2) * zz c

lemma q2_smul {k : ℕ} {f : V k → ZMod 2} (c : ZMod 2) (hf : Q2 f) : Q2 (fun x => c * f x) := by
  intro h x y z; linear_combination c * hf h x y z

lemma q2_lin {k : ℕ} {f : V k → ZMod 2} (hf : Lin f) : Q2 f := by
  have hf' : ∀ x y, f (x + y) = f x + f y := hf
  intro h x y z; simp only [hf']; linear_combination (-1 : ZMod 2) * zz (f h)

lemma q2_mul {k : ℕ} {P Q : V k → ZMod 2} (hP : Lin P) (hQ : Lin Q) : Q2 (fun x => P x * Q x) := by
  have hP' : ∀ x y, P (x + y) = P x + P y := hP
  have hQ' : ∀ x y, Q (x + y) = Q x + Q y := hQ
  intro h x y z
  simp only [hP', hQ']
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination (P x * Q y + P x * Q z + P y * Q x + P y * Q z + P z * Q x + P z * Q y
    - P h * Q h) * two

lemma q2_sum {k : ℕ} {ι : Type} (s : Finset ι) (F : ι → V k → ZMod 2) (hF : ∀ i, Q2 (F i)) :
    Q2 (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using q2_const (k := k) 0
  | insert a s ha ih =>
    have := q2_add (hF a) ih
    simpa [Finset.sum_insert ha] using this


lemma subz (x y : ZMod 2) : x - y = x + y := by revert x y; decide

lemma vsub {k : ℕ} (x y : V k) : x - y = x + y := by funext j; exact subz (x j) (y j)

lemma sg_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) : sg (∑ i ∈ s, f i) = ∏ i ∈ s, sg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sg_add, ih]

section Defs
variable (k : ℕ) (hk : 0 < k)

def ix (t : ℕ) : Fin k := ⟨t % k, Nat.mod_lt _ hk⟩
def rot (amount : ℕ) (x : V k) (j : Fin k) : ZMod 2 := x (ix k hk (j.val + k - amount % k))
def mm (gap : ℕ) (x : V k) (j : Fin k) : ZMod 2 :=
  x j + x (ix k hk (j.val + gap)) + x (ix k hk (j.val + k - gap % k))
def Lf (y : V k) (j : Fin k) : ZMod 2 := y j + (1 + y (ix k hk (j.val+1))) * y (ix k hk (j.val+2))
def layer (gap : ℕ) (x : V k) : V k := Lf k hk (mm k hk gap x)

variable (r : ℕ) (gap initial : ℕ) (inject : ℕ → ℕ)

def state (data : V k × (Fin r → V k)) (key : V k) (time : Fin (r+1)) : V k :=
  ((List.finRange r).take time.val).foldl (fun v tick =>
    layer k hk gap v + rot k hk (inject tick.val) key + data.2 tick) (rot k hk initial key + data.1)

end Defs

section Traj
variable {k : ℕ} {hk : 0 < k} {r : ℕ} {gap initial : ℕ} {inject : ℕ → ℕ}

lemma rot_add (a : ℕ) (x y : V k) : rot k hk a (x + y) = rot k hk a x + rot k hk a y := rfl

lemma state_zero (d : V k × (Fin r → V k)) (key : V k) :
    state k hk r gap initial inject d key 0 = rot k hk initial key + d.1 := by
  simp [state]

lemma state_succ (d : V k × (Fin r → V k)) (key : V k) (t : Fin r) :
    state k hk r gap initial inject d key t.succ =
      layer k hk gap (state k hk r gap initial inject d key t.castSucc) +
        rot k hk (inject t.val) key + d.2 t := by
  simp only [state, Fin.val_succ, Fin.coe_castSucc]
  rw [List.take_succ, List.foldl_append]
  have : (List.finRange r)[t.val]? = some t := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp
  rw [this]
  simp

/-- the trajectory parametrisation -/
def Phi (raw : V k) (v : Fin (r+1) → V k) : V k × (Fin r → V k) :=
  (v 0 - rot k hk initial raw,
    fun t => v t.succ - layer k hk gap (v t.castSucc) - rot k hk (inject t.val) raw)

lemma state_Phi (raw : V k) (v : Fin (r+1) → V k) (t : Fin (r+1)) :
    state k hk r gap initial inject (Phi (hk := hk) (gap := gap) (initial := initial)
      (inject := inject) raw v) raw t = v t := by
  induction t using Fin.induction with
  | zero => rw [state_zero]; simp [Phi]
  | succ t ih => rw [state_succ, ih]; simp [Phi]

lemma Phi_bij (raw : V k) : Function.Bijective
    (Phi (r := r) (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun d => fun t => state k hk r gap initial inject d raw t, ?_, ?_⟩
  · intro v; funext t; exact state_Phi raw v t
  · intro d
    rcases d with ⟨n, c⟩
    simp only [Phi, state_zero]
    congr 1
    · abel
    · funext t; rw [state_succ]; abel

lemma delta_iff (d : V k × (Fin r → V k)) (key δ : V k) (pth : Fin (r+1) → V k) :
    (∀ t, state k hk r gap initial inject d (key + δ) t - state k hk r gap initial inject d key t
        = pth t) ↔
      (rot k hk initial δ = pth 0 ∧ ∀ t : Fin r,
        layer k hk gap (state k hk r gap initial inject d key t.castSucc + pth t.castSucc) -
          layer k hk gap (state k hk r gap initial inject d key t.castSucc) +
          rot k hk (inject t.val) δ = pth t.succ) := by
  constructor
  · intro h
    refine ⟨?_, fun t => ?_⟩
    · have := h 0; rw [state_zero, state_zero, rot_add] at this; rw [← this]; abel
    · have h1 := h t.succ
      have h2 := h t.castSucc
      rw [state_succ, state_succ, rot_add] at h1
      have e : state k hk r gap initial inject d (key + δ) t.castSucc =
          state k hk r gap initial inject d key t.castSucc + pth t.castSucc := by
        rw [← h2]; abel
      rw [e] at h1; rw [← h1]; abel
  · rintro ⟨h0, h⟩ t
    induction t using Fin.induction with
    | zero => rw [state_zero, state_zero, rot_add, ← h0]; abel
    | succ t ih =>
      rw [state_succ, state_succ, rot_add, ← h t]
      have e : state k hk r gap initial inject d (key + δ) t.castSucc =
          state k hk r gap initial inject d key t.castSucc + pth t.castSucc := by
        rw [← ih]; abel
      rw [e]; abel

end Traj

section Factor
variable (k : ℕ) (hk : 0 < k) (r s : ℕ) (gap initial : ℕ) (inject : ℕ → ℕ)
variable (raw : V k) (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k) (test target : V k)
variable (b : Fin r → V k)

def bprev (t : Fin (r+1)) : V k := if h : 0 < t.val then b ⟨t.val - 1, by omega⟩ else 0

def condT (t : Fin (r+1)) (x : V k) : Prop :=
  if h : t.val < r then ∀ p, layer k hk gap (x + path t p) - layer k hk gap x +
      rot k hk (inject t.val) (delta p) = path ⟨t.val+1, by omega⟩ p
  else ∀ j, test j ≠ 0 → x j = target j

def qT (t : Fin (r+1)) (x : V k) : ZMod 2 :=
  (if h : t.val < r then dotProduct (b ⟨t.val, h⟩) (layer k hk gap x) else 0) +
    dotProduct (bprev k r b t) x

open Classical in
noncomputable def ST (t : Fin (r+1)) : ℤ :=
  ∑ x : V k, if condT k hk r s gap inject delta path test target t x then
    sg (qT k hk r gap b t x) else 0

def G0 : Prop := ∀ p, rot k hk initial (delta p) = path 0 p

def Kc : ZMod 2 := ∑ t : Fin r, dotProduct (b t) (rot k hk (inject t.val) raw)

open Classical in
noncomputable def G0i : ℤ := if G0 k hk r s initial delta path then 1 else 0

end Factor

section FactorProof
variable {k : ℕ} {hk : 0 < k} {r s : ℕ} {gap initial : ℕ} {inject : ℕ → ℕ}

theorem factor (raw : V k) (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k)
    (test target : V k) (b : Fin r → V k) :
    (∑ c : Fin r → V k, ∑ name : V k,
      if ((∀ t p, state k hk r gap initial inject (name, c) (raw + delta p) t -
        state k hk r gap initial inject (name, c) raw t = path t p) ∧
      (∀ j, test j ≠ 0 → state k hk r gap initial inject (name, c) raw (Fin.last r) j =
        target j)) then sg (∑ t : Fin r, dotProduct (b t) (c t)) else 0) =
    sg (Kc k hk r inject raw b) * G0i k hk r s initial delta path *
      ∏ t, ST k hk r s gap inject delta path test target b t := by
  classical
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  rw [← Function.Bijective.sum_comp (Phi_bij (hk := hk) (gap := gap) (initial := initial)
    (inject := inject) (r := r) raw)]
  have point : ∀ v : Fin (r+1) → V k,
      (if ((∀ t p, state k hk r gap initial inject
          ((Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).1,
           (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).2)
          (raw + delta p) t -
        state k hk r gap initial inject
          ((Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).1,
           (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).2)
          raw t = path t p) ∧
      (∀ j, test j ≠ 0 → state k hk r gap initial inject
          ((Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).1,
           (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).2)
          raw (Fin.last r) j = target j))
        then sg (∑ t : Fin r, dotProduct (b t)
          ((Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).2 t))
        else 0) =
      sg (Kc k hk r inject raw b) * G0i k hk r s initial delta path *
        ∏ t, (if condT k hk r s gap inject delta path test target t (v t) then
          sg (qT k hk r gap b t (v t)) else 0) := by
    intro v
    simp only [Prod.mk.eta]
    have hstate := state_Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v
    have hp : ∀ p, (∀ t, state k hk r gap initial inject
          (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v)
          (raw + delta p) t - state k hk r gap initial inject
          (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v) raw t
          = path t p) ↔
        (rot k hk initial (delta p) = path 0 p ∧ ∀ t : Fin r,
          layer k hk gap (v t.castSucc + path t.castSucc p) - layer k hk gap (v t.castSucc) +
          rot k hk (inject t.val) (delta p) = path t.succ p) := by
      intro p
      have := delta_iff (hk := hk) (gap := gap) (initial := initial) (inject := inject)
        (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v)
        raw (delta p) (fun t => path t p)
      simpa only [hstate] using this
    have key : ((∀ t p, state k hk r gap initial inject
          (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v)
          (raw + delta p) t - state k hk r gap initial inject
          (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v) raw t
          = path t p) ∧
        (∀ j, test j ≠ 0 → state k hk r gap initial inject
          (Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v)
          raw (Fin.last r) j = target j)) ↔
        (G0 k hk r s initial delta path ∧
          ∀ t, condT k hk r s gap inject delta path test target t (v t)) := by
      constructor
      · rintro ⟨h1, h2⟩
        have h1' := fun p => (hp p).1 (fun t => h1 t p)
        refine ⟨fun p => (h1' p).1, ?_⟩
        intro t
        induction t using Fin.lastCases with
        | last =>
          rw [condT, dif_neg (by simp)]
          intro j hj; rw [← hstate]; exact h2 j hj
        | cast i =>
          rw [condT, dif_pos (show (Fin.castSucc i).val < r from i.isLt)]
          intro p; exact (h1' p).2 i
      · rintro ⟨g0, hc⟩
        refine ⟨fun t p => ((hp p).2 ⟨g0 p, fun i => ?_⟩) t, ?_⟩
        · have := hc i.castSucc
          rw [condT, dif_pos (show (Fin.castSucc i).val < r from i.isLt)] at this
          exact this p
        · intro j hj
          have := hc (Fin.last r)
          rw [condT, dif_neg (by simp)] at this
          rw [hstate]; exact this j hj
    have pair : (∑ t : Fin r, dotProduct (b t)
          ((Phi (hk := hk) (gap := gap) (initial := initial) (inject := inject) raw v).2 t)) =
        Kc k hk r inject raw b + ∑ t, qT k hk r gap b t (v t) := by
      simp only [Phi, vsub, dotProduct_add, Finset.sum_add_distrib, qT, Kc]
      rw [Fin.sum_univ_castSucc (f := fun t => if h : t.val < r then
        dotProduct (b ⟨t.val, h⟩) (layer k hk gap (v t)) else 0)]
      rw [Fin.sum_univ_succ (f := fun t => dotProduct (bprev k r b t) (v t))]
      have e1 : ∀ i : Fin r, (if h : (Fin.castSucc i).val < r then
          dotProduct (b ⟨(Fin.castSucc i).val, h⟩) (layer k hk gap (v (Fin.castSucc i))) else 0)
          = dotProduct (b i) (layer k hk gap (v i.castSucc)) := by
        intro i; rw [dif_pos (show (Fin.castSucc i).val < r from i.isLt)]; rfl
      have e2 : (if h : (Fin.last r).val < r then
          dotProduct (b ⟨(Fin.last r).val, h⟩) (layer k hk gap (v (Fin.last r))) else 0) = 0 := by
        rw [dif_neg (by simp)]
      have e3 : bprev k r b 0 = 0 := by simp [bprev]
      have e4 : ∀ i : Fin r, bprev k r b i.succ = b i := by
        intro i; simp only [bprev, Fin.val_succ]; rw [dif_pos (by omega)]; rfl
      simp only [e1, e2, e3, e4, zero_dotProduct, add_zero, zero_add]
      abel
    rw [pair, sg_add, sg_sum, Fintype.prod_ite_zero]
    by_cases hg : G0 k hk r s initial delta path <;>
      by_cases hc : ∀ t, condT k hk r s gap inject delta path test target t (v t) <;>
      simp [key, hg, hc, G0i]
  rw [Finset.sum_congr rfl (fun v _ => point v), ← Finset.mul_sum]
  congr 1
  simp only [ST]
  rw [Fintype.prod_sum]

end FactorProof


end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ReadsBack n ⟨gates,0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (B : Bank n) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, ∀ x, B.val i x = f x

def Ext (B D : Bank n) : Prop := ∀ {f}, B.Has f → D.Has f

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[],by simp [FanInTwo],by simp [ReadsBack]⟩

lemma input (i : Fin n) : (empty n).Has (fun x => x i) := by
  refine ⟨i,i.isLt,?_⟩
  intro x
  simp [val,empty,Circuit.wires,List.getD_eq_getElem?_getD,i.isLt]

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B,fun h => h,by omega,h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D,e,c,t⟩ := h
  exact ⟨D,e,by omega,hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a+b) q := by
  obtain ⟨D,e,c,t⟩ := h
  obtain ⟨E,e',c',t'⟩ := f D e t
  exact ⟨E,fun h => e' (e h),by omega,t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires,List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n+B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      fan := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h|h
        · exact B.fan g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates,0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D,val,Circuit.wires,List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).length = n+B.gates.length := by
    simp [wireLen]
  refine ⟨D,?_,by simp [D],n+B.gates.length,by simp [D],?_⟩
  · intro f hf
    obtain ⟨i,hi,he⟩ := hf
    refine ⟨i,by simp [D]; omega,?_⟩
    intro x
    unfold val
    rw [hv,List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold val
    rw [hv,← hl x]
    simp [val,List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or,[]⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and,[]⟩ (by simp) (by simp)

lemma inv {B : Bank n} {f : BitFn n} (a : B.Has f) :
    B.Grow 1 (fun D => D.Has (fun x => !(f x))) := by
  obtain ⟨i,hi,he⟩ := a
  simpa [GateOp.eval,he] using B.gate ⟨.not,[i]⟩ (by simp) (by simpa using hi)

lemma meet {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x && g x)) := by
  obtain ⟨i,hi,he⟩ := a
  obtain ⟨j,hj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.and,[i,j]⟩ (by simp) (by simp [hi,hj])

lemma join {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x || g x)) := by
  obtain ⟨i,hi,he⟩ := a
  obtain ⟨j,hj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.or,[i,j]⟩ (by simp) (by simp [hi,hj])

lemma xor2 {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => xor (f x) (g x))) := by
  apply (meet a b).bind (b := 3)
  intro C e hab
  apply (inv hab).bind (b := 2)
  intro D e' hn
  apply (join (e' (e a)) (e' (e b))).bind (b := 1)
  intro E e'' hor
  apply (meet hor (e'' hn)).weaken (le_refl _)
  intro F h
  have eq (x) : ((f x || g x) && !(f x && g x)) = xor (f x) (g x) := by
    cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma collect {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (l.length*cost) (fun D => ∀ i ∈ l, D.Has (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure B (p:=fun D => ∀ i ∈ ([] : List α), D.Has (f i)) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost) (q:=fun E => ∀ i ∈ a::l, E.Has (f i)) (by
      intro D e haveL
      obtain ⟨E,e',c',ha⟩ := emit D e a (by simp)
      refine ⟨E,e',c',?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin (B : Bank n) (m : Nat) (f : Fin m → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (m*cost) (fun D => ∀ i, D.Has (f i)) := by
  simpa using B.collect (List.finRange m) f cost (fun D e i _ => emit D e i)

lemma finish {f : BitFn n} {b : Nat} (h : (empty n).Grow b (fun B => B.Has f)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ b ∧
      ∀ bits, C.eval (List.ofFn bits) = f bits := by
  obtain ⟨B,_,budget,i,_,he⟩ := h
  exact ⟨⟨B.gates,i⟩, B.fan, B.back, by simpa [Circuit.size, empty] using budget, he⟩

end Bank
end PEqualNP.Outside.L_meta_25887_aux.Builder

namespace PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

variable {n : Nat}

lemma xorConst {B : Bank n} {f : BitFn n} (a : B.Has f) (b : Bool) :
    B.Grow 1 (fun D => D.Has (fun x => xor (f x) b)) := by
  cases b with
  | false =>
    have h := Grow.pure B (p:=fun D => D.Has f) a
    simpa using h.weaken (b:=1) (q:=fun D => D.Has f) (by decide) (fun _ t => t)
  | true => simpa using inv a

def foldOp (all : Bool) (a b : Bool) : Bool := if all then a && b else a || b

lemma emitFoldOp {B : Bank n} (all : Bool) {f g : BitFn n}
    (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => foldOp all (f x) (g x))) := by
  cases all with
  | true => exact meet a b
  | false => exact join a b

lemma foldSlots {α : Type} (all : Bool) (B : Bank n) (l : List α)
    (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1)) (fun D => D.Has (fun x =>
      if all then l.all (fun i => f i x) else l.any (fun i => f i x))) := by
  induction l with
  | nil =>
    simpa using B.const all
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost+1)
      (q:=fun E => E.Has (fun x => if all then (a::l).all (fun i => f i x)
        else (a::l).any (fun i => f i x))) (by
      intro D e acc
      apply (emit D e a (by simp)).bind (b:=1)
      intro E e' ha
      have computed := emitFoldOp all ha (e' acc)
      cases all <;> simpa [foldOp] using computed)
    simpa [Nat.succ_mul,Nat.add_assoc] using out

lemma anySlots {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1))
      (fun D => D.Has (fun x => l.any (fun i => f i x))) :=
  foldSlots false B l f cost emit

lemma anyBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.any (fun i => f i x))) := by
  simpa using anySlots B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))


lemma allBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.all (fun i => f i x))) := by
  simpa using foldSlots true B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))

lemma hasCongr {B : Bank n} {f g : BitFn n} (h : B.Has f) (e : ∀ x, f x = g x) : B.Has g := by
  have : f = g := funext e
  exact this ▸ h

lemma collectP {α : Type} (B : Bank n) (l : List α) (P : α → Bank n → Prop)
    (mono : ∀ a D E, D.Ext E → P a D → P a E) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (P i)) :
    B.Grow (l.length*cost) (fun D => ∀ i ∈ l, P i D) := by
  induction l with
  | nil => simpa using Grow.pure B (p := fun D => ∀ i ∈ ([] : List α), P i D) (by simp)
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost) (q:=fun E => ∀ i ∈ a::l, P i E) (by
      intro D e haveL
      obtain ⟨E,e',c',ha⟩ := emit D e a (by simp)
      refine ⟨E,e',c',?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact mono i D E e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma xorBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1 + 4 * l.length)
      (fun D => D.Has (fun x => l.foldr (fun i acc => xor (f i x) acc) false)) := by
  induction l with
  | nil => simpa using B.const false
  | cons a l ih =>
    have t := ih (fun i hi => h i (by simp [hi]))
    have out := t.bind (b := 4)
      (q := fun D => D.Has (fun x => (a :: l).foldr (fun i acc => xor (f i x) acc) false)) (by
      intro D e hl
      simpa using xor2 (e (h a (by simp))) hl)
    exact out.weaken (by simp; omega) (fun _ h => h)

/-! numbers -/

def HasNat (B : Bank n) (L : ℕ) (U : (Fin n → Bool) → ℕ) : Prop :=
  (∀ x, U x < 2 ^ L) ∧ ∀ i < L, B.Has (fun x => (U x).testBit i)

lemma HasNat.lift {B D : Bank n} {L : ℕ} {U : (Fin n → Bool) → ℕ} (e : B.Ext D)
    (h : HasNat B L U) : HasNat D L U :=
  ⟨h.1, fun i hi => e (h.2 i hi)⟩

lemma HasNat.widen {B : Bank n} {L L' : ℕ} {U : (Fin n → Bool) → ℕ} (h : HasNat B L U)
    (hL : L ≤ L') (z : B.Has (fun _ => false)) : HasNat B L' U := by
  refine ⟨fun x => lt_of_lt_of_le (h.1 x) (Nat.pow_le_pow_right (by norm_num) hL),
    fun i hi => ?_⟩
  by_cases hiL : i < L
  · exact h.2 i hiL
  · refine hasCongr z (fun x => ?_)
    exact (Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le (h.1 x) (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

def carry (U W i : ℕ) : Bool := decide (2 ^ i ≤ U % 2 ^ i + W % 2 ^ i)

lemma par3 (a b c : ℕ) (hc : c ≤ 1) :
    decide ((c + (a + b)) % 2 = 1) =
      xor (xor (decide (a % 2 = 1)) (decide (b % 2 = 1))) (decide (c = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  interval_cases c <;> simp [Nat.add_mod, ha, hb]

lemma sum_bit (U W i : ℕ) :
    (U + W).testBit i = xor (xor (U.testBit i) (W.testBit i)) (carry U W i) := by
  have hU := Nat.div_add_mod U (2^i)
  have hW := Nat.div_add_mod W (2^i)
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hu := Nat.mod_lt U hp
  have hw := Nat.mod_lt W hp
  have e : U + W = (U % 2^i + W % 2^i) + 2^i * (U / 2^i + W / 2^i) := by
    rw [mul_add]; linarith
  have hdiv : (U + W) / 2^i = (U % 2^i + W % 2^i) / 2^i + (U / 2^i + W / 2^i) := by
    rw [e, Nat.add_mul_div_left _ _ hp]
  have hc : (U % 2^i + W % 2^i) / 2^i ≤ 1 := by
    have : (U % 2^i + W % 2^i) / 2^i < 2 := by
      rw [Nat.div_lt_iff_lt_mul hp]; omega
    omega
  have hcar : carry U W i = decide ((U % 2^i + W % 2^i) / 2^i = 1) := by
    unfold carry
    apply decide_eq_decide.mpr
    constructor
    · intro h
      have : 1 ≤ (U % 2^i + W % 2^i) / 2^i := (Nat.le_div_iff_mul_le hp).mpr (by simpa using h)
      omega
    · intro h
      have : 1 ≤ (U % 2^i + W % 2^i) / 2^i := by omega
      simpa using (Nat.le_div_iff_mul_le hp).mp this
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq, hdiv, hcar]
  exact par3 _ _ _ hc

lemma carry_succ (U W i : ℕ) :
    carry U W (i+1) = ((U.testBit i && W.testBit i) ||
      (carry U W i && xor (U.testBit i) (W.testBit i))) := by
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hu := Nat.mod_lt U hp
  have hw := Nat.mod_lt W hp
  simp only [carry, Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.mod_pow_succ, Nat.mod_pow_succ, pow_succ]
  generalize U % 2 ^ i = u at *
  generalize W % 2 ^ i = w at *
  rcases Nat.mod_two_eq_zero_or_one (U / 2^i) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (W / 2^i) with h2 | h2 <;>
  simp only [h1, h2] <;>
  generalize 2 ^ i = Q at * <;>
  by_cases hc : Q ≤ u + w <;> simp [hc] <;> omega

lemma top_bit {U W L : ℕ} (hU : U < 2 ^ L) (hW : W < 2 ^ L) :
    (U + W).testBit L = carry U W L := by
  rw [sum_bit, Nat.testBit_eq_false_of_lt hU, Nat.testBit_eq_false_of_lt hW]
  simp

lemma adder {B : Bank n} {L : ℕ} {U W : (Fin n → Bool) → ℕ} (hU : HasNat B L U)
    (hW : HasNat B L W) :
    B.Grow (11 * L + 1) (fun D => HasNat D (L+1) (fun x => U x + W x)) := by
  have inv : ∀ i ≤ L, B.Grow (11 * i + 1) (fun D => D.Has (fun x => carry (U x) (W x) i) ∧
      ∀ j < i, D.Has (fun x => (U x + W x).testBit j)) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact (B.const false).weaken (by omega) (fun D h =>
        ⟨hasCongr h (fun x => by simp [carry, Nat.mod_one]), fun j hj => absurd hj (by omega)⟩)
    | succ i ih =>
      intro hi
      have := (ih (by omega)).bind (b := 11) (q := fun D =>
          D.Has (fun x => carry (U x) (W x) (i+1)) ∧
          ∀ j < i+1, D.Has (fun x => (U x + W x).testBit j)) (by
        intro D e hcs
        obtain ⟨hc, hs⟩ := hcs
        have hu := e (hU.2 i (by omega))
        have hw := e (hW.2 i (by omega))
        obtain ⟨D1, e1, c1, t⟩ := xor2 hu hw
        obtain ⟨D2, e2, c2, s⟩ := xor2 t (e1 hc)
        obtain ⟨D3, e3, c3, a⟩ := meet (e2 (e1 hu)) (e2 (e1 hw))
        obtain ⟨D4, e4, c4, bb⟩ := meet (e3 (e2 (e1 hc))) (e3 (e2 t))
        obtain ⟨D5, e5, c5, cc⟩ := join (e4 a) bb
        refine ⟨D5, fun h => e5 (e4 (e3 (e2 (e1 h)))), by omega, ?_, ?_⟩
        · exact hasCongr cc (fun x => (carry_succ _ _ _).symm)
        · intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact e5 (e4 (e3 (e2 (e1 (hs j hj)))))
          · exact e5 (e4 (e3 (hasCongr s (fun x => (sum_bit _ _ _).symm)))))
      exact this.weaken (by omega) (fun _ h => h)
  refine (inv L le_rfl).weaken le_rfl (fun D hcs => ?_)
  obtain ⟨hc, hs⟩ := hcs
  refine ⟨fun x => ?_, fun j hj => ?_⟩
  · show U x + W x < 2 ^ (L+1)
    have := hU.1 x; have := hW.1 x; rw [pow_succ]; omega
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hs j hj
    · exact hasCongr hc (fun x => (top_bit (hU.1 x) (hW.1 x)).symm)

lemma mux {B : Bank n} {L : ℕ} {P N : (Fin n → Bool) → ℕ} {a g : BitFn n}
    (hP : HasNat B L P) (hN : HasNat B L N) (ha : B.Has a) (hg : B.Has g)
    (excl : ∀ x, ¬ (a x = true ∧ g x = true)) :
    B.Grow (L * 3) (fun D => HasNat D L (fun x => if a x then P x else if g x then N x else 0)) := by
  have := B.collectFin L (fun i x => (a x && (P x).testBit i) || (g x && (N x).testBit i)) 3 (by
    intro D e i
    obtain ⟨D1, e1, c1, t1⟩ := meet (e ha) (e (hP.2 i i.isLt))
    obtain ⟨D2, e2, c2, t2⟩ := meet (e1 (e hg)) (e1 (e (hN.2 i i.isLt)))
    obtain ⟨D3, e3, c3, t3⟩ := join (e2 t1) t2
    exact ⟨D3, fun h => e3 (e2 (e1 h)), by omega, t3⟩)
  refine this.weaken le_rfl (fun D h => ⟨fun x => ?_, fun i hi => hasCongr (h ⟨i, hi⟩) (fun x => ?_)⟩)
  · beta_reduce
    split_ifs
    · exact hP.1 x
    · exact hN.1 x
    · exact Nat.two_pow_pos L
  · have := excl x
    cases ha' : a x <;> cases hg' : g x <;> simp_all

/-! comparison and the lowest differing bit -/

def lowE (P N L ℓ : ℕ) : Bool :=
  ((List.range L).filter (fun i => i.testBit ℓ)).any
    (fun i => decide (P % 2^i = N % 2^i) && xor (P.testBit i) (N.testBit i))

lemma mod_succ_ne (P N i : ℕ) : decide (P % 2^(i+1) ≠ N % 2^(i+1)) =
    (decide (P % 2^i ≠ N % 2^i) || xor (P.testBit i) (N.testBit i)) := by
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hu := Nat.mod_lt P hp
  have hw := Nat.mod_lt N hp
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_pow_succ]
  generalize P % 2 ^ i = u at *
  generalize N % 2 ^ i = w at *
  rcases Nat.mod_two_eq_zero_or_one (P / 2^i) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (N / 2^i) with h2 | h2 <;>
  simp only [h1, h2] <;>
  generalize 2 ^ i = Q at * <;>
  by_cases hc : u = w <;> simp [hc] <;> omega

lemma mod_succ_lt (P N i : ℕ) : decide (P % 2^(i+1) < N % 2^(i+1)) =
    ((!P.testBit i && N.testBit i) ||
      (!xor (P.testBit i) (N.testBit i) && decide (P % 2^i < N % 2^i))) := by
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hu := Nat.mod_lt P hp
  have hw := Nat.mod_lt N hp
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_pow_succ]
  generalize P % 2 ^ i = u at *
  generalize N % 2 ^ i = w at *
  rcases Nat.mod_two_eq_zero_or_one (P / 2^i) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (N / 2^i) with h2 | h2 <;>
  simp only [h1, h2] <;>
  generalize 2 ^ i = Q at * <;>
  by_cases hc : u < w <;> simp [hc] <;> omega

lemma extract {B : Bank n} {L : ℕ} (w : ℕ) {P N : (Fin n → Bool) → ℕ}
    (hP : HasNat B L P) (hN : HasNat B L N) :
    B.Grow (2 + 12 * L + w * (L + 1)) (fun D => D.Has (fun x => decide (P x ≠ N x)) ∧
      D.Has (fun x => decide (P x < N x)) ∧ ∀ ℓ < w, D.Has (fun x => lowE (P x) (N x) L ℓ)) := by
  have stage : ∀ i ≤ L, B.Grow (2 + 12 * i) (fun D =>
      D.Has (fun x => decide (P x % 2^i ≠ N x % 2^i)) ∧
      D.Has (fun x => decide (P x % 2^i < N x % 2^i)) ∧
      ∀ j < i, D.Has (fun x => decide (P x % 2^j = N x % 2^j) &&
        xor ((P x).testBit j) ((N x).testBit j))) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨D1, e1, c1, z1⟩ := B.const false
      obtain ⟨D2, e2, c2, z2⟩ := D1.const false
      refine ⟨D2, fun h => e2 (e1 h), by omega, hasCongr (e2 z1) (fun x => by simp [Nat.mod_one]),
        hasCongr z2 (fun x => by simp [Nat.mod_one]), fun j hj => absurd hj (by omega)⟩
    | succ i ih =>
      intro hi
      have := (ih (by omega)).bind (b := 12) (q := fun D =>
        D.Has (fun x => decide (P x % 2^(i+1) ≠ N x % 2^(i+1))) ∧
        D.Has (fun x => decide (P x % 2^(i+1) < N x % 2^(i+1))) ∧
        ∀ j < i+1, D.Has (fun x => decide (P x % 2^j = N x % 2^j) &&
          xor ((P x).testBit j) ((N x).testBit j))) (by
        intro D e hh
        obtain ⟨ho, hl, hs⟩ := hh
        have hp := e (hP.2 i (by omega))
        have hn := e (hN.2 i (by omega))
        obtain ⟨D1, e1, c1, d⟩ := xor2 hp hn
        obtain ⟨D2, e2, c2, o'⟩ := join (e1 ho) d
        obtain ⟨D3, e3, c3, np⟩ := inv (e2 (e1 hp))
        obtain ⟨D4, e4, c4, m1⟩ := meet np (e3 (e2 (e1 hn)))
        obtain ⟨D5, e5, c5, nd⟩ := inv (e4 (e3 (e2 d)))
        obtain ⟨D6, e6, c6, m2⟩ := meet nd (e5 (e4 (e3 (e2 (e1 hl)))))
        obtain ⟨D7, e7, c7, ltn⟩ := join (e6 (e5 m1)) m2
        obtain ⟨D8, e8, c8, nO⟩ := inv (e7 (e6 (e5 (e4 (e3 (e2 (e1 ho)))))))
        obtain ⟨D9, e9, c9, low⟩ := meet nO (e8 (e7 (e6 (e5 (e4 (e3 (e2 d)))))))
        have E : D.Ext D9 := fun h => e9 (e8 (e7 (e6 (e5 (e4 (e3 (e2 (e1 h))))))))
        refine ⟨D9, E, by omega, ?_, ?_, ?_⟩
        · exact e9 (e8 (e7 (e6 (e5 (e4 (e3 (hasCongr o' (fun x => (mod_succ_ne _ _ _).symm))))))))
        · exact e9 (e8 (hasCongr ltn (fun x => (mod_succ_lt _ _ _).symm)))
        · intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact E (hs j hj)
          · exact hasCongr low (fun x => by simp))
      exact this.weaken (by omega) (fun _ h => h)
  have fin := (stage L le_rfl).bind (b := w * (L + 1)) (q := fun D =>
      D.Has (fun x => decide (P x ≠ N x)) ∧
      D.Has (fun x => decide (P x < N x)) ∧ ∀ ℓ < w, D.Has (fun x => lowE (P x) (N x) L ℓ)) (by
    intro D e hh
    obtain ⟨ho, hl, hs⟩ := hh
    have := D.collectFin w (fun ℓ x => lowE (P x) (N x) L ℓ.val) (L + 1) (by
      intro E e' ℓ
      have := anyBits (B := E) ((List.range L).filter (fun i => i.testBit ℓ.val))
        (fun i x => decide (P x % 2^i = N x % 2^i) && xor ((P x).testBit i) ((N x).testBit i))
        (fun i hi => e' (hs i (by simpa using (List.mem_filter.mp hi).1)))
      have hlen := List.length_filter_le (fun i => i.testBit ℓ.val) (List.range L)
      rw [List.length_range] at hlen
      exact this.weaken (by omega) (fun _ h => h))
    obtain ⟨E, eE, cE, hE⟩ := this
    refine ⟨E, eE, cE, ?_, ?_, fun ℓ hℓ => hE ⟨ℓ, hℓ⟩⟩
    · exact eE (hasCongr ho (fun x => by rw [Nat.mod_eq_of_lt (hP.1 x), Nat.mod_eq_of_lt (hN.1 x)]))
    · exact eE (hasCongr hl (fun x => by rw [Nat.mod_eq_of_lt (hP.1 x), Nat.mod_eq_of_lt (hN.1 x)])))
  exact fin.weaken (by omega) (fun _ h => h)

end PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

variable {n : Nat}

def zb (z : ZMod 2) : Bool := decide (z ≠ 0)
def bz (b : Bool) : ZMod 2 := if b then 1 else 0
lemma zb_add (a c : ZMod 2) : zb (a + c) = xor (zb a) (zb c) := by revert a c; decide
lemma zb_mul (a c : ZMod 2) : zb (a * c) = (zb a && zb c) := by revert a c; decide
lemma zb_bz (b : Bool) : zb (bz b) = b := by cases b <;> decide
lemma bz_zb (z : ZMod 2) : bz (zb z) = z := by revert z; decide

inductive ZE (n : ℕ) where
  | atom : ((Fin n → Bool) → ZMod 2) → ZE n
  | cst : ZMod 2 → ZE n
  | add : ZE n → ZE n → ZE n
  | mul : ZE n → ZE n → ZE n

def ZE.eval : ZE n → (Fin n → Bool) → ZMod 2
  | .atom f, x => f x
  | .cst c, _ => c
  | .add a b, x => a.eval x + b.eval x
  | .mul a b, x => a.eval x * b.eval x

def ZE.cost : ZE n → ℕ
  | .atom _ => 0
  | .cst _ => 1
  | .add a b => a.cost + b.cost + 4
  | .mul a b => a.cost + b.cost + 1

def ZE.Ok (B : Bank n) : ZE n → Prop
  | .atom f => B.Has (fun x => zb (f x))
  | .cst _ => True
  | .add a b => a.Ok B ∧ b.Ok B
  | .mul a b => a.Ok B ∧ b.Ok B

lemma ZE.ok_mono {B D : Bank n} (e : B.Ext D) : ∀ (E : ZE n), E.Ok B → E.Ok D
  | .atom _, h => e h
  | .cst _, h => h
  | .add a b, h => ⟨ok_mono e a h.1, ok_mono e b h.2⟩
  | .mul a b, h => ⟨ok_mono e a h.1, ok_mono e b h.2⟩

lemma ZE.build {B : Bank n} : ∀ (E : ZE n), E.Ok B →
    B.Grow E.cost (fun D => D.Has (fun x => zb (E.eval x)))
  | .atom f, h => Grow.pure B h
  | .cst c, _ => by simpa [ZE.cost, ZE.eval] using B.const (zb c)
  | .add a b, h => by
      have := (build a h.1).bind (b := b.cost + 4)
        (q := fun D => D.Has (fun x => zb ((ZE.add a b).eval x))) (fun D e ha =>
        (build b (ok_mono e b h.2)).bind (b := 4)
          (q := fun D => D.Has (fun x => zb ((ZE.add a b).eval x))) (fun D' e' hb => by
          have := xor2 (e' ha) hb
          simpa [ZE.eval, zb_add] using this))
      simpa [ZE.cost, Nat.add_assoc] using this
  | .mul a b, h => by
      have := (build a h.1).bind (b := b.cost + 1)
        (q := fun D => D.Has (fun x => zb ((ZE.mul a b).eval x))) (fun D e ha =>
        (build b (ok_mono e b h.2)).bind (b := 1)
          (q := fun D => D.Has (fun x => zb ((ZE.mul a b).eval x))) (fun D' e' hb => by
          have := meet (e' ha) hb
          simpa [ZE.eval, zb_mul] using this))
      simpa [ZE.cost, Nat.add_assoc] using this

end PEqualNP.Outside.L_meta_25887_aux.Builder.Bank


namespace PEqualNP.Outside.L_meta_25887_aux

open Finset

def lowE (P N L ℓ : ℕ) : Bool :=
  ((List.range L).filter (fun i => i.testBit ℓ)).any
    (fun i => decide (P % 2^i = N % 2^i) && xor (P.testBit i) (N.testBit i))

lemma low_iff_aux (N e i : ℕ) :
    (decide ((N + 2^e) % 2^i = N % 2^i) && xor ((N + 2^e).testBit i) (N.testBit i)) =
      decide (i = e) := by
  have bitE : (N + 2^e).testBit e = !N.testBit e := by
    rw [add_comm]; exact Nat.testBit_two_pow_add_eq N e
  have modle : ∀ j ≤ e, (N + 2^e) % 2^j = N % 2^j := by
    intro j hj
    have : 2^e = 2^j * 2^(e-j) := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.add_mul_mod_self_left]
  rcases lt_trichotomy i e with h | rfl | h
  · have m := modle (i+1) (by omega)
    have b1 : (N + 2^e).testBit i = N.testBit i := by
      have := congrArg (fun z => z.testBit i) m
      simpa [Nat.testBit_mod_two_pow] using this
    simp [b1, show i ≠ e by omega]
  · simp [modle i le_rfl, bitE]
  · have : (N + 2^e) % 2^i ≠ N % 2^i := by
      intro hm
      have h2 : (N + 2^e) % 2^(e+1) = N % 2^(e+1) := by
        have d : 2^(e+1) ∣ 2^i := Nat.pow_dvd_pow 2 (by omega)
        rw [← Nat.mod_mod_of_dvd (N + 2^e) d, hm, Nat.mod_mod_of_dvd N d]
      have := congrArg (fun z => z.testBit e) h2
      simp [Nat.testBit_mod_two_pow, bitE] at this
    simp [this, show i ≠ e by omega]

lemma lowE_eq {P N L e : ℕ} (hP : P < 2^L) (hN : N < 2^L) (h : P = N + 2^e ∨ N = P + 2^e)
    (ℓ : ℕ) : lowE P N L ℓ = e.testBit ℓ := by
  have low : ∀ i, (decide (P % 2^i = N % 2^i) && xor (P.testBit i) (N.testBit i)) =
      decide (i = e) := by
    intro i
    rcases h with rfl | rfl
    · exact low_iff_aux N e i
    · rw [← low_iff_aux P e i, Bool.xor_comm]
      congr 1
      exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
  have eL : e < L := by
    have : 2^e < 2^L := by rcases h with rfl | rfl <;> omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  unfold lowE
  simp only [low]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
  · intro hb; exact ⟨e, ⟨eL, hb⟩, rfl⟩

/-! the cyclic chain -/

def selN (a g : Bool) (p q : ℕ) : ℕ := if (a && !g) then p else if (a && g) then q else 0

def runPN (al sgn : ℕ → Bool → Bool → Bool) (st : Bool) : ℕ → (Bool → ℕ) × (Bool → ℕ)
  | 0 => (fun v => if v = st then 1 else 0, fun _ => 0)
  | i+1 =>
    (fun v => selN (al i false v) (sgn i false v) ((runPN al sgn st i).1 false)
        ((runPN al sgn st i).2 false) +
      selN (al i true v) (sgn i true v) ((runPN al sgn st i).1 true) ((runPN al sgn st i).2 true),
     fun v => selN (al i false v) (sgn i false v) ((runPN al sgn st i).2 false)
        ((runPN al sgn st i).1 false) +
      selN (al i true v) (sgn i true v) ((runPN al sgn st i).2 true) ((runPN al sgn st i).1 true))

def phiB (al sgn : ℕ → Bool → Bool → Bool) (i : ℕ) (u v : Bool) : ℤ :=
  if al i u v then (if sgn i u v then -1 else 1) else 0

def runD (φ : ℕ → Bool → Bool → ℤ) (st : Bool) : ℕ → Bool → ℤ
  | 0 => fun v => if v = st then 1 else 0
  | i+1 => fun v => runD φ st i false * φ i false v + runD φ st i true * φ i true v

lemma runPN_bound (al sgn : ℕ → Bool → Bool → Bool) (st : Bool) :
    ∀ i v, (runPN al sgn st i).1 v < 2^(i+1) ∧ (runPN al sgn st i).2 v < 2^(i+1) := by
  intro i
  induction i with
  | zero => intro v; simp only [runPN]; constructor <;> (try split_ifs) <;> norm_num
  | succ i ih =>
    intro v
    have hf := ih false
    have ht := ih true
    have sb : ∀ a g p q, p < 2^(i+1) → q < 2^(i+1) → selN a g p q < 2^(i+1) := by
      intro a g p q hp hq; unfold selN; split_ifs <;> first | exact hp | exact hq | positivity
    simp only [runPN]
    rw [pow_succ]
    refine ⟨?_, ?_⟩
    · have := sb (al i false v) (sgn i false v) _ _ hf.1 hf.2
      have := sb (al i true v) (sgn i true v) _ _ ht.1 ht.2
      omega
    · have := sb (al i false v) (sgn i false v) _ _ hf.2 hf.1
      have := sb (al i true v) (sgn i true v) _ _ ht.2 ht.1
      omega

lemma sel_diff (a g : Bool) (p q : ℕ) : (selN a g p q : ℤ) - selN a g q p =
    ((p : ℤ) - q) * (if a then (if g then -1 else 1) else 0) := by
  cases a <;> cases g <;> simp [selN]

lemma runPN_diff (al sgn : ℕ → Bool → Bool → Bool) (st : Bool) :
    ∀ i v, ((runPN al sgn st i).1 v : ℤ) - (runPN al sgn st i).2 v =
      runD (phiB al sgn) st i v := by
  intro i
  induction i with
  | zero => intro v; simp only [runPN, runD]; split_ifs <;> simp
  | succ i ih =>
    intro v
    simp only [runPN, runD, phiB]
    push_cast
    rw [← ih false, ← ih true]
    linear_combination sel_diff (al i false v) (sgn i false v) ((runPN al sgn st i).1 false)
      ((runPN al sgn st i).2 false) + sel_diff (al i true v) (sgn i true v)
      ((runPN al sgn st i).1 true) ((runPN al sgn st i).2 true)

lemma sum_snoc {M : Type} [AddCommMonoid M] (j : ℕ) (F : (Fin (j+1) → Bool) → M) :
    ∑ y, F y = ∑ y : Fin j → Bool, ∑ w : Bool, F (Fin.snoc y w) := by
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

def pathP (φ : ℕ → Bool → Bool → ℤ) (j : ℕ) (y : Fin (j+1) → Bool) : ℤ :=
  ∏ i : Fin j, φ i (y i.castSucc) (y i.succ)

lemma pathP_snoc (φ : ℕ → Bool → Bool → ℤ) (j : ℕ) (y : Fin (j+1) → Bool) (w : Bool) :
    pathP φ (j+1) (Fin.snoc y w) = pathP φ j y * φ j (y (Fin.last j)) w := by
  unfold pathP
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
  · simp

lemma snoc0 {j : ℕ} (y : Fin (j+1) → Bool) (w : Bool) : (Fin.snoc y w : Fin (j+2) → Bool) 0 = y 0 := by
  have : (0 : Fin (j+2)) = Fin.castSucc 0 := rfl
  rw [this, Fin.snoc_castSucc]

lemma runD_path (φ : ℕ → Bool → Bool → ℤ) (st : Bool) : ∀ j v, runD φ st j v =
    ∑ y : Fin (j+1) → Bool, if y 0 = st ∧ y (Fin.last j) = v then pathP φ j y else 0 := by
  intro j
  induction j with
  | zero =>
    intro v
    rw [sum_snoc]
    simp only [runD, pathP, Finset.univ_unique, Finset.sum_singleton, Fintype.sum_bool,
      Finset.univ_eq_empty, Finset.prod_empty]
    cases st <;> cases v <;> simp [Fin.snoc]
  | succ j ih =>
    intro v
    rw [sum_snoc]
    simp only [runD, ih]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Fintype.sum_bool]
    simp only [pathP_snoc, Fin.snoc_last, snoc0]
    cases hl : y (Fin.last j) <;> cases v <;> by_cases h0 : y 0 = st <;> simp [h0, hl]

theorem chain (k : ℕ) (hk : 0 < k) (φ : ℕ → Bool → Bool → ℤ) :
    runD φ false k false + runD φ true k true =
      ∑ y : Fin k → Bool, ∏ i : Fin k, φ i (y i) (y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) := by
  rw [runD_path, runD_path, ← Finset.sum_add_distrib]
  have e : ∀ y : Fin (k+1) → Bool,
      ((if y 0 = false ∧ y (Fin.last k) = false then pathP φ k y else 0) +
        (if y 0 = true ∧ y (Fin.last k) = true then pathP φ k y else 0)) =
      if y 0 = y (Fin.last k) then pathP φ k y else 0 := by
    intro y; cases h0 : y 0 <;> cases hl : y (Fin.last k) <;> simp
  rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => fun i : Fin k => y i.castSucc)
    (fun z => fun i : Fin (k+1) => z ⟨i.val % k, Nat.mod_lt _ hk⟩)
  · intros; simp
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero, Fin.val_last,
      Nat.zero_mod, Nat.mod_self]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    funext i
    rcases Nat.lt_or_ge i.val k with h | h
    · beta_reduce; congr 1; ext; simp [Nat.mod_eq_of_lt h]
    · have : i = Fin.last k := Fin.ext (by simp; omega)
      subst this
      simp only [Fin.val_last, Nat.mod_self]
      rw [← hy]; rfl
  · intro z _
    funext i
    simp [Nat.mod_eq_of_lt i.isLt]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold pathP
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    rcases Nat.lt_or_ge (i.val + 1) k with h | h
    · beta_reduce; congr 1; ext; simp [Nat.mod_eq_of_lt h]
    · have hi : i.succ = Fin.last k := Fin.ext (by simp; omega)
      rw [hi, ← hy]
      have : (i.val + 1) % k = 0 := by rw [show i.val + 1 = k by omega, Nat.mod_self]
      beta_reduce; congr 1; ext; simp [this]


end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux

open Finset
open Builder.Bank (zb bz zb_bz bz_zb zb_add zb_mul)

/-! index shifts -/

lemma mod_back {k : ℕ} (a j : ℕ) (hk : 0 < k) (hj : j < k) :
    ((j + a) % k + k - a % k) % k = j := by
  have ha : a % k < k := Nat.mod_lt _ hk
  rw [Nat.add_mod j a k, Nat.mod_eq_of_lt hj]
  generalize a % k = c at ha ⊢
  by_cases h : j + c < k
  · rw [Nat.mod_eq_of_lt h, show j + c + k - c = j + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  · have e : (j + c) % k = j + c - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e, show j + c - k + k - c = j by omega, Nat.mod_eq_of_lt hj]

lemma mod_fwd {k : ℕ} (a i : ℕ) (hk : 0 < k) (hi : i < k) :
    ((i + k - a % k) % k + a) % k = i := by
  have ha : a % k < k := Nat.mod_lt _ hk
  rw [Nat.add_mod _ a k, Nat.mod_mod]
  generalize a % k = c at ha ⊢
  by_cases h : c ≤ i
  · rw [show i + k - c = (i - c) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : i - c < k), show i - c + c = i by omega, Nat.mod_eq_of_lt hi]
  · rw [Nat.mod_eq_of_lt (by omega : i + k - c < k), show i + k - c + c = i + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]

def shiftE (k : ℕ) (hk : 0 < k) (a : ℕ) : Fin k ≃ Fin k where
  toFun j := ix k hk (j.val + a)
  invFun i := ix k hk (i.val + k - a % k)
  left_inv j := Fin.ext (by simp only [ix]; exact mod_back a j.val hk j.isLt)
  right_inv i := Fin.ext (by simp only [ix]; exact mod_fwd a i.val hk i.isLt)

section MathA
variable {k : ℕ} (hk : 0 < k)

lemma ix_val (i : Fin k) : ix k hk i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

lemma ix_two (m : ℕ) : ix k hk (m + 2) = ix k hk ((ix k hk (m+1)).val + 1) := by
  apply Fin.ext
  show (m+2) % k = ((m+1) % k + 1) % k
  rw [Nat.add_mod ((m+1) % k), Nat.mod_mod, ← Nat.add_mod]

lemma mm_add (gap : ℕ) (x y : V k) : mm k hk gap (x + y) = mm k hk gap x + mm k hk gap y := by
  funext j; simp only [mm, Pi.add_apply]; ring

lemma mm_sym (gap : ℕ) (γ x : V k) :
    dotProduct γ (mm k hk gap x) = dotProduct (mm k hk gap γ) x := by
  have e1 : ∀ j : Fin k, ix k hk (j.val + gap) = shiftE k hk gap j := fun _ => rfl
  have e2 : ∀ j : Fin k, ix k hk (j.val + k - gap % k) = (shiftE k hk gap).symm j := fun _ => rfl
  simp only [dotProduct, mm, e1, e2, mul_add, add_mul, Finset.sum_add_distrib]
  have s1 : ∑ j, γ j * x (shiftE k hk gap j) = ∑ i, γ ((shiftE k hk gap).symm i) * x i := by
    rw [← Equiv.sum_comp (shiftE k hk gap).symm]; simp
  have s2 : ∑ j, γ j * x ((shiftE k hk gap).symm j) = ∑ i, γ (shiftE k hk gap i) * x i := by
    rw [← Equiv.sum_comp (shiftE k hk gap)]; simp
  rw [s1, s2]; ring

end MathA

lemma univZ2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

lemma orth {k : ℕ} (v : V k) :
    ∑ γ : V k, sg (dotProduct γ v) = if v = 0 then (2:ℤ)^k else 0 := by
  have h1 : ∀ γ : V k, sg (dotProduct γ v) = ∏ j, sg (γ j * v j) := fun γ => by
    rw [dotProduct, sg_sum]
  simp only [h1]
  rw [← Fintype.prod_sum (fun j (a : ZMod 2) => sg (a * v j))]
  have h2 : ∀ j, ∑ a : ZMod 2, sg (a * v j) = if v j = 0 then 2 else 0 := by
    intro j
    rw [univZ2, Finset.sum_pair (by decide)]
    rcases z01 (v j) with h | h <;> rw [h] <;> decide
  simp only [h2]
  rw [Finset.prod_ite_zero]
  by_cases hv : v = 0
  · subst hv; simp
  · have : ¬ ∀ i ∈ (Finset.univ : Finset (Fin k)), v i = 0 := by
      intro h; apply hv; funext i; exact h i (Finset.mem_univ _)
    rw [if_neg this, if_neg hv]

lemma orth' {k : ℕ} (v : V k) :
    ∑ x : V k, sg (dotProduct v x) = if v = 0 then (2:ℤ)^k else 0 := by
  rw [← orth v]; simp only [dotProduct_comm v]

theorem fourier {k : ℕ} (M : V k → V k) (hlin : ∀ x y, M (x + y) = M x + M y)
    (hsym : ∀ x y, dotProduct x (M y) = dotProduct (M x) y) (F : V k → ℤ) (b : V k) :
    ∑ x, F (M x) * sg (dotProduct b x) =
      ∑ γ ∈ Finset.univ.filter (fun γ => M γ = b), ∑ y, F y * sg (dotProduct γ y) := by
  have two : (2 : ZMod 2) = 0 := rfl
  have hpos : (0:ℤ) < 2^k := by positivity
  apply mul_left_cancel₀ hpos.ne'
  have L1 : ∀ x, (2:ℤ)^k * (F (M x) * sg (dotProduct b x)) =
      ∑ y, ∑ γ, F y * sg (dotProduct b x) * sg (dotProduct γ (y + M x)) := by
    intro x
    simp only [← Finset.mul_sum, orth]
    have : ∀ y, (y + M x = 0 ↔ y = M x) := fun y => by
      constructor
      · intro h
        have := congrArg (· + M x) h
        simpa [add_assoc, vv] using this
      · rintro rfl; exact vv _
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]; ring
  have R1 : ∀ γ, (2:ℤ)^k * (if M γ = b then ∑ y, F y * sg (dotProduct γ y) else 0) =
      ∑ y, ∑ x, F y * sg (dotProduct γ y) * sg (dotProduct (b + M γ) x) := by
    intro γ
    simp only [← Finset.mul_sum, orth']
    have : (b + M γ = 0 ↔ M γ = b) := by
      constructor
      · intro h
        funext j
        have := congrFun h j
        simp only [Pi.add_apply, Pi.zero_apply] at this
        linear_combination this - b j * two
      · intro h; rw [h]; exact vv _
    simp only [this]
    split_ifs
    · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun y _ => by ring)
    · simp
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun x _ => L1 x)]
  rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_congr rfl (fun γ _ => R1 γ)]
  have pt : ∀ x y γ, F y * sg (dotProduct b x) * sg (dotProduct γ (y + M x)) =
      F y * sg (dotProduct γ y) * sg (dotProduct (b + M γ) x) := by
    intro x y γ
    rw [dotProduct_add, add_dotProduct, hsym, sg_add, sg_add]; ring
  simp only [pt]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (V k))) (t := (Finset.univ : Finset (V k)))
    (f := fun γ y => ∑ x, F y * sg (dotProduct γ y) * sg (dotProduct (b + M γ) x))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_comm]

/-! sections of the mixer -/

section Sec
open Matrix
variable {k : ℕ} (hk : 0 < k)

def mmL (gap : ℕ) : V k →ₗ[ZMod 2] V k where
  toFun := mm k hk gap
  map_add' x y := mm_add hk gap x y
  map_smul' c x := by funext j; simp only [mm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma sec_exists (gap : ℕ) : ∃ S : Matrix (Fin k) (Fin k) (ZMod 2),
    ∀ b, (∃ x, mm k hk gap x = b) → mm k hk gap (S *ᵥ b) = b := by
  let f := mmL hk gap
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict f)
  obtain ⟨p, hp⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (g ∘ₗ p), fun b ⟨x, hx⟩ => ?_⟩
  have hb : b ∈ LinearMap.range f := ⟨x, hx⟩
  rw [LinearMap.toMatrix'_mulVec]
  have e1 : p b = ⟨b, hb⟩ := LinearMap.congr_fun hp ⟨b, hb⟩
  have e2 := LinearMap.congr_fun hg (p b)
  have e3 : f (g (p b)) = b := by
    have := congrArg Subtype.val e2
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [e1] at this ⊢
    exact this
  exact e3

lemma ker_zero (gap : ℕ) (hg1 : 1 ≤ gap) (hg2 : gap ≤ 2) (z : V k)
    (hz : mm k hk gap z = 0) (h4 : ∀ i : Fin k, i.val < 4 → z i = 0) : z = 0 := by
  have main : ∀ i (hi : i < k), z ⟨i, hi⟩ = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h : i < 4
      · exact h4 ⟨i, hi⟩ h
      · have hz' := congrFun hz ⟨i - gap, by omega⟩
        simp only [mm, Pi.zero_apply] at hz'
        have a1 : ix k hk (i - gap + gap) = ⟨i, hi⟩ := Fin.ext (by
          simp only [ix]; rw [show i - gap + gap = i by omega, Nat.mod_eq_of_lt hi])
        have a2 : ix k hk (i - gap + k - gap % k) = ⟨i - 2 * gap, by omega⟩ := Fin.ext (by
          simp only [ix]
          rw [Nat.mod_eq_of_lt (show gap < k by omega),
            show i - gap + k - gap = (i - 2 * gap) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)])
        rw [a1, a2, ih (i - gap) (by omega) (by omega), ih (i - 2 * gap) (by omega) (by omega)]
          at hz'
        simpa using hz'
  funext i; exact main i.val i.isLt

lemma ker_card (gap : ℕ) (hg1 : 1 ≤ gap) (hg2 : gap ≤ 2) :
    (Finset.univ.filter (fun z : V k => mm k hk gap z = 0)).card ≤ 16 := by
  let ρ : V k → (Fin 4 → ZMod 2) := fun z i => if h : i.val < k then z ⟨i.val, h⟩ else 0
  have hc : (Finset.univ : Finset (Fin 4 → ZMod 2)).card = 16 := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card]; rfl
  rw [← hc]
  apply Finset.card_le_card_of_injOn ρ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  intro z1 h1 z2 h2 he
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h1 h2
  have hz : mm k hk gap (z1 + z2) = 0 := by rw [mm_add, h1, h2, add_zero]
  have := ker_zero hk gap hg1 hg2 (z1 + z2) hz (fun i hi => by
    have := congrFun he ⟨i.val, hi⟩
    simp only [ρ, i.isLt, dif_pos] at this
    simp only [Pi.add_apply, this, zz])
  funext j
  have := congrFun this j
  simp only [Pi.add_apply, Pi.zero_apply] at this
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination this - z2 j * two

lemma fiber_sum (gap : ℕ) (S : Matrix (Fin k) (Fin k) (ZMod 2))
    (hS : ∀ b, (∃ x, mm k hk gap x = b) → mm k hk gap (S *ᵥ b) = b) (T : V k → ℤ) (b : V k) :
    ∑ γ ∈ Finset.univ.filter (fun γ => mm k hk gap γ = b), T γ =
      if mm k hk gap (S *ᵥ b) = b then
        ∑ z ∈ Finset.univ.filter (fun z => mm k hk gap z = 0), T (S *ᵥ b + z) else 0 := by
  split_ifs with h
  · symm
    apply Finset.sum_nbij' (fun z => S *ᵥ b + z) (fun γ => γ + S *ᵥ b)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [mm_add, h, hz, add_zero]
    · intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      rw [mm_add, h, hγ, vv]
    · intro z _
      show S *ᵥ b + z + S *ᵥ b = z
      rw [add_right_comm, vv, zero_add]
    · intro γ _
      show S *ᵥ b + (γ + S *ᵥ b) = γ
      rw [add_comm γ, ← add_assoc, vv, zero_add]
    · intro z _; rfl
  · apply Finset.sum_eq_zero
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    exact absurd (hS b ⟨γ, hγ⟩) h

end Sec

end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux

open Finset
open Builder.Bank (zb bz zb_bz bz_zb zb_add zb_mul)

def zbE : ZMod 2 ≃ Bool := ⟨zb, bz, bz_zb, zb_bz⟩

lemma chainSum {k : ℕ} (hk : 0 < k) (al sgn : ℕ → Bool → Bool → Bool) :
    ∑ y : V k, (if ∀ i : Fin k, al i (zb (y i)) (zb (y (ix k hk (i.val+1)))) = true then
      sg (∑ i : Fin k, bz (sgn i (zb (y i)) (zb (y (ix k hk (i.val+1)))))) else 0) =
    runD (phiB al sgn) false k false + runD (phiB al sgn) true k true := by
  rw [chain k hk]
  let e : V k ≃ (Fin k → Bool) := Equiv.arrowCongr (Equiv.refl _) zbE
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show (if ∀ i : Fin k, al i (zb (y i)) (zb (y (ix k hk (i.val+1)))) = true then
      sg (∑ i : Fin k, bz (sgn i (zb (y i)) (zb (y (ix k hk (i.val+1)))))) else 0) =
    ∏ i : Fin k, phiB al sgn i (zb (y i)) (zb (y (ix k hk (i.val+1))))
  by_cases hall : ∀ i : Fin k, al i (zb (y i)) (zb (y (ix k hk (i.val+1)))) = true
  · rw [if_pos hall, sg_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [phiB, hall i, if_true]
    cases sgn i _ _ <;> rfl
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨i, hi⟩ := hall
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [phiB, hi])).symm

section Pair
variable {k : ℕ} (hk : 0 < k)

def jp (i : Fin k) : Fin k := (shiftE k hk 1).symm i

lemma jp_one (i : Fin k) : ix k hk ((jp hk i).val + 1) = i := (shiftE k hk 1).apply_symm_apply i

lemma jp_two (i : Fin k) : ix k hk ((jp hk i).val + 2) = ix k hk (i.val + 1) := by
  rw [ix_two, jp_one]

/-- the local condition of one tested difference at the pair ending at `i` -/
def Ecnd (U cc d : V k) (i : Fin k) (u v : Bool) : ZMod 2 :=
  U (jp hk i) + (1 + bz u) * U (ix k hk ((jp hk i).val + 2)) +
    U (ix k hk ((jp hk i).val + 1)) * (bz v + U (ix k hk ((jp hk i).val + 2))) +
    cc (jp hk i) + d (jp hk i)

def alS {s : ℕ} (U cc d : Fin s → V k) (n : ℕ) (u v : Bool) : Bool :=
  decide (∀ p, Ecnd hk (U p) (cc p) (d p) (ix k hk n) u v = 0)

def sgnS (bt γ : V k) (n : ℕ) (u v : Bool) : Bool :=
  zb ((bt (ix k hk n) + γ (ix k hk n)) * bz u + bt (jp hk (ix k hk n)) * (1 + bz u) * bz v)

def alR (test target : V k) (n : ℕ) (u _v : Bool) : Bool :=
  decide (test (ix k hk n) ≠ 0 → bz u = target (ix k hk n))

def sgnR (b' : V k) (n : ℕ) (u _v : Bool) : Bool := zb (b' (ix k hk n) * bz u)

lemma pairT {s : ℕ} (U cc d : Fin s → V k) (bt γ y : V k) :
    (if (∀ p, Lf k hk (y + U p) - Lf k hk y + cc p = d p) then
        sg (dotProduct bt (Lf k hk y)) else 0) * sg (dotProduct γ y) =
    (if ∀ i : Fin k, alS hk U cc d i (zb (y i)) (zb (y (ix k hk (i.val+1)))) = true then
      sg (∑ i : Fin k, bz (sgnS hk bt γ i (zb (y i)) (zb (y (ix k hk (i.val+1)))))) else 0) := by
  have two : (2 : ZMod 2) = 0 := rfl
  have cond : (∀ p, Lf k hk (y + U p) - Lf k hk y + cc p = d p) ↔
      ∀ i : Fin k, alS hk U cc d i (zb (y i)) (zb (y (ix k hk (i.val+1)))) = true := by
    simp only [alS, ix_val, decide_eq_true_eq, Ecnd, bz_zb, jp_one, jp_two]
    constructor
    · intro h i p
      have := congrFun (h p) (jp hk i)
      simp only [Pi.add_apply, Pi.sub_apply, Lf, jp_one, jp_two] at this
      linear_combination this + d p (jp hk i) * two
    · intro h p
      funext j
      have hj : j = jp hk (shiftE k hk 1 j) := ((shiftE k hk 1).symm_apply_apply j).symm
      have := h (shiftE k hk 1 j) p
      rw [hj]
      simp only [Pi.add_apply, Pi.sub_apply, Lf, jp_one, jp_two]
      linear_combination this - d p (jp hk (shiftE k hk 1 j)) * two
  have phase : sg (dotProduct bt (Lf k hk y)) * sg (dotProduct γ y) =
      sg (∑ i : Fin k, bz (sgnS hk bt γ i (zb (y i)) (zb (y (ix k hk (i.val+1)))))) := by
    rw [← sg_add]
    congr 1
    simp only [sgnS, ix_val, bz_zb, dotProduct, Lf]
    have re : ∑ j, bt j * ((1 + y (ix k hk (j.val+1))) * y (ix k hk (j.val+2))) =
        ∑ i, bt (jp hk i) * (1 + y i) * y (ix k hk (i.val+1)) := by
      rw [← Equiv.sum_comp (shiftE k hk 1).symm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have e1 := jp_one hk i
      have e2 := jp_two hk i
      simp only [jp] at e1 e2 ⊢
      rw [e1, e2]; ring
    simp only [mul_add, add_mul, Finset.sum_add_distrib] at re ⊢
    linear_combination re
  by_cases hc : ∀ p, Lf k hk (y + U p) - Lf k hk y + cc p = d p
  · rw [if_pos hc, if_pos (cond.1 hc), phase]
  · rw [if_neg hc, if_neg (fun h => hc (cond.2 h)), zero_mul]

lemma pairR (test target b' x : V k) :
    (if ∀ j, test j ≠ 0 → x j = target j then sg (dotProduct b' x) else 0) =
    (if ∀ i : Fin k, alR hk test target i (zb (x i)) (zb (x (ix k hk (i.val+1)))) = true then
      sg (∑ i : Fin k, bz (sgnR hk b' i (zb (x i)) (zb (x (ix k hk (i.val+1)))))) else 0) := by
  simp only [alR, sgnR, ix_val, bz_zb, decide_eq_true_eq, dotProduct]

end Pair

/-! power of two for each local sum -/

section Pow
variable {k : ℕ} (hk : 0 < k)

lemma lin_mm (gap : ℕ) (j : Fin k) : Lin (fun x : V k => mm k hk gap x j) := fun x y => by
  simp only [mm, Pi.add_apply]; ring

lemma lin_dot (b : V k) : Lin (fun x : V k => dotProduct b x) := fun x y => dotProduct_add b x y

lemma q2_layer (gap : ℕ) (j : Fin k) : Q2 (fun x : V k => layer k hk gap x j) := by
  have e : (fun x : V k => layer k hk gap x j) = fun x =>
      (mm k hk gap x j + mm k hk gap x (ix k hk (j.val+2))) +
        mm k hk gap x (ix k hk (j.val+1)) * mm k hk gap x (ix k hk (j.val+2)) := by
    funext x; simp only [layer, Lf]; ring
  rw [e]
  exact q2_add (q2_add (q2_lin (lin_mm hk gap _)) (q2_lin (lin_mm hk gap _)))
    (q2_mul (lin_mm hk gap _) (lin_mm hk gap _))

variable {r s : ℕ} {gap : ℕ} {inject : ℕ → ℕ}

lemma q2_qT (b : Fin r → V k) (t : Fin (r+1)) : Q2 (qT k hk r gap b t) := by
  unfold qT
  by_cases h : t.val < r
  · simp only [dif_pos h]
    refine q2_add ?_ (q2_lin (lin_dot _))
    simp only [dotProduct]
    exact q2_sum _ _ (fun j => q2_smul _ (q2_layer hk gap j))
  · simp only [dif_neg h, zero_add]
    exact q2_lin (lin_dot _)

lemma cond_closed (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k) (test target : V k)
    (t : Fin (r+1)) (x y z : V k)
    (hx : condT k hk r s gap inject delta path test target t x)
    (hy : condT k hk r s gap inject delta path test target t y)
    (hz : condT k hk r s gap inject delta path test target t z) :
    condT k hk r s gap inject delta path test target t (x + y + z) := by
  have two : (2 : ZMod 2) = 0 := rfl
  unfold condT at *
  by_cases h : t.val < r
  · simp only [dif_pos h] at *
    intro p
    funext j
    have Q := q2_layer hk gap j (path t p) x y z
    have hx' := congrFun (hx p) j
    have hy' := congrFun (hy p) j
    have hz' := congrFun (hz p) j
    simp only [Pi.add_apply, Pi.sub_apply] at hx' hy' hz' ⊢
    linear_combination Q + hx' + hy' + hz' +
      (layer k hk gap x j + layer k hk gap y j + layer k hk gap z j - layer k hk gap (x+y+z) j
        - rot k hk (inject t.val) (delta p) j + path ⟨t.val+1, by omega⟩ p j) * two
  · simp only [dif_neg h] at *
    intro j hj
    have := hx j hj; have := hy j hj; have := hz j hj
    simp only [Pi.add_apply]
    linear_combination hx j hj + hy j hj + hz j hj + target j * two

lemma ST_pow (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k) (test target : V k)
    (b : Fin r → V k) (t : Fin (r+1)) :
    ST k hk r s gap inject delta path test target b t = 0 ∨
      ∃ e, (ST k hk r s gap inject delta path test target b t).natAbs = 2 ^ e := by
  classical
  have : ST k hk r s gap inject delta path test target b t =
      ∑ x ∈ Finset.univ.filter (fun x => condT k hk r s gap inject delta path test target t x),
        sg (qT k hk r gap b t x) := by
    rw [ST, Finset.sum_filter]
  rw [this]
  refine gauss _ ?_ _ (q2_qT hk b t)
  intro x hx y hy z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz ⊢
  exact cond_closed hk delta path test target t x y z hx hy hz

lemma ST_le (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k) (test target : V k)
    (b : Fin r → V k) (t : Fin (r+1)) :
    (ST k hk r s gap inject delta path test target b t).natAbs ≤ 2 ^ k := by
  classical
  have h1 : |ST k hk r s gap inject delta path test target b t| ≤ 2 ^ k := by
    unfold ST
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x : V k, |(if condT k hk r s gap inject delta path test target t x then
        sg (qT k hk r gap b t x) else 0)| ≤ 1 := by
      intro x; split_ifs <;> simp [sg] <;> split_ifs <;> simp
    refine (Finset.sum_le_sum (fun x _ => this x)).trans ?_
    simp [Finset.card_univ, Fintype.card_fun, ZMod.card]
  have h2 : ((ST k hk r s gap inject delta path test target b t).natAbs : ℤ) ≤ 2 ^ k := by
    rw [Int.natCast_natAbs]; exact h1
  exact_mod_cast h2

lemma log_le_of {n k : ℕ} (h : n ≤ 2 ^ k) : Nat.log2 n ≤ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.log2_zero]
  · have := (Nat.log2_lt hn.ne').mpr (lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num)
      (Nat.lt_succ_self k)))
    omega

end Pow

end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux.Builder.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

lemma wires_getD_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    ((⟨gs,0⟩ : Circuit).wires x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    have hl := wireLen gs x
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih hl ⊢
    rw [List.getD_append _ _ _ _ (by omega)]
    exact ih

lemma inputHas (B : Bank n) (i : Fin n) : B.Has (fun x => x i) := by
  refine ⟨i, by omega, fun x => ?_⟩
  unfold val
  rw [wires_getD_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma natConst {B : Bank n} (hf : B.Has (fun _ => false)) (ht : B.Has (fun _ => true))
    {c L : ℕ} (hc : c < 2 ^ L) : HasNat B L (fun _ => c) := by
  refine ⟨fun _ => hc, fun i _ => ?_⟩
  cases h : c.testBit i
  · exact hasCongr hf (fun _ => h.symm)
  · exact hasCongr ht (fun _ => h.symm)

lemma HasNat.congr {B : Bank n} {L : ℕ} {U W : (Fin n → Bool) → ℕ} (h : HasNat B L U)
    (e : ∀ x, U x = W x) : HasNat B L W := by
  have : U = W := funext e
  exact this ▸ h

lemma truncate {B : Bank n} {L : ℕ} {U : (Fin n → Bool) → ℕ} (h : HasNat B (L+1) U)
    (hb : ∀ x, U x < 2 ^ L) : HasNat B L U :=
  ⟨hb, fun i hi => h.2 i (by omega)⟩

lemma sumList {α : Type} (B : Bank n) (l : List α) (f : α → (Fin n → Bool) → ℕ) (L : ℕ)
    (hb : ∀ x, (l.map (fun a => f a x)).sum < 2 ^ L) (hf : ∀ a ∈ l, HasNat B L (f a))
    (z : B.Has (fun _ => false)) :
    B.Grow (l.length * (11 * L + 1))
      (fun D => HasNat D L (fun x => (l.map (fun a => f a x)).sum)) := by
  induction l with
  | nil =>
    exact (Grow.pure B (p := fun D => HasNat D L (fun x => (([] : List α).map (fun a => f a x)).sum))
      ⟨fun x => by simp, fun i _ => hasCongr z (fun x => by simp)⟩).weaken (Nat.zero_le _)
        (fun _ h => h)
  | cons a l ih =>
    have hb' : ∀ x, (l.map (fun a => f a x)).sum < 2 ^ L := fun x => by
      have := hb x; simp only [List.map_cons, List.sum_cons] at this; omega
    have t := ih hb' (fun a ha => hf a (by simp [ha]))
    have out := t.bind (b := 11 * L + 1)
      (q := fun D => HasNat D L (fun x => ((a :: l).map (fun a => f a x)).sum)) (by
        intro D e hl
        refine (adder ((hf a (by simp)).lift e) hl).weaken le_rfl (fun D' h => ?_)
        refine truncate (h.congr (fun x => ?_)) hb
        simp)
    simpa [Nat.succ_mul, Nat.add_comm] using out

lemma selHas {B : Bank n} {L : ℕ} {p q : (Fin n → Bool) → ℕ} {a g : BitFn n}
    (hp : HasNat B L p) (hq : HasNat B L q) (ha : B.Has a) (hg : B.Has g) :
    B.Grow (3 * L + 3) (fun D => HasNat D L (fun x =>
      PEqualNP.Outside.L_meta_25887_aux.selN (a x) (g x) (p x) (q x))) := by
  obtain ⟨D1, e1, c1, ng⟩ := inv hg
  obtain ⟨D2, e2, c2, a'⟩ := meet (e1 ha) ng
  obtain ⟨D3, e3, c3, g'⟩ := meet (e2 (e1 ha)) (e2 (e1 hg))
  obtain ⟨D4, e4, c4, m⟩ := mux ((hp.lift e1).lift e2 |>.lift e3) ((hq.lift e1).lift e2 |>.lift e3)
    (e3 a') g' (fun x => by cases a x <;> cases g x <;> simp)
  refine ⟨D4, fun h => e4 (e3 (e2 (e1 h))), by omega, m.congr (fun x => ?_)⟩
  unfold PEqualNP.Outside.L_meta_25887_aux.selN
  cases a x <;> cases g x <;> simp

lemma entry {B : Bank n} {L : ℕ} {p0 q0 p1 q1 : (Fin n → Bool) → ℕ} {a0 g0 a1 g1 : BitFn n}
    (hp0 : HasNat B L p0) (hq0 : HasNat B L q0) (hp1 : HasNat B L p1) (hq1 : HasNat B L q1)
    (ha0 : B.Has a0) (hg0 : B.Has g0) (ha1 : B.Has a1) (hg1 : B.Has g1)
    (bd : ∀ x, PEqualNP.Outside.L_meta_25887_aux.selN (a0 x) (g0 x) (p0 x) (q0 x) +
      PEqualNP.Outside.L_meta_25887_aux.selN (a1 x) (g1 x) (p1 x) (q1 x) < 2 ^ L) :
    B.Grow (20 * L + 10) (fun D => HasNat D L (fun x =>
      PEqualNP.Outside.L_meta_25887_aux.selN (a0 x) (g0 x) (p0 x) (q0 x) +
      PEqualNP.Outside.L_meta_25887_aux.selN (a1 x) (g1 x) (p1 x) (q1 x))) := by
  obtain ⟨D1, e1, c1, s0⟩ := selHas hp0 hq0 ha0 hg0
  obtain ⟨D2, e2, c2, s1⟩ := selHas (hp1.lift e1) (hq1.lift e1) (e1 ha1) (e1 hg1)
  obtain ⟨D3, e3, c3, sm⟩ := adder (s0.lift e2) s1
  exact ⟨D3, fun h => e3 (e2 (e1 h)), by omega, truncate sm bd⟩

open PEqualNP.Outside.L_meta_25887_aux in
lemma dpRun (k : ℕ) (al sgn : (Fin n → Bool) → ℕ → Bool → Bool → Bool) (st : Bool) (B : Bank n)
    (hal : ∀ (i : Fin k) u v, B.Has (fun x => al x i u v))
    (hsg : ∀ (i : Fin k) u v, B.Has (fun x => sgn x i u v))
    (hf : B.Has (fun _ => false)) (ht : B.Has (fun _ => true)) :
    ∀ i ≤ k, B.Grow (i * (4 * (20 * (k+1) + 10))) (fun D => ∀ v,
      HasNat D (k+1) (fun x => (runPN (al x) (sgn x) st i).1 v) ∧
      HasNat D (k+1) (fun x => (runPN (al x) (sgn x) st i).2 v)) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine (Grow.pure B (fun v => ⟨?_, ?_⟩)).weaken (by omega) (fun _ h => h)
    · by_cases h : v = st
      · exact (natConst hf ht (c := 1) (L := k+1) (Nat.one_lt_two_pow (by omega))).congr
          (fun x => by simp [runPN, h])
      · exact (natConst hf ht (c := 0) (L := k+1) (Nat.two_pow_pos _)).congr
          (fun x => by simp [runPN, h])
    · exact (natConst hf ht (c := 0) (L := k+1) (Nat.two_pow_pos _)).congr
          (fun x => by simp [runPN])
  | succ i ih =>
    intro hi
    have bnd : ∀ x v, (runPN (al x) (sgn x) st (i+1)).1 v < 2 ^ (k+1) ∧
        (runPN (al x) (sgn x) st (i+1)).2 v < 2 ^ (k+1) := by
      intro x v
      have := runPN_bound (al x) (sgn x) st (i+1) v
      have hp : 2 ^ (i+1+1) ≤ 2 ^ (k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := (ih (by omega)).bind (b := 4 * (20 * (k+1) + 10)) (q := fun D => ∀ v,
      HasNat D (k+1) (fun x => (runPN (al x) (sgn x) st (i+1)).1 v) ∧
      HasNat D (k+1) (fun x => (runPN (al x) (sgn x) st (i+1)).2 v)) (by
        intro D e hD
        have A : ∀ u v, D.Has (fun x => al x i u v) := fun u v => e (hal ⟨i, by omega⟩ u v)
        have G : ∀ u v, D.Has (fun x => sgn x i u v) := fun u v => e (hsg ⟨i, by omega⟩ u v)
        obtain ⟨D1, e1, c1, h1⟩ := entry (hD false).1 (hD false).2 (hD true).1 (hD true).2
          (A false false) (G false false) (A true false) (G true false)
          (fun x => (bnd x false).1)
        obtain ⟨D2, e2, c2, h2⟩ := entry ((hD false).2.lift e1) ((hD false).1.lift e1)
          ((hD true).2.lift e1) ((hD true).1.lift e1)
          (e1 (A false false)) (e1 (G false false)) (e1 (A true false)) (e1 (G true false))
          (fun x => (bnd x false).2)
        obtain ⟨D3, e3, c3, h3⟩ := entry (((hD false).1.lift e1).lift e2)
          (((hD false).2.lift e1).lift e2) (((hD true).1.lift e1).lift e2)
          (((hD true).2.lift e1).lift e2)
          (e2 (e1 (A false true))) (e2 (e1 (G false true))) (e2 (e1 (A true true)))
          (e2 (e1 (G true true)))
          (fun x => (bnd x true).1)
        obtain ⟨D4, e4, c4, h4⟩ := entry ((((hD false).2.lift e1).lift e2).lift e3)
          ((((hD false).1.lift e1).lift e2).lift e3) ((((hD true).2.lift e1).lift e2).lift e3)
          ((((hD true).1.lift e1).lift e2).lift e3)
          (e3 (e2 (e1 (A false true)))) (e3 (e2 (e1 (G false true))))
          (e3 (e2 (e1 (A true true)))) (e3 (e2 (e1 (G true true))))
          (fun x => (bnd x true).2)
        refine ⟨D4, fun h => e4 (e3 (e2 (e1 h))), by omega, fun v => ?_⟩
        cases v
        · exact ⟨((h1.lift e2).lift e3).lift e4, (h2.lift e3).lift e4⟩
        · exact ⟨h3.lift e4, h4⟩)
    exact this.weaken (Nat.le_of_eq (by ring)) (fun _ h => h)

open PEqualNP.Outside.L_meta_25887_aux in
lemma dp (k : ℕ) (al sgn : (Fin n → Bool) → ℕ → Bool → Bool → Bool) (B : Bank n)
    (hal : ∀ (i : Fin k) u v, B.Has (fun x => al x i u v))
    (hsg : ∀ (i : Fin k) u v, B.Has (fun x => sgn x i u v))
    (hf : B.Has (fun _ => false)) (ht : B.Has (fun _ => true)) :
    B.Grow (2 * (k * (4 * (20 * (k+1) + 10))) + 2 * (11 * (k+1) + 1)) (fun D =>
      HasNat D (k+2) (fun x => (runPN (al x) (sgn x) false k).1 false +
        (runPN (al x) (sgn x) true k).1 true) ∧
      HasNat D (k+2) (fun x => (runPN (al x) (sgn x) false k).2 false +
        (runPN (al x) (sgn x) true k).2 true)) := by
  obtain ⟨D1, e1, c1, h1⟩ := dpRun k al sgn false B hal hsg hf ht k le_rfl
  obtain ⟨D2, e2, c2, h2⟩ := dpRun k al sgn true D1 (fun i u v => e1 (hal i u v))
    (fun i u v => e1 (hsg i u v)) (e1 hf) (e1 ht) k le_rfl
  obtain ⟨D3, e3, c3, h3⟩ := adder ((h1 false).1.lift e2) (h2 true).1
  obtain ⟨D4, e4, c4, h4⟩ := adder (((h1 false).2.lift e2).lift e3) ((h2 true).2.lift e3)
  exact ⟨D4, fun h => e4 (e3 (e2 (e1 h))), by omega, h3.lift e4, h4⟩

/-- what each local factor supplies to the final block -/
def Res (B : Bank n) (w : ℕ) (Z : (Fin n → Bool) → ℤ) : Prop :=
  B.Has (fun x => decide (Z x ≠ 0)) ∧ B.Has (fun x => decide (Z x < 0)) ∧
    HasNat B w (fun x => Nat.log2 (Z x).natAbs)

lemma Res.lift {B D : Bank n} {w : ℕ} {Z : (Fin n → Bool) → ℤ} (e : B.Ext D) (h : Res B w Z) :
    Res D w Z := ⟨e h.1, e h.2.1, h.2.2.lift e⟩

lemma lowE_self (P L ℓ : ℕ) : lowE P P L ℓ = false := by
  unfold lowE; simp

lemma resOf {B : Bank n} {L w : ℕ} {P N : (Fin n → Bool) → ℕ} {Z : (Fin n → Bool) → ℤ}
    (hP : HasNat B L P) (hN : HasNat B L N) (hZ : ∀ x, (P x : ℤ) - N x = Z x)
    (hpow : ∀ x, Z x = 0 ∨ ∃ e, (Z x).natAbs = 2 ^ e)
    (hw : ∀ x, Nat.log2 (Z x).natAbs < 2 ^ w) :
    B.Grow (2 + 12 * L + w * (L + 1)) (fun D => Res D w Z) := by
  refine (extract w hP hN).weaken le_rfl (fun D h => ?_)
  obtain ⟨hne, hlt, hlow⟩ := h
  refine ⟨hasCongr hne (fun x => ?_), hasCongr hlt (fun x => ?_), ⟨hw, fun ℓ hℓ =>
    hasCongr (hlow ℓ hℓ) (fun x => ?_)⟩⟩
  · rw [← hZ x]; apply decide_eq_decide.mpr; omega
  · rw [← hZ x]; apply decide_eq_decide.mpr; omega
  · show lowE (P x) (N x) L ℓ = (Nat.log2 (Z x).natAbs).testBit ℓ
    rcases hpow x with h0 | ⟨e, he⟩
    · have : P x = N x := by have := hZ x; omega
      rw [this, lowE_self, h0]; simp
    · have hlog : Nat.log2 (Z x).natAbs = e := by rw [he, Nat.log2_two_pow]
      rw [hlog]
      have hPN : P x = N x + 2 ^ e ∨ N x = P x + 2 ^ e := by
        have := hZ x
        rcases Int.natAbs_eq (Z x) with h | h <;> rw [he] at h <;> push_cast at h <;> omega
      exact PEqualNP.Outside.L_meta_25887_aux.lowE_eq (hP.1 x) (hN.1 x) hPN ℓ

end PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25887_aux

open Finset Matrix
open Builder.Bank (zb bz zb_bz bz_zb zb_add zb_mul)

section STval
variable {k : ℕ} (hk : 0 < k) {r s : ℕ} {gap : ℕ} {inject : ℕ → ℕ}

lemma ST_cast (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k) (test target : V k)
    (b : Fin r → V k) (S : Matrix (Fin k) (Fin k) (ZMod 2))
    (hS : ∀ v, (∃ x, mm k hk gap x = v) → mm k hk gap (S *ᵥ v) = v) (t : Fin r) :
    ST k hk r s gap inject delta path test target b t.castSucc =
      if mm k hk gap (S *ᵥ bprev k r b t.castSucc) = bprev k r b t.castSucc then
        ∑ z ∈ Finset.univ.filter (fun z => mm k hk gap z = 0),
          (runD (phiB (alS hk (fun p => mm k hk gap (path t.castSucc p))
              (fun p => rot k hk (inject t.val) (delta p)) (fun p => path t.succ p))
            (sgnS hk (b t) (S *ᵥ bprev k r b t.castSucc + z))) false k false +
          runD (phiB (alS hk (fun p => mm k hk gap (path t.castSucc p))
              (fun p => rot k hk (inject t.val) (delta p)) (fun p => path t.succ p))
            (sgnS hk (b t) (S *ᵥ bprev k r b t.castSucc + z))) true k true)
      else 0 := by
  classical
  let F : V k → ℤ := fun y => if (∀ p, Lf k hk (y + mm k hk gap (path t.castSucc p)) -
      Lf k hk y + rot k hk (inject t.val) (delta p) = path t.succ p) then
      sg (dotProduct (b t) (Lf k hk y)) else 0
  have hlt : (Fin.castSucc t).val < r := t.isLt
  have h1 : ∀ x, (if condT k hk r s gap inject delta path test target t.castSucc x then
      sg (qT k hk r gap b t.castSucc x) else 0) =
      F (mm k hk gap x) * sg (dotProduct (bprev k r b t.castSucc) x) := by
    intro x
    have hc : condT k hk r s gap inject delta path test target t.castSucc x ↔
        (∀ p, Lf k hk (mm k hk gap x + mm k hk gap (path t.castSucc p)) -
          Lf k hk (mm k hk gap x) + rot k hk (inject t.val) (delta p) = path t.succ p) := by
      unfold condT; rw [dif_pos hlt]
      simp only [layer, mm_add]; rfl
    have hq : qT k hk r gap b t.castSucc x =
        dotProduct (b t) (Lf k hk (mm k hk gap x)) + dotProduct (bprev k r b t.castSucc) x := by
      unfold qT; rw [dif_pos hlt]; rfl
    simp only [F]
    by_cases h : condT k hk r s gap inject delta path test target t.castSucc x
    · rw [if_pos h, if_pos (hc.1 h), hq, sg_add]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h')), zero_mul]
  unfold ST
  rw [Finset.sum_congr rfl (fun x _ => h1 x), fourier (mm k hk gap) (mm_add hk gap)
    (mm_sym hk gap) F (bprev k r b t.castSucc), fiber_sum hk gap S hS]
  split_ifs with hI
  · refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [← chainSum hk]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact pairT hk _ _ _ (b t) _ y
  · rfl

lemma ST_last (delta : Fin s → V k) (path : Fin (r+1) → Fin s → V k) (test target : V k)
    (b : Fin r → V k) :
    ST k hk r s gap inject delta path test target b (Fin.last r) =
      runD (phiB (alR hk test target) (sgnR hk (bprev k r b (Fin.last r)))) false k false +
      runD (phiB (alR hk test target) (sgnR hk (bprev k r b (Fin.last r)))) true k true := by
  classical
  unfold ST
  rw [← chainSum hk]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hlt : ¬ (Fin.last r).val < r := by simp
  have hc : condT k hk r s gap inject delta path test target (Fin.last r) x ↔
      ∀ j, test j ≠ 0 → x j = target j := by
    unfold condT; rw [dif_neg hlt]
  have hq : qT k hk r gap b (Fin.last r) x = dotProduct (bprev k r b (Fin.last r)) x := by
    unfold qT; rw [dif_neg hlt, zero_add]
  rw [← pairR hk test target _ x, hq]
  by_cases h : condT k hk r s gap inject delta path test target (Fin.last r) x
  · rw [if_pos h, if_pos (hc.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

lemma runPN_two (al sgn : ℕ → Bool → Bool → Bool) :
    ((((runPN al sgn false k).1 false + (runPN al sgn true k).1 true : ℕ) : ℤ) -
      (((runPN al sgn false k).2 false + (runPN al sgn true k).2 true : ℕ) : ℤ)) =
      runD (phiB al sgn) false k false + runD (phiB al sgn) true k true := by
  rw [← runPN_diff, ← runPN_diff]; push_cast; ring

end STval

end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux.Builder.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

def ZE.sumL : List (ZE n) → ZE n
  | [] => .cst 0
  | e :: l => .add e (ZE.sumL l)

lemma ZE.eval_sumL (x : Fin n → Bool) : ∀ l : List (ZE n),
    (ZE.sumL l).eval x = (l.map (fun e => e.eval x)).sum
  | [] => rfl
  | e :: l => by simp [ZE.sumL, ZE.eval, ZE.eval_sumL x l]

lemma ZE.cost_sumL : ∀ l : List (ZE n),
    (ZE.sumL l).cost = 1 + (l.map (fun e => e.cost + 4)).sum
  | [] => rfl
  | e :: l => by simp [ZE.sumL, ZE.cost, ZE.cost_sumL l]; omega

lemma ZE.ok_sumL {B : Bank n} : ∀ l : List (ZE n), (∀ e ∈ l, e.Ok B) → (ZE.sumL l).Ok B
  | [] => fun _ => trivial
  | e :: l => fun h => ⟨h e (by simp), ZE.ok_sumL l (fun e' he => h e' (by simp [he]))⟩

lemma ZE.cost_sumL_le (l : List (ZE n)) (c : ℕ) (h : ∀ e ∈ l, e.cost ≤ c) :
    (ZE.sumL l).cost ≤ 1 + l.length * (c + 4) := by
  rw [ZE.cost_sumL]
  have := List.sum_le_card_nsmul (l.map (fun e => e.cost + 4)) (c+4)
    (by simp only [List.mem_map]; rintro _ ⟨e, he, rfl⟩; have := h e he; omega)
  simp only [List.length_map, smul_eq_mul] at this
  omega

lemma zeroBit {B : Bank n} (E : ZE n) (h : E.Ok B) :
    B.Grow (E.cost + 1) (fun D => D.Has (fun x => decide (E.eval x = 0))) := by
  refine (ZE.build E h).bind (b := 1) (fun D _ hE =>
    (inv hE).weaken le_rfl (fun D' h' => hasCongr h' (fun x => ?_)))
  generalize E.eval x = z; revert z; decide

lemma allUniv {ι : Type} [Fintype ι] (B : Bank n) (f : ι → BitFn n) (cost : ℕ)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1 + Fintype.card ι * (cost + 1))
      (fun D => D.Has (fun x => decide (∀ i, f i x = true))) := by
  classical
  have := foldSlots true B (Finset.univ : Finset ι).toList f cost (fun D e i _ => emit D e i)
  rw [Finset.length_toList, Finset.card_univ] at this
  refine this.weaken le_rfl (fun D h => hasCongr h (fun x => ?_))
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

lemma collectU {ι : Type} [Fintype ι] (B : Bank n) (P : ι → Bank n → Prop)
    (mono : ∀ a D E, D.Ext E → P a D → P a E) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (P i)) :
    B.Grow (Fintype.card ι * cost) (fun D => ∀ i, P i D) := by
  classical
  have := collectP B (Finset.univ : Finset ι).toList P mono cost (fun D e i _ => emit D e i)
  rw [Finset.length_toList, Finset.card_univ] at this
  exact this.weaken le_rfl (fun D h i => h i (by simp))

end PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25887_aux.Builder.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25887_aux (V ix mm rot layer ST bprev alS sgnS alR sgnR Ecnd jp
  runPN runD phiB ST_cast ST_last runPN_two ST_pow ST_le log_le_of ix_val)
open Matrix

section Blocks
variable {n k r s : ℕ} (hk : 0 < k) (gap : ℕ) (inject : ℕ → ℕ)

def zU (P : (Fin n → Bool) → V k) (m : Fin k) : ZE n :=
  .add (.add (.atom (fun x => P x m)) (.atom (fun x => P x (ix k hk (m.val + gap)))))
    (.atom (fun x => P x (ix k hk (m.val + k - gap % k))))

def zE (P cc d : (Fin n → Bool) → V k) (i : Fin k) (u v : Bool) : ZE n :=
  .add (.add (.add (.add (zU hk gap P (jp hk i))
      (.mul (.cst (1 + bz u)) (zU hk gap P (ix k hk ((jp hk i).val + 2)))))
      (.mul (zU hk gap P (ix k hk ((jp hk i).val + 1)))
        (.add (.cst (bz v)) (zU hk gap P (ix k hk ((jp hk i).val + 2))))))
      (.atom (fun x => cc x (jp hk i)))) (.atom (fun x => d x (jp hk i)))

lemma zU_ok {B : Bank n} (P : (Fin n → Bool) → V k) (hP : ∀ j, B.Has (fun x => zb (P x j)))
    (m : Fin k) : (zU hk gap P m).Ok B := ⟨⟨hP _, hP _⟩, hP _⟩

lemma zE_ok {B : Bank n} (P cc d : (Fin n → Bool) → V k) (hP : ∀ j, B.Has (fun x => zb (P x j)))
    (hc : ∀ j, B.Has (fun x => zb (cc x j))) (hd : ∀ j, B.Has (fun x => zb (d x j)))
    (i : Fin k) (u v : Bool) : (zE hk gap P cc d i u v).Ok B :=
  ⟨⟨⟨⟨zU_ok hk gap P hP _, trivial, zU_ok hk gap P hP _⟩, zU_ok hk gap P hP _, trivial,
    zU_ok hk gap P hP _⟩, hc _⟩, hd _⟩

lemma zE_cost (P cc d : (Fin n → Bool) → V k) (i : Fin k) (u v : Bool) :
    (zE hk gap P cc d i u v).cost = 56 := rfl

lemma zE_eval (P cc d : (Fin n → Bool) → V k) (i : Fin k) (u v : Bool) (x : Fin n → Bool) :
    (zE hk gap P cc d i u v).eval x = Ecnd hk (mm k hk gap (P x)) (cc x) (d x) i u v := rfl

lemma impl_eq (a c d : ZMod 2) : decide (a * (c + d) = 0) = decide (a ≠ 0 → c = d) := by
  revert a c d; decide

lemma sum2 (a c : ZMod 2) : (a + c = 0) ↔ a = c := by revert a c; decide

variable (dDelta : (Fin n → Bool) → Fin s → V k) (dPath : (Fin n → Bool) → Fin (r+1) → Fin s → V k)
  (dTest dTarget : (Fin n → Bool) → V k) (dB : (Fin n → Bool) → Fin r → V k)

lemma bpAv (avB : ∀ (B : Bank n) t j, B.Has (fun x => zb (dB x t j))) (t' : Fin (r+1))
    (D : Bank n) (hfD : D.Has (fun _ => false)) (j : Fin k) :
    D.Has (fun x => zb (bprev k r (dB x) t' j)) := by
  unfold bprev
  by_cases h : 0 < t'.val
  · simp only [dif_pos h]; exact avB D _ j
  · simp only [dif_neg h]; exact hasCongr hfD (fun x => by simp [zb])

lemma blockCast (avD : ∀ (B : Bank n) p j, B.Has (fun x => zb (dDelta x p j)))
    (avP : ∀ (B : Bank n) t p j, B.Has (fun x => zb (dPath x t p j)))
    (avB : ∀ (B : Bank n) t j, B.Has (fun x => zb (dB x t j)))
    (hg1 : 1 ≤ gap) (hg2 : gap ≤ 2) (w : ℕ) (hkw : k < 2 ^ w) (t : Fin r) (B : Bank n)
    (hf : B.Has (fun _ => false)) (ht : B.Has (fun _ => true)) :
    B.Grow (12000 * (k+1) * (k+s+1) + (w+1) * (k+7)) (fun D => Res D w (fun x =>
      ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x) t.castSucc)) := by
  classical
  obtain ⟨S, hS⟩ := PEqualNP.Outside.L_meta_25887_aux.sec_exists hk gap
  let bp : (Fin n → Bool) → V k := fun x => bprev k r (dB x) t.castSucc
  have avBp : ∀ (D : Bank n), D.Has (fun _ => false) → ∀ j, D.Has (fun x => zb (bp x j)) :=
    fun D hfD j => bpAv dB avB t.castSucc D hfD j
  let al : (Fin n → Bool) → ℕ → Bool → Bool → Bool := fun x => alS hk
    (fun p => mm k hk gap (dPath x t.castSucc p)) (fun p => rot k hk (inject t.val) (dDelta x p))
    (fun p => dPath x t.succ p)
  -- allowed bits
  obtain ⟨D1, e1, c1, h1⟩ := collectU B (fun (iuv : Fin k × Bool × Bool) D =>
      D.Has (fun x => al x iuv.1 iuv.2.1 iuv.2.2)) (fun a D E e h => e h) (1 + s * 58) (by
    rintro D _ ⟨i, u, v⟩
    refine (allUniv D (fun (p : Fin s) x => decide ((zE hk gap (fun x => dPath x t.castSucc p)
      (fun x => rot k hk (inject t.val) (dDelta x p)) (fun x => dPath x t.succ p) i u v).eval x
        = 0)) 57 (fun E _ p => ?_)).weaken (by simp) (fun E h => hasCongr h (fun x => ?_))
    · refine (zeroBit _ (zE_ok hk gap _ _ _ (fun j => avP E _ p j)
        (fun j => avD E p _) (fun j => avP E _ p j) i u v)).weaken (by rw [zE_cost]) (fun _ h => h)
    · rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, al, alS, ix_val, zE_eval]
      exact forall_congr' (fun p => decide_eq_true_iff))
  -- the section bits
  obtain ⟨D2, e2, c2, h2⟩ := collectU D1 (fun (i : Fin k) D => D.Has (fun x => zb ((S *ᵥ bp x) i)))
      (fun a D E e h => e h) (1 + k * 6) (by
    intro D e i
    let E : ZE n := ZE.sumL ((List.finRange k).map (fun j => .mul (.cst (S i j))
      (.atom (fun x => bp x j))))
    have ok : E.Ok D := ZE.ok_sumL _ (by
      simp only [List.mem_map]; rintro _ ⟨j, _, rfl⟩; exact ⟨trivial, avBp D (e (e1 hf)) j⟩)
    have cost : E.cost ≤ 1 + k * 6 := by
      have := ZE.cost_sumL_le ((List.finRange k).map (fun j => (.mul (.cst (S i j))
        (.atom (fun x => bp x j)) : ZE n))) 2
        (by simp only [List.mem_map]; rintro _ ⟨j, _, rfl⟩; simp [ZE.cost])
      simpa using this
    refine (ZE.build E ok).weaken cost (fun D' h => hasCongr h (fun x => ?_))
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_def]
    simp [E, ZE.eval_sumL, ZE.eval, List.map_map, Function.comp_def])
  -- the compatibility bit
  let Ix : (Fin n → Bool) → Bool := fun x => decide (mm k hk gap (S *ᵥ bp x) = bp x)
  let zI : Fin k → ZE n := fun j => .add (.add (.add (.atom (fun x => (S *ᵥ bp x) j))
    (.atom (fun x => (S *ᵥ bp x) (ix k hk (j.val + gap)))))
    (.atom (fun x => (S *ᵥ bp x) (ix k hk (j.val + k - gap % k))))) (.atom (fun x => bp x j))
  obtain ⟨D3, e3, c3, h3⟩ : D2.Grow (1 + k * 14) (fun D => D.Has Ix) := by
    refine (allUniv D2 (fun (j : Fin k) x => decide ((zI j).eval x = 0)) 13
      (fun D e j => (zeroBit (zI j) ⟨⟨⟨e (h2 _), e (h2 _)⟩, e (h2 _)⟩,
        avBp D (e (e2 (e1 hf))) j⟩).weaken (by simp [zI, ZE.cost]) (fun _ h => h))).weaken (by simp)
      (fun D h => hasCongr h (fun x => ?_))
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Ix]
    rw [funext_iff]
    exact forall_congr' (fun j => sum2 _ _)
  -- the lifts
  let kerL : List (V k) := (Finset.univ.filter (fun z : V k => mm k hk gap z = 0)).toList
  have hlen : kerL.length ≤ 16 := by
    rw [Finset.length_toList]; exact PEqualNP.Outside.L_meta_25887_aux.ker_card hk gap hg1 hg2
  let sg : V k → (Fin n → Bool) → ℕ → Bool → Bool → Bool := fun z x =>
    sgnS hk (dB x t) (S *ᵥ bp x + z)
  let Pz : V k → (Fin n → Bool) → ℕ := fun z x => (runPN (al x) (sg z x) false k).1 false +
    (runPN (al x) (sg z x) true k).1 true
  let Nz : V k → (Fin n → Bool) → ℕ := fun z x => (runPN (al x) (sg z x) false k).2 false +
    (runPN (al x) (sg z x) true k).2 true
  have hf3 : D3.Has (fun _ => false) := e3 (e2 (e1 hf))
  have ht3 : D3.Has (fun _ => true) := e3 (e2 (e1 ht))
  obtain ⟨D4, e4, c4, h4⟩ := collectP D3 kerL (fun z D =>
      HasNat D (k+2) (fun x => if Ix x then Pz z x else 0) ∧
      HasNat D (k+2) (fun x => if Ix x then Nz z x else 0))
      (fun a D E e h => ⟨h.1.lift e, h.2.lift e⟩)
      (k * 2 * 2 * 19 + (2 * (k * (4 * (20 * (k+1) + 10))) + 2 * (11 * (k+1) + 1)) +
        (k + 2) * 3 + (k + 2) * 3) (by
    intro D e z _
    obtain ⟨E1, f1, d1, g1⟩ := collectU D (fun (iuv : Fin k × Bool × Bool) D =>
        D.Has (fun x => sg z x iuv.1 iuv.2.1 iuv.2.2)) (fun a D E e h => e h) 19 (by
      rintro E f ⟨i, u, v⟩
      let Es : ZE n := .add (.mul (.add (.atom (fun x => dB x t i)) (.add
        (.atom (fun x => (S *ᵥ bp x) i)) (.cst (z i)))) (.cst (bz u)))
        (.mul (.mul (.atom (fun x => dB x t (jp hk i))) (.cst (1 + bz u))) (.cst (bz v)))
      refine (ZE.build Es ⟨⟨⟨avB E t i, f (e (e3 (h2 i))), trivial⟩, trivial⟩, ⟨avB E t _, trivial⟩,
        trivial⟩).weaken (by simp [Es, ZE.cost]) (fun E' h => hasCongr h (fun x => ?_))
      simp only [sg, sgnS, ix_val, Es, ZE.eval]
      rfl)
    have A : ∀ (i : Fin k) u v, E1.Has (fun x => al x i u v) :=
      fun i u v => f1 (e (e3 (e2 (h1 (i, u, v)))))
    have G : ∀ (i : Fin k) u v, E1.Has (fun x => sg z x i u v) := fun i u v => g1 (i, u, v)
    obtain ⟨E2, f2, d2, g2⟩ := dp k al (sg z) E1 A G (f1 (e hf3)) (f1 (e ht3))
    obtain ⟨E3, f3, d3, g3⟩ := mux g2.1 g2.1 (f2 (f1 (e h3))) (f2 (f1 (e hf3)))
      (fun x => by simp)
    obtain ⟨E4, f4, d4, g4⟩ := mux (g2.2.lift f3) (g2.2.lift f3) (f3 (f2 (f1 (e h3))))
      (f3 (f2 (f1 (e hf3)))) (fun x => by simp)
    refine ⟨E4, fun h => f4 (f3 (f2 (f1 h))), ?_, (g3.lift f4).congr (fun x => ?_),
      g4.congr (fun x => ?_)⟩
    · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at d1
      omega
    · simp only [Bool.false_eq_true, if_false]; rfl
    · simp only [Bool.false_eq_true, if_false]; rfl)
  -- sums over the lifts
  have hf4 : D4.Has (fun _ => false) := e4 hf3
  have bnd : ∀ (F : V k → (Fin n → Bool) → ℕ), (∀ z ∈ kerL, ∀ x, F z x < 2 ^ (k+2)) →
      ∀ x, (kerL.map (fun z => F z x)).sum < 2 ^ (k+6) := by
    intro F hF x
    have := List.sum_le_card_nsmul (kerL.map (fun z => F z x)) (2 ^ (k+2) - 1)
      (by simp only [List.mem_map]; rintro _ ⟨z, hz, rfl⟩; have := hF z hz x; omega)
    simp only [List.length_map, smul_eq_mul] at this
    have h16 : 2 ^ (k+6) = 16 * 2 ^ (k+2) := by rw [show k + 6 = (k+2) + 4 by omega, pow_add]; ring
    have hp : 0 < 2 ^ (k+2) := Nat.two_pow_pos _
    have : kerL.length * (2 ^ (k+2) - 1) ≤ 16 * (2 ^ (k+2) - 1) := Nat.mul_le_mul_right _ hlen
    omega
  obtain ⟨D5, e5, c5, h5⟩ := sumList D4 kerL (fun z x => if Ix x then Pz z x else 0) (k+6)
    (bnd _ (fun z hz x => (h4 z hz).1.1 x)) (fun z hz => (h4 z hz).1.widen (by omega) hf4) hf4
  obtain ⟨D6, e6, c6, h6⟩ := sumList D5 kerL (fun z x => if Ix x then Nz z x else 0) (k+6)
    (bnd _ (fun z hz x => (h4 z hz).2.1 x))
    (fun z hz => ((h4 z hz).2.lift e5).widen (by omega) (e5 hf4)) (e5 hf4)
  have hZ : ∀ x, (((kerL.map (fun z => if Ix x then Pz z x else 0)).sum : ℕ) : ℤ) -
      (((kerL.map (fun z => if Ix x then Nz z x else 0)).sum : ℕ) : ℤ) =
      ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x) t.castSucc := by
    intro x
    rw [ST_cast hk _ _ _ _ _ S hS t]
    rw [Finset.sum_map_toList, Finset.sum_map_toList]
    push_cast
    rw [← Finset.sum_sub_distrib]
    by_cases hI : Ix x
    · rw [if_pos (by simpa [Ix] using hI)]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [if_pos hI]
      have := runPN_two (k := k) (al x) (sg z x)
      push_cast at this
      exact this
    · rw [if_neg (by simpa [Ix] using hI)]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      simp [if_neg hI]
  obtain ⟨D7, e7, c7, h7⟩ := resOf (w := w) (h5.lift e6) h6
    (Z := fun x => ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x)
      t.castSucc) hZ
    (fun x => ST_pow hk _ _ _ _ _ _)
    (fun x => lt_of_le_of_lt (log_le_of (ST_le hk _ _ _ _ _ _)) hkw)
  refine ⟨D7, fun h => e7 (e6 (e5 (e4 (e3 (e2 (e1 h)))))), ?_, h7⟩
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at c1 c2 c3
  have l4 := Nat.mul_le_mul_right (k * 2 * 2 * 19 + (2 * (k * (4 * (20 * (k+1) + 10))) +
    2 * (11 * (k+1) + 1)) + (k + 2) * 3 + (k + 2) * 3) hlen
  have l5 := Nat.mul_le_mul_right (11 * (k + 6) + 1) hlen
  have hw7 : w * (k + 6 + 1) ≤ (w+1) * (k+7) := by nlinarith
  nlinarith

end Blocks

end PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25887_aux.Builder.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25887_aux (V ix mm rot layer ST bprev alS sgnS alR sgnR Ecnd jp
  runPN runD phiB ST_cast ST_last runPN_two ST_pow ST_le log_le_of ix_val)
open Matrix

section Blocks2
variable {n k r s : ℕ} (hk : 0 < k) (gap : ℕ) (inject : ℕ → ℕ)
variable (dDelta : (Fin n → Bool) → Fin s → V k) (dPath : (Fin n → Bool) → Fin (r+1) → Fin s → V k)
  (dTest dTarget : (Fin n → Bool) → V k) (dB : (Fin n → Bool) → Fin r → V k)

lemma blockLast (avT : ∀ (B : Bank n) j, B.Has (fun x => zb (dTest x j)))
    (avG : ∀ (B : Bank n) j, B.Has (fun x => zb (dTarget x j)))
    (avB : ∀ (B : Bank n) t j, B.Has (fun x => zb (dB x t j)))
    (w : ℕ) (hkw : k < 2 ^ w) (B : Bank n)
    (hf : B.Has (fun _ => false)) (ht : B.Has (fun _ => true)) :
    B.Grow (12000 * (k+1) * (k+s+1) + (w+1) * (k+7)) (fun D => Res D w (fun x =>
      ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x) (Fin.last r))) := by
  classical
  let bp : (Fin n → Bool) → V k := fun x => bprev k r (dB x) (Fin.last r)
  let al : (Fin n → Bool) → ℕ → Bool → Bool → Bool := fun x => alR hk (dTest x) (dTarget x)
  let sg : (Fin n → Bool) → ℕ → Bool → Bool → Bool := fun x => sgnR hk (bp x)
  obtain ⟨D1, e1, c1, h1⟩ := collectU B (fun (iuv : Fin k × Bool × Bool) D =>
      D.Has (fun x => al x iuv.1 iuv.2.1 iuv.2.2)) (fun a D E e h => e h) 7 (by
    rintro D _ ⟨i, u, v⟩
    refine (zeroBit (.mul (.atom (fun x => dTest x i)) (.add (.cst (bz u))
      (.atom (fun x => dTarget x i)))) ⟨avT D i, trivial, avG D i⟩).weaken (by simp [ZE.cost])
      (fun E h => hasCongr h (fun x => ?_))
    simp only [ZE.eval, al, alR, ix_val]
    exact impl_eq _ _ _)
  obtain ⟨D2, e2, c2, h2⟩ := collectU D1 (fun (iuv : Fin k × Bool × Bool) D =>
      D.Has (fun x => sg x iuv.1 iuv.2.1 iuv.2.2)) (fun a D E e h => e h) 2 (by
    rintro D e ⟨i, u, v⟩
    refine (ZE.build (.mul (.atom (fun x => bp x i)) (.cst (bz u)))
      ⟨bpAv dB avB _ D (e (e1 hf)) i, trivial⟩).weaken (by simp [ZE.cost])
      (fun E h => hasCongr h (fun x => ?_))
    simp only [ZE.eval, sg, sgnR, ix_val])
  obtain ⟨D3, e3, c3, h3⟩ := dp k al sg D2 (fun i u v => e2 (h1 (i, u, v)))
    (fun i u v => h2 (i, u, v)) (e2 (e1 hf)) (e2 (e1 ht))
  have hZ : ∀ x, ((((runPN (al x) (sg x) false k).1 false + (runPN (al x) (sg x) true k).1 true
      : ℕ) : ℤ) - (((runPN (al x) (sg x) false k).2 false + (runPN (al x) (sg x) true k).2 true
      : ℕ) : ℤ)) =
      ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x) (Fin.last r) := by
    intro x
    rw [ST_last hk]; exact runPN_two (al x) (sg x)
  obtain ⟨D4, e4, c4, h4⟩ := resOf (w := w) h3.1 h3.2
    (Z := fun x => ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x)
      (Fin.last r)) hZ
    (fun x => ST_pow hk _ _ _ _ _ _)
    (fun x => lt_of_le_of_lt (log_le_of (ST_le hk _ _ _ _ _ _)) hkw)
  refine ⟨D4, fun h => e4 (e3 (e2 (e1 h))), ?_, h4⟩
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at c1 c2
  have hw7 : w * (k + 2 + 1) ≤ (w+1) * (k+7) := by nlinarith
  nlinarith

lemma perT (avD : ∀ (B : Bank n) p j, B.Has (fun x => zb (dDelta x p j)))
    (avP : ∀ (B : Bank n) t p j, B.Has (fun x => zb (dPath x t p j)))
    (avT : ∀ (B : Bank n) j, B.Has (fun x => zb (dTest x j)))
    (avG : ∀ (B : Bank n) j, B.Has (fun x => zb (dTarget x j)))
    (avB : ∀ (B : Bank n) t j, B.Has (fun x => zb (dB x t j)))
    (hg1 : 1 ≤ gap) (hg2 : gap ≤ 2) (w : ℕ) (hkw : k < 2 ^ w) (t : Fin (r+1)) (B : Bank n)
    (hf : B.Has (fun _ => false)) (ht : B.Has (fun _ => true)) :
    B.Grow (12000 * (k+1) * (k+s+1) + (w+1) * (k+7)) (fun D => Res D w (fun x =>
      ST k hk r s gap inject (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x) t)) := by
  induction t using Fin.lastCases with
  | last => exact blockLast hk gap inject dDelta dPath dTest dTarget dB avT avG avB w hkw B hf ht
  | cast t =>
    exact blockCast hk gap inject dDelta dPath dTest dTarget dB avD avP avB hg1 hg2 w hkw t B hf ht

end Blocks2

lemma finalBlock {r w : ℕ} (Z : Fin (r+1) → (Fin n → Bool) → ℤ) (G : BitFn n) (KE : ZE n)
    (B : Bank n) (hres : ∀ t, Res B w (Z t)) (hG : B.Has G) (hK : KE.Ok B)
    (hf : B.Has (fun _ => false))
    (hb : ∀ x, ((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)).sum < 2 ^ w) :
    B.Grow (KE.cost + 20 * (r+1) * (w+1) + 20)
      (fun D => D.Has (fun x => G x && decide (∀ t, decide (Z t x ≠ 0) = true)) ∧
        D.Has (fun x => (G x && decide (∀ t, decide (Z t x ≠ 0) = true)) &&
          zb (KE.eval x + ((List.finRange (r+1)).map
            (fun t => bz (decide (Z t x < 0)))).sum)) ∧
        ∀ j < w, D.Has (fun x => (G x && decide (∀ t, decide (Z t x ≠ 0) = true)) &&
          (((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)).sum).testBit j)) := by
  obtain ⟨D1, e1, c1, h1⟩ := allUniv B (fun t x => decide (Z t x ≠ 0)) 0
    (fun D e t => Grow.pure D (e (hres t).1))
  have h1' : D1.Has (fun x => decide (∀ t, decide (Z t x ≠ 0) = true)) :=
    hasCongr h1 (fun x => decide_eq_decide.mpr Iff.rfl)
  obtain ⟨D2, e2, c2, h2⟩ := meet (e1 hG) h1'
  let E : ZE n := .add KE (ZE.sumL ((List.finRange (r+1)).map
    (fun t => .atom (fun x => bz (decide (Z t x < 0))))))
  have ok : E.Ok D2 := ⟨ZE.ok_mono (fun h => e2 (e1 h)) KE hK, ZE.ok_sumL _ (by
    simp only [List.mem_map]; rintro _ ⟨t, _, rfl⟩
    exact hasCongr (e2 (e1 (hres t).2.1)) (fun x => (zb_bz _).symm))⟩
  have cE : E.cost ≤ KE.cost + (1 + (r+1) * 4) + 4 := by
    have := ZE.cost_sumL_le ((List.finRange (r+1)).map
      (fun t => (.atom (fun x => bz (decide (Z t x < 0))) : ZE n))) 0
      (by simp only [List.mem_map]; rintro _ ⟨t, _, rfl⟩; simp [ZE.cost])
    simp only [List.length_map, List.length_finRange] at this
    simp only [E, ZE.cost]; omega
  obtain ⟨D3, e3, c3, h3⟩ := ZE.build E ok
  obtain ⟨D4, e4, c4, h4⟩ := meet (e3 h2) h3
  obtain ⟨D5, e5, c5, h5⟩ := sumList D4 (List.finRange (r+1))
    (fun t x => Nat.log2 (Z t x).natAbs) w hb
    (fun t _ => (((hres t).2.2.lift e1).lift e2 |>.lift e3).lift e4) (e4 (e3 (e2 (e1 hf))))
  obtain ⟨D6, e6, c6, h6⟩ := collectFin D5 w (fun j x =>
      (G x && decide (∀ t, decide (Z t x ≠ 0) = true)) &&
      (((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)).sum).testBit j) 1
    (fun D e j => meet (e (e5 (e4 (e3 h2)))) (e (h5.2 j j.isLt)))
  refine ⟨D6, fun h => e6 (e5 (e4 (e3 (e2 (e1 h))))), ?_, e6 (e5 (e4 (e3 h2))),
    e6 (e5 (hasCongr h4 (fun x => by simp [E, ZE.eval, ZE.eval_sumL, List.map_map,
      Function.comp_def]))), fun j hj => h6 ⟨j, hj⟩⟩
  simp only [Fintype.card_fin, List.length_finRange] at c1 c5 c6
  nlinarith [cE, c1, c2, c3, c4, c5, c6]

end PEqualNP.Outside.L_meta_25887_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25887_aux
open Builder.Bank (zb bz zb_bz bz_zb zb_add zb_mul)

lemma signed (z : ℤ) (e : ℕ) (h : z.natAbs = 2 ^ e) :
    z = sg (bz (decide (z < 0))) * 2 ^ e := by
  rcases Int.natAbs_eq z with h1 | h1 <;> rw [h] at h1
  · have : ¬ z < 0 := by rw [h1]; exact not_lt.mpr (by positivity)
    simp [this, bz, sg, h1]
  · have : z < 0 := by rw [h1]; simp
    simp [this, bz, sg, h1]

theorem combine {r : ℕ} (c : ℤ) (K : ZMod 2) (G : Prop) {inst : Decidable G} (Z : Fin (r+1) → ℤ)
    (hc : c = sg K * (if G then 1 else 0) * ∏ t, Z t)
    (hZ : ∀ t, Z t = 0 ∨ ∃ e, (Z t).natAbs = 2 ^ e) :
    (c ≠ 0 ↔ G ∧ ∀ t, Z t ≠ 0) ∧
    (c < 0 ↔ (G ∧ ∀ t, Z t ≠ 0) ∧ zb (K + ∑ t, bz (decide (Z t < 0))) = true) ∧
    (c ≠ 0 → c.natAbs = 2 ^ (∑ t, Nat.log2 (Z t).natAbs)) := by
  have sg0 : ∀ a, sg a ≠ 0 := fun a => by unfold sg; split_ifs <;> norm_num
  by_cases hall : G ∧ ∀ t, Z t ≠ 0
  · obtain ⟨hG, hnz⟩ := hall
    have he : ∀ t, (Z t).natAbs = 2 ^ (Nat.log2 (Z t).natAbs) := by
      intro t
      rcases hZ t with h | ⟨e, he⟩
      · exact absurd h (hnz t)
      · rw [he, Nat.log2_two_pow]
    have hprod : ∏ t, Z t = sg (∑ t, bz (decide (Z t < 0))) *
        2 ^ (∑ t, Nat.log2 (Z t).natAbs) := by
      rw [sg_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun t _ => signed _ _ (he t))
    have hc' : c = sg (K + ∑ t, bz (decide (Z t < 0))) * 2 ^ (∑ t, Nat.log2 (Z t).natAbs) := by
      rw [hc, if_pos hG, hprod, sg_add]; ring
    have hpos : (0:ℤ) < 2 ^ (∑ t, Nat.log2 (Z t).natAbs) := by positivity
    refine ⟨⟨fun _ => ⟨hG, hnz⟩, fun _ => ?_⟩, ⟨fun h => ⟨⟨hG, hnz⟩, ?_⟩, fun h => ?_⟩, fun _ => ?_⟩
    · rw [hc']; exact mul_ne_zero (sg0 _) hpos.ne'
    · rw [hc'] at h
      unfold sg at h
      split_ifs at h with h0
      · linarith
      · revert h0; generalize K + ∑ t, bz (decide (Z t < 0)) = q; revert q; decide
    · rw [hc']
      have : sg (K + ∑ t, bz (decide (Z t < 0))) = -1 := by
        have := h.2; unfold sg; revert this
        generalize K + ∑ t, bz (decide (Z t < 0)) = q; revert q; decide
      rw [this]; linarith
    · rw [hc', Int.natAbs_mul]
      have : (sg (K + ∑ t, bz (decide (Z t < 0)))).natAbs = 1 := by
        unfold sg; split_ifs <;> rfl
      rw [this, one_mul, Int.natAbs_pow]; rfl
  · have hc0 : c = 0 := by
      rw [hc]
      by_cases hG : G
      · rw [if_pos hG]
        have : ∃ t, Z t = 0 := by
          by_contra hh; push_neg at hh; exact hall ⟨hG, hh⟩
        obtain ⟨t, ht⟩ := this
        rw [Finset.prod_eq_zero (Finset.mem_univ t) ht, mul_zero]
      · rw [if_neg hG]; ring
    refine ⟨⟨fun h => absurd hc0 h, fun h => absurd h hall⟩, ⟨fun h => ?_, fun h => absurd h.1 hall⟩,
      fun h => absurd hc0 h⟩
    rw [hc0] at h; exact absurd h (lt_irrefl 0)

end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux

open Builder.Bank (zb bz zb_bz bz_zb)

def xb {n : ℕ} (x : Fin n → Bool) (q : ℕ) : Bool := if h : q < n then x ⟨q, h⟩ else false

lemma avAt {n : ℕ} (B : Builder.Bank n) (q : ℕ) (hq : q < n) :
    B.Has (fun x => zb (bz (xb x q))) :=
  Builder.Bank.hasCongr (Builder.Bank.inputHas B ⟨q, hq⟩)
    (fun x => by simp only [xb, dif_pos hq, zb_bz])

lemma lt_mul_of {p m j k : ℕ} (hp : p < m) (hj : j < k) : p * k + j < m * k := by
  have : (p + 1) * k ≤ m * k := Nat.mul_le_mul_right _ hp
  rw [add_mul, one_mul] at this; omega

lemma flat_len {α : Type} (ℓ m : ℕ) (g : Fin m → List α) (hg : ∀ p, (g p).length = ℓ) :
    ((List.finRange m).flatMap g).length = m * ℓ := by
  simp [List.length_flatMap, hg]

lemma flat_get {α : Type} (ℓ : ℕ) : ∀ (m : ℕ) (g : Fin m → List α), (∀ p, (g p).length = ℓ) →
    ∀ (p : Fin m) (i : ℕ), i < ℓ → ((List.finRange m).flatMap g)[p.val * ℓ + i]? = (g p)[i]?
  | 0, _, _, p, _, _ => p.elim0
  | m+1, g, hg, p, i, hi => by
    rw [List.finRange_succ, List.flatMap_cons]
    cases p using Fin.cases with
    | zero =>
      rw [List.getElem?_append_left (by rw [hg]; simpa using hi)]
      simp
    | succ p =>
      have hle : (g 0).length ≤ (Fin.succ p).val * ℓ + i := by
        rw [hg, Fin.val_succ, add_mul, one_mul]; omega
      rw [List.getElem?_append_right hle, List.flatMap_map]
      have := flat_get ℓ m (fun q => g q.succ) (fun q => hg _) p i hi
      rw [← this, hg, Fin.val_succ, add_mul, one_mul]
      congr 1; omega

lemma bits_get {k : ℕ} (x : V k) (j : Fin k) :
    ((List.finRange k).map (fun j => decide (x j ≠ 0)))[j.val]? = some (zb (x j)) := by
  simp [zb]

lemma bits_len {k : ℕ} (x : V k) : ((List.finRange k).map (fun j => decide (x j ≠ 0))).length = k := by
  simp

lemma xb_of {n : ℕ} (xs : List Bool) (hlen : xs.length = n) (q : ℕ) (v : Bool)
    (h : xs[q]? = some v) : xb (fun i : Fin n => xs[i.val]'(by rw [hlen]; exact i.isLt)) q = v := by
  have hq : q < xs.length := by
    rcases Nat.lt_or_ge q xs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  unfold xb
  rw [dif_pos (by omega)]
  rw [List.getElem?_eq_getElem hq] at h
  exact Option.some.inj h

end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux
open Builder.Bank (zb bz zb_bz bz_zb)

lemma xb_of' {n : ℕ} (x : Fin n → Bool) (xs : List Bool) (hx : List.ofFn x = xs) (q : ℕ)
    (v : Bool) (h : xs[q]? = some v) : xb x q = v := by
  subst hx
  have hq : q < n := by
    rcases Nat.lt_or_ge q n with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none (by simpa using h')] at h; cases h
  unfold xb
  rw [dif_pos hq]
  rw [List.getElem?_ofFn] at h
  simpa [hq] using h

lemma flat_bits {m k : ℕ} (f : Fin m → V k) (p : Fin m) (j : Fin k) :
    ((List.finRange m).flatMap (fun p => (List.finRange k).map
      (fun j => decide (f p j ≠ 0))))[p.val * k + j.val]? = some (zb (f p j)) := by
  rw [flat_get k m _ (fun p => bits_len (f p)) p j.val j.isLt]
  exact bits_get (f p) j

lemma flat_bits_len {m k : ℕ} (f : Fin m → V k) :
    ((List.finRange m).flatMap (fun p => (List.finRange k).map
      (fun j => decide (f p j ≠ 0)))).length = m * k :=
  flat_len k m _ (fun p => bits_len (f p))

lemma flat_path {m s k : ℕ} (f : Fin m → Fin s → V k) (t : Fin m) (p : Fin s) (j : Fin k) :
    ((List.finRange m).flatMap (fun t => (List.finRange s).flatMap (fun p =>
      (List.finRange k).map (fun j => decide (f t p j ≠ 0)))))[t.val * (s * k) +
        (p.val * k + j.val)]? = some (zb (f t p j)) := by
  rw [flat_get (s * k) m _ (fun t => flat_bits_len (f t)) t _ (lt_mul_of p.isLt j.isLt)]
  exact flat_bits (f t) p j

lemma flat_path_len {m s k : ℕ} (f : Fin m → Fin s → V k) :
    ((List.finRange m).flatMap (fun t => (List.finRange s).flatMap (fun p =>
      (List.finRange k).map (fun j => decide (f t p j ≠ 0))))).length = m * (s * k) :=
  flat_len (s * k) m _ (fun t => flat_bits_len (f t))

end PEqualNP.Outside.L_meta_25887_aux

namespace PEqualNP.Outside.L_meta_25887_aux
open Builder Builder.Bank
open PEqualNP.CircuitLowerBounds

theorem mainAux : ∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ col : Bool,
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let S := Fin r → W
    let encodeInput := fun (raw : W) (delta : Fin s → W)
      (path : Fin (r+1) → Fin s → W) (test target : W) =>
      let bits := fun (x : W) => (List.finRange k).map (fun j => decide (x j ≠ 0))
      bits raw ++ (List.finRange s).flatMap (fun p => bits (delta p)) ++
      (List.finRange (r+1)).flatMap (fun t =>
        (List.finRange s).flatMap (fun p => bits (path t p))) ++ bits test ++ bits target
    let coords := fun (b : S) => (List.finRange r).flatMap (fun t =>
      (List.finRange k).map (fun j => decide (b t j ≠ 0)))
    let hits := fun (raw : W) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W)
      (test target : W) (c : S) =>
      ((Finset.univ : Finset W).filter (fun name =>
        (∀ t p, state (name,c) (raw+delta p) t - state (name,c) raw t = path t p) ∧
        (∀ j, test j ≠ 0 → state (name,c) raw (Fin.last r) j = target j))).card
    let pairing := fun (b c : S) => ∑ t : Fin r, dotProduct (b t) (c t)
    let countBits := (r+1)*k
    let w := Nat.log2 countBits + 1
    let common := (3+s+(r+1)*s)*k
    let inputs := common + r*k
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (nz neg : Fin (inputs+C.size))
      (expo : Fin w → Fin (inputs+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.output = nz.val ∧
      C.size ≤ 65536*(r+1)*((k+1)*(k+s+1)+(w+1)^2) ∧
      ∀ (raw : W) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W) (test target : W) (b : S),
        let xs := encodeInput raw delta path test target ++ coords b
        let coef : ℤ := ∑ c : S, (hits raw delta path test target c : ℤ) *
          (if pairing b c = 0 then (1 : ℤ) else -1)
        let e := Nat.log2 coef.natAbs
        (coef ≠ 0 → coef.natAbs = 2^e) ∧
        (C.wires xs).getD nz.val false = decide (coef ≠ 0) ∧
        (C.wires xs).getD neg.val false = decide (coef < 0) ∧
        (∀ j : Fin w, (C.wires xs).getD (expo j).val false = e.testBit j.val) := by
  intro k r s hk F' W' ix' rot' layer' col initial' gap' inject' state' S' encodeInput coords hits
    pairing countBits w common inputs
  have hn : inputs = k + s*k + (r+1)*(s*k) + k + k + r*k := by
    show (3+s+(r+1)*s)*k + r*k = _; ring
  let dRaw : (Fin inputs → Bool) → V k := fun x j => bz (xb x j.val)
  let dDelta : (Fin inputs → Bool) → Fin s → V k := fun x p j => bz (xb x (k + (p.val*k + j.val)))
  let dPath : (Fin inputs → Bool) → Fin (r+1) → Fin s → V k := fun x t p j =>
    bz (xb x (k + s*k + (t.val*(s*k) + (p.val*k + j.val))))
  let dTest : (Fin inputs → Bool) → V k := fun x j => bz (xb x (k + s*k + (r+1)*(s*k) + j.val))
  let dTarget : (Fin inputs → Bool) → V k := fun x j =>
    bz (xb x (k + s*k + (r+1)*(s*k) + k + j.val))
  let dB : (Fin inputs → Bool) → Fin r → V k := fun x t j =>
    bz (xb x (k + s*k + (r+1)*(s*k) + k + k + (t.val*k + j.val)))
  have avR : ∀ (B : Bank inputs) j, B.Has (fun x => zb (dRaw x j)) := fun B j =>
    avAt B _ (by have := j.isLt; omega)
  have avD : ∀ (B : Bank inputs) p j, B.Has (fun x => zb (dDelta x p j)) := fun B p j =>
    avAt B _ (by have := lt_mul_of p.isLt j.isLt; omega)
  have avP : ∀ (B : Bank inputs) t p j, B.Has (fun x => zb (dPath x t p j)) := fun B t p j =>
    avAt B _ (by have := lt_mul_of t.isLt (lt_mul_of p.isLt j.isLt); omega)
  have avT : ∀ (B : Bank inputs) j, B.Has (fun x => zb (dTest x j)) := fun B j =>
    avAt B _ (by have := j.isLt; omega)
  have avG : ∀ (B : Bank inputs) j, B.Has (fun x => zb (dTarget x j)) := fun B j =>
    avAt B _ (by have := j.isLt; omega)
  have avB : ∀ (B : Bank inputs) t j, B.Has (fun x => zb (dB x t j)) := fun B t j =>
    avAt B _ (by have := lt_mul_of t.isLt j.isLt; omega)
  have hg1 : 1 ≤ gap' := by cases col <;> simp [gap']
  have hg2 : gap' ≤ 2 := by cases col <;> simp [gap']
  have hrk : (r+1)*k < 2 ^ w := Nat.lt_log2_self
  have hkw : k < 2 ^ w := lt_of_le_of_lt (Nat.le_mul_of_pos_left k (by omega)) hrk
  let Z : Fin (r+1) → (Fin inputs → Bool) → ℤ := fun t x =>
    ST k hk r s gap' inject' (dDelta x) (dPath x) (dTest x) (dTarget x) (dB x) t
  let G0f : BitFn inputs := fun x =>
    @decide (G0 k hk r s initial' (dDelta x) (dPath x)) (Classical.propDecidable _)
  let KE : ZE inputs := ZE.sumL ((Finset.univ : Finset (Fin r × Fin k)).toList.map (fun tj =>
    .mul (.atom (fun x => dB x tj.1 tj.2))
      (.atom (fun x => dRaw x (ix k hk (tj.2.val + k - inject' tj.1.val % k))))))
  have hb : ∀ x, ((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)).sum < 2 ^ w := by
    intro x
    have := List.sum_le_length_nsmul ((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)) k
      (by simp only [List.mem_map]; rintro _ ⟨t, _, rfl⟩; exact log_le_of (ST_le hk _ _ _ _ _ _))
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at this
    omega
  have hKc : KE.cost ≤ 1 + r * k * 5 := by
    have := ZE.cost_sumL_le ((Finset.univ : Finset (Fin r × Fin k)).toList.map (fun tj =>
      (.mul (.atom (fun x => dB x tj.1 tj.2))
      (.atom (fun x => dRaw x (ix k hk (tj.2.val + k - inject' tj.1.val % k)))) : ZE inputs))) 1
      (by simp only [List.mem_map]; rintro _ ⟨t, _, rfl⟩; simp [ZE.cost])
    simpa [Finset.length_toList] using this
  have big : (Bank.empty inputs).Grow (65536*(r+1)*((k+1)*(k+s+1)+(w+1)^2))
      (fun D => D.Has (fun x => G0f x && decide (∀ t, decide (Z t x ≠ 0) = true)) ∧
        D.Has (fun x => (G0f x && decide (∀ t, decide (Z t x ≠ 0) = true)) &&
          zb (KE.eval x + ((List.finRange (r+1)).map
            (fun t => bz (decide (Z t x < 0)))).sum)) ∧
        ∀ j < w, D.Has (fun x => (G0f x && decide (∀ t, decide (Z t x ≠ 0) = true)) &&
          (((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)).sum).testBit j)) := by
    obtain ⟨D1, e1, c1, hf⟩ := (Bank.empty inputs).const false
    obtain ⟨D2, e2, c2, ht⟩ := D1.const true
    obtain ⟨D3, e3, c3, h3⟩ := collectU D2 (fun t D => Res D w (Z t))
      (fun a D E e h => h.lift e) (12000*(k+1)*(k+s+1) + (w+1)*(k+7))
      (fun D e t => perT hk gap' inject' dDelta dPath dTest dTarget dB avD avP avT avG avB
        hg1 hg2 w hkw t D (e (e2 hf)) (e ht))
    obtain ⟨D4, e4, c4, h4⟩ := allUniv D3 (fun (pj : Fin s × Fin k) x =>
      decide ((ZE.add (.atom (fun x => dDelta x pj.1 (ix k hk (pj.2.val + k - initial' % k))))
        (.atom (fun x => dPath x 0 pj.1 pj.2))).eval x = 0)) 5
      (fun D e pj => (zeroBit (ZE.add (.atom (fun x => dDelta x pj.1
        (ix k hk (pj.2.val + k - initial' % k)))) (.atom (fun x => dPath x 0 pj.1 pj.2)))
        ⟨avD D _ _, avP D _ _ _⟩).weaken (by simp [ZE.cost])
        (fun _ h => h))
    have hG : D4.Has G0f := by
      refine hasCongr h4 (fun x => ?_)
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, G0f, G0, funext_iff, Prod.forall]
      exact forall_congr' (fun p => forall_congr' (fun j => sum2 _ _))
    have okK : KE.Ok D4 := ZE.ok_sumL _ (by
      simp only [List.mem_map]; rintro _ ⟨tj, _, rfl⟩; exact ⟨avB D4 _ _, avR D4 _⟩)
    obtain ⟨D5, e5, c5, h5⟩ := finalBlock Z G0f KE D4 (fun t => (h3 t).lift e4) hG okK
      (e4 (e3 (e2 hf))) hb
    refine ⟨D5, fun h => e5 (e4 (e3 (e2 (e1 h)))), ?_, h5⟩
    simp only [Fintype.card_prod, Fintype.card_fin, Bank.empty, List.length_nil] at c1 c2 c3 c4 c5 ⊢
    have hA1 : 1 ≤ (k+1)*(k+s+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsk : s * k ≤ (k+1)*(k+s+1) := by nlinarith
    have hrk' : r * k ≤ (r+1)*((k+1)*(k+s+1)) := by nlinarith
    have hwQ : w + 1 ≤ (w+1)^2 := by nlinarith
    have hT : (w+1)*(k+7) ≤ 49*((k+1)*(k+s+1)) + (w+1)^2 := by
      rcases le_total (w+1) (k+7) with h | h
      · have := Nat.mul_le_mul_right (k+7) h; nlinarith
      · have := Nat.mul_le_mul_left (w+1) h; nlinarith
    have hT2 := Nat.mul_le_mul_left (r+1) hT
    have hQ2 := Nat.mul_le_mul_left (r+1) hwQ
    have hA2 : (k+1)*(k+s+1) ≤ (r+1)*((k+1)*(k+s+1)) := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  obtain ⟨D, -, hsize, ⟨iz, hiz, hz⟩, ⟨ig, hig, hg⟩, hE⟩ := big
  choose ie hie hE' using hE
  refine ⟨⟨D.gates, iz⟩, ⟨iz, hiz⟩, ⟨ig, hig⟩, fun j => ⟨ie j.val j.isLt, hie j.val j.isLt⟩,
    D.fan, D.back, rfl, ?_, ?_⟩
  · simpa [Circuit.size, Bank.empty] using hsize
  intro raw delta path test target b xs coef e
  have L1 : (List.map (fun j => decide (raw j ≠ 0)) (List.finRange k)).length = k := bits_len _
  have L2 := flat_bits_len delta
  have L3 := flat_path_len path
  have L4 : (List.map (fun j => decide (test j ≠ 0)) (List.finRange k)).length = k := bits_len _
  have L5 : (List.map (fun j => decide (target j ≠ 0)) (List.finRange k)).length = k := bits_len _
  have L6 := flat_bits_len b
  have hlen : xs.length = inputs := by
    simp only [xs, encodeInput, coords, List.length_append]
    rw [L1, L2, L3, L4, L5, L6, hn]
  let x : Fin inputs → Bool := fun i => xs[i.val]'(by rw [hlen]; exact i.isLt)
  have hofn : List.ofFn x = xs := List.ext_getElem (by simp [hlen]) (fun i h1 h2 => by simp [x])
  have wire : ∀ i, (Circuit.wires ⟨D.gates, iz⟩ xs).getD i false = D.val i x := by
    intro i; simp only [Bank.val, hofn]; rfl
  -- decoding
  have dR : dRaw x = raw := by
    funext j
    simp only [dRaw]
    rw [xb_of' x xs hofn j.val (zb (raw j)) (by
      simp only [xs, encodeInput, coords]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by omega), bits_get]), bz_zb]
  have dD : dDelta x = delta := by
    funext p j
    simp only [dDelta]
    have hpj := lt_mul_of p.isLt j.isLt
    rw [xb_of' x xs hofn _ (zb (delta p j)) (by
      simp only [xs, encodeInput, coords]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (by omega), L1, Nat.add_sub_cancel_left, flat_bits]), bz_zb]
  have dP : dPath x = path := by
    funext t p j
    simp only [dPath]
    have hpj := lt_mul_of p.isLt j.isLt
    have htpj := lt_mul_of t.isLt hpj
    rw [xb_of' x xs hofn _ (zb (path t p j)) (by
      simp only [xs, encodeInput, coords]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (by simp only [List.length_append]; omega),
        List.length_append, L1, L2, Nat.add_sub_cancel_left, flat_path]), bz_zb]
  have dT : dTest x = test := by
    funext j
    simp only [dTest]
    rw [xb_of' x xs hofn _ (zb (test j)) (by
      simp only [xs, encodeInput, coords]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (by simp only [List.length_append]; omega),
        List.length_append, List.length_append, L1, L2, L3, Nat.add_sub_cancel_left, bits_get]),
      bz_zb]
  have dG : dTarget x = target := by
    funext j
    simp only [dTarget]
    rw [xb_of' x xs hofn _ (zb (target j)) (by
      simp only [xs, encodeInput, coords]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (by simp only [List.length_append]; omega),
        List.length_append, List.length_append, List.length_append, L1, L2, L3, L4,
        Nat.add_sub_cancel_left, bits_get]), bz_zb]
  have dBb : dB x = b := by
    funext t j
    simp only [dB]
    have htj := lt_mul_of t.isLt j.isLt
    rw [xb_of' x xs hofn _ (zb (b t j)) (by
      simp only [xs, encodeInput, coords]
      rw [List.getElem?_append_right (by simp only [List.length_append]; omega),
        List.length_append, List.length_append, List.length_append, List.length_append,
        L1, L2, L3, L4, L5, Nat.add_sub_cancel_left, flat_bits]), bz_zb]
  -- semantics
  have hZx : ∀ t, Z t x = ST k hk r s gap' inject' delta path test target b t := by
    intro t; simp only [Z, dD, dP, dT, dG, dBb]
  have hKx : KE.eval x = Kc k hk r inject' raw b := by
    simp only [KE, ZE.eval_sumL, List.map_map, Function.comp_def, ZE.eval, dBb, dR]
    rw [Finset.sum_map_toList, Fintype.sum_prod_type]
    simp only [Kc, dotProduct, rot]
  have hc : coef = sg (Kc k hk r inject' raw b) * G0i k hk r s initial' delta path *
      ∏ t, ST k hk r s gap' inject' delta path test target b t := by
    rw [← factor]
    show ∑ c : Fin r → V k, ((Finset.univ.filter (fun name : V k =>
        (∀ t p, state k hk r gap' initial' inject' (name, c) (raw + delta p) t -
          state k hk r gap' initial' inject' (name, c) raw t = path t p) ∧
        (∀ j, test j ≠ 0 → state k hk r gap' initial' inject' (name, c) raw (Fin.last r) j =
          target j))).card : ℤ) *
        (if (∑ t : Fin r, dotProduct (b t) (c t)) = 0 then (1:ℤ) else -1) = _
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun name _ => ?_)
    split_ifs <;> simp [sg, *]
  obtain ⟨c1, c2, c3⟩ := combine coef (Kc k hk r inject' raw b) (G0 k hk r s initial' delta path)
    (fun t => ST k hk r s gap' inject' delta path test target b t) hc
    (fun t => ST_pow hk _ _ _ _ _ t)
  have hnz : (G0f x && decide (∀ t, decide (Z t x ≠ 0) = true)) = decide (coef ≠ 0) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, G0f, hZx, dD, dP]
    exact c1.symm
  have hsum : ((List.finRange (r+1)).map (fun t => Nat.log2 (Z t x).natAbs)).sum =
      ∑ t, Nat.log2 (ST k hk r s gap' inject' delta path test target b t).natAbs := by
    rw [Fin.sum_univ_def]; simp only [hZx]
  refine ⟨fun h => ?_, ?_, ?_, fun j => ?_⟩
  · have := c3 h
    show coef.natAbs = 2 ^ (Nat.log2 coef.natAbs)
    rw [this, Nat.log2_two_pow]
  · show (Circuit.wires ⟨D.gates, iz⟩ xs).getD iz false = _
    rw [wire, hz]; beta_reduce; rw [hnz]
  · show (Circuit.wires ⟨D.gates, iz⟩ xs).getD ig false = _
    rw [wire, hg]; beta_reduce; rw [hnz, hKx]
    have : ((List.finRange (r+1)).map (fun t => bz (decide (Z t x < 0)))).sum =
        ∑ t, bz (decide (ST k hk r s gap' inject' delta path test target b t < 0)) := by
      rw [Fin.sum_univ_def]; simp only [hZx]
    rw [this, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, c2, c1]
  · show (Circuit.wires ⟨D.gates, iz⟩ xs).getD (ie j.val j.isLt) false = _
    rw [wire, hE']; beta_reduce; rw [hnz, hsum]
    show _ = (Nat.log2 coef.natAbs).testBit j.val
    by_cases h0 : coef = 0
    · simp [h0]
    · rw [c3 h0, Nat.log2_two_pow]; simp [h0]

end PEqualNP.Outside.L_meta_25887_aux

theorem PEqualNP.Outside.L_meta_25887 : ∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ col : Bool,
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let S := Fin r → W
    let encodeInput := fun (raw : W) (delta : Fin s → W)
      (path : Fin (r+1) → Fin s → W) (test target : W) =>
      let bits := fun (x : W) => (List.finRange k).map (fun j => decide (x j ≠ 0))
      bits raw ++ (List.finRange s).flatMap (fun p => bits (delta p)) ++
      (List.finRange (r+1)).flatMap (fun t =>
        (List.finRange s).flatMap (fun p => bits (path t p))) ++ bits test ++ bits target
    let coords := fun (b : S) => (List.finRange r).flatMap (fun t =>
      (List.finRange k).map (fun j => decide (b t j ≠ 0)))
    let hits := fun (raw : W) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W)
      (test target : W) (c : S) =>
      ((Finset.univ : Finset W).filter (fun name =>
        (∀ t p, state (name,c) (raw+delta p) t - state (name,c) raw t = path t p) ∧
        (∀ j, test j ≠ 0 → state (name,c) raw (Fin.last r) j = target j))).card
    let pairing := fun (b c : S) => ∑ t : Fin r, dotProduct (b t) (c t)
    let countBits := (r+1)*k
    let w := Nat.log2 countBits + 1
    let common := (3+s+(r+1)*s)*k
    let inputs := common + r*k
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (nz neg : Fin (inputs+C.size))
      (expo : Fin w → Fin (inputs+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.output = nz.val ∧
      C.size ≤ 65536*(r+1)*((k+1)*(k+s+1)+(w+1)^2) ∧
      ∀ (raw : W) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W) (test target : W) (b : S),
        let xs := encodeInput raw delta path test target ++ coords b
        let coef : ℤ := ∑ c : S, (hits raw delta path test target c : ℤ) *
          (if pairing b c = 0 then (1 : ℤ) else -1)
        let e := Nat.log2 coef.natAbs
        (coef ≠ 0 → coef.natAbs = 2^e) ∧
        (C.wires xs).getD nz.val false = decide (coef ≠ 0) ∧
        (C.wires xs).getD neg.val false = decide (coef < 0) ∧
        (∀ j : Fin w, (C.wires xs).getD (expo j).val false = e.testBit j.val) :=
  PEqualNP.Outside.L_meta_25887_aux.mainAux
