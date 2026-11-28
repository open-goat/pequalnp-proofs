import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32578_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F2 := ZMod 2
abbrev F4 := ZMod 4

def b2f (b : Bool) : F2 := if b then 1 else 0

def b2f4 (b : Bool) : F4 := if b then 1 else 0

lemma f2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

def nonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthList (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat])
    (List.replicate width 0)

def distFn {n m : ℕ} (H : Fin n → Fin m → Bool) (i j : Fin n) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => H i c ≠ H j c)).card % 8

def gramMat {n : ℕ} (m : ℕ) (D : Fin n → Fin n → ℕ) (u : Fin n) :
    Matrix (Option (Fin n)) (Option (Fin n)) F4 :=
  fun i j =>
    let x := i.getD u
    let y := j.getD u
    if i.isNone then (if j.isNone then (m : F4) else (D u y : F4))
    else if j.isNone then (D u x : F4)
    else ((((D u x + D u y + 8 - D x y) % 8 / 2 : ℕ)) : F4)

def liftM {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) :
    Matrix (Option (Fin n)) (Fin m) F4 :=
  fun i c =>
    match i with
    | none => 1
    | some x => if T x c ≠ T u c then 1 else 0

def liftM2 {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) :
    Matrix (Option (Fin n)) (Fin m) F2 :=
  fun i c =>
    match i with
    | none => 1
    | some x => if T x c ≠ T u c then 1 else 0

lemma cast_mod8_f4 (k : ℕ) : ((k % 8 : ℕ) : F4) = (k : F4) := by
  have h : k = 8 * (k / 8) + k % 8 := (Nat.div_add_mod k 8).symm
  conv_rhs => rw [h]
  push_cast
  have h8 : (8 : F4) = 0 := by decide
  rw [h8, zero_mul, zero_add]

lemma inter_mod4_eq (a b c k : ℕ) (hab : a + b = c + 2 * k) :
    ((((a % 8 + b % 8 + 8 - c % 8) % 8 / 2 : ℕ)) : F4) = (k : F4) := by
  have h1 : (a % 8 + b % 8 + 8 - c % 8) % 8 = (2 * k) % 8 := by omega
  rw [h1]
  have h2 : (2 * k) % 8 / 2 = k % 4 := by omega
  rw [h2]
  have h3 : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  conv_rhs => rw [h3]
  push_cast
  have h4 : (4 : F4) = 0 := by decide
  rw [h4, zero_mul, zero_add]

lemma gramMat_eq_mul_transpose {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) :
    gramMat m (distFn T) u = liftM T u * (liftM T u).transpose := by
  ext i j
  rw [Matrix.mul_apply]
  cases i with
  | none =>
    cases j with
    | none =>
      simp [gramMat, liftM]
    | some y =>
      simp only [gramMat, liftM, Matrix.transpose_apply, Option.isNone_none, Option.isNone_some,
        Option.getD_some, ↓reduceIte, Bool.false_eq_true, one_mul, distFn]
      rw [cast_mod8_f4]
      have hsum : (∑ c : Fin m, (if T y c ≠ T u c then (1 : F4) else 0)) =
          ((Finset.univ.filter (fun c : Fin m => T u c ≠ T y c)).card : F4) := by
        rw [Finset.sum_boole]
        congr 2
        ext c
        simp [ne_comm]
      exact hsum.symm
  | some x =>
    cases j with
    | none =>
      simp only [gramMat, liftM, Matrix.transpose_apply, Option.isNone_none, Option.isNone_some,
        Option.getD_some, ↓reduceIte, Bool.false_eq_true, mul_one, distFn]
      rw [cast_mod8_f4]
      have hsum : (∑ c : Fin m, (if T x c ≠ T u c then (1 : F4) else 0)) =
          ((Finset.univ.filter (fun c : Fin m => T u c ≠ T x c)).card : F4) := by
        rw [Finset.sum_boole]
        congr 2
        ext c
        simp [ne_comm]
      exact hsum.symm
    | some y =>
      simp only [gramMat, liftM, Matrix.transpose_apply, Option.isNone_some, Option.getD_some,
        Bool.false_eq_true, ↓reduceIte, distFn]
      let a := (Finset.univ.filter (fun c : Fin m => T u c ≠ T x c)).card
      let b := (Finset.univ.filter (fun c : Fin m => T u c ≠ T y c)).card
      let d := (Finset.univ.filter (fun c : Fin m => T x c ≠ T y c)).card
      let k := (Finset.univ.filter (fun c : Fin m => T x c ≠ T u c ∧ T y c ≠ T u c)).card
      have hab : a + b = d + 2 * k := by
        have hpt : ∀ c : Fin m,
            (if T u c ≠ T x c then 1 else 0) + (if T u c ≠ T y c then 1 else 0) =
            (if T x c ≠ T y c then 1 else 0) + 2 * (if T x c ≠ T u c ∧ T y c ≠ T u c then 1 else 0) := by
          intro c
          cases T u c <;> cases T x c <;> cases T y c <;> decide
        have htot := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin m))) rfl (fun c _ => hpt c)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at htot
        simp only [Finset.sum_boole, Nat.cast_id] at htot
        exact htot
      have hrhs : (∑ c : Fin m, (if T x c ≠ T u c then (1 : F4) else 0) *
          (if T y c ≠ T u c then (1 : F4) else 0)) = (k : F4) := by
        have hpt : ∀ c : Fin m,
            (if T x c ≠ T u c then (1 : F4) else 0) * (if T y c ≠ T u c then (1 : F4) else 0) =
            if T x c ≠ T u c ∧ T y c ≠ T u c then 1 else 0 := by
          intro c
          by_cases h1 : T x c ≠ T u c <;> by_cases h2 : T y c ≠ T u c <;> simp [h1, h2]
        rw [Finset.sum_congr rfl (fun c _ => hpt c), Finset.sum_boole]
      rw [hrhs]
      exact inter_mod4_eq a b d k hab

lemma image_card_congr_mul {I : Type} [Fintype I] [DecidableEq I]
    (G E Einv : Matrix I I F4) (hL : Einv * E = 1) (hR : E * Einv = 1) :
    (Finset.univ.image (fun x : I → F4 => (E * G * E.transpose).mulVec x)).card =
    (Finset.univ.image (fun x : I → F4 => G.mulVec x)).card := by
  have hLT : E.transpose * Einv.transpose = 1 := by
    rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
  have hRT : Einv.transpose * E.transpose = 1 := by
    rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  have hsurj : Finset.univ.image (fun x : I → F4 => E.transpose.mulVec x) = Finset.univ := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    refine ⟨Einv.transpose.mulVec y, ?_⟩
    rw [Matrix.mulVec_mulVec, hLT, Matrix.one_mulVec]
  have h1 : Finset.univ.image (fun x : I → F4 => (E * G * E.transpose).mulVec x) =
      (Finset.univ.image (fun x : I → F4 => G.mulVec x)).image (fun y => E.mulVec y) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨G.mulVec (E.transpose.mulVec x), ⟨E.transpose.mulVec x, rfl⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨Einv.transpose.mulVec y, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        ← Matrix.mulVec_mulVec, hLT, Matrix.one_mulVec]
  have hinj : Function.Injective (fun y : I → F4 => E.mulVec y) := by
    intro y1 y2 h
    have := congrArg Einv.mulVec h
    simpa [Matrix.mulVec_mulVec, hL] using this
  rw [h1, Finset.card_image_of_injective _ hinj]

lemma dist_colFlip {n m : ℕ} (T : Fin n → Fin m → Bool) (cf : Fin m → Bool) :
    distFn (fun i j => xor (T i j) (cf j)) = distFn T := by
  funext i j
  dsimp only [distFn]
  congr 2
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases T i c <;> cases T j c <;> cases cf c <;> decide

lemma image_card_rowFlip {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (rf : Fin n → Bool) :
    (Finset.univ.image (fun x : Option (Fin n) → F4 =>
      (gramMat m (distFn (fun i j => xor (rf i) (T i j))) u).mulVec x)).card =
    (Finset.univ.image (fun x : Option (Fin n) → F4 =>
      (gramMat m (distFn T) u).mulVec x)).card := by
  let T' := fun i j => xor (rf i) (T i j)
  let E : Matrix (Option (Fin n)) (Option (Fin n)) F4 := fun i j =>
    match i with
    | none => if j = none then 1 else 0
    | some x =>
      if rf x = rf u then (if j = some x then 1 else 0)
      else (if j = none then 1 else if j = some x then -1 else 0)
  have hEE : E * E = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    cases i with
    | none =>
      rw [Finset.sum_eq_single none]
      · simp [E, eq_comm]
      · intro k _ hk; simp [E, hk]
      · intro h; exact (h (Finset.mem_univ _)).elim
    | some x =>
      by_cases hrf : rf x = rf u
      · rw [Finset.sum_eq_single (some x)]
        · simp [E, hrf, eq_comm]
        · intro k _ hk; simp [E, hrf, hk]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · have hpair : ∀ k : Option (Fin n), k ≠ none → k ≠ some x → E (some x) k * E k j = 0 := by
          intro k h1 h2; simp [E, hrf, h1, h2]
        rw [Finset.sum_eq_add none (some x) (by simp) (fun k _ h => hpair k h.1 h.2)
          (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
        cases j with
        | none => simp [E, hrf]
        | some y =>
          by_cases hxy : y = x
          · subst hxy; simp [E, hrf]
          · simp [E, hrf, hxy, Ne.symm hxy]
  have hEM : liftM T' u = E * liftM T u := by
    ext i c
    rw [Matrix.mul_apply]
    cases i with
    | none =>
      rw [Finset.sum_eq_single none]
      · simp [E, liftM]
      · intro k _ hk; simp [E, hk]
      · intro h; exact (h (Finset.mem_univ _)).elim
    | some x =>
      by_cases hrf : rf x = rf u
      · rw [Finset.sum_eq_single (some x)]
        · simp only [E, hrf, ↓reduceIte, one_mul, liftM, T']
          revert hrf; cases rf x <;> cases rf u <;> cases T x c <;> cases T u c <;> decide
        · intro k _ hk; simp [E, hrf, hk]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · have hpair : ∀ k : Option (Fin n), k ≠ none → k ≠ some x → E (some x) k * liftM T u k c = 0 := by
          intro k h1 h2; simp [E, hrf, h1, h2]
        rw [Finset.sum_eq_add none (some x) (by simp) (fun k _ h => hpair k h.1 h.2)
          (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
        simp only [E, hrf, ↓reduceIte, Option.some_ne_none, one_mul, neg_one_mul, liftM, T']
        have hbool : ∀ a b p q : Bool, a ≠ b →
            (if xor a p ≠ xor b q then (1 : F4) else 0) = 1 + -(if p ≠ q then (1 : F4) else 0) := by decide
        exact hbool (rf x) (rf u) (T x c) (T u c) hrf
  have hG : gramMat m (distFn T') u = E * gramMat m (distFn T) u * E.transpose := by
    rw [gramMat_eq_mul_transpose T' u, gramMat_eq_mul_transpose T u, hEM,
      Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [hG]
  exact image_card_congr_mul (gramMat m (distFn T) u) E E hEE hEE

lemma image_card_changeRef {n m : ℕ} (T : Fin n → Fin m → Bool) (u v : Fin n) :
    (Finset.univ.image (fun x : Option (Fin n) → F4 =>
      (gramMat m (distFn T) v).mulVec x)).card =
    (Finset.univ.image (fun x : Option (Fin n) → F4 =>
      (gramMat m (distFn T) u).mulVec x)).card := by
  by_cases huv : u = v
  · subst huv; rfl
  let s : Fin m → F4 := fun c => if T u c ≠ T v c then -1 else 1
  let D : Matrix (Fin m) (Fin m) F4 := Matrix.diagonal s
  have hDD : D * D.transpose = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab; simp [D, s]; split_ifs <;> decide
      · simp [D, Matrix.diagonal_apply_ne _ (Ne.symm hab), hab]
    · intro k _ hk; simp [D, Matrix.diagonal_apply_ne _ (Ne.symm hk)]
    · intro h; exact (h (Finset.mem_univ _)).elim
  let F : Matrix (Option (Fin n)) (Option (Fin n)) F4 := fun i j =>
    match i with
    | none => if j = none then 1 else if j = some v then (-2 : F4) else 0
    | some x =>
      if x = v then (if j = some u then 1 else 0)
      else if x = u then (if j = some v then -1 else 0)
      else (if j = some x then 1 else if j = some v then -1 else 0)
  let Finv : Matrix (Option (Fin n)) (Option (Fin n)) F4 := fun i j =>
    match i with
    | none => if j = none then 1 else if j = some u then (-2 : F4) else 0
    | some x =>
      if x = u then (if j = some v then 1 else 0)
      else if x = v then (if j = some u then -1 else 0)
      else (if j = some x then 1 else if j = some u then -1 else 0)
  have hF_mul : ∀ (A B : Matrix (Option (Fin n)) (Option (Fin n)) F4) (a b : Fin n),
      a ≠ b →
      (∀ i j, A i j = match i with
        | none => if j = none then 1 else if j = some b then (-2 : F4) else 0
        | some x =>
          if x = b then (if j = some a then 1 else 0)
          else if x = a then (if j = some b then -1 else 0)
          else (if j = some x then 1 else if j = some b then -1 else 0)) →
      (∀ i j, B i j = match i with
        | none => if j = none then 1 else if j = some a then (-2 : F4) else 0
        | some x =>
          if x = a then (if j = some b then 1 else 0)
          else if x = b then (if j = some a then -1 else 0)
          else (if j = some x then 1 else if j = some a then -1 else 0)) →
      A * B = 1 := by
    intro A B a b hab hA hB
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    cases i with
    | none =>
      have hp : ∀ k : Option (Fin n), k ≠ none → k ≠ some b → A none k * B k j = 0 := by
        intro k h1 h2; rw [hA]; simp [h1, h2]
      rw [Finset.sum_eq_add none (some b) (by simp) (fun k _ h => hp k h.1 h.2)
        (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
      rw [hA, hA, hB, hB]
      cases j with
      | none => simp [hab.symm]
      | some y =>
        by_cases hya : y = a
        · subst hya; simp [hab.symm]
        · simp [hab.symm, hya]
    | some x =>
      by_cases hxb : x = b
      · subst hxb
        rw [Finset.sum_eq_single (some a)]
        · rw [hA, hB]; simp [eq_comm]
        · intro k _ hk; rw [hA]; simp [hk]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · by_cases hxa : x = a
        · subst hxa
          rw [Finset.sum_eq_single (some b)]
          · rw [hA, hB]; simp [hab, hab.symm, eq_comm]
          · intro k _ hk; rw [hA]; simp [hab, hk]
          · intro h; exact (h (Finset.mem_univ _)).elim
        · have hp : ∀ k : Option (Fin n), k ≠ some x → k ≠ some b → A (some x) k * B k j = 0 := by
            intro k h1 h2; rw [hA]; simp [hxb, hxa, h1, h2]
          rw [Finset.sum_eq_add (some x) (some b) (by simp [hxb]) (fun k _ h => hp k h.1 h.2)
            (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
          rw [hA, hA, hB, hB]
          cases j with
          | none => simp [hxb, hxa, hab.symm]
          | some y =>
            by_cases hyx : y = x
            · subst hyx; simp [hxb, hxa, hab.symm]
            · by_cases hya : y = a
              · subst hya; simp [hxb, hxa, hab.symm, hyx, Ne.symm hxb]
              · simp [hxb, hxa, hab.symm, hyx, Ne.symm hyx, hya]
  have hL : Finv * F = 1 := hF_mul Finv F v u (Ne.symm huv) (fun _ _ => rfl) (fun _ _ => rfl)
  have hR : F * Finv = 1 := hF_mul F Finv u v huv (fun _ _ => rfl) (fun _ _ => rfl)
  have hFM : liftM T v = F * liftM T u * D := by
    ext i c
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single c]
    · simp only [D, Matrix.diagonal_apply_eq, Matrix.mul_apply]
      cases i with
      | none =>
        have hp : ∀ k : Option (Fin n), k ≠ none → k ≠ some v → F none k * liftM T u k c = 0 := by
          intro k h1 h2; simp [F, h1, h2]
        rw [Finset.sum_eq_add none (some v) (by simp) (fun k _ h => hp k h.1 h.2)
          (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
        simp only [F, liftM, s, ↓reduceIte, Option.some_ne_none, one_mul]
        cases T u c <;> cases T v c <;> decide
      | some x =>
        by_cases hxv : x = v
        · subst hxv
          rw [Finset.sum_eq_single (some u)]
          · simp [F, liftM]
          · intro k _ hk; simp [F, hk]
          · intro h; exact (h (Finset.mem_univ _)).elim
        · by_cases hxu : x = u
          · subst hxu
            rw [Finset.sum_eq_single (some v)]
            · simp only [F, liftM, s, huv, ↓reduceIte, neg_one_mul]
              cases T x c <;> cases T v c <;> decide
            · intro k _ hk; simp [F, huv, hk]
            · intro h; exact (h (Finset.mem_univ _)).elim
          · have hp : ∀ k : Option (Fin n), k ≠ some x → k ≠ some v → F (some x) k * liftM T u k c = 0 := by
              intro k h1 h2; simp [F, hxv, hxu, h1, h2]
            rw [Finset.sum_eq_add (some x) (some v) (by simp [hxv]) (fun k _ h => hp k h.1 h.2)
              (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
            simp only [F, liftM, s, hxv, hxu, ↓reduceIte, Option.some.injEq, Ne.symm hxv, one_mul, neg_one_mul]
            cases T x c <;> cases T u c <;> cases T v c <;> decide
    · intro k _ hk; simp [D, Matrix.diagonal_apply_ne _ hk]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hG : gramMat m (distFn T) v = F * gramMat m (distFn T) u * F.transpose := by
    rw [gramMat_eq_mul_transpose T v, gramMat_eq_mul_transpose T u, hFM,
      Matrix.transpose_mul, Matrix.transpose_mul]
    calc F * liftM T u * D * (D.transpose * ((liftM T u).transpose * F.transpose))
        = F * liftM T u * (D * D.transpose) * (liftM T u).transpose * F.transpose := by
          simp only [Matrix.mul_assoc]
      _ = F * (liftM T u * (liftM T u).transpose) * F.transpose := by
          rw [hDD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hG]
  exact image_card_congr_mul (gramMat m (distFn T) u) F Finv hL hR

def red42 : F4 →+* F2 := ZMod.castHom (by decide : 2 ∣ 4) F2

def lift24 (a : F2) : F4 := if a = 0 then 0 else 2

lemma mul2_eq_lift24 (a : F4) : (2 : F4) * a = lift24 (red42 a) := by
  fin_cases a <;> decide

lemma even_eq_two_mul_half (a : F4) (h : red42 a = 0) :
    (2 : F4) * ((a.val / 2 : ℕ) : F4) = a := by
  have hmod : a.val % 2 = 0 := by
    have h1 : (a.val : F2) = 0 := by
      have hz : red42 (a.val : F4) = (a.val : F2) := map_natCast red42 a.val
      rw [ZMod.natCast_zmod_val] at hz
      exact hz.symm.trans h
    exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff a.val 2).mp h1)
  have h2 : 2 * (a.val / 2) = a.val := by omega
  calc (2 : F4) * ((a.val / 2 : ℕ) : F4)
      = ((2 * (a.val / 2) : ℕ) : F4) := by push_cast; rfl
    _ = (a.val : F4) := by rw [h2]
    _ = a := ZMod.natCast_zmod_val a

lemma red42_mulVec {I J : Type} [Fintype I] [Fintype J]
    (M : Matrix I J F4) (M2 : Matrix I J F2)
    (hred : ∀ i j, red42 (M i j) = M2 i j) (x : J → F4) (i : I) :
    red42 (M.mulVec x i) = M2.mulVec (fun j => red42 (x j)) i := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hred]

lemma image_card_gram_le_pow4 {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I J F4) (M2 : Matrix I J F2) (hred : ∀ i j, red42 (M i j) = M2 i j) :
    (Finset.univ.image (fun x : I → F4 => (M * M.transpose).mulVec x)).card ≤
    4 ^ Module.finrank F2 (LinearMap.range M2.transpose.mulVecLin) := by
  classical
  let W : Finset (J → F2) := Finset.univ.image (fun v : I → F2 => M2.transpose.mulVec v)
  let V : Finset (I → F2) := Finset.univ.image (fun v : J → F2 => M2.mulVec v)
  have hW_card : W.card = 2 ^ Module.finrank F2 (LinearMap.range M2.transpose.mulVecLin) := by
    have h1 : W.card = Fintype.card (LinearMap.range M2.transpose.mulVecLin) := by
      refine Finset.card_bij (fun y hy => ⟨y, ?_⟩) ?_ ?_ ?_
      · rcases Finset.mem_image.mp hy with ⟨v, _, rfl⟩
        exact ⟨v, rfl⟩
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · rintro ⟨y, v, rfl⟩ _
        exact ⟨M2.transpose.mulVec v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, rfl⟩
    rw [h1, Module.card_eq_pow_finrank (K := F2), ZMod.card 2]
  have hV_card : V.card = 2 ^ Module.finrank F2 (LinearMap.range M2.mulVecLin) := by
    have h1 : V.card = Fintype.card (LinearMap.range M2.mulVecLin) := by
      refine Finset.card_bij (fun y hy => ⟨y, ?_⟩) ?_ ?_ ?_
      · rcases Finset.mem_image.mp hy with ⟨v, _, rfl⟩
        exact ⟨v, rfl⟩
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · rintro ⟨y, v, rfl⟩ _
        exact ⟨M2.mulVec v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, rfl⟩
    rw [h1, Module.card_eq_pow_finrank (K := F2), ZMod.card 2]
  have hrk_eq : Module.finrank F2 (LinearMap.range M2.mulVecLin) =
      Module.finrank F2 (LinearMap.range M2.transpose.mulVecLin) := by
    simpa [Matrix.rank] using (Matrix.rank_transpose M2).symm
  let pick : (J → F2) → (I → F4) := fun w =>
    if h : ∃ x : I → F4, (fun j => red42 (M.transpose.mulVec x j)) = w then Classical.choose h else 0
  let dec : (J → F2) × (I → F2) → (I → F4) := fun p i =>
    (M * M.transpose).mulVec (pick p.1) i + lift24 (p.2 i)
  have hsub : Finset.univ.image (fun x : I → F4 => (M * M.transpose).mulVec x) ⊆ (W ×ˢ V).image dec := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, _, rfl⟩
    let w : J → F2 := fun j => red42 (M.transpose.mulVec x j)
    have hwW : w ∈ W := by
      refine Finset.mem_image.mpr ⟨fun i => red42 (x i), Finset.mem_univ _, ?_⟩
      funext j
      exact (red42_mulVec M.transpose M2.transpose (fun a b => hred b a) x j).symm
    have hex : ∃ x0 : I → F4, (fun j => red42 (M.transpose.mulVec x0 j)) = w := ⟨x, rfl⟩
    let x0 := pick w
    have hx0 : (fun j => red42 (M.transpose.mulVec x0 j)) = w := by
      dsimp only [x0, pick]
      simp only [hex, ↓reduceDIte]
      exact Classical.choose_spec hex
    let diff : J → F4 := fun j => M.transpose.mulVec x j - M.transpose.mulVec x0 j
    have hdiff_even : ∀ j, red42 (diff j) = 0 := by
      intro j
      dsimp only [diff]
      rw [map_sub, congrFun hx0 j]
      exact sub_self _
    let z : J → F4 := fun j => ((diff j).val / 2 : ℕ)
    have hdiff_eq : diff = (2 : F4) • z := by
      funext j
      exact (even_eq_two_mul_half (diff j) (hdiff_even j)).symm
    let v : I → F2 := M2.mulVec (fun j => red42 (z j))
    have hvV : v ∈ V := Finset.mem_image.mpr ⟨fun j => red42 (z j), Finset.mem_univ _, rfl⟩
    refine Finset.mem_image.mpr ⟨(w, v), Finset.mem_product.mpr ⟨hwW, hvV⟩, ?_⟩
    funext i
    dsimp only [dec]
    have hsplit : M.transpose.mulVec x = M.transpose.mulVec x0 + (2 : F4) • z := by
      funext j
      rw [Pi.add_apply, ← congrFun hdiff_eq j]
      dsimp only [diff]
      ring
    have hM1 : (M * M.transpose).mulVec x i =
        (M * M.transpose).mulVec x0 i + (2 : F4) * (M.mulVec z i) := by
      rw [← Matrix.mulVec_mulVec, hsplit, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec]
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hM1, mul2_eq_lift24, red42_mulVec M M2 hred z i]
  calc (Finset.univ.image (fun x : I → F4 => (M * M.transpose).mulVec x)).card
      ≤ ((W ×ˢ V).image dec).card := Finset.card_le_card hsub
    _ ≤ (W ×ˢ V).card := Finset.card_image_le
    _ = W.card * V.card := Finset.card_product W V
    _ = 2 ^ Module.finrank F2 (LinearMap.range M2.transpose.mulVecLin) *
        2 ^ Module.finrank F2 (LinearMap.range M2.transpose.mulVecLin) := by
        rw [hW_card, hV_card, hrk_eq]
    _ = 4 ^ Module.finrank F2 (LinearMap.range M2.transpose.mulVecLin) := by
        rw [← mul_pow]; norm_num

lemma foldl_append_length {α β : Type} (f : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih]; omega

lemma foldl_append_getD_lt {α β : Type} (d0 : α) (f : List α → β → α)
    (gs : List β) (init : List α) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD i d0 = init.getD i d0 := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (init ++ [f init g]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_append_getD_gate {α β : Type} (d0 : α) (f : List α → β → α)
    (gs : List β) (init : List α) (j : ℕ) (hj : j < gs.length) :
    let pref := (gs.take j).foldl (fun acc g => acc ++ [f acc g]) init
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD (init.length + j) d0 =
      f pref (gs[j]) ∧
    ∀ a < init.length + j, pref.getD a d0 =
      (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD a d0 := by
  intro pref
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    congr 1
    exact (List.cons_getElem_drop_succ (h := hj)).symm
  have hplen : pref.length = init.length + j := by
    dsimp only [pref]
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : gs.foldl (fun acc g => acc ++ [f acc g]) init =
      (gs.drop (j + 1)).foldl (fun acc g => acc ++ [f acc g]) (pref ++ [f pref (gs[j])]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  constructor
  · rw [hfold, foldl_append_getD_lt d0 f (gs.drop (j + 1)) (pref ++ [f pref (gs[j])])
      (init.length + j) (by simp [hplen])]
    simp only [List.getD_eq_getElem?_getD, ← hplen, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  · intro a ha
    rw [hfold, foldl_append_getD_lt d0 f (gs.drop (j + 1)) (pref ++ [f pref (gs[j])])
      a (by simp [hplen]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : a < pref.length)]

lemma le_foldr_max {α : Type} (f : α → ℕ) (l : List α) (a : α) (ha : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact le_max_left _ _
    · exact (ih hmem).trans (le_max_right _ _)

lemma gate_affine_of_len1 (op : GateOp) :
    ∃ c0 c1 : F2, ∀ u : Bool, b2f (op.eval [u]) = c0 + c1 * b2f u := by
  refine ⟨b2f (op.eval [false]), b2f (op.eval [false]) + b2f (op.eval [true]), fun u => ?_⟩
  cases u <;> cases op.eval [false] <;> cases op.eval [true] <;> decide

lemma gate_affine_of_nonlin_false (op : GateOp)
    (hnl : xor (xor (op.eval [false, false]) (op.eval [false, true]))
        (xor (op.eval [true, false]) (op.eval [true, true])) = false) :
    ∃ c0 c1 c2 : F2, ∀ u v : Bool, b2f (op.eval [u, v]) = c0 + c1 * b2f u + c2 * b2f v := by
  refine ⟨b2f (op.eval [false, false]),
    b2f (op.eval [false, false]) + b2f (op.eval [true, false]),
    b2f (op.eval [false, false]) + b2f (op.eval [false, true]), fun u v => ?_⟩
  revert hnl
  cases u <;> cases v <;>
    cases op.eval [false, false] <;> cases op.eval [false, true] <;>
    cases op.eval [true, false] <;> cases op.eval [true, true] <;>
    decide

lemma gate_quad_of_len2 (op : GateOp) :
    ∃ c0 c1 c2 c3 : F2, ∀ u v : Bool,
      b2f (op.eval [u, v]) = c0 + c1 * b2f u + c2 * b2f v + c3 * b2f u * b2f v := by
  refine ⟨b2f (op.eval [false, false]),
    b2f (op.eval [false, false]) + b2f (op.eval [true, false]),
    b2f (op.eval [false, false]) + b2f (op.eval [false, true]),
    b2f (op.eval [false, false]) + b2f (op.eval [false, true]) +
      b2f (op.eval [true, false]) + b2f (op.eval [true, true]), fun u v => ?_⟩
  cases u <;> cases v <;>
    cases op.eval [false, false] <;> cases op.eval [false, true] <;>
    cases op.eval [true, false] <;> cases op.eval [true, true] <;>
    decide

lemma oneEach_getD {n m : ℕ} (x : Fin n) (y : Fin m) (a : ℕ) :
    (oneEach x y).getD a false =
      if h1 : a < n then decide (⟨a, h1⟩ = x)
      else if h2 : a < n + m then decide (⟨a - n, by omega⟩ = y)
      else false := by
  dsimp only [oneEach]
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left (by simp [h1]), List.getElem?_ofFn]
    simp [h1]
  · rw [List.getElem?_append_right (by simp; omega), List.length_ofFn, List.getElem?_ofFn]
    have hlt : a - n < m := by omega
    simp [hlt]
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma finrank_anchored_circuit_le {n m : ℕ} (P : Fin n → Fin m → Bool) (C : Circuit)
    (v : Fin n)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hread : ReadsBack (n + m) C)
    (hrep : Represents P C)
    (hdep : (depthList (n + m) C).getD C.output 0 ≤ 1) :
    ∃ U : Submodule F2 (Fin m → F2),
      Module.finrank F2 U ≤ 2 * C.gates.countP nonlin + 1 ∧
      (fun _ : Fin m => (1 : F2)) ∈ U ∧
      ∀ x : Fin n, (fun y : Fin m => b2f (P x y) + b2f (P v y)) ∈ U := by
  classical
  let W := n + m
  let ds := depthList W C
  let val : ℕ → Fin n → Fin m → F2 := fun w x y => b2f ((C.wires (oneEach x y)).getD w false)
  have hsep : ∀ w : ℕ, ds.getD w 0 = 0 →
      ∃ (r : Fin n → F2) (c : Fin m → F2), ∀ x y, val w x y = r x + c y := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw0
      by_cases hltW : w < W
      · refine ⟨fun x => if h1 : w < n then b2f (decide (⟨w, h1⟩ = x)) else 0,
          fun y => if h1 : w < n then 0 else b2f (decide (⟨w - n, by omega⟩ = y)), fun x y => ?_⟩
        dsimp only [val, Circuit.wires]
        have hlen : (oneEach x y).length = W := by simp [oneEach, W]
        rw [foldl_append_getD_lt false _ C.gates (oneEach x y) w (by omega), oneEach_getD]
        split_ifs with h1
        · simp
        · simp
      · by_cases hltC : w < W + C.gates.length
        · let j := w - W
          have hj : j < C.gates.length := by omega
          have hwj : w = W + j := by omega
          let g := C.gates[j]
          have hgat : gateAt C j = g := by
            dsimp only [gateAt, g]
            simp [List.getD_eq_getElem?_getD, hj]
          have hdg := foldl_append_getD_gate 0
            (fun (d : List ℕ) (gt : Gate) =>
              (gt.inputs.map (fun a => d.getD a 0)).foldr max 0 + (nonlin gt).toNat)
            C.gates (List.replicate W 0) j hj
          have hdw : ds.getD w 0 =
              (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat := by
            have h1 := hdg.1
            simp only [List.length_replicate] at h1
            rw [hwj]
            dsimp only [ds, depthList]
            rw [h1]
            congr 1
            congr 1
            refine List.map_congr_left (fun a ha => ?_)
            have halt : a < W + j := by
              have hr := hread j hj a
              rw [hgat] at hr
              exact hr ha
            have h2 := hdg.2 a (by simp; exact halt)
            exact h2
          rw [hw0] at hdw
          have hnl0 : nonlin g = false := by
            cases hn : nonlin g
            · rfl
            · rw [hn] at hdw; simp at hdw
          have hinputs0 : ∀ a ∈ g.inputs, ds.getD a 0 = 0 := by
            intro a ha
            have hle := le_foldr_max (fun a => ds.getD a 0) g.inputs a ha
            omega
          have hinputs_lt : ∀ a ∈ g.inputs, a < w := by
            intro a ha
            have hr := hread j hj a
            rw [hgat] at hr
            have := hr ha
            omega
          have hval_w : ∀ x y, val w x y =
              b2f (g.op.eval (g.inputs.map (fun a => (C.wires (oneEach x y)).getD a false))) := by
            intro x y
            dsimp only [val, Circuit.wires]
            have hwg := foldl_append_getD_gate false
              (fun (ws : List Bool) (gt : Gate) =>
                gt.op.eval (gt.inputs.map (fun a => ws.getD a false)))
              C.gates (oneEach x y) j hj
            have hlen : (oneEach x y).length = W := by simp [oneEach, W]
            have h1 := hwg.1
            rw [hlen] at h1
            rw [hwj, h1]
            congr 2
            refine List.map_congr_left (fun a ha => ?_)
            have halt : a < (oneEach x y).length + j := by
              rw [hlen]
              have hr := hread j hj a
              rw [hgat] at hr
              exact hr ha
            exact hwg.2 a halt
          have hlen_g : g.inputs.length ≤ 2 := hfan g (List.getElem_mem hj)
          rcases hgl : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
          · refine ⟨fun _ => b2f (g.op.eval []), fun _ => 0, fun x y => ?_⟩
            rw [hval_w x y, hgl]; simp
          · have ha_lt : a < w := hinputs_lt a (by rw [hgl]; simp)
            have ha0 : ds.getD a 0 = 0 := hinputs0 a (by rw [hgl]; simp)
            rcases ih a ha_lt ha0 with ⟨ra, ca, hra⟩
            rcases gate_affine_of_len1 g.op with ⟨c0, c1, haff⟩
            refine ⟨fun x => c0 + c1 * ra x, fun y => c1 * ca y, fun x y => ?_⟩
            rw [hval_w x y, hgl, List.map_cons, List.map_nil, haff]
            have := hra x y
            dsimp only [val] at this
            rw [this]; ring
          · have ha_lt : a < w := hinputs_lt a (by rw [hgl]; simp)
            have hb_lt : b < w := hinputs_lt b (by rw [hgl]; simp)
            have ha0 : ds.getD a 0 = 0 := hinputs0 a (by rw [hgl]; simp)
            have hb0 : ds.getD b 0 = 0 := hinputs0 b (by rw [hgl]; simp)
            rcases ih a ha_lt ha0 with ⟨ra, ca, hra⟩
            rcases ih b hb_lt hb0 with ⟨rb, cb, hrb⟩
            have hnl_op : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              dsimp only [nonlin] at hnl0
              rw [hgl] at hnl0
              simpa using hnl0
            rcases gate_affine_of_nonlin_false g.op hnl_op with ⟨c0, c1, c2, haff⟩
            refine ⟨fun x => c0 + c1 * ra x + c2 * rb x, fun y => c1 * ca y + c2 * cb y, fun x y => ?_⟩
            rw [hval_w x y, hgl, List.map_cons, List.map_cons, List.map_nil, haff]
            have h1 := hra x y
            have h2 := hrb x y
            dsimp only [val] at h1 h2
            rw [h1, h2]; ring
          · rw [hgl] at hlen_g; simp at hlen_g
        · refine ⟨fun _ => 0, fun _ => 0, fun x y => ?_⟩
          dsimp only [val]
          have hlen : (C.wires (oneEach x y)).length = W + C.gates.length := by
            dsimp only [Circuit.wires]
            rw [foldl_append_length]; simp [oneEach, W]
          have hnone : (C.wires (oneEach x y))[w]? = none :=
            List.getElem?_eq_none (by omega)
          rw [List.getD_eq_getElem?_getD, hnone]
          simp [b2f]
  let cOf : ℕ → (Fin m → F2) := fun w =>
    if h : ds.getD w 0 = 0 then Classical.choose (Classical.choose_spec (hsep w h)) else 0
  let rOf : ℕ → (Fin n → F2) := fun w =>
    if h : ds.getD w 0 = 0 then Classical.choose (hsep w h) else 0
  have hsep_spec : ∀ w, ds.getD w 0 = 0 → ∀ x y, val w x y = rOf w x + cOf w y := by
    intro w hw x y
    dsimp only [rOf, cOf]
    simp only [hw, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec (hsep w hw)) x y
  let nlIdx : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    ∃ hj : j < C.gates.length, nonlin (C.gates[j]) = true)
  have hnlIdx_card : nlIdx.card ≤ C.gates.countP nonlin := by
    have hcount : C.gates.countP nonlin =
        ((Finset.range C.gates.length).filter (fun j =>
          if hj : j < C.gates.length then nonlin (C.gates[j]) = true else False)).card := by
      have hgen : ∀ (l : List Gate), l.countP nonlin =
          ((Finset.range l.length).filter (fun j =>
            if hj : j < l.length then nonlin (l[j]) = true else False)).card := by
        intro l
        induction l with
        | nil => simp
        | cons g gs ih =>
          rw [List.countP_cons, ih]
          have hrange : Finset.range (gs.length + 1) =
              insert 0 ((Finset.range gs.length).image (· + 1)) := by
            ext k
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
            constructor
            · intro hk
              cases k with
              | zero => left; rfl
              | succ k => right; exact ⟨k, by omega, rfl⟩
            · rintro (rfl | ⟨k, hk, rfl⟩) <;> omega
          simp only [List.length_cons, hrange, Finset.filter_insert]
          have hnot0 : 0 ∉ ((Finset.range gs.length).image (· + 1)).filter
              (fun j => if hj : j < gs.length + 1 then nonlin ((g :: gs)[j]) = true else False) := by
            simp
          have hshift : (((Finset.range gs.length).image (· + 1)).filter
              (fun j => if hj : j < gs.length + 1 then nonlin ((g :: gs)[j]) = true else False)).card =
              ((Finset.range gs.length).filter
                (fun j => if hj : j < gs.length then nonlin (gs[j]) = true else False)).card := by
            refine Finset.card_bij (fun j _ => j - 1) ?_ ?_ ?_
            · intro j hj
              rcases Finset.mem_filter.mp hj with ⟨him, hcond⟩
              rcases Finset.mem_image.mp him with ⟨k, hk, rfl⟩
              have hklt : k < gs.length := Finset.mem_range.mp hk
              refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
              simp only [Nat.add_sub_cancel, hklt, ↓reduceDIte]
              simpa [hklt] using hcond
            · intro j1 h1 j2 h2 heq
              rcases Finset.mem_image.mp (Finset.mem_filter.mp h1).1 with ⟨k1, _, rfl⟩
              rcases Finset.mem_image.mp (Finset.mem_filter.mp h2).1 with ⟨k2, _, rfl⟩
              omega
            · intro k hk
              rcases Finset.mem_filter.mp hk with ⟨hklt, hcond⟩
              have hk' : k < gs.length := Finset.mem_range.mp hklt
              refine ⟨k + 1, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, hklt, rfl⟩, ?_⟩, by omega⟩
              simpa [hk'] using hcond
          cases hg : nonlin g
          · simp only [Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero, hg,
              Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact hshift.symm
          · simp only [Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero, hg, ↓reduceIte]
            rw [Finset.card_insert_of_notMem hnot0, hshift]
      exact hgen C.gates
    rw [hcount]
    refine Finset.card_le_card (fun j hj => ?_)
    rcases Finset.mem_filter.mp hj with ⟨hr, hlt, hnl⟩
    exact Finset.mem_filter.mpr ⟨hr, by simp [hlt, hnl]⟩
  let genSet : Finset (Fin m → F2) :=
    insert (fun _ : Fin m => (1 : F2))
      (nlIdx.biUnion (fun j =>
        if hj : j < C.gates.length then
          {cOf ((C.gates[j]).inputs.getD 0 0), cOf ((C.gates[j]).inputs.getD 1 0)}
        else ∅))
  let U : Submodule F2 (Fin m → F2) := Submodule.span F2 (genSet : Set (Fin m → F2))
  have hU_rank : Module.finrank F2 U ≤ 2 * C.gates.countP nonlin + 1 := by
    have h1 : Module.finrank F2 U ≤ genSet.card := by
      simpa [U] using finrank_span_le_card (R := F2) (s := (genSet : Set (Fin m → F2)))
    have h2 : genSet.card ≤ 1 + 2 * nlIdx.card := by
      dsimp only [genSet]
      refine (Finset.card_insert_le _ _).trans ?_
      have hbi : (nlIdx.biUnion (fun j =>
          if hj : j < C.gates.length then
            {cOf ((C.gates[j]).inputs.getD 0 0), cOf ((C.gates[j]).inputs.getD 1 0)}
          else ∅)).card ≤ 2 * nlIdx.card := by
        calc _ ≤ nlIdx.sum (fun j =>
              (if hj : j < C.gates.length then
                ({cOf ((C.gates[j]).inputs.getD 0 0), cOf ((C.gates[j]).inputs.getD 1 0)} : Finset (Fin m → F2))
              else ∅).card) := Finset.card_biUnion_le
          _ ≤ nlIdx.sum (fun _ => 2) := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              split_ifs
              · exact (Finset.card_insert_le _ _).trans (by simp)
              · simp
          _ = 2 * nlIdx.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    omega
  have hone_mem : (fun _ : Fin m => (1 : F2)) ∈ U :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hwire_mem : ∀ w : ℕ, ds.getD w 0 ≤ 1 →
      ∀ x : Fin n, (fun y : Fin m => val w x y + val w v y) ∈ U := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw1 x
      by_cases hw0 : ds.getD w 0 = 0
      · have heq : (fun y : Fin m => val w x y + val w v y) =
            (rOf w x + rOf w v) • (fun _ : Fin m => (1 : F2)) := by
          funext y
          rw [hsep_spec w hw0 x y, hsep_spec w hw0 v y]
          simp only [Pi.smul_apply, smul_eq_mul, mul_one]
          have h2 := f2_add_self (cOf w y)
          calc rOf w x + cOf w y + (rOf w v + cOf w y)
              = (rOf w x + rOf w v) + (cOf w y + cOf w y) := by ring
            _ = rOf w x + rOf w v := by rw [h2, add_zero]
        rw [heq]
        exact U.smul_mem _ hone_mem
      · have hgeW : W ≤ w := by
          by_contra hlt
          push Not at hlt
          have h0 : ds.getD w 0 = 0 := by
            dsimp only [ds, depthList]
            rw [foldl_append_getD_lt 0 _ C.gates (List.replicate W 0) w (by simp; exact hlt)]
            simp [List.getD_eq_getElem?_getD, hlt]
          exact hw0 h0
        have hltC : w < W + C.gates.length := by
          by_contra hge
          push Not at hge
          have h0 : ds.getD w 0 = 0 := by
            have hlen : (depthList W C).length = W + C.gates.length := by
              dsimp only [depthList]; rw [foldl_append_length]; simp
            have hnone : (depthList W C)[w]? = none := List.getElem?_eq_none (by omega)
            dsimp only [ds]
            rw [List.getD_eq_getElem?_getD, hnone]
            rfl
          exact hw0 h0
        let j := w - W
        have hj : j < C.gates.length := by omega
        have hwj : w = W + j := by omega
        let g := C.gates[j]
        have hgat : gateAt C j = g := by
          dsimp only [gateAt, g]; simp [List.getD_eq_getElem?_getD, hj]
        have hdg := foldl_append_getD_gate 0
          (fun (d : List ℕ) (gt : Gate) =>
            (gt.inputs.map (fun a => d.getD a 0)).foldr max 0 + (nonlin gt).toNat)
          C.gates (List.replicate W 0) j hj
        have hdw : ds.getD w 0 =
            (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat := by
          have h1 := hdg.1
          simp only [List.length_replicate] at h1
          rw [hwj]; dsimp only [ds, depthList]; rw [h1]
          congr 1; congr 1
          refine List.map_congr_left (fun a ha => ?_)
          have halt : a < W + j := by
            have hr := hread j hj a; rw [hgat] at hr; exact hr ha
          exact hdg.2 a (by simp; exact halt)
        have hinputs_lt : ∀ a ∈ g.inputs, a < w := by
          intro a ha
          have hr := hread j hj a; rw [hgat] at hr
          have := hr ha; omega
        have hval_w : ∀ x' y, val w x' y =
            b2f (g.op.eval (g.inputs.map (fun a => (C.wires (oneEach x' y)).getD a false))) := by
          intro x' y
          dsimp only [val, Circuit.wires]
          have hwg := foldl_append_getD_gate false
            (fun (ws : List Bool) (gt : Gate) =>
              gt.op.eval (gt.inputs.map (fun a => ws.getD a false)))
            C.gates (oneEach x' y) j hj
          have hlen : (oneEach x' y).length = W := by simp [oneEach, W]
          have h1 := hwg.1; rw [hlen] at h1; rw [hwj, h1]
          congr 2
          refine List.map_congr_left (fun a ha => ?_)
          have halt : a < (oneEach x' y).length + j := by
            rw [hlen]; have hr := hread j hj a; rw [hgat] at hr; exact hr ha
          exact hwg.2 a halt
        have hlen_g : g.inputs.length ≤ 2 := hfan g (List.getElem_mem hj)
        by_cases hnl : nonlin g = true
        · have hj_mem : j ∈ nlIdx :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, hnl⟩
          have hlen2 : g.inputs.length = 2 := by
            dsimp only [nonlin] at hnl
            have := (Bool.and_eq_true _ _).mp hnl
            exact beq_iff_eq.mp this.1
          rcases hgl : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
          · rw [hgl] at hlen2; simp at hlen2
          · rw [hgl] at hlen2; simp at hlen2
          · have ha0 : ds.getD a 0 = 0 := by
              have hle := le_foldr_max (fun z => ds.getD z 0) g.inputs a (by rw [hgl]; simp)
              rw [hnl, Bool.toNat_true] at hdw; omega
            have hb0 : ds.getD b 0 = 0 := by
              have hle := le_foldr_max (fun z => ds.getD z 0) g.inputs b (by rw [hgl]; simp)
              rw [hnl, Bool.toNat_true] at hdw; omega
            have hca_mem : cOf a ∈ U := by
              refine Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem ?_))
              refine Finset.mem_biUnion.mpr ⟨j, hj_mem, ?_⟩
              simp only [hj, ↓reduceDIte]
              have hget0 : (C.gates[j]).inputs.getD 0 0 = a := by change g.inputs.getD 0 0 = a; rw [hgl]; rfl
              rw [hget0]; simp
            have hcb_mem : cOf b ∈ U := by
              refine Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem ?_))
              refine Finset.mem_biUnion.mpr ⟨j, hj_mem, ?_⟩
              simp only [hj, ↓reduceDIte]
              have hget1 : (C.gates[j]).inputs.getD 1 0 = b := by change g.inputs.getD 1 0 = b; rw [hgl]; rfl
              rw [hget1]; simp
            rcases gate_quad_of_len2 g.op with ⟨c0, c1, c2, c3, hquad⟩
            have heq : (fun y : Fin m => val w x y + val w v y) =
                (c1 * (rOf a x + rOf a v) + c2 * (rOf b x + rOf b v) +
                  c3 * (rOf a x * rOf b x + rOf a v * rOf b v)) • (fun _ : Fin m => (1 : F2)) +
                (c3 * (rOf a x + rOf a v)) • cOf b +
                (c3 * (rOf b x + rOf b v)) • cOf a := by
              funext y
              rw [hval_w x y, hval_w v y, hgl]
              simp only [List.map_cons, List.map_nil]
              rw [hquad, hquad]
              have hax := hsep_spec a ha0 x y
              have hav := hsep_spec a ha0 v y
              have hbx := hsep_spec b hb0 x y
              have hbv := hsep_spec b hb0 v y
              dsimp only [val] at hax hav hbx hbv
              rw [hax, hav, hbx, hbv]
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
              have h2 : ∀ z : F2, z + z = 0 := f2_add_self
              have hkill : (c0 + c0) + (c1 * cOf a y + c1 * cOf a y) +
                  (c2 * cOf b y + c2 * cOf b y) +
                  (c3 * cOf a y * cOf b y + c3 * cOf a y * cOf b y) = 0 := by
                rw [h2 c0, h2 (c1 * cOf a y), h2 (c2 * cOf b y), h2 (c3 * cOf a y * cOf b y)]
                simp
              calc c0 + c1 * (rOf a x + cOf a y) + c2 * (rOf b x + cOf b y) +
                    c3 * (rOf a x + cOf a y) * (rOf b x + cOf b y) +
                    (c0 + c1 * (rOf a v + cOf a y) + c2 * (rOf b v + cOf b y) +
                    c3 * (rOf a v + cOf a y) * (rOf b v + cOf b y))
                  = (c1 * (rOf a x + rOf a v) + c2 * (rOf b x + rOf b v) +
                    c3 * (rOf a x * rOf b x + rOf a v * rOf b v)) +
                    c3 * (rOf a x + rOf a v) * cOf b y +
                    c3 * (rOf b x + rOf b v) * cOf a y +
                    ((c0 + c0) + (c1 * cOf a y + c1 * cOf a y) +
                    (c2 * cOf b y + c2 * cOf b y) +
                    (c3 * cOf a y * cOf b y + c3 * cOf a y * cOf b y)) := by ring
                _ = _ := by rw [hkill, add_zero]
            rw [heq]
            exact U.add_mem (U.add_mem (U.smul_mem _ hone_mem) (U.smul_mem _ hcb_mem)) (U.smul_mem _ hca_mem)
          · rw [hgl] at hlen2; simp at hlen2
        · have hnl0 : nonlin g = false := Bool.eq_false_iff.mpr hnl
          have hinputs1 : ∀ a ∈ g.inputs, ds.getD a 0 ≤ 1 := by
            intro a ha
            have hle := le_foldr_max (fun z => ds.getD z 0) g.inputs a ha
            omega
          rcases hgl : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
          · have heq : (fun y : Fin m => val w x y + val w v y) = 0 := by
              funext y; rw [hval_w x y, hval_w v y, hgl]; exact f2_add_self _
            rw [heq]; exact U.zero_mem
          · have ha_mem := ih a (hinputs_lt a (by rw [hgl]; simp)) (hinputs1 a (by rw [hgl]; simp)) x
            rcases gate_affine_of_len1 g.op with ⟨c0, c1, haff⟩
            have heq : (fun y : Fin m => val w x y + val w v y) =
                c1 • (fun y => val a x y + val a v y) := by
              funext y
              rw [hval_w x y, hval_w v y, hgl]
              simp only [List.map_cons, List.map_nil]
              rw [haff, haff]
              dsimp only [val, Pi.smul_apply, smul_eq_mul]
              have h2 := f2_add_self c0
              calc c0 + c1 * b2f ((C.wires (oneEach x y)).getD a false) +
                    (c0 + c1 * b2f ((C.wires (oneEach v y)).getD a false))
                  = (c0 + c0) + c1 * (b2f ((C.wires (oneEach x y)).getD a false) +
                    b2f ((C.wires (oneEach v y)).getD a false)) := by ring
                _ = _ := by rw [h2, zero_add]
            rw [heq]; exact U.smul_mem _ ha_mem
          · have ha_mem := ih a (hinputs_lt a (by rw [hgl]; simp)) (hinputs1 a (by rw [hgl]; simp)) x
            have hb_mem := ih b (hinputs_lt b (by rw [hgl]; simp)) (hinputs1 b (by rw [hgl]; simp)) x
            have hnl_op : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              dsimp only [nonlin] at hnl0; rw [hgl] at hnl0; simpa using hnl0
            rcases gate_affine_of_nonlin_false g.op hnl_op with ⟨c0, c1, c2, haff⟩
            have heq : (fun y : Fin m => val w x y + val w v y) =
                c1 • (fun y => val a x y + val a v y) + c2 • (fun y => val b x y + val b v y) := by
              funext y
              rw [hval_w x y, hval_w v y, hgl]
              simp only [List.map_cons, List.map_nil]
              rw [haff, haff]
              dsimp only [val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have h2 := f2_add_self c0
              calc c0 + c1 * b2f ((C.wires (oneEach x y)).getD a false) +
                    c2 * b2f ((C.wires (oneEach x y)).getD b false) +
                    (c0 + c1 * b2f ((C.wires (oneEach v y)).getD a false) +
                    c2 * b2f ((C.wires (oneEach v y)).getD b false))
                  = (c0 + c0) +
                    c1 * (b2f ((C.wires (oneEach x y)).getD a false) +
                      b2f ((C.wires (oneEach v y)).getD a false)) +
                    c2 * (b2f ((C.wires (oneEach x y)).getD b false) +
                      b2f ((C.wires (oneEach v y)).getD b false)) := by ring
                _ = _ := by rw [h2, zero_add]
            rw [heq]; exact U.add_mem (U.smul_mem _ ha_mem) (U.smul_mem _ hb_mem)
          · rw [hgl] at hlen_g; simp at hlen_g
  refine ⟨U, hU_rank, hone_mem, fun x => ?_⟩
  have h1 := hwire_mem C.output hdep x
  have heq : (fun y : Fin m => b2f (P x y) + b2f (P v y)) =
      (fun y : Fin m => val C.output x y + val C.output v y) := by
    funext y
    dsimp only [val]
    rw [← Circuit.eval, ← Circuit.eval, hrep x y, hrep v y]
  rwa [heq]

lemma main_proof :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
        xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
            (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depth := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      (C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)).getD C.output 0
    ∀ (n m : ℕ) (T : Fin n → Fin m → Bool),
      let dist := fun (H : Fin n → Fin m → Bool) (i j : Fin n) =>
        (Finset.univ.filter (fun c : Fin m => H i c ≠ H j c)).card % 8
      let size := fun (D : Fin n → Fin n → ℕ) (u : Fin n) =>
        let I := Option (Fin n)
        let G : Matrix I I (ZMod 4) := fun i j =>
          let x := i.getD u
          let y := j.getD u
          if i.isNone then (if j.isNone then (m : ZMod 4) else (D u y : ZMod 4))
          else if j.isNone then (D u x : ZMod 4)
          else ((((D u x + D u y + 8 - D x y) % 8 / 2 : ℕ)) : ZMod 4)
        (Finset.univ.image (fun x : I → ZMod 4 => G.mulVec x)).card
      (∀ (u v : Fin n) (rf : Fin n → Bool) (cf : Fin m → Bool),
        size (dist (fun i j => xor (rf i) (xor (T i j) (cf j)))) v = size (dist T) u) ∧
      ∀ (u : Fin n) (R : Finset (Fin n)) (S : Finset (Fin m)) (P : Fin n → Fin m → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ i ∉ R, ∀ j ∉ S, P i j = T i j) →
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
        PEqualNP.Represents.Represents P C → depth (n+m) C ≤ 1 →
        size (dist T) u ≤ 4^(2*C.gates.countP nonlinear + R.card + S.card + 1) := by
  intro nonlinear depth n m T dist size
  constructor
  · intro u v rf cf
    have h1 := image_card_changeRef (fun i j => xor (rf i) (xor (T i j) (cf j))) u v
    have h2 := image_card_rowFlip (fun i j => xor (T i j) (cf j)) u rf
    have h3 : distFn (fun i j => xor (T i j) (cf j)) = distFn T := dist_colFlip T cf
    change (Finset.univ.image (fun x : Option (Fin n) → F4 =>
        (gramMat m (distFn (fun i j => xor (rf i) (xor (T i j) (cf j)))) v).mulVec x)).card =
      (Finset.univ.image (fun x : Option (Fin n) → F4 =>
        (gramMat m (distFn T) u).mulVec x)).card
    rw [h1, h2, h3]
  · intro u R S P C hagree hfan hread hrep hdep
    have hred : ∀ (w : Fin n) (i : Option (Fin n)) (c : Fin m),
        red42 (liftM T w i c) = liftM2 T w i c := by
      intro w i c
      cases i with
      | none =>
        dsimp only [liftM, liftM2]
        decide
      | some x =>
        dsimp only [liftM, liftM2]
        split_ifs <;> decide
    by_cases hRuniv : R = Finset.univ
    · have hcardR : R.card = n := by rw [hRuniv]; simp
      have hbound : (Finset.univ.image (fun x : Option (Fin n) → F4 =>
          (gramMat m (distFn T) u).mulVec x)).card ≤
          4 ^ Module.finrank F2 (LinearMap.range (liftM2 T u).transpose.mulVecLin) := by
        rw [gramMat_eq_mul_transpose T u]
        exact image_card_gram_le_pow4 (liftM T u) (liftM2 T u) (hred u)
      have hrk : Module.finrank F2 (LinearMap.range (liftM2 T u).transpose.mulVecLin) ≤ n + 1 := by
        calc Module.finrank F2 (LinearMap.range (liftM2 T u).transpose.mulVecLin)
            ≤ Module.finrank F2 (Option (Fin n) → F2) := LinearMap.finrank_range_le _
          _ = n + 1 := by simp [Fintype.card_option, Fintype.card_fin]
      exact hbound.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · have hex_v : ∃ v : Fin n, v ∉ R := by
        by_contra hall
        push Not at hall
        apply hRuniv
        ext i; simp [hall i]
      rcases hex_v with ⟨v, hvR⟩
      have hchg := image_card_changeRef T v u
      change (Finset.univ.image (fun x : Option (Fin n) → F4 =>
          (gramMat m (distFn T) u).mulVec x)).card ≤ _
      rw [hchg]
      have hbound : (Finset.univ.image (fun x : Option (Fin n) → F4 =>
          (gramMat m (distFn T) v).mulVec x)).card ≤
          4 ^ Module.finrank F2 (LinearMap.range (liftM2 T v).transpose.mulVecLin) := by
        rw [gramMat_eq_mul_transpose T v]
        exact image_card_gram_le_pow4 (liftM T v) (liftM2 T v) (hred v)
      rcases finrank_anchored_circuit_le P C v hfan hread hrep hdep with ⟨U, hUrk, honeU, hPU⟩
      let VS : Submodule F2 (Fin m → F2) :=
        Submodule.span F2 ((S.image (fun y : Fin m => Pi.single y (1 : F2))) : Set (Fin m → F2))
      let VR : Submodule F2 (Fin m → F2) :=
        Submodule.span F2 ((R.image (fun x : Fin n => liftM2 T v (some x))) : Set (Fin m → F2))
      let Ubig : Submodule F2 (Fin m → F2) := U ⊔ VS ⊔ VR
      have hrange_le : LinearMap.range (liftM2 T v).transpose.mulVecLin ≤ Ubig := by
        rintro z ⟨w, rfl⟩
        have hvec : (liftM2 T v).transpose.mulVecLin w =
            ∑ i : Option (Fin n), w i • liftM2 T v i := by
          funext y
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
        rw [hvec]
        refine Ubig.sum_mem (fun i _ => Ubig.smul_mem (w i) ?_)
        cases i with
        | none =>
          exact Submodule.mem_sup_left (Submodule.mem_sup_left honeU)
        | some x =>
          by_cases hxR : x ∈ R
          · exact Submodule.mem_sup_right
              (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hxR, rfl⟩)))
          · let pvec : Fin m → F2 := fun y => b2f (P x y) + b2f (P v y)
            let dvec : Fin m → F2 := fun y => liftM2 T v (some x) y - pvec y
            have hdeq : liftM2 T v (some x) = pvec + dvec := by
              funext y; dsimp only [dvec]; simp only [Pi.add_apply]; ring
            have hd_in_VS : dvec ∈ VS := by
              have hsum : dvec = ∑ y ∈ S, dvec y • Pi.single y (1 : F2) := by
                funext c
                rw [Finset.sum_apply]
                by_cases hcS : c ∈ S
                · rw [Finset.sum_eq_single c]
                  · simp
                  · intro y _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
                  · intro h; exact (h hcS).elim
                · rw [Finset.sum_eq_zero (fun y hy => by
                    have hne : c ≠ y := fun h => hcS (h ▸ hy)
                    simp [Pi.single_eq_of_ne hne])]
                  dsimp only [dvec, pvec, liftM2]
                  have h1 : P x c = T x c := hagree x hxR c hcS
                  have h2 : P v c = T v c := hagree v hvR c hcS
                  rw [h1, h2]
                  cases T x c <;> cases T v c <;> decide
              rw [hsum]
              exact VS.sum_mem (fun y hy =>
                VS.smul_mem _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y, hy, rfl⟩))))
            rw [hdeq]
            exact Ubig.add_mem
              (Submodule.mem_sup_left (Submodule.mem_sup_left (hPU x)))
              (Submodule.mem_sup_left (Submodule.mem_sup_right hd_in_VS))
      have hVS_rk : Module.finrank F2 VS ≤ S.card := by
        have h1 : Module.finrank F2 VS ≤ (S.image (fun y : Fin m => Pi.single y (1 : F2))).card := by
          simpa [VS] using finrank_span_le_card (R := F2) (s := ((S.image (fun y : Fin m => Pi.single y (1 : F2))) : Set (Fin m → F2)))
        exact h1.trans Finset.card_image_le
      have hVR_rk : Module.finrank F2 VR ≤ R.card := by
        have h1 : Module.finrank F2 VR ≤ (R.image (fun x : Fin n => liftM2 T v (some x))).card := by
          simpa [VR] using finrank_span_le_card (R := F2) (s := ((R.image (fun x : Fin n => liftM2 T v (some x))) : Set (Fin m → F2)))
        exact h1.trans Finset.card_image_le
      have hUbig_rk : Module.finrank F2 Ubig ≤ 2 * C.gates.countP nonlin + R.card + S.card + 1 := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ VS) VR
        have h2 := Submodule.finrank_sup_add_finrank_inf_eq U VS
        dsimp only [Ubig]
        omega
      have hrk_le : Module.finrank F2 (LinearMap.range (liftM2 T v).transpose.mulVecLin) ≤
          2 * C.gates.countP nonlinear + R.card + S.card + 1 :=
        (Submodule.finrank_mono hrange_le).trans hUbig_rk
      exact hbound.trans (Nat.pow_le_pow_right (by decide) hrk_le)

end PEqualNP.Outside.L_meta_32578_aux

theorem PEqualNP.Outside.L_meta_32578 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)).getD C.output 0
∀ (n m : ℕ) (T : Fin n → Fin m → Bool),
  let dist := fun (H : Fin n → Fin m → Bool) (i j : Fin n) =>
    (Finset.univ.filter (fun c : Fin m => H i c ≠ H j c)).card % 8
  let size := fun (D : Fin n → Fin n → ℕ) (u : Fin n) =>
    let I := Option (Fin n)
    let G : Matrix I I (ZMod 4) := fun i j =>
      let x := i.getD u
      let y := j.getD u
      if i.isNone then (if j.isNone then (m : ZMod 4) else (D u y : ZMod 4))
      else if j.isNone then (D u x : ZMod 4)
      else ((((D u x + D u y + 8 - D x y) % 8 / 2 : ℕ)) : ZMod 4)
    (Finset.univ.image (fun x : I → ZMod 4 => G.mulVec x)).card
  (∀ (u v : Fin n) (rf : Fin n → Bool) (cf : Fin m → Bool),
    size (dist (fun i j => xor (rf i) (xor (T i j) (cf j)))) v = size (dist T) u) ∧
  ∀ (u : Fin n) (R : Finset (Fin n)) (S : Finset (Fin m)) (P : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ i ∉ R, ∀ j ∉ S, P i j = T i j) →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
    PEqualNP.Represents.Represents P C → depth (n+m) C ≤ 1 →
    size (dist T) u ≤ 4^(2*C.gates.countP nonlinear + R.card + S.card + 1) := by
  exact PEqualNP.Outside.L_meta_32578_aux.main_proof
