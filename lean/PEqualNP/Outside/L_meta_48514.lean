import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48514

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fullMask : Nat := 0xffffffffffffffff

abbrev Masked (mask w : Nat) : Prop := w &&& mask = w

def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c

theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all

theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all

def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)

theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]

theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]

theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]

theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]

theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w

theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]

theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne

theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]

def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))

theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _

theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩

theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp

theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]

theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h

theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1

def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank

def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b

def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs

def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length

theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)

theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩

theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)

theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2

def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S

theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _

theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega

inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S

theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0

theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega

theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1

theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩

theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))

def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w

theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl

def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k

theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]

def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws

theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢

theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha

theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq

def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)

theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]

theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega

theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit

def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws

theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]

def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w

theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l

def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws

def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l

theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]

theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩

def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l

theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩

theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2

theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]

def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits

theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)

theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)

theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩

def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)

theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i

theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi

theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2

theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]

theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega

abbrev ReplayState := Nat × List Nat × List (Nat × Nat × Nat)

def RefTransfers (mask goal count : Nat) (states : Nat → Option ReplayState)
    (reference : Nat → Nat → ReplayState → Bool) : Prop :=
  ∀ parent token current, reference parent token current = true →
    ∃ dest saved, dest < count ∧ states dest = some saved ∧ saved.1 = current.1 ∧
      ∀ k, LiveBin mask goal k current.2.1.toFinset → LiveBin mask goal k saved.2.1.toFinset

theorem plainRefTransfers (mask goal count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRef count states links) := by
  intro parent token current h
  unfold dagRef at h
  cases he : links parent token with
  | none => simp [he] at h
  | some dest =>
    simp only [he, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hlt, hmatch⟩ := h
    cases hs : states dest with
    | none => simp [hs] at hmatch
    | some saved =>
      simp only [hs, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hmatch
      exact ⟨dest, saved, hlt, hs, hmatch.1, fun _ hLive => hmatch.2 ▸ hLive⟩

def dagCheckNodeWith (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool)
    (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (reference (i + 1)) st

theorem dagAllNodesWith {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal bounds
      (dagTrace mask stock fuel forest) reference i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeWith at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr2, hfEq, hMove⟩ :=
              hrefs (i + 1) (makeToken a b op keep) _ href
            have hbelow : rem - 1 < cap := by omega
            exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hMove k' hlive')

theorem lowerDagWith {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (reference 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal bounds
      (dagTrace mask stock fuel forest) reference i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · obtain ⟨dest, saved, hdest, htr, hfEq, hMove⟩ := hrefs 0 tok _ href
    exact dagAllNodesWith hrefs hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k
      (by omega) (hMove k hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) :=
  lowerDagWith (plainRefTransfers mask goal count (dagTrace mask stock fuel forest) links)
    hgm hgnz hcs snd hknown hsub hroots hnodes

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k

def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide

theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]

theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]

def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)

theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)

theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i

theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl

def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1

theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]

def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)

theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl

def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)

theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws

theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l

theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl

def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop

theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl

def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits

theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl

def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)

theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl

def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i

theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl

def dagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Bool.rec
    (Bool.rec true
      (knownClosesF bounds state)
      (dagPartF ws goal (Nat.xor mask goal)))
    true (Nat.blt (Nat.add fuel 1) (lenN ws))

theorem dagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagLocalF mask goal bounds state = dagLocal mask goal bounds state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagLocalF dagLocal; dsimp only
  rw [lenN_eq, dagPartF_eq, knownClosesF_eq hgoals]
  cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;> rfl

def dagRefF (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Bool.rec false
      (match states dest with
       | none => false
       | some saved => Bool.rec false (eqListN saved.2.1 state.2.1) (Nat.beq saved.1 state.1))
      (Nat.blt dest count)

theorem dagRefF_eq (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagRefF count states links parent token state = dagRef count states links parent token state := by
  unfold dagRefF dagRef
  cases links parent token with
  | none => rfl
  | some dest =>
    dsimp only
    cases Nat.blt dest count
    · rfl
    · dsimp only
      cases states dest with
      | none => rfl
      | some saved =>
        dsimp only
        rw [eqListN_eq]; cases Nat.beq saved.1 state.1 <;> rfl

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl

def dagCheckChildrenF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (treeBlockF 0 n (fun a =>
          let x := getDN ws a
          treeBlockF (Nat.add a 1) n (fun b =>
            let y := getDN ws b
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          Bool.rec (dagLocalF mask goal bounds ch) true (ref tok ch)))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        congr 1; funext a
        simp only [getDN_eq]
        congr 1; funext b
        congr 1; funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            congr 1; funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq, dagLocalF_eq hgoals]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals cases ref (makeToken a b op keep) _ <;> cases dagLocal mask goal bounds _ <;> rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (dagRefF count states links (Nat.add i 1)) st

theorem dagCheckNodeF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) :
    dagCheckNodeF mask goal bounds count states links i = dagCheckNode mask goal bounds count states links i := by
  unfold dagCheckNodeF dagCheckNode
  cases states i with
  | none => rfl
  | some st =>
    have href : dagRefF count states links (Nat.add i 1) = dagRef count states links (i + 1) := by
      funext tok s; exact dagRefF_eq count states links (i + 1) tok s
    rw [href]; exact dagCheckChildrenF_eq hgoals _ st

def dagCheckRootsF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlockF 0 (Nat.shiftLeft 1 (lenN stock)) (fun token =>
    forceWs (subsetWordsF stock token) (fun ws =>
      let st := (fuel, ws, [])
      Bool.rec (dagLocalF mask goal bounds st) true (ref token st)))

theorem dagCheckRootsF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) :
    dagCheckRootsF mask goal bounds ref stock fuel = dagCheckRoots mask goal bounds ref stock fuel := by
  unfold dagCheckRootsF dagCheckRoots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow, treeBlockF_eq]
  congr 1; funext tok
  simp only [subsetWordsF_eq, forceWs_eq, dagLocalF_eq hgoals]
  cases ref tok (fuel, subsetWords stock tok, []) <;> cases dagLocal mask goal bounds (fuel, subsetWords stock tok, []) <;> rfl

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksF (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpackF index idxW parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    let w := Nat.add tokBits destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := unpackF data w mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

theorem lowerDagF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal bounds count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq hgoals] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

theorem certBlock {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true :=
  fun _ hi₁ hi₂ => treeBlockF_at h hi₁ hi₂

theorem joinChecks {lo mid hi : Nat} {f : Nat → Bool}
    (left : ∀ i, lo ≤ i → i < mid → f i = true)
    (right : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i h₁ h₂
  by_cases hl : i < mid
  · exact left i h₁ hl
  · exact right i (Nat.le_of_not_gt hl) h₂

def selectRows (w : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => 2 * selectRows w ps + (w.testBit p).toNat

theorem selectRows_testBit (w : Nat) (rows : List Nat) (i : Nat) :
    (selectRows w rows).testBit i = (rows[i]?).any w.testBit := by
  induction rows generalizing i with
  | nil => simp [selectRows]
  | cons p ps ih =>
    cases i with
    | zero =>
      simp only [selectRows, Nat.testBit_zero, List.getElem?_cons_zero, Option.any_some]
      cases w.testBit p
      · change decide ((2 * selectRows w ps + 0) % 2 = 1) = false
        simp
      · change decide ((2 * selectRows w ps + 1) % 2 = 1) = true
        have ht : (2 * selectRows w ps + 1) % 2 = 1 := by omega
        simp [ht]
    | succ i =>
      simp only [selectRows, Nat.testBit_succ, List.getElem?_cons_succ]
      have hd : (2 * selectRows w ps + (w.testBit p).toNat) / 2 = selectRows w ps := by
        cases w.testBit p
        · change (2 * selectRows w ps + 0) / 2 = selectRows w ps
          omega
        · change (2 * selectRows w ps + 1) / 2 = selectRows w ps
          omega
      rw [hd, ih]

theorem selectRows_zero (rows : List Nat) : selectRows 0 rows = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [selectRows_testBit, Nat.zero_testBit]
  cases rows[i]? <;> simp [Nat.zero_testBit]

theorem selectRows_and (rows : List Nat) (x y : Nat) :
    selectRows (x &&& y) rows = selectRows x rows &&& selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_and]

theorem selectRows_or (rows : List Nat) (x y : Nat) :
    selectRows (x ||| y) rows = selectRows x rows ||| selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_or]

theorem selectRows_xor (rows : List Nat) (x y : Nat) :
    selectRows (x ^^^ y) rows = selectRows x rows ^^^ selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_xor]

def rowProjection (rows : List Nat) (cut w : Nat) := canon cut (selectRows w rows)

theorem rowProjection_zero (rows : List Nat) (cut : Nat) :
    rowProjection rows cut 0 = 0 := by
  simp [rowProjection, selectRows_zero, canon_zero]

theorem rowProjection_canon {rows : List Nat} {mask cut : Nat}
    (hm : selectRows mask rows = cut) (w : Nat) :
    rowProjection rows cut (canon mask w) = rowProjection rows cut w := by
  have hp : rowProjection rows cut (w &&& mask) = rowProjection rows cut w := by
    simp only [rowProjection, selectRows_and, hm, canon_land]
  rcases canon_cases mask w with ⟨he, h0 | h1⟩ | ⟨_, h0 | h1⟩
  · rw [he, rowProjection_zero, ← hp, h0, rowProjection_zero]
  · rw [he, rowProjection_zero, ← hp, h1]
    simp [rowProjection, hm, canon_self]
  · rw [h0, hp]
  · rw [h1, ← hp]
    simp only [rowProjection, selectRows_xor, hm, canon_xor_mask]

theorem rowProjection_op {rows : List Nat} {mask cut : Nat}
    (hm : selectRows mask rows = cut) (op a b : Nat) :
    rowProjection rows cut (binOp mask op a b) =
      binOp cut op (selectRows a rows) (selectRows b rows) := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp only [bsel_true, bsel_false, rowProjection_canon hm] <;>
    simp only [rowProjection, selectRows_and, selectRows_or, selectRows_xor, hm]

theorem rowProjection_avail {rows : List Nat} {mask cut : Nat} {big small : List Nat}
    (hm : selectRows mask rows = cut)
    (sub : ∀ x, Avail big x → Avail small (rowProjection rows cut x)) {y : Nat}
    (gate : GateBin mask big y) : GateBin cut small (rowProjection rows cut y) := by
  obtain ⟨a, b, op, _, ha, hb, rfl⟩ := gate
  have ea := sub a ha
  have eb := sub b hb
  have ca : canon cut (rowProjection rows cut a) = rowProjection rows cut a :=
    canon_idem _ _
  have cb : canon cut (rowProjection rows cut b) = rowProjection rows cut b :=
    canon_idem _ _
  have eq := rowProjection_op hm op a b
  have hs := canon_sub_binOp (op := op) (a := selectRows a rows)
    (b := selectRows b rows) (masked_self cut)
  rw [binOp_canon, ← eq] at hs
  change _ = 0 ∨ _ = rowProjection rows cut a ∨ _ = rowProjection rows cut b ∨ _ at hs
  rcases hs with h | h | h | ⟨op', hop', h⟩
  · exact ⟨0, 0, 0, by decide, Or.inl rfl, Or.inl rfl, by
      rw [h]; simp [binOp, bsel, canon_zero]⟩
  · exact ⟨_, _, 0, by decide, ea, ea, by rw [h]; simpa [binOp, bsel] using ca.symm⟩
  · exact ⟨_, _, 0, by decide, eb, eb, by rw [h]; simpa [binOp, bsel] using cb.symm⟩
  · exact ⟨_, _, op', hop', ea, eb, h⟩

theorem rowProjection_builds {rows : List Nat} {mask cut : Nat} {big small : List Nat}
    (hm : selectRows mask rows = cut)
    (sub : ∀ x, Avail big x → Avail small (rowProjection rows cut x))
    {vs : List Nat} (h : BuildsBin mask big vs) :
    BuildsBin cut small (vs.map (rowProjection rows cut)) := by
  induction vs generalizing big small with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨rowProjection_avail hm sub h.1, ih ?_ h.2⟩
    intro y hy
    rcases hy with hz | hmem
    · exact Or.inl (by rw [hz, rowProjection_zero])
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inr List.mem_cons_self
      · exact avail_weaken (fun z hz => List.mem_cons_of_mem _ hz) (sub y (Or.inr hmem))

theorem lowerByRows {mask cut goal smallGoal n : Nat} {big small : List Nat}
    (rows : List Nat) (hm : selectRows mask rows = cut)
    (hs : ∀ w ∈ big, Avail small (rowProjection rows cut w))
    (hg : rowProjection rows cut goal = smallGoal)
    (cert : LowerBin cut small smallGoal n) : LowerBin mask big goal n := by
  intro vs hv ha
  have sub (w : Nat) (hw : Avail big w) : Avail small (rowProjection rows cut w) := by
    rcases hw with rfl | hw
    · exact Or.inl (rowProjection_zero rows cut)
    · exact hs w hw
  have hv' := rowProjection_builds hm sub hv
  have ha' : Avail (vs.map (rowProjection rows cut) ++ small) smallGoal := by
    rw [← hg]
    rcases ha with rfl | ha
    · exact Or.inl (rowProjection_zero rows cut)
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem ha))
      · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (hs _ ha)
  simpa only [List.length_map] using cert _ hv' ha'

def swapIndex (i : Nat) : Nat :=
  if i < 64 then if i.testBit 3 == i.testBit 4 then i else i ^^^ 24 else i

def swapWord (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xff0000ffff0000ff)) |||
    (((w &&& 0x0000ff000000ff00) <<< 8) ||| ((w &&& 0x00ff000000ff0000) >>> 8))

theorem swapIndex_inv (i : Nat) : swapIndex (swapIndex i) = i := by
  by_cases hi : i < 64
  · interval_cases i <;> decide
  · simp [swapIndex, hi]

theorem swapWord_bit (w i : Nat) : (swapWord w).testBit i = w.testBit (swapIndex i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [swapWord, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [swapIndex, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have h8 : 8 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xff0000ffff0000ff : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xff0000ffff0000ff < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0x0000ff000000ff00 : Nat).testBit (i - 8) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x0000ff000000ff00 < 2 ^ 56)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0x00ff000000ff0000 : Nat).testBit (8 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x00ff000000ff0000 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [swapWord, swapIndex, hi, h64, h8, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

theorem swapWord_inv (w : Nat) : swapWord (swapWord w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, swapIndex_inv]

theorem swapWord_injective : Function.Injective swapWord :=
  fun _ _ h => by simpa only [swapWord_inv] using congrArg swapWord h

def swap23Index (i : Nat) : Nat :=
  if i < 64 then if i.testBit 2 == i.testBit 3 then i else i ^^^ 12 else i

def swap23Word (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xf00ff00ff00ff00f)) |||
    (((w &&& 0x00f000f000f000f0) <<< 4) ||| ((w &&& 0x0f000f000f000f00) >>> 4))

theorem swap23Index_inv (i : Nat) : swap23Index (swap23Index i) = i := by
  by_cases hi : i < 64
  · interval_cases i <;> decide
  · simp [swap23Index, hi]

theorem swap23Word_bit (w i : Nat) : (swap23Word w).testBit i = w.testBit (swap23Index i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [swap23Word, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [swap23Index, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have h4 : 4 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xf00ff00ff00ff00f : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xf00ff00ff00ff00f < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0x00f000f000f000f0 : Nat).testBit (i - 4) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x00f000f000f000f0 < 2 ^ 60)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0x0f000f000f000f00 : Nat).testBit (4 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x0f000f000f000f00 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [swap23Word, swap23Index, hi, h64, h4, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

theorem swap23Word_inv (w : Nat) : swap23Word (swap23Word w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swap23Word_bit, swap23Index_inv]

theorem swap23Word_injective : Function.Injective swap23Word :=
  fun _ _ h => by simpa only [swap23Word_inv] using congrArg swap23Word h

structure RowTransform where
  word : Nat → Nat
  slot : Nat → Nat
  bit_spec : ∀ w i, (word w).testBit i = w.testBit (slot i)
  word_injective : Function.Injective word

def composeRows (outer inner : RowTransform) : RowTransform where
  word := outer.word ∘ inner.word
  slot := inner.slot ∘ outer.slot
  bit_spec := by intro w i; simp only [Function.comp_apply, outer.bit_spec, inner.bit_spec]
  word_injective := outer.word_injective.comp inner.word_injective

def firstRowSwap : RowTransform :=
  ⟨swap23Word, swap23Index, swap23Word_bit, swap23Word_injective⟩

def lastRowSwap : RowTransform :=
  ⟨swapWord, swapIndex, swapWord_bit, swapWord_injective⟩

def chooseRows (tag : Nat) : RowTransform :=
  match tag with
  | 1 => firstRowSwap
  | 2 => composeRows firstRowSwap (composeRows lastRowSwap firstRowSwap)
  | 3 => lastRowSwap
  | 4 => composeRows firstRowSwap lastRowSwap
  | 5 => composeRows lastRowSwap firstRowSwap
  | _ => ⟨id, id, by intros; rfl, Function.injective_id⟩

def moveWord (tag word : Nat) : Nat := (chooseRows tag).word word

def moveSlot (tag slot : Nat) : Nat := (chooseRows tag).slot slot

theorem moveWord_bit (tag w i : Nat) : (moveWord tag w).testBit i = w.testBit (moveSlot tag i) :=
  (chooseRows tag).bit_spec w i

theorem moveWord_injective (tag : Nat) : Function.Injective (moveWord tag) :=
  (chooseRows tag).word_injective

theorem moveWord_and (tag x y : Nat) :
    moveWord tag (x &&& y) = moveWord tag x &&& moveWord tag y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.testBit_and]

theorem moveWord_or (tag x y : Nat) :
    moveWord tag (x ||| y) = moveWord tag x ||| moveWord tag y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.testBit_or]

theorem moveWord_xor (tag x y : Nat) :
    moveWord tag (x ^^^ y) = moveWord tag x ^^^ moveWord tag y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.testBit_xor]

theorem moveWord_zero (tag : Nat) : moveWord tag 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.zero_testBit]

theorem canonByTopBit {mask top : Nat} (hp : mask = 2 ^ (top + 1) - 1) (w : Nat) :
    canon mask w =
      if (w &&& mask).testBit top then mask ^^^ (w &&& mask) else w &&& mask := by
  unfold canon; dsimp only
  set v := w &&& mask
  have hhigh (j : Nat) (hj : top < j) :
      v.testBit j = (mask ^^^ v).testBit j := by
    have hj' : ¬ j < top + 1 := by omega
    have hb : mask.testBit j = false := by
      rw [hp, Nat.testBit_two_pow_sub_one]
      simp [hj']
    simp [Nat.testBit_xor, hb]
  have hone : mask.testBit top = true := by
    rw [hp, Nat.testBit_two_pow_sub_one]
    simp
  by_cases hz : v = 0
  · rw [hz]
    simp [bsel]
  by_cases hf : v = mask
  · rw [hf]
    simp [bsel, hone]
  rw [beq_false_ne hz, beq_false_ne hf]
  simp only [Bool.or_false, bsel_false]
  cases hbit : v.testBit top
  · have hv : (mask ^^^ v).testBit top = true := by
      simp [Nat.testBit_xor, hone, hbit]
    have hlt := Nat.lt_of_testBit top hbit hv hhigh
    have hcheck : Nat.blt v (mask ^^^ v) = true := by simpa only [Nat.blt_eq] using hlt
    simp [hcheck, bsel]
  · have hv : (mask ^^^ v).testBit top = false := by
      simp [Nat.testBit_xor, hone, hbit]
    have hlt := Nat.lt_of_testBit top hv hbit (fun j hj => (hhigh j hj).symm)
    have hcheck : Nat.blt v (mask ^^^ v) = false := by
      cases hh : Nat.blt v (mask ^^^ v)
      · rfl
      · rw [Nat.blt_eq] at hh; omega
    simp [hcheck, bsel]

theorem moveWord_canon {mask top : Nat} {tag : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : moveWord tag mask = mask) (ht : moveSlot tag top = top) (w : Nat) :
    moveWord tag (canon mask w) = canon mask (moveWord tag w) := by
  rw [canonByTopBit hp, canonByTopBit hp]
  have h : ((moveWord tag w) &&& mask).testBit top = (w &&& mask).testBit top := by
    rw [← hm, ← moveWord_and, moveWord_bit, ht, hm]
  rw [h]
  by_cases htop : (w &&& mask).testBit top = true <;>
    simp [htop, moveWord_xor, moveWord_and, hm]

theorem moveWord_gate {mask top : Nat} {tag : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : moveWord tag mask = mask) (ht : moveSlot tag top = top) (op a b : Nat) :
    moveWord tag (binOp mask op a b) = binOp mask op (moveWord tag a) (moveWord tag b) := by
  unfold binOp
  simp only [bsel]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp [moveWord_canon hp hm ht, moveWord_and, moveWord_or, moveWord_xor, hm]

theorem moveWord_drop (tag : Nat) (keep : Bool) (w : Nat) (S : Finset Nat) :
    (dropIf keep w S).image (moveWord tag) = dropIf keep (moveWord tag w) (S.image (moveWord tag)) := by
  cases keep <;> simp [dropIf, Finset.image_erase (moveWord_injective tag)]

theorem moveLiveBin {mask top goal fuel tag : Nat} {S : Finset Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hm : moveWord tag mask = mask) (ht : moveSlot tag top = top)
    (g : moveWord tag goal = goal)
    (h : LiveBin mask goal fuel S) : LiveBin mask goal fuel (S.image (moveWord tag)) := by
  induction h with
  | done => simpa only [Finset.image_singleton, g] using (LiveBin.done (mask := mask) (goal := goal))
  | @step k T a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    refine LiveBin.step (a := moveWord tag a) (b := moveWord tag b) (op := op)
      (Finset.mem_image_of_mem (moveWord tag) ha) (Finset.mem_image_of_mem (moveWord tag) hb)
      ((moveWord_injective tag).ne hab) ?_ ?_ hop ?_ ?_ keepA keepB ?_
    · intro h; exact ha0 (moveWord_injective tag (h.trans (moveWord_zero tag).symm))
    · intro h; exact hb0 (moveWord_injective tag (h.trans (moveWord_zero tag).symm))
    · rw [← moveWord_gate hp hm ht]
      intro h; exact hz (moveWord_injective tag (h.trans (moveWord_zero tag).symm))
    · rw [← moveWord_gate hp hm ht]
      intro h
      obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp h
      exact hf ((moveWord_injective tag eq) ▸ hx)
    · simpa only [Finset.image_insert, moveWord_drop, moveWord_gate hp hm ht] using ih

def moveBankF (tag : Nat) (saved current : List Nat) : Bool :=
  let mapped := current.map (moveWord tag)
  Bool.rec false (allN (fun w => memN w mapped) saved)
    (allN (fun w => memN w saved) mapped)

theorem moveBank_image {tag : Nat} {saved current : List Nat} (h : moveBankF tag saved current = true) :
    current.toFinset.image (moveWord tag) = saved.toFinset := by
  let mapped := current.map (moveWord tag)
  change Bool.rec false (allN (fun w => memN w mapped) saved)
    (allN (fun w => memN w saved) mapped) = true at h
  have hh : (allN (fun w => memN w saved) mapped) = true ∧
      (allN (fun w => memN w mapped) saved) = true := by
    cases hc : allN (fun w => memN w saved) mapped <;> rw [hc] at h
    · contradiction
    · exact ⟨rfl, h⟩
  simp only [allN_eq, List.all_eq_true, memN_eq, List.contains_iff_mem] at hh
  ext w; constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (hh.1 _ (List.mem_map.mpr ⟨v,List.mem_toFinset.mp hv,rfl⟩))
  · intro hw
    obtain ⟨v, hv, he⟩ := List.mem_map.mp (hh.2 _ (List.mem_toFinset.mp hw))
    exact Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,he⟩

def allowedMove (mask goal top tag : Nat) : Bool :=
  Nat.beq (moveWord tag mask) mask && (Nat.beq (moveWord tag goal) goal && Nat.beq (moveSlot tag top) top)

def dagRefPermF (mask goal top count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) (parent token : Nat) (current : ReplayState) : Bool :=
  match links parent token with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code 3
    let tag := Nat.land code 7
    Bool.rec false
      (match states dest with
       | none => false
       | some saved =>
         Bool.rec false
           (Bool.rec
             (Bool.rec false (moveBankF tag saved.2.1 current.2.1) (allowedMove mask goal top tag))
             (eqListN saved.2.1 current.2.1) (Nat.beq tag 0))
           (Nat.beq saved.1 current.1))
      (Nat.blt dest count)

theorem permRefTransfers {mask top goal count : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (states : Nat → Option ReplayState) (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRefPermF mask goal top count states links) := by
  intro parent token current h
  unfold dagRefPermF at h
  cases he : links parent token with
  | none => rw [he] at h; contradiction
  | some code =>
    rw [he] at h
    let dest := Nat.shiftRight code 3
    let tag := Nat.land code 7
    change Bool.rec false _ (Nat.blt dest count) = true at h
    cases hb : Nat.blt dest count
    · rw [hb] at h; contradiction
    · rw [hb] at h
      have hlt : dest < count := by simpa only [Nat.blt_eq] using hb
      cases hs : states dest with
      | none =>
        change (match states dest with | none => false | some _ => _) = true at h
        rw [hs] at h
        contradiction
      | some saved =>
        change (match states dest with | none => false | some _ => _) = true at h
        rw [hs] at h
        change Bool.rec false _ (Nat.beq saved.1 current.1) = true at h
        cases hf : Nat.beq saved.1 current.1
        · rw [hf] at h; contradiction
        · rw [hf] at h
          refine ⟨dest, saved, hlt, hs, Nat.beq_eq.mp hf, ?_⟩
          intro k hLive
          change Bool.rec _ (eqListN saved.2.1 current.2.1) (Nat.beq tag 0) = true at h
          cases hz : Nat.beq tag 0
          · rw [hz] at h
            change Bool.rec false _ (allowedMove mask goal top tag) = true at h
            cases hm : allowedMove mask goal top tag
            · rw [hm] at h; contradiction
            · rw [hm] at h
              change moveBankF tag saved.2.1 current.2.1 = true at h
              have hfixed : moveWord tag mask = mask ∧ moveWord tag goal = goal ∧ moveSlot tag top = top := by
                simpa only [allowedMove, Bool.and_eq_true, Nat.beq_eq] using hm
              simpa only [moveBank_image h] using
                moveLiveBin hp hfixed.1 hfixed.2.2 hfixed.2.1 hLive
          · rw [hz] at h
            change eqListN saved.2.1 current.2.1 = true at h
            rw [eqListN_eq, beq_iff_eq] at h
            exact h ▸ hLive

def dagCheckNodeWithF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool)
    (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (reference (Nat.add i 1)) st

theorem dagCheckNodeWithF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool) (i : Nat) :
    dagCheckNodeWithF mask goal bounds states reference i =
      dagCheckNodeWith mask goal bounds states reference i := by
  unfold dagCheckNodeWithF dagCheckNodeWith
  cases states i with
  | none => rfl
  | some state => exact dagCheckChildrenF_eq hgoals _ state

theorem lowerDagPermF {mask top goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefPermF mask goal top count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWithF mask goal bounds
      (dagTraceF mask stock fuel forest)
      (dagRefPermF mask goal top count (dagTraceF mask stock fuel forest) links) i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr, dagCheckRootsF_eq hgoals] at hroots
  rw [htr] at hnodes
  refine lowerDagWith (permRefTransfers hp _ _) hgm hgnz hcs snd hknown hsub hroots ?_
  intro i hlo hhi
  simpa only [dagCheckNodeWithF_eq hgoals] using hnodes i hlo hhi

def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
theorem dagAllNodesWithPicks {mask goal fuel count : Nat} {stock : List Nat}
    {picked : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hknown : ∀ i, KnownBin (picked i))
    (hsub : ∀ i b, b ∈ picked i → mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal (picked i)
      (dagTrace mask stock fuel forest) reference i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeWith at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (hknown i) (hsub i) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr2, hfEq, hMove⟩ :=
              hrefs (i + 1) (makeToken a b op keep) _ href
            have hbelow : rem - 1 < cap := by omega
            exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hMove k' hlive')

theorem lowerDagWithPicks {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {picked : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hknownPicked : ∀ i, KnownBin (picked i))
    (hsubPicked : ∀ i b, b ∈ picked i → mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (reference 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal (picked i)
      (dagTrace mask stock fuel forest) reference i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · obtain ⟨dest, saved, hdest, htr, hfEq, hMove⟩ := hrefs 0 tok _ href
    exact dagAllNodesWithPicks hrefs hgm hknownPicked hsubPicked snd hnodes fuel dest saved hdest htr hfEq k
      (by omega) (hMove k hlive')

abbrev ReplayBound := Nat × List Nat × Nat × Nat

def pickedBounds (bounds : List ReplayBound) (indices : List Nat) : List ReplayBound :=
  indices.filterMap (fun j => bounds[j]?)

theorem memPickedBounds {bounds : List ReplayBound} {indices : List Nat} {b : ReplayBound}
    (h : b ∈ pickedBounds bounds indices) : b ∈ bounds := by
  obtain ⟨_, _, hb⟩ := List.mem_filterMap.mp h
  exact List.mem_of_getElem? hb

def pickBlockF (index split low high : Nat) : Nat :=
  Bool.rec high low (Nat.blt index split)

def pagedUnpackF (width pageLog : Nat) (blocks : Nat → Nat) (index : Nat) : Nat :=
  unpackF (blocks (Nat.shiftRight index pageLog)) width
    (Nat.land index (Nat.sub (Nat.shiftLeft 1 pageLog) 1))

def unpackIndexedForestF (words : Nat → Nat) (tokenBits : Nat) : Nat → Nat × Nat :=
  fun i =>
    let code := words i
    (Nat.shiftRight code tokenBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tokenBits) 1))

def unpackIndexedLinksF (index data : Nat → Nat) (sizeBits tokBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := index parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := data mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)
def unpackIndexedPicks (positions elems : Nat → Nat) (lenSize i : Nat) : List Nat :=
  forceW (positions i) fun atIndex =>
    forceW (Nat.land atIndex (Nat.sub (Nat.shiftLeft 1 lenSize) 1)) fun count =>
      forceW (Nat.shiftRight atIndex lenSize) fun start =>
        (List.range count).map fun j => elems (Nat.add start j)

def unpackPicks (positions elems indexSize lenSize eltSize i : Nat) : List Nat :=
  forceW (unpackF positions indexSize i) fun atIndex =>
    forceW (Nat.land atIndex (Nat.sub (Nat.shiftLeft 1 lenSize) 1)) fun count =>
      forceW (Nat.shiftRight atIndex lenSize) fun start =>
        (List.range count).map fun j => unpackF elems eltSize (Nat.add start j)

theorem lowerDagPickedF {mask top goal fuel count : Nat} {stock : List Nat}
    {bounds : List ReplayBound} {picks : Nat → List Nat}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefPermF mask goal top count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWithF mask goal (pickedBounds bounds (picks i))
      (dagTraceF mask stock fuel forest)
      (dagRefPermF mask goal top count (dagTraceF mask stock fuel forest) links) i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr, dagCheckRootsF_eq hgoals] at hroots
  rw [htr] at hnodes
  refine lowerDagWithPicks (picked := fun i => pickedBounds bounds (picks i))
    (permRefTransfers hp _ _) hgm hgnz hcs snd hknown hsub ?_ ?_ hroots ?_
  · intro i b hb; exact hknown b (memPickedBounds hb)
  · intro i b hb; exact hsub b (memPickedBounds hb)
  · intro i hlo hhi
    have hg : ∀ b ∈ pickedBounds bounds (picks i), canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 :=
      fun b hb => hgoals b (memPickedBounds hb)
    simpa only [dagCheckNodeWithF_eq hg] using hnodes i hlo hhi


def m_15 : Nat := 0xcccc
def s_15 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_15 : Nat := 0x44c
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by
  intro b hb
  simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_15] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 1 (dagTraceF m_15 s_15 3 f_15) l_15 0) s_15 3 = true := by decide +kernel
def node_15 : Nat → Bool := dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 1 node_15 = true := by decide +kernel
theorem nc_15 : ∀ j, 0 ≤ j → j < 1 → node_15 j = true :=
  (certBlock nb_15_0)
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_42 : Nat := 0xcc00cc
def s_42 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_42 : Nat := 0x4004c
theorem lb_42 : LowerBin m_42 s_42 g_42 4 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 6, 7, 0, 0, 18, 19, 0, 0, 22, 23] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_42, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_75 : Nat := 0xc0c0c0c
def s_75 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_75 : Nat := 0x4040c
theorem lb_75 : LowerBin m_75 s_75 g_75 4 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 10, 11, 0, 0, 18, 19, 0, 0, 26, 27] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_75, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_104 : Nat := 0x22228888
def s_104 : List Nat := [0x8888, 0x2020808, 0x220088]
def g_104 : Nat := 0x2220008
theorem lb_104 : LowerBin m_104 s_104 g_104 4 := by
  refine lowerByRows [0, 0, 17, 3, 0, 0, 21, 7, 0, 0, 25, 11, 0, 0, 29, 15] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_104, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_118 : Nat := 0x3030c0c0
def s_118 : List Nat := [0x10104040, 0xc0c0, 0x3000c0]
def g_118 : Nat := 0x10300040
theorem lb_118 : LowerBin m_118 s_118 g_118 4 := by
  refine lowerByRows [0, 0, 20, 21, 0, 0, 6, 7, 0, 0, 28, 29, 0, 0, 14, 15] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_118, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_124 : Nat := 0x3300cc00
def s_124 : List Nat := [0x11004400, 0xcc00, 0x3000c00]
def g_124 : Nat := 0x13000400
theorem lb_124 : LowerBin m_124 s_124 g_124 4 := by
  refine lowerByRows [0, 0, 24, 25, 0, 0, 10, 11, 0, 0, 28, 29, 0, 0, 14, 15] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_124, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_126 : Nat := 0x33cc0000
def s_126 : List Nat := [0x11440000, 0xcc0000, 0x30c0000]
def g_126 : Nat := 0x13040000
theorem lb_126 : LowerBin m_126 s_126 g_126 4 := by
  refine lowerByRows [0, 0, 24, 25, 0, 0, 18, 19, 0, 0, 28, 29, 0, 0, 22, 23] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_126, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_136 : Nat := 0x44444444
def s_136 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_136 : Nat := 0x40444
theorem lb_136 : LowerBin m_136 s_136 g_136 4 := by
  refine lowerByRows [0, 0, 2, 6, 0, 0, 10, 14, 0, 0, 18, 22, 0, 0, 26, 30] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_136, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_157 : Nat := 0x66660000
def s_157 : List Nat := [0x22220000, 0x6060000, 0x660000]
def g_157 : Nat := 0x2260000
theorem lb_157 : LowerBin m_157 s_157 g_157 4 := by
  refine lowerByRows [0, 0, 17, 18, 0, 0, 21, 22, 0, 0, 25, 26, 0, 0, 29, 30] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_157, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_290 : Nat → Nat × Nat := unpackForestF 0x32d32592c21a424216007 3 9
def l_290 : Nat → Nat → Option Nat := unpackLinksF 0x82e5c3160a4601 0x81841492c424d2db2561a216007 7 3 9 3 4
def m_290 : Nat := 0x60606060000
def s_290 : List Nat := [0x20202020000, 0x600060000, 0x6060000]
def g_290 : Nat := 0x20004000000
def bds_290 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_290 : KnownBin bds_290 := by
  intro b hb
  simp [bds_290] at hb
theorem sub_290 : ∀ b ∈ bds_290, m_290 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_290] at hb
theorem gl_290 : ∀ b ∈ bds_290, canon b.1 g_290 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_290] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_290 : dagCheckRootsF m_290 g_290 bds_290 (dagRefF 7 (dagTraceF m_290 s_290 3 f_290) l_290 0) s_290 3 = true := by decide +kernel
def node_290 : Nat → Bool := dagCheckNodeF m_290 g_290 bds_290 7 (dagTraceF m_290 s_290 3 f_290) l_290
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_290_0 : treeBlockF 0 7 node_290 = true := by decide +kernel
theorem nc_290 : ∀ j, 0 ≤ j → j < 7 → node_290 j = true :=
  (certBlock nb_290_0)
theorem lb_290 : LowerBin m_290 s_290 g_290 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_290 sub_290 gl_290 rc_290 nc_290

def m_297 : Nat := 0xa0a00000a0a
def s_297 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_297 : Nat := 0x20000020a
theorem lb_297 : LowerBin m_297 s_297 g_297 4 := by
  refine lowerByRows [0, 0, 1, 3, 0, 0, 9, 11, 0, 0, 33, 35, 0, 0, 41, 43] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_297, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_355 : Nat := 0x222222220000
def s_355 : List Nat := [0x20202020000, 0x2200220000, 0x22220000]
def g_355 : Nat := 0x202220000
theorem lb_355 : LowerBin m_355 s_355 g_355 4 := by
  refine lowerByRows [0, 0, 17, 21, 0, 0, 25, 29, 0, 0, 33, 37, 0, 0, 41, 45] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_355, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_402 : Nat := 0x444444440000
def s_402 : List Nat := [0x40404040000, 0x4400440000, 0x44440000]
def g_402 : Nat := 0x44400040000
theorem lb_402 : LowerBin m_402 s_402 g_402 4 := by
  refine lowerByRows [0, 0, 30, 26, 0, 0, 22, 18, 0, 0, 46, 42, 0, 0, 38, 34] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_402, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_439 : Nat := 0x606000006060
def s_439 : List Nat := [0x202000002020, 0x6000000060, 0x6060]
def g_439 : Nat := 0x4000002060
def bds_439 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_439 : KnownBin bds_439 := by
  intro b hb
  simp [bds_439] at hb
theorem sub_439 : ∀ b ∈ bds_439, m_439 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_439] at hb
theorem gl_439 : ∀ b ∈ bds_439, canon b.1 g_439 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_439] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_439 : dagCheckRootsF m_439 g_439 bds_439 (dagRefF 1 (dagTraceF m_439 s_439 2 f_15) l_15 0) s_439 2 = true := by decide +kernel
def node_439 : Nat → Bool := dagCheckNodeF m_439 g_439 bds_439 1 (dagTraceF m_439 s_439 2 f_15) l_15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_439_0 : treeBlockF 0 1 node_439 = true := by decide +kernel
theorem nc_439 : ∀ j, 0 ≤ j → j < 1 → node_439 j = true :=
  (certBlock nb_439_0)
theorem lb_439 : LowerBin m_439 s_439 g_439 3 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_439 sub_439 gl_439 rc_439 nc_439

def m_440 : Nat := 0x606060600000
def s_440 : List Nat := [0x202020200000, 0x6000600000, 0x60600000]
def g_440 : Nat := 0x4000200000
theorem lb_440 : LowerBin m_440 s_440 g_440 4 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 29, 0, 0, 0, 0, 0, 0, 22, 21, 0, 0, 0, 0, 0, 0, 46, 45, 0, 0, 0, 0, 0, 0, 38, 37] (by decide +kernel) ?_ (by decide +kernel) lb_290
  intro w hw
  simp only [s_440, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_442 : Nat := 0x660000006600
def s_442 : List Nat := [0x220000002200, 0x60000000600, 0x6600]
def g_442 : Nat := 0x40000002600
theorem lb_442 : LowerBin m_442 s_442 g_442 3 := by
  refine lowerByRows [0, 0, 0, 0, 0, 9, 10, 0, 0, 0, 0, 0, 0, 13, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 42, 0, 0, 0, 0, 0, 0, 45, 46] (by decide +kernel) ?_ (by decide +kernel) lb_439
  intro w hw
  simp only [s_442, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_444 : Nat := 0x666600000000
def s_444 : List Nat := [0x222200000000, 0x60600000000, 0x6600000000]
def g_444 : Nat := 0x44600000000
theorem lb_444 : LowerBin m_444 s_444 g_444 4 := by
  refine lowerByRows [0, 0, 34, 33, 0, 0, 38, 37, 0, 0, 42, 41, 0, 0, 46, 45] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_444, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_566 : Nat := 0xa000a000a000a
def s_566 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_566 : Nat := 0x20002000a
theorem lb_566 : LowerBin m_566 s_566 g_566 4 := by
  refine lowerByRows [0, 0, 1, 3, 0, 0, 17, 19, 0, 0, 33, 35, 0, 0, 49, 51] (by decide +kernel) ?_ (by decide +kernel) lb_15
  intro w hw
  simp only [s_566, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1742 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1742 : Nat → Nat → Option Nat := fun _ _ => none
def m_1742 : Nat := 0xffff
def s_1742 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_1742 : Nat := 0x377f
def bds_1742 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_1742 : KnownBin bds_1742 := by
  intro b hb
  simp only [bds_1742, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_15
theorem sub_1742 : ∀ b ∈ bds_1742, m_1742 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1742, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1742 : ∀ b ∈ bds_1742, canon b.1 g_1742 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1742, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1742 : dagCheckRootsF m_1742 g_1742 bds_1742 (dagRefF 0 (dagTraceF m_1742 s_1742 4 f_1742) l_1742 0) s_1742 4 = true := by decide +kernel
def node_1742 : Nat → Bool := dagCheckNodeF m_1742 g_1742 bds_1742 0 (dagTraceF m_1742 s_1742 4 f_1742) l_1742
theorem nc_1742 : ∀ j, 0 ≤ j → j < 0 → node_1742 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1742 : LowerBin m_1742 s_1742 g_1742 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1742 sub_1742 gl_1742 rc_1742 nc_1742

def f_1743 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1743 : Nat → Nat → Option Nat := fun _ _ => none
def m_1743 : Nat := 0xff00ff
def s_1743 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_1743 : Nat := 0x37007f
def bds_1743 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 4, g_42)]
theorem kn_1743 : KnownBin bds_1743 := by
  intro b hb
  simp only [bds_1743, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_42
theorem sub_1743 : ∀ b ∈ bds_1743, m_1743 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1743, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1743 : ∀ b ∈ bds_1743, canon b.1 g_1743 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1743, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1743 : dagCheckRootsF m_1743 g_1743 bds_1743 (dagRefF 0 (dagTraceF m_1743 s_1743 4 f_1743) l_1743 0) s_1743 4 = true := by decide +kernel
def node_1743 : Nat → Bool := dagCheckNodeF m_1743 g_1743 bds_1743 0 (dagTraceF m_1743 s_1743 4 f_1743) l_1743
theorem nc_1743 : ∀ j, 0 ≤ j → j < 0 → node_1743 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1743 : LowerBin m_1743 s_1743 g_1743 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1743 sub_1743 gl_1743 rc_1743 nc_1743

def f_1745 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1745 : Nat → Nat → Option Nat := fun _ _ => none
def m_1745 : Nat := 0xf0f0f0f
def s_1745 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_1745 : Nat := 0x307070f
def bds_1745 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 4, g_75)]
theorem kn_1745 : KnownBin bds_1745 := by
  intro b hb
  simp only [bds_1745, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_75
theorem sub_1745 : ∀ b ∈ bds_1745, m_1745 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1745, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1745 : ∀ b ∈ bds_1745, canon b.1 g_1745 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1745, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1745 : dagCheckRootsF m_1745 g_1745 bds_1745 (dagRefF 0 (dagTraceF m_1745 s_1745 4 f_1745) l_1745 0) s_1745 4 = true := by decide +kernel
def node_1745 : Nat → Bool := dagCheckNodeF m_1745 g_1745 bds_1745 0 (dagTraceF m_1745 s_1745 4 f_1745) l_1745
theorem nc_1745 : ∀ j, 0 ≤ j → j < 0 → node_1745 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1745 : LowerBin m_1745 s_1745 g_1745 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1745 sub_1745 gl_1745 rc_1745 nc_1745

def f_1749 : Nat → Nat × Nat := unpackForestF 0xa54da4410637964d963594410537774a8840774676467d347546743105276345624560366026043b3f463e3553443d4a48243c4a3c463c26042b0a460a362e44094a2634093a1c34084a08461044083a0836041b000f 6 10
def l_1749 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2a1522a41482184027c4f81e13c0744e81d02b05049893024248088910202400800f11e01e00b001 0xa94d8545993581254449a4416c3958297d249e4d86459a357926184994416839341988407d347d348f4a8746824679460c3974315429301951382d286f456a454d3a292a443a6436182a602651382528534448245b4656354d4a212a444a40460c2a3c262d3825282e4426341c34104436463236294a213a184a14460c3a0836a237913771275c3b382b041b000f 11 4 10 6 5
def m_1749 : Nat := 0x3333cccc
def s_1749 : List Nat := [0x11114444, 0xcccc, 0x3030c0c, 0x3300cc]
def g_1749 : Nat := 0x1333044c
def bds_1749 : List (Nat × List Nat × Nat × Nat) := [(m_124, s_124, 4, g_124), (m_15, s_15, 4, g_15), (m_118, s_118, 4, g_118), (m_104, s_104, 4, g_104)]
theorem kn_1749 : KnownBin bds_1749 := by
  intro b hb
  simp only [bds_1749, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_124
  · exact lb_15
  · exact lb_118
  · exact lb_104
theorem sub_1749 : ∀ b ∈ bds_1749, m_1749 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1749, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1749 : ∀ b ∈ bds_1749, canon b.1 g_1749 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1749, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1749 : dagCheckRootsF m_1749 g_1749 bds_1749 (dagRefF 43 (dagTraceF m_1749 s_1749 6 f_1749) l_1749 0) s_1749 6 = true := by decide +kernel
def node_1749 : Nat → Bool := dagCheckNodeF m_1749 g_1749 bds_1749 43 (dagTraceF m_1749 s_1749 6 f_1749) l_1749
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1749_0 : treeBlockF 0 43 node_1749 = true := by decide +kernel
theorem nc_1749 : ∀ j, 0 ≤ j → j < 43 → node_1749 j = true :=
  (certBlock nb_1749_0)
theorem lb_1749 : LowerBin m_1749 s_1749 g_1749 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1749 sub_1749 gl_1749 rc_1749 nc_1749

def m_1750 : Nat := 0x33cc33cc
def s_1750 : List Nat := [0x11441144, 0xcc00cc, 0x30c030c, 0x33cc]
def g_1750 : Nat := 0x1304334c
theorem lb_1750 : LowerBin m_1750 s_1750 g_1750 7 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 6, 7, 0, 0, 18, 19, 0, 0, 22, 23, 8, 9, 0, 0, 12, 13, 0, 0, 24, 25, 0, 0, 28, 29] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_1750, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1751 : Nat := 0x3c3c3c3c
def s_1751 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_1751 : Nat := 0x1034343c
theorem lb_1751 : LowerBin m_1751 s_1751 g_1751 7 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 10, 11, 0, 0, 18, 19, 0, 0, 26, 27, 4, 5, 0, 0, 12, 13, 0, 0, 20, 21, 0, 0, 28, 29] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_1751, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1752 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1752 : Nat → Nat → Option Nat := fun _ _ => none
def m_1752 : Nat := 0x55555555
def s_1752 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_1752 : Nat := 0x11151555
def bds_1752 : List (Nat × List Nat × Nat × Nat) := [(m_136, s_136, 4, g_136)]
theorem kn_1752 : KnownBin bds_1752 := by
  intro b hb
  simp only [bds_1752, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_136
theorem sub_1752 : ∀ b ∈ bds_1752, m_1752 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1752, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1752 : ∀ b ∈ bds_1752, canon b.1 g_1752 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1752, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1752 : dagCheckRootsF m_1752 g_1752 bds_1752 (dagRefF 0 (dagTraceF m_1752 s_1752 4 f_1752) l_1752 0) s_1752 4 = true := by decide +kernel
def node_1752 : Nat → Bool := dagCheckNodeF m_1752 g_1752 bds_1752 0 (dagTraceF m_1752 s_1752 4 f_1752) l_1752
theorem nc_1752 : ∀ j, 0 ≤ j → j < 0 → node_1752 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1752 : LowerBin m_1752 s_1752 g_1752 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1752 sub_1752 gl_1752 rc_1752 nc_1752

def m_1756 : Nat := 0x66666666
def s_1756 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_1756 : Nat := 0x2262666
theorem lb_1756 : LowerBin m_1756 s_1756 g_1756 7 := by
  refine lowerByRows [0, 0, 5, 6, 0, 0, 13, 14, 0, 0, 21, 22, 0, 0, 29, 30, 1, 2, 0, 0, 9, 10, 0, 0, 17, 18, 0, 0, 25, 26] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_1756, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1761 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_1761 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
def m_1761 : Nat := 0xaaaaaaaa
def s_1761 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_1761 : Nat := 0x222222a
def bds_1761 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1761 : KnownBin bds_1761 := by
  intro b hb
  simp [bds_1761] at hb
theorem sub_1761 : ∀ b ∈ bds_1761, m_1761 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_1761] at hb
theorem gl_1761 : ∀ b ∈ bds_1761, canon b.1 g_1761 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_1761] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1761 : dagCheckRootsF m_1761 g_1761 bds_1761 (dagRefF 64 (dagTraceF m_1761 s_1761 5 f_1761) l_1761 0) s_1761 5 = true := by decide +kernel
def node_1761 : Nat → Bool := dagCheckNodeF m_1761 g_1761 bds_1761 64 (dagTraceF m_1761 s_1761 5 f_1761) l_1761
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1761_0 : treeBlockF 0 64 node_1761 = true := by decide +kernel
theorem nc_1761 : ∀ j, 0 ≤ j → j < 64 → node_1761 j = true :=
  (certBlock nb_1761_0)
theorem lb_1761 : LowerBin m_1761 s_1761 g_1761 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1761 sub_1761 gl_1761 rc_1761 nc_1761

def m_1765 : Nat := 0xcccccccc
def s_1765 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_1765 : Nat := 0x4044c
theorem lb_1765 : LowerBin m_1765 s_1765 g_1765 7 := by
  refine lowerByRows [0, 0, 27, 26, 0, 0, 19, 18, 0, 0, 11, 10, 0, 0, 3, 2, 31, 30, 0, 0, 23, 22, 0, 0, 15, 14, 0, 0, 7, 6] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_1765, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1768 : Nat := 0xf0f0f0f0
def s_1768 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_1768 : Nat := 0x10303070
theorem lb_1768 : LowerBin m_1768 s_1768 g_1768 6 := by
  refine lowerByRows [0, 4, 0, 6, 0, 5, 0, 7, 0, 12, 0, 14, 0, 13, 0, 15, 0, 20, 0, 22, 0, 21, 0, 23, 0, 28, 0, 30, 0, 29, 0, 31] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1768, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1770 : Nat := 0xff00ff00
def s_1770 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_1770 : Nat := 0x13003700
theorem lb_1770 : LowerBin m_1770 s_1770 g_1770 6 := by
  refine lowerByRows [0, 8, 0, 10, 0, 9, 0, 11, 0, 12, 0, 14, 0, 13, 0, 15, 0, 24, 0, 26, 0, 25, 0, 27, 0, 28, 0, 30, 0, 29, 0, 31] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1770, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1771 : Nat := 0xffff0000
def s_1771 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_1771 : Nat := 0x13370000
theorem lb_1771 : LowerBin m_1771 s_1771 g_1771 6 := by
  refine lowerByRows [0, 16, 0, 18, 0, 17, 0, 19, 0, 20, 0, 22, 0, 21, 0, 23, 0, 24, 0, 26, 0, 25, 0, 27, 0, 28, 0, 30, 0, 29, 0, 31] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1771, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1776 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1776 : Nat → Nat → Option Nat := fun _ _ => none
def m_1776 : Nat := 0xf0f00000f0f
def s_1776 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_1776 : Nat := 0x5070000070f
def bds_1776 : List (Nat × List Nat × Nat × Nat) := [(m_297, s_297, 4, g_297)]
theorem kn_1776 : KnownBin bds_1776 := by
  intro b hb
  simp only [bds_1776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_297
theorem sub_1776 : ∀ b ∈ bds_1776, m_1776 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1776 : ∀ b ∈ bds_1776, canon b.1 g_1776 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1776 : dagCheckRootsF m_1776 g_1776 bds_1776 (dagRefF 0 (dagTraceF m_1776 s_1776 4 f_1776) l_1776 0) s_1776 4 = true := by decide +kernel
def node_1776 : Nat → Bool := dagCheckNodeF m_1776 g_1776 bds_1776 0 (dagTraceF m_1776 s_1776 4 f_1776) l_1776
theorem nc_1776 : ∀ j, 0 ≤ j → j < 0 → node_1776 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1776 : LowerBin m_1776 s_1776 g_1776 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1776 sub_1776 gl_1776 rc_1776 nc_1776

def f_1787 : Nat → Nat × Nat := unpackForestF 0xc7e18eeea65d40b88018de6944d24985018cdf1c3e34787014fd69e2d34583014ec29b85330a5e68f029590300a4e2060291800f 5 10
def l_1787 : Nat → Nat → Option Nat := unpackLinksF 0x1d0e8743a1d0d1e8341a0b9dc2e170a1d02814089c422101803c5e0e1703443801 0x654cc2817102a945124985118e211a3c386a78c4d160c1938347840c040c6e3fd47768de519b93f527694dd0999d2f2a56349c291800f 9 4 10 5 5
def m_1787 : Nat := 0x33cc33cc0000
def s_1787 : List Nat := [0x114411440000, 0xcc00cc0000, 0x30c030c0000, 0x33cc0000]
def g_1787 : Nat := 0x114413040000
def bds_1787 : List (Nat × List Nat × Nat × Nat) := [(m_126, s_126, 4, g_126)]
theorem kn_1787 : KnownBin bds_1787 := by
  intro b hb
  simp only [bds_1787, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_126
theorem sub_1787 : ∀ b ∈ bds_1787, m_1787 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1787, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1787 : ∀ b ∈ bds_1787, canon b.1 g_1787 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1787, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1787 : dagCheckRootsF m_1787 g_1787 bds_1787 (dagRefF 28 (dagTraceF m_1787 s_1787 5 f_1787) l_1787 0) s_1787 5 = true := by decide +kernel
def node_1787 : Nat → Bool := dagCheckNodeF m_1787 g_1787 bds_1787 28 (dagTraceF m_1787 s_1787 5 f_1787) l_1787
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1787_0 : treeBlockF 0 28 node_1787 = true := by decide +kernel
theorem nc_1787 : ∀ j, 0 ≤ j → j < 28 → node_1787 j = true :=
  (certBlock nb_1787_0)
theorem lb_1787 : LowerBin m_1787 s_1787 g_1787 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1787 sub_1787 gl_1787 rc_1787 nc_1787

def m_1795 : Nat := 0x55aa55aa0000
def s_1795 : List Nat := [0xaa00aa0000, 0x112211220000, 0x50a050a0000, 0x55aa0000]
def g_1795 : Nat := 0x150211220000
theorem lb_1795 : LowerBin m_1795 s_1795 g_1795 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 35, 0, 0, 37, 39, 40, 42, 0, 0, 44, 46, 0, 0, 0, 0, 17, 19, 0, 0, 21, 23, 24, 26, 0, 0, 28, 30] (by decide +kernel) ?_ (by decide +kernel) lb_1787
  intro w hw
  simp only [s_1795, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1797 : Nat := 0x5a5a5a5a0000
def s_1797 : List Nat := [0xa0a0a0a0000, 0x121212120000, 0x5a005a0000, 0x5a5a0000]
def g_1797 : Nat := 0x105212120000
theorem lb_1797 : LowerBin m_1797 s_1797 g_1797 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 35, 0, 0, 41, 43, 36, 38, 0, 0, 44, 46, 0, 0, 0, 0, 17, 19, 0, 0, 25, 27, 20, 22, 0, 0, 28, 30] (by decide +kernel) ?_ (by decide +kernel) lb_1787
  intro w hw
  simp only [s_1797, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1798 : Nat → Nat × Nat := unpackForestF 0x41340c7ee13031bb2340a7ea13029b8527384824f449a9124107a20d421f000f 5 10
def l_1798 : Nat → Nat → Option Nat := unpackLinksF 0xb1a2a092897a786a686861606059583c0e01 0x70f209a184c709850f081632341898a13041e1c24224864f4a9a8c3d106af8fdb1bad3f4a6e849c21f000f 8 3 10 5 4
def m_1798 : Nat := 0x666600006666
def s_1798 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_1798 : Nat := 0x44600002666
def bds_1798 : List (Nat × List Nat × Nat × Nat) := [(m_444, s_444, 4, g_444), (m_439, s_439, 3, g_439), (m_442, s_442, 3, g_442)]
theorem kn_1798 : KnownBin bds_1798 := by
  intro b hb
  simp only [bds_1798, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact lb_444
  · exact lb_439
  · exact lb_442
theorem sub_1798 : ∀ b ∈ bds_1798, m_1798 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1798, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_1798 : ∀ b ∈ bds_1798, canon b.1 g_1798 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1798, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1798 : dagCheckRootsF m_1798 g_1798 bds_1798 (dagRefF 17 (dagTraceF m_1798 s_1798 5 f_1798) l_1798 0) s_1798 5 = true := by decide +kernel
def node_1798 : Nat → Bool := dagCheckNodeF m_1798 g_1798 bds_1798 17 (dagTraceF m_1798 s_1798 5 f_1798) l_1798
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1798_0 : treeBlockF 0 17 node_1798 = true := by decide +kernel
theorem nc_1798 : ∀ j, 0 ≤ j → j < 17 → node_1798 j = true :=
  (certBlock nb_1798_0)
theorem lb_1798 : LowerBin m_1798 s_1798 g_1798 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1798 sub_1798 gl_1798 rc_1798 nc_1798

def f_1799 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def l_1799 : Nat → Nat → Option Nat := unpackLinksF 0x9 0xf 2 1 4 1 2
def m_1799 : Nat := 0x666666660000
def s_1799 : List Nat := [0x222222220000, 0x60606060000, 0x6600660000, 0x66660000]
def g_1799 : Nat := 0x44602260000
def bds_1799 : List (Nat × List Nat × Nat × Nat) := [(m_444, s_444, 4, g_444), (m_157, s_157, 4, g_157), (m_402, s_402, 4, g_402), (m_355, s_355, 4, g_355), (m_440, s_440, 4, g_440), (m_290, s_290, 4, g_290)]
theorem kn_1799 : KnownBin bds_1799 := by
  intro b hb
  simp only [bds_1799, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_444
  · exact lb_157
  · exact lb_402
  · exact lb_355
  · exact lb_440
  · exact lb_290
theorem sub_1799 : ∀ b ∈ bds_1799, m_1799 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1799, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1799 : ∀ b ∈ bds_1799, canon b.1 g_1799 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1799, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1799 : dagCheckRootsF m_1799 g_1799 bds_1799 (dagRefF 1 (dagTraceF m_1799 s_1799 6 f_1799) l_1799 0) s_1799 6 = true := by decide +kernel
def node_1799 : Nat → Bool := dagCheckNodeF m_1799 g_1799 bds_1799 1 (dagTraceF m_1799 s_1799 6 f_1799) l_1799
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1799_0 : treeBlockF 0 1 node_1799 = true := by decide +kernel
theorem nc_1799 : ∀ j, 0 ≤ j → j < 1 → node_1799 j = true :=
  (certBlock nb_1799_0)
theorem lb_1799 : LowerBin m_1799 s_1799 g_1799 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1799 sub_1799 gl_1799 rc_1799 nc_1799

def m_1802 : Nat := 0xa5a5a5a50000
def s_1802 : List Nat := [0x50505050000, 0x212121210000, 0xa500a50000, 0xa5a50000]
def g_1802 : Nat := 0x50501250000
theorem lb_1802 : LowerBin m_1802 s_1802 g_1802 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 23, 0, 0, 26, 31, 16, 21, 0, 0, 24, 29, 0, 0, 0, 0, 34, 39, 0, 0, 42, 47, 32, 37, 0, 0, 40, 45] (by decide +kernel) ?_ (by decide +kernel) lb_1787
  intro w hw
  simp only [s_1802, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1805 : Nat := 0xaaaa00005555
def s_1805 : List Nat := [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055]
def g_1805 : Nat := 0x200001555
theorem lb_1805 : LowerBin m_1805 s_1805 g_1805 6 := by
  refine lowerByRows [1, 0, 1, 33, 1, 2, 1, 35, 1, 4, 1, 37, 1, 6, 1, 39, 1, 8, 1, 41, 1, 10, 1, 43, 1, 12, 1, 45, 1, 14, 1, 47] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1805, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1806 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1806 : Nat → Nat → Option Nat := fun _ _ => none
def m_1806 : Nat := 0xaaaa0000aaaa
def s_1806 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_1806 : Nat := 0x20000222a
def bds_1806 : List (Nat × List Nat × Nat × Nat) := [(m_297, s_297, 4, g_297)]
theorem kn_1806 : KnownBin bds_1806 := by
  intro b hb
  simp only [bds_1806, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_297
theorem sub_1806 : ∀ b ∈ bds_1806, m_1806 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1806, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1806 : ∀ b ∈ bds_1806, canon b.1 g_1806 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1806, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1806 : dagCheckRootsF m_1806 g_1806 bds_1806 (dagRefF 0 (dagTraceF m_1806 s_1806 4 f_1806) l_1806 0) s_1806 4 = true := by decide +kernel
def node_1806 : Nat → Bool := dagCheckNodeF m_1806 g_1806 bds_1806 0 (dagTraceF m_1806 s_1806 4 f_1806) l_1806
theorem nc_1806 : ∀ j, 0 ≤ j → j < 0 → node_1806 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1806 : LowerBin m_1806 s_1806 g_1806 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1806 sub_1806 gl_1806 rc_1806 nc_1806

def m_1812 : Nat := 0xcc33cc330000
def s_1812 : List Nat := [0x441144110000, 0x3300330000, 0xc030c030000, 0xcc330000]
def g_1812 : Nat := 0x41300330000
theorem lb_1812 : LowerBin m_1812 s_1812 g_1812 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 43, 0, 0, 37, 47, 32, 42, 0, 0, 36, 46, 0, 0, 0, 0, 17, 27, 0, 0, 21, 31, 16, 26, 0, 0, 20, 30] (by decide +kernel) ?_ (by decide +kernel) lb_1787
  intro w hw
  simp only [s_1812, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1820 : Nat := 0xf0f00000f0f0
def s_1820 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_1820 : Nat := 0x105000003070
def bds_1820 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1820 : KnownBin bds_1820 := by
  intro b hb
  simp [bds_1820] at hb
theorem sub_1820 : ∀ b ∈ bds_1820, m_1820 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_1820] at hb
theorem gl_1820 : ∀ b ∈ bds_1820, canon b.1 g_1820 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_1820] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1820 : dagCheckRootsF m_1820 g_1820 bds_1820 (dagRefF 1 (dagTraceF m_1820 s_1820 3 f_1799) l_1799 0) s_1820 3 = true := by decide +kernel
def node_1820 : Nat → Bool := dagCheckNodeF m_1820 g_1820 bds_1820 1 (dagTraceF m_1820 s_1820 3 f_1799) l_1799
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1820_0 : treeBlockF 0 1 node_1820 = true := by decide +kernel
theorem nc_1820 : ∀ j, 0 ≤ j → j < 1 → node_1820 j = true :=
  (certBlock nb_1820_0)
theorem lb_1820 : LowerBin m_1820 s_1820 g_1820 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1820 sub_1820 gl_1820 rc_1820 nc_1820

def m_1827 : Nat := 0xffff00000000
def s_1827 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_1827 : Nat := 0x155700000000
theorem lb_1827 : LowerBin m_1827 s_1827 g_1827 6 := by
  refine lowerByRows [0, 32, 0, 33, 0, 34, 0, 35, 0, 36, 0, 37, 0, 38, 0, 39, 0, 40, 0, 41, 0, 42, 0, 43, 0, 44, 0, 45, 0, 46, 0, 47] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1827, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1828 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1828 : Nat → Nat → Option Nat := fun _ _ => none
def m_1828 : Nat := 0xf000f000f000f
def s_1828 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_1828 : Nat := 0x500070007000f
def bds_1828 : List (Nat × List Nat × Nat × Nat) := [(m_566, s_566, 4, g_566)]
theorem kn_1828 : KnownBin bds_1828 := by
  intro b hb
  simp only [bds_1828, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_566
theorem sub_1828 : ∀ b ∈ bds_1828, m_1828 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1828, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1828 : ∀ b ∈ bds_1828, canon b.1 g_1828 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1828, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1828 : dagCheckRootsF m_1828 g_1828 bds_1828 (dagRefF 0 (dagTraceF m_1828 s_1828 4 f_1828) l_1828 0) s_1828 4 = true := by decide +kernel
def node_1828 : Nat → Bool := dagCheckNodeF m_1828 g_1828 bds_1828 0 (dagTraceF m_1828 s_1828 4 f_1828) l_1828
theorem nc_1828 : ∀ j, 0 ≤ j → j < 0 → node_1828 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1828 : LowerBin m_1828 s_1828 g_1828 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1828 sub_1828 gl_1828 rc_1828 nc_1828

def m_1861 : Nat := 0x66006600660066
def s_1861 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_1861 : Nat := 0x4004600260066
theorem lb_1861 : LowerBin m_1861 s_1861 g_1861 6 := by
  refine lowerByRows [0, 1, 2, 0, 0, 5, 6, 0, 0, 17, 18, 0, 0, 21, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0, 37, 38, 0, 0, 49, 50, 0, 0, 53, 54] (by decide +kernel) ?_ (by decide +kernel) lb_1798
  intro w hw
  simp only [s_1861, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1862 : Nat := 0x66006666006600
def s_1862 : List Nat := [0x22002222002200, 0x6000606000600, 0x66006600, 0x6600006600]
def g_1862 : Nat := 0x4004602002600
theorem lb_1862 : LowerBin m_1862 s_1862 g_1862 7 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 10, 0, 0, 13, 14, 0, 0, 25, 26, 0, 0, 29, 30, 0, 0, 33, 34, 0, 0, 37, 38, 0, 0, 49, 50, 0, 0, 53, 54] (by decide +kernel) ?_ (by decide +kernel) lb_1799
  intro w hw
  simp only [s_1862, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1870 : Nat := 0xaa00aa00550055
def s_1870 : List Nat := [0x550055, 0x22002200110011, 0xa000a00050005, 0xaa00000055]
def g_1870 : Nat := 0x200150055
theorem lb_1870 : LowerBin m_1870 s_1870 g_1870 6 := by
  refine lowerByRows [1, 0, 1, 33, 1, 2, 1, 35, 1, 4, 1, 37, 1, 6, 1, 39, 1, 16, 1, 49, 1, 18, 1, 51, 1, 20, 1, 53, 1, 22, 1, 55] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1870, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1871 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1871 : Nat → Nat → Option Nat := fun _ _ => none
def m_1871 : Nat := 0xaa00aa00aa00aa
def s_1871 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_1871 : Nat := 0x20022002a
def bds_1871 : List (Nat × List Nat × Nat × Nat) := [(m_566, s_566, 4, g_566)]
theorem kn_1871 : KnownBin bds_1871 := by
  intro b hb
  simp only [bds_1871, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_566
theorem sub_1871 : ∀ b ∈ bds_1871, m_1871 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1871, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1871 : ∀ b ∈ bds_1871, canon b.1 g_1871 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1871, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1871 : dagCheckRootsF m_1871 g_1871 bds_1871 (dagRefF 0 (dagTraceF m_1871 s_1871 4 f_1871) l_1871 0) s_1871 4 = true := by decide +kernel
def node_1871 : Nat → Bool := dagCheckNodeF m_1871 g_1871 bds_1871 0 (dagTraceF m_1871 s_1871 4 f_1871) l_1871
theorem nc_1871 : ∀ j, 0 ≤ j → j < 0 → node_1871 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1871 : LowerBin m_1871 s_1871 g_1871 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1871 sub_1871 gl_1871 rc_1871 nc_1871

def m_1902 : Nat := 0xff00ff00000000
def s_1902 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_1902 : Nat := 0x15005700000000
theorem lb_1902 : LowerBin m_1902 s_1902 g_1902 6 := by
  refine lowerByRows [0, 32, 0, 33, 0, 34, 0, 35, 0, 36, 0, 37, 0, 38, 0, 39, 0, 48, 0, 49, 0, 50, 0, 51, 0, 52, 0, 53, 0, 54, 0, 55] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1902, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1936 : Nat := 0x606060606060606
def s_1936 : List Nat := [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606]
def g_1936 : Nat := 0x4040602060606
theorem lb_1936 : LowerBin m_1936 s_1936 g_1936 6 := by
  refine lowerByRows [0, 1, 2, 0, 0, 9, 10, 0, 0, 17, 18, 0, 0, 25, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 34, 0, 0, 41, 42, 0, 0, 49, 50, 0, 0, 57, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1798
  intro w hw
  simp only [s_1936, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1937 : Nat := 0x606060660606060
def s_1937 : List Nat := [0x202020220202020, 0x60606060, 0x6000600600060, 0x60600006060]
def g_1937 : Nat := 0x4040600202060
theorem lb_1937 : LowerBin m_1937 s_1937 g_1937 7 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 6, 0, 0, 13, 14, 0, 0, 21, 22, 0, 0, 29, 30, 0, 0, 33, 34, 0, 0, 41, 42, 0, 0, 49, 50, 0, 0, 57, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1799
  intro w hw
  simp only [s_1937, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1946 : Nat := 0xa0a0a0a05050505
def s_1946 : List Nat := [0x5050505, 0x202020201010101, 0xa000a00050005, 0xa0a00000505]
def g_1946 : Nat := 0x201050505
theorem lb_1946 : LowerBin m_1946 s_1946 g_1946 6 := by
  refine lowerByRows [1, 0, 1, 33, 1, 2, 1, 35, 1, 8, 1, 41, 1, 10, 1, 43, 1, 16, 1, 49, 1, 18, 1, 51, 1, 24, 1, 57, 1, 26, 1, 59] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1946, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1947 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1947 : Nat → Nat → Option Nat := fun _ _ => none
def m_1947 : Nat := 0xa0a0a0a0a0a0a0a
def s_1947 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_1947 : Nat := 0x20202020a
def bds_1947 : List (Nat × List Nat × Nat × Nat) := [(m_566, s_566, 4, g_566)]
theorem kn_1947 : KnownBin bds_1947 := by
  intro b hb
  simp only [bds_1947, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_566
theorem sub_1947 : ∀ b ∈ bds_1947, m_1947 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1947, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1947 : ∀ b ∈ bds_1947, canon b.1 g_1947 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1947, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1947 : dagCheckRootsF m_1947 g_1947 bds_1947 (dagRefF 0 (dagTraceF m_1947 s_1947 4 f_1947) l_1947 0) s_1947 4 = true := by decide +kernel
def node_1947 : Nat → Bool := dagCheckNodeF m_1947 g_1947 bds_1947 0 (dagTraceF m_1947 s_1947 4 f_1947) l_1947
theorem nc_1947 : ∀ j, 0 ≤ j → j < 0 → node_1947 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1947 : LowerBin m_1947 s_1947 g_1947 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1947 sub_1947 gl_1947 rc_1947 nc_1947

def f_1963 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1963 : Nat → Nat → Option Nat := fun _ _ => none
def m_1963 : Nat := 0xc0c0c0c0c0c0c0c
def s_1963 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_1963 : Nat := 0x404040004040c
def bds_1963 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 4, g_75)]
theorem kn_1963 : KnownBin bds_1963 := by
  intro b hb
  simp only [bds_1963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_75
theorem sub_1963 : ∀ b ∈ bds_1963, m_1963 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1963 : ∀ b ∈ bds_1963, canon b.1 g_1963 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1963 : dagCheckRootsF m_1963 g_1963 bds_1963 (dagRefF 0 (dagTraceF m_1963 s_1963 4 f_1963) l_1963 0) s_1963 4 = true := by decide +kernel
def node_1963 : Nat → Bool := dagCheckNodeF m_1963 g_1963 bds_1963 0 (dagTraceF m_1963 s_1963 4 f_1963) l_1963
theorem nc_1963 : ∀ j, 0 ≤ j → j < 0 → node_1963 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1963 : LowerBin m_1963 s_1963 g_1963 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1963 sub_1963 gl_1963 rc_1963 nc_1963

def m_1978 : Nat := 0xf000f000f000f00
def s_1978 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_1978 : Nat := 0x100050003000700
theorem lb_1978 : LowerBin m_1978 s_1978 g_1978 4 := by
  refine lowerByRows [0, 0, 0, 0, 8, 9, 10, 11, 0, 0, 0, 0, 24, 25, 26, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 41, 42, 43, 0, 0, 0, 0, 56, 57, 58, 59] (by decide +kernel) ?_ (by decide +kernel) lb_1820
  intro w hw
  simp only [s_1978, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1984 : Nat := 0xf0f00000f0f0000
def s_1984 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_1984 : Nat := 0x105000003070000
theorem lb_1984 : LowerBin m_1984 s_1984 g_1984 4 := by
  refine lowerByRows [0, 0, 0, 0, 16, 17, 18, 19, 0, 0, 0, 0, 24, 25, 26, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 0, 0, 0, 0, 56, 57, 58, 59] (by decide +kernel) ?_ (by decide +kernel) lb_1820
  intro w hw
  simp only [s_1984, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1986 : Nat := 0xf0f0f0f00000000
def s_1986 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_1986 : Nat := 0x105050700000000
theorem lb_1986 : LowerBin m_1986 s_1986 g_1986 6 := by
  refine lowerByRows [0, 32, 0, 33, 0, 34, 0, 35, 0, 40, 0, 41, 0, 42, 0, 43, 0, 48, 0, 49, 0, 50, 0, 51, 0, 56, 0, 57, 0, 58, 0, 59] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_1986, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1993 : Nat := 0x1111111144444444
def s_1993 : List Nat := [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444]
def g_1993 : Nat := 0x111111100040444
theorem lb_1993 : LowerBin m_1993 s_1993 g_1993 7 := by
  refine lowerByRows [0, 0, 36, 6, 0, 0, 44, 14, 0, 0, 52, 22, 0, 0, 60, 30, 32, 2, 0, 0, 40, 10, 0, 0, 48, 18, 0, 0, 56, 26] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_1993, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2026 : Nat := 0x2222222222222222
def s_2026 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_2026 : Nat := 0x202222222
theorem lb_2026 : LowerBin m_2026 s_2026 g_2026 6 := by
  refine lowerByRows [0, 1, 0, 33, 0, 5, 0, 37, 0, 9, 0, 41, 0, 13, 0, 45, 0, 17, 0, 49, 0, 21, 0, 53, 0, 25, 0, 57, 0, 29, 0, 61] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_2026, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2027 : Nat := 0x2222222244444444
def s_2027 : List Nat := [0x44444444, 0x202020204040404, 0x22002200440044, 0x222200004444]
def g_2027 : Nat := 0x200040444
theorem lb_2027 : LowerBin m_2027 s_2027 g_2027 7 := by
  refine lowerByRows [0, 0, 57, 26, 0, 0, 49, 18, 0, 0, 41, 10, 0, 0, 33, 2, 61, 30, 0, 0, 53, 22, 0, 0, 45, 14, 0, 0, 37, 6] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2027, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2041 : Nat := 0x3003300330033003
def s_2041 : List Nat := [0x1001100110011001, 0x3000300030003, 0x300300003003, 0x30033003]
def g_2041 : Nat := 0x1100310033003
theorem lb_2041 : LowerBin m_2041 s_2041 g_2041 7 := by
  refine lowerByRows [2, 2, 12, 13, 2, 2, 28, 29, 2, 2, 44, 45, 2, 2, 60, 61, 0, 1, 2, 2, 16, 17, 2, 2, 32, 33, 2, 2, 48, 49] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2041, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2045 : Nat := 0x3030030330300303
def s_2045 : List Nat := [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303]
def g_2045 : Nat := 0x10010310300303
theorem lb_2045 : LowerBin m_2045 s_2045 g_2045 7 := by
  refine lowerByRows [2, 2, 20, 21, 2, 2, 28, 29, 2, 2, 52, 53, 2, 2, 60, 61, 0, 1, 2, 2, 8, 9, 2, 2, 32, 33, 2, 2, 40, 41] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2045, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2057 : Nat := 0x3300003333000033
def s_2057 : List Nat := [0x1100001111000011, 0x300000303000003, 0x3300000033, 0x33000033]
def g_2057 : Nat := 0x100001313000033
theorem lb_2057 : LowerBin m_2057 s_2057 g_2057 7 := by
  refine lowerByRows [2, 2, 4, 5, 2, 2, 28, 29, 2, 2, 36, 37, 2, 2, 60, 61, 0, 1, 2, 2, 24, 25, 2, 2, 32, 33, 2, 2, 56, 57] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2057, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2070 : Nat := 0x3333333300000000
def s_2070 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_2070 : Nat := 0x111111300000000
theorem lb_2070 : LowerBin m_2070 s_2070 g_2070 6 := by
  refine lowerByRows [0, 32, 0, 33, 0, 36, 0, 37, 0, 40, 0, 41, 0, 44, 0, 45, 0, 48, 0, 49, 0, 52, 0, 53, 0, 56, 0, 57, 0, 60, 0, 61] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_2070, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2094 : Nat := 0x4444444422222222
def s_2094 : List Nat := [0x22222222, 0x404040402020202, 0x44004400220022, 0x444400002222]
def g_2094 : Nat := 0x4044402222222
theorem lb_2094 : LowerBin m_2094 s_2094 g_2094 7 := by
  refine lowerByRows [0, 0, 5, 38, 0, 0, 13, 46, 0, 0, 21, 54, 0, 0, 29, 62, 1, 34, 0, 0, 9, 42, 0, 0, 17, 50, 0, 0, 25, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2094, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2096 : Nat := 0x4444444488888888
def s_2096 : List Nat := [0x88888888, 0x404040408080808, 0x44004400880088, 0x444400008888]
def g_2096 : Nat := 0x4044400000008
theorem lb_2096 : LowerBin m_2096 s_2096 g_2096 7 := by
  refine lowerByRows [0, 0, 27, 58, 0, 0, 19, 50, 0, 0, 11, 42, 0, 0, 3, 34, 31, 62, 0, 0, 23, 54, 0, 0, 15, 46, 0, 0, 7, 38] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2096, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2113 : Nat := 0x5050505005050505
def s_2113 : List Nat := [0x1010101001010101, 0x5050505, 0x50005000050005, 0x505000000505]
def g_2113 : Nat := 0x10105001050505
theorem lb_2113 : LowerBin m_2113 s_2113 g_2113 7 := by
  refine lowerByRows [1, 1, 36, 38, 1, 1, 44, 46, 1, 1, 52, 54, 1, 1, 60, 62, 0, 2, 1, 1, 8, 10, 1, 1, 16, 18, 1, 1, 24, 26] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2113, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2125 : Nat := 0x5500550000550055
def s_2125 : List Nat := [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055]
def g_2125 : Nat := 0x100150000150055
theorem lb_2125 : LowerBin m_2125 s_2125 g_2125 7 := by
  refine lowerByRows [1, 1, 4, 6, 1, 1, 44, 46, 1, 1, 20, 22, 1, 1, 60, 62, 0, 2, 1, 1, 40, 42, 1, 1, 16, 18, 1, 1, 56, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2125, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2131 : Nat := 0x5555000000005555
def s_2131 : List Nat := [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555]
def g_2131 : Nat := 0x115000000001555
theorem lb_2131 : LowerBin m_2131 s_2131 g_2131 7 := by
  refine lowerByRows [1, 1, 4, 6, 1, 1, 12, 14, 1, 1, 52, 54, 1, 1, 60, 62, 0, 2, 1, 1, 8, 10, 1, 1, 48, 50, 1, 1, 56, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2131, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2135 : Nat := 0x5555555500000000
def s_2135 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_2135 : Nat := 0x115155500000000
theorem lb_2135 : LowerBin m_2135 s_2135 g_2135 7 := by
  refine lowerByRows [0, 0, 36, 38, 0, 0, 44, 46, 0, 0, 52, 54, 0, 0, 60, 62, 32, 34, 0, 0, 40, 42, 0, 0, 48, 50, 0, 0, 56, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2135, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2136 : Nat := 0x5555aaaa00000000
def s_2136 : List Nat := [0xaaaa00000000, 0x1111222200000000, 0x5050a0a00000000, 0x5500aa00000000]
def g_2136 : Nat := 0x115000200000000
theorem lb_2136 : LowerBin m_2136 s_2136 g_2136 7 := by
  refine lowerByRows [0, 0, 45, 60, 0, 0, 41, 56, 0, 0, 37, 52, 0, 0, 33, 48, 47, 62, 0, 0, 43, 58, 0, 0, 39, 54, 0, 0, 35, 50] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2136, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2139 : Nat := 0x55aa55aa00000000
def s_2139 : List Nat := [0xaa00aa00000000, 0x1122112200000000, 0x50a050a00000000, 0x55aa00000000]
def g_2139 : Nat := 0x100150200000000
theorem lb_2139 : LowerBin m_2139 s_2139 g_2139 7 := by
  refine lowerByRows [0, 0, 53, 60, 0, 0, 49, 56, 0, 0, 37, 44, 0, 0, 33, 40, 55, 62, 0, 0, 51, 58, 0, 0, 39, 46, 0, 0, 35, 42] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2139, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2145 : Nat := 0x5a5a5a5a00000000
def s_2145 : List Nat := [0xa0a0a0a00000000, 0x1212121200000000, 0x5a005a00000000, 0x5a5a00000000]
def g_2145 : Nat := 0x10105200000000
theorem lb_2145 : LowerBin m_2145 s_2145 g_2145 7 := by
  refine lowerByRows [0, 0, 57, 60, 0, 0, 49, 52, 0, 0, 41, 44, 0, 0, 33, 36, 59, 62, 0, 0, 51, 54, 0, 0, 43, 46, 0, 0, 35, 38] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2145, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2146 : Nat := 0x6006600660066006
def s_2146 : List Nat := [0x2002200220022002, 0x6000600060006, 0x600600006006, 0x60066006]
def g_2146 : Nat := 0x4000600062006
theorem lb_2146 : LowerBin m_2146 s_2146 g_2146 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 29, 0, 0, 49, 61, 1, 13, 0, 0, 33, 45, 0, 0, 0, 0, 18, 30, 0, 0, 50, 62, 2, 14, 0, 0, 34, 46] (by decide +kernel) ?_ (by decide +kernel) lb_1787
  intro w hw
  simp only [s_2146, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2149 : Nat := 0x6060606060606060
def s_2149 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_2149 : Nat := 0x4000202060
theorem lb_2149 : LowerBin m_2149 s_2149 g_2149 6 := by
  refine lowerByRows [0, 61, 62, 0, 0, 53, 54, 0, 0, 45, 46, 0, 0, 37, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 21, 22, 0, 0, 13, 14, 0, 0, 5, 6] (by decide +kernel) ?_ (by decide +kernel) lb_1798
  intro w hw
  simp only [s_2149, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2150 : Nat := 0x6600006666000066
def s_2150 : List Nat := [0x2200002222000022, 0x600000606000006, 0x6600000066, 0x66000066]
def g_2150 : Nat := 0x4602000066
theorem lb_2150 : LowerBin m_2150 s_2150 g_2150 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 29, 0, 0, 37, 61, 1, 25, 0, 0, 33, 57, 0, 0, 0, 0, 6, 30, 0, 0, 38, 62, 2, 26, 0, 0, 34, 58] (by decide +kernel) ?_ (by decide +kernel) lb_1787
  intro w hw
  simp only [s_2150, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2152 : Nat := 0x6600660066006600
def s_2152 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_2152 : Nat := 0x40002002600
theorem lb_2152 : LowerBin m_2152 s_2152 g_2152 6 := by
  refine lowerByRows [0, 61, 62, 0, 0, 57, 58, 0, 0, 45, 46, 0, 0, 41, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 25, 26, 0, 0, 13, 14, 0, 0, 9, 10] (by decide +kernel) ?_ (by decide +kernel) lb_1798
  intro w hw
  simp only [s_2152, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2154 : Nat := 0x6666000066660000
def s_2154 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_2154 : Nat := 0x4000002260000
theorem lb_2154 : LowerBin m_2154 s_2154 g_2154 6 := by
  refine lowerByRows [0, 61, 62, 0, 0, 57, 58, 0, 0, 53, 54, 0, 0, 49, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 25, 26, 0, 0, 21, 22, 0, 0, 17, 18] (by decide +kernel) ?_ (by decide +kernel) lb_1798
  intro w hw
  simp only [s_2154, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2155 : Nat := 0x6666666600000000
def s_2155 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_2155 : Nat := 0x4044600000000
theorem lb_2155 : LowerBin m_2155 s_2155 g_2155 7 := by
  refine lowerByRows [0, 0, 57, 58, 0, 0, 49, 50, 0, 0, 41, 42, 0, 0, 33, 34, 61, 62, 0, 0, 53, 54, 0, 0, 45, 46, 0, 0, 37, 38] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2155, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2190 : Nat := 0xa00aa00aa00aa00a
def s_2190 : List Nat := [0x2002200220022002, 0xa000a000a000a, 0xa00a0000a00a, 0xa00aa00a]
def g_2190 : Nat := 0x20002200a
theorem lb_2190 : LowerBin m_2190 s_2190 g_2190 7 := by
  refine lowerByRows [0, 0, 51, 49, 0, 0, 35, 33, 0, 0, 19, 17, 0, 0, 3, 1, 63, 61, 0, 0, 47, 45, 0, 0, 31, 29, 0, 0, 15, 13] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2190, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2196 : Nat := 0xa0a00a0aa0a00a0a
def s_2196 : List Nat := [0x2020020220200202, 0xa0a00000a0a, 0xa0000a00a0000a, 0xa0a00a0a]
def g_2196 : Nat := 0x20020020a
theorem lb_2196 : LowerBin m_2196 s_2196 g_2196 7 := by
  refine lowerByRows [0, 0, 43, 41, 0, 0, 35, 33, 0, 0, 11, 9, 0, 0, 3, 1, 63, 61, 0, 0, 55, 53, 0, 0, 31, 29, 0, 0, 23, 21] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2196, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2211 : Nat := 0xaa0000aaaa0000aa
def s_2211 : List Nat := [0x2200002222000022, 0xa00000a0a00000a, 0xaa000000aa, 0xaa0000aa]
def g_2211 : Nat := 0x20200002a
theorem lb_2211 : LowerBin m_2211 s_2211 g_2211 7 := by
  refine lowerByRows [0, 0, 59, 57, 0, 0, 35, 33, 0, 0, 27, 25, 0, 0, 3, 1, 63, 61, 0, 0, 39, 37, 0, 0, 31, 29, 0, 0, 7, 5] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2211, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2240 : Nat := 0xc0c0c0c00c0c0c0c
def s_2240 : List Nat := [0x4040404004040404, 0xc0c0c0c, 0xc000c0000c000c, 0xc0c000000c0c]
def g_2240 : Nat := 0x400004040c
theorem lb_2240 : LowerBin m_2240 s_2240 g_2240 7 := by
  refine lowerByRows [0, 0, 27, 26, 0, 0, 19, 18, 0, 0, 11, 10, 0, 0, 3, 2, 63, 62, 0, 0, 55, 54, 0, 0, 47, 46, 0, 0, 39, 38] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2240, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2241 : Nat := 0xc0c0c0c030303030
def s_2241 : List Nat := [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030]
def g_2241 : Nat := 0x4010303030
theorem lb_2241 : LowerBin m_2241 s_2241 g_2241 6 := by
  refine lowerByRows [0, 4, 0, 38, 0, 5, 0, 39, 0, 12, 0, 46, 0, 13, 0, 47, 0, 20, 0, 54, 0, 21, 0, 55, 0, 28, 0, 62, 0, 29, 0, 63] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_2241, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2255 : Nat := 0xcc00cc0000cc00cc
def s_2255 : List Nat := [0x4400440000440044, 0xc000c00000c000c, 0xcc00cc, 0xcc00000000cc]
def g_2255 : Nat := 0x4000004004c
theorem lb_2255 : LowerBin m_2255 s_2255 g_2255 7 := by
  refine lowerByRows [0, 0, 59, 58, 0, 0, 19, 18, 0, 0, 43, 42, 0, 0, 3, 2, 63, 62, 0, 0, 23, 22, 0, 0, 47, 46, 0, 0, 7, 6] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2255, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2256 : Nat := 0xcc00cc0033003300
def s_2256 : List Nat := [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300]
def g_2256 : Nat := 0x40013003300
theorem lb_2256 : LowerBin m_2256 s_2256 g_2256 6 := by
  refine lowerByRows [0, 8, 0, 42, 0, 9, 0, 43, 0, 12, 0, 46, 0, 13, 0, 47, 0, 24, 0, 58, 0, 25, 0, 59, 0, 28, 0, 62, 0, 29, 0, 63] (by decide +kernel) ?_ (by decide +kernel) lb_1761
  intro w hw
  simp only [s_2256, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2262 : Nat := 0xcccc00000000cccc
def s_2262 : List Nat := [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc]
def g_2262 : Nat := 0x400000000044c
theorem lb_2262 : LowerBin m_2262 s_2262 g_2262 7 := by
  refine lowerByRows [0, 0, 59, 58, 0, 0, 51, 50, 0, 0, 11, 10, 0, 0, 3, 2, 63, 62, 0, 0, 55, 54, 0, 0, 15, 14, 0, 0, 7, 6] (by decide +kernel) ?_ (by decide +kernel) lb_1749
  intro w hw
  simp only [s_2262, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2292 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2292 : Nat → Nat → Option Nat := fun _ _ => none
def m_2292 : Nat := 0x5555555555555555
def s_2292 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_2292 : Nat := 0x115155511151555
def bds_2292 : List (Nat × List Nat × Nat × Nat) := [(m_2135, s_2135, 7, g_2135)]
theorem kn_2292 : KnownBin bds_2292 := by
  intro b hb
  simp only [bds_2292, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_2135
theorem sub_2292 : ∀ b ∈ bds_2292, m_2292 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2292, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2292 : ∀ b ∈ bds_2292, canon b.1 g_2292 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2292, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2292 : dagCheckRootsF m_2292 g_2292 bds_2292 (dagRefF 0 (dagTraceF m_2292 s_2292 7 f_2292) l_2292 0) s_2292 7 = true := by decide +kernel
def node_2292 : Nat → Bool := dagCheckNodeF m_2292 g_2292 bds_2292 0 (dagTraceF m_2292 s_2292 7 f_2292) l_2292
theorem nc_2292 : ∀ j, 0 ≤ j → j < 0 → node_2292 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2292 : LowerBin m_2292 s_2292 g_2292 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2292 sub_2292 gl_2292 rc_2292 nc_2292

def f_2293 : Nat → Nat × Nat := unpackIndexedForestF (pagedUnpackF 23 7 (fun p => (pickBlockF p 9 (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0x6e0ba0dc1381b82683704c06e08a0dc0f81e02603c04406e07a0dc0f01d02603a04406e06a0dc0b81c02203803406e05a0dc0740082903625000209e0bcd78179a903412805e4920bc9041791c82f15e05e2a40c44f0178a482f14105f2a00bc1480082702b15c05b0980ac1301582202b03c0560580ac0700082582a24000208e0a413013caa02783c04f05800410c1342201d45e03a8a40941100e92f01d2520468a008c9400e8a901d05e0410980820f01041601d05203a09c0741340e81f01d02e03a05a0740740082101c24000207e06c4e00a5a7014b420294bc0529480a527014a420292bc0525480b4a60149390292620545400a42900103e02129804c0f00842e0108540210780420b00840e00103b01f4600040dc0741e00d14401a0780340b00081980c0440036bc006d4805422001a5e0034a4022d40045280019520030bc0181300301e00602c0030a40061380242e00184200307c0060f400c1700182d00303a0040c80040980001f 0xff0981f91503f01c07e0340026861f0d243e12487c0450024bc00494c3cd27079a3e0f32540049483a9af0752490ea4821dc0903a91c8760260ea4701d40d40092707324c0e64881cc8f0009258012430d88bc1c4110362290700440d869a1ba930374a006c3450d84bc1b09483611f06c12a00248419ed3833da1067a5e0d306819e9383441b067a4c0cf04a0048f832d2e065a540cb4780048ec0091985d35e0c7068174d483141a05d34a0c24981845002e9a305d25e0ba4a41749382f49805e3440ba4841744a80091905c04409f8a216c0d027da884fa510b249c1648f827d28057b5c0af47013e9382b422055c500ab4a013e9082a12e05424c09f47c14c0d0291a805225009f46413e4b42812005023009f24a0045482713004e1600020be124d24249248491510972501244f82489904a13c09225c1244880082f04585c08b0a811613022c2204583c08b05800414c22412043a380870680dc9381b9210420340824981040901b91f037232) (pickBlockF p 3 0x17d2842fcd405f4290b702e1762782f40b05d82e0bb0541760982ec0b05b8158ba24016e04e2e40b05bc9a0b784c16f0582dc08c004118b5a5816b0a823b17c5a42208ec531664b02cc150475af8b203411d6a62c29205842208eb4f15e4702bc0d0475a58ada5015b0b823ad1c55e2a0ac34415706823ad0c54d270a9a3e15304c23a94851e2f0a3c5214769a29c93051da28a3a5e14b04828e948524120a3a3e14704c23a9084e5af09cb521396942849304e5a309ca5e13f0482729484f41a09ca4e13b6882729084e41308ea321346922689244d09909a12211d0bc2551784aa2909535e12a6a42549344b5a609524512a4722545484742708f35e11e6a423cd284952608f34611e4bc23c9484792709034411e48423c5484741f00081b1194b02321604642a00145f11609022c11000a298892581120b0224150009af88783810f068004d4c42d2408584810b088004d3c41d1c083838107068004d2c409280811501020b8204140009a387f940 0x1ff0483e69447f12e0fe24c1f34723f40d07e1a80fc2501f34623e64f47d1a00fa2301f326a2dc5487c1b00f816016e0be3ccd24799288f61281e647c3cc8c8798a48f413c1e62523cc4845b82f0ef85c1df0a83be13077c1e0ef8341df0582dc14c774120eda381db068384d38709a10ec0341d64983ac0907091c8e12311c20ba384138708268e104c1c208a3840f8734220e103d1c205c392130724220e102d1c2058388130710220e203c1c204a3840745b8290e035016e09e364d786c9a90d925e1b24a43744a06c9248d92411b72783645246c8a08d91391b34a03641485b8270d515c1aa09835c1306a81e0d50341aa0583540705b8258d434016e08e34c13068caa0d184c1a30582dc10c684220c745e18e8a433c110639af0c735219a8a0334d40638a90c705e19509832a0f0654160c705218e09c31c1346381f0c703d18e05c31c0745b8210c634016e05e2fad785f5a90c423817d49c2fa908615260bea3e17d4642fa5785f4a90be94e)) (pickBlockF p 6 (pickBlockF p 5 0x27e28a4fc4e49c4271393522724bc4e49489c92513c14c27248c4e45789c8a913914e2734884e45089c41700082b26d6b04da1609b42a0b745f26a0904d41105ba299333492664924cc1145b9af0b735326169c4c28e49849d0b735225a6bc4bc0909691c92e02625a4704b40d45b9a712b34c2564704ac8d05b9a58b734324d8bc4a411093629126b5e24d6a449a8e49349d0b73422496b04921609242a0b725f24605048c0905b9299203502406904801209052012004416e49e4771708ed2611d82823b0482dc92c8cda811c34c23368046cd008cca811985c2330a02dc91c8b22e11794022f098458d508b01411602416e486452d708a5aa0b723f21f69c43ed0887d2f11203421f49c4440d887d2610fa3e21f04a2dc8e45b91990735e21b06841cd488641a10734a21649842c500839a310725e20e4a441c9388449810834420e48441c4a85b9189060441f38a23e6d44821a71042391f36a040ad708151c0f9b4e203088403140805a80f9b42 0x2c20a45fd140b081f97845e2f08a45f44e0bc1a71783422f04bc5e0948bd4a61781392f02625e04a4bc6281780522c207c5d2530ba42e17603c2e90785d20d0ba41616103b2e76a05840dcb941e1711442e20b85c40b0b08199703502c205e5a3178b462916e2382d149c5a2908b6526168a3e2d14645a2578b44a916893e2d12645a5140b442916102e2ca278594170b341616504c2ca0885940b0b08159642502c204e58c0b0b0c9a16185c2c305858408c0041995fb582bf0a84e317caf422138c532b969c5728e4ae41b138b522b08bc561148ac1af15a0342b06a4564090ac11c95803627168455ad60ab42a138a5f2ab0484e294ca9da8153b482a70884e293ca912615202427149653ed40a85a614fb4029f0b84e291ca6daa14e24429b0484e290ca35af146b5228d69452c930a35a3146a5e29304851a948a441a146a4e28f68851a908a3413138a312886925108c8a20a49441212710bc4fd1789fa2913f35e27e6a44fc9489f8a694034c) (pickBlockF p 7 0x3794bc6fc0d0de5271be0363794986f28f8de4129612492c24866e0d78dd41a1b83523704bc6e0948dc1271b812a2c24826d3140da5ae1b4a583690706d4d00da41a16123f3628b06c4d40d892e1b10283634806c4090b091d9abc5035f6986aed40d75261aba5035a6806b4900d5ca01ab84c3570805848dcd322c1a63583522606a40f0d31a21a813034f688698940d30141a60242c2466663144d21a49a42493318a068c0d0cc5a89a1b5c343470662d24d042219fc5033f6a0662d04cf412198a5133a4b8674930cc52499c0343366a066c940cc52099894d332680664900cc4a296115232e8c065c580b082f9923513244926544a0c911c99223132429264c4f0c909c9921312c20bc63a170c742618e84431d07863a0d0c741616105331b0486328e0c641a18034930068262c0d0c512618a024300492600904c002e98004e30009a6000f8c001e98003c30b0986000d4c001718383c3070686000b4c001618104c3020786040d0c001298001d (pickBlockF p 8 0x10867f8d24ff1249fe0463af8a47f3160fe42a1d7b5f3f706875ed4cfba2f1f74523ee6bc7e40d0fb9a91f80243ee4727dc0d8ebda09f5c583eb0a875e97cfa4121d7a533e06bc7c0d48f812f1f20243e04a47c40d0f81271f00263af4827b9140f71ae1ee0343af47e7b0d40f612e1ec0243af4767a3140f55a61e8b503d34987a2940f44261d7a373cb68879cd10f2d281e62343cb04875e8ccf19249e32313c629278c4c4ebc2f1de4523bc6bc778d48ef12f1de2523bc27a77c8f0ef09a9de1293af07c761148ec12f1d82523b047476c4f0ec11b1d815e3b02a47604f8ec51a1d81323af05c0020eceada49d5a493ab08a585178b0a299d33493a649274c528b0a291d14583a20b0744150b09af9cf83839f068584d4ce71241ce2442c269e728d78e51a71cc02439447272c098e511c1ca0352c2692584d0ce2e2f1c804438b8a4716d78e2da91c5a3938b274584d04e1e2c1c38583870a858497ce10141c20242c24a6702d20e05a216124f 0x47848a8fc4a11e11ca3e23447829a8f05151e49e23c13940009c8e65711cc3623982c47303880012d1ae30235b5c46f8a08d6d411ad2e23645046b4a080011d19da0233a404670988b85511703622e04c4632608c41111702222e03c45f4608bc1111701a22e02c4000868b51810001fa2c12444d69489ad191549c226a4e45368889a9091452222693d44d26a89c53113494a0003e4482988901b11201622401c400076881161102282224504406c0880931105a822024040006e878d010f11821e03c4302888601b10c02e21ba3043724086c0d10c02a21803c4334608640d10c01a21802c40006685cd8100017a1613441f49483e9190a4a220fa3a41f46c84c8e107ca721224441f28484493107c9f21023441f2648000b90689e20d06c41a05883407100015a093584126a0824d21049a0209b5041368082498100013a0724040e46081c0b10049a20086c4010b88124c1024902040244010a88021310109820212040304880211100416200023)))) (pickBlockF p 14 (pickBlockF p 11 (pickBlockF p 10 0x40069e9ed5813d9b627e4504f64709ec8d13e62827b1384f60709ec0d1001a5a785604f02a09e01713c41627805040068e9bf58137e302754504ea2809d410137e2a26fb604df0709cad01394182703444e24609c40813851a2701204df068800d0d36d2f26da4e4db25480094534636268b484d16889acd213453026a2504d12909a21213442220024f4c7ac098e9b133628263a4c4c748899514131c942638284c704880092d306b02609504c10b89840f1304282002474b0ac0960d812ee2825d9404bb080960d512c1302580284b668096c0c12c522259a304b30409648d12c49825802440048694cdb1299ae2533544ab6b894c9812a5282531384a607094c0d10011fa4e46049c4d8944d412712e24e25449f6a09384a12701424e02440047692d181258a024b04c49709892c1010011ba42c604856c0920d412409824803048568890a98121414245a4048b04090c8d12211824402048746890c50121412200233483ac080013d2049a23c24d 0x51229ead2d795a5a92be2445694bcad29495e5222b4a49569482ad28e95d5222b495e5692a4ae45115a4a4ab4941569274ad65095ac952b592856b022ad24915a41ca8914e567278abed1157d2e2b214c55f298ac453157c9e2b023455f258a2452d5751a28914755a498ab45315362a2aba4c557298a9ad515549e2a6b44552468aa45315352a2a824454d298a9cd115349e2891435218bca43149485af290b52545684a8a4f551418a90b44543468a42979505a02a03445214a4a72d094e52729e340539484a724f54e418a90a4453269ca64d094d5a029924253225aa640854851a29095e52f030a425494b49229094e52b468a425354a4a229093e527488a424f5495a229092e523688a424b54840ca8914251e260a3c0c1475a228901b5166bca2cd494592f28b2525160bca2c1394480ca8a03c513688a2404c00491a8734950e492a1c52900228a8535e50a472a144e9001a8a8046c5006c0a0cd41401242802445036a0a0052140024280044) (pickBlockF p 12 0x5f727abf8d397f1a12fe1325f7278bf08f17e0a62fc13c5f7242be25097c9a12f92425f20bcbe41397c4188009275ee2b0bdc55144a2faf4b485e9490bd25217a4a22894535e628abcc125449af2893535e1474bc28d97841ca89352512696bb9149771af2ee039512694baf14975ca6aeb94c5d7082a24d19449a1ae823a5d3278ba08d9740a2ae80495124bca2494d7351a2e334a5ca8a0b94531719a32e323d5c646ab8c0a54492928924b5be8a4b7cd797051a2df3525be4bcb7c0a5449252d8c525b14bcb751416c5292dc24c5b1462b625356cca72d99425b3242b625316c420a892465ae498b5c5316b62a2892435aa290b54511675a7ad423859d686b4ad0569414acea425a049cb408f56811aad002959d25ab3c13967410a892345976c0b2e981661282cc240597468a2457d649a4ac92515922a2b24125448af2c813c58d688b1a5316349e2891535852bab0a5396149f2c293d58525cb0a4b56140ca891525806b0b009616051c2c0234 (pickBlockF p 13 0x678294cfc8e19e5a733cb426794a4cf21799e42733c02900125ecea9619d4aa31345f672690ce451189a29b3793666f072c4cd499ae29335b5e66b072c4cd299a4a63132536664a4ccc8e18992733194c663278c4c92d9849a33014c626486cb51799752232d45265a6a4cb44f589921329b496532a2cac4a194c9f329932653092c4c5799262f324c526496bcc92d499351a324a52649292c925059241cb1314e63869ec8c8e18e1a1b21a36643052c7090990127320029638474c7c4f18e0a1b1c13b63b278c704cd8e01db1c033626298c6c50d898a231735262e694c5c9498b92531715e62e2a4c5c06589897313b5262b470c4e93989d2131385e62709cc4c06400495b10358623478c409618849e3101585f18bec3cd217c629b0d45161a49cc340a57c5a930a45e6148a4c289798512930a0295f1684c0f17981e293084506076a4c0e8f5831a7306342607478c108f1820a630413c607244be29097de2f2fbc526038a0beed498051e2fba42 0x6fc27cdf84b9bf096b7e0196c22a4df1171be52637c2546c227edec911b962f372c526f3468dcad39b95a1372a5e6e54a4ddc511b94af3729526e8684dd04f5ba09e3740316e5288dca4a9b9414b6113e6e2298dc44b1b79aa36f24c6df278dbc4f1b089db6e2546c226edb2931b64a6368c546d7298da2d51b512236a13c6d1488da4d11b449e3611336ce280d9c101b35aa36101b6c68bcd8d149b192f3632526c60bcd8c0f9b080cb6204c6c36a8d8404c00499b5fb586bf4a8cf117daf12235e1486788a6d744a19e1a9b5c13867869cd6a931ad49433c34b6b3248d644a19e1a1b56c5e6af688d5b149ab49533c3426a6692d4c945aa49435323e6a6464d4c1259e12f34f45e69e8a4d3cd79a79a934f24969e482d3c0e59e127349b4f69b270d26d0da6494349a43693476d2c4b1a4d19b4983b693066cf0931a4521b3c24468769cd0ed09a349a343a4e68b26cd0e931a1c92b4424c687032cf0549a022934024c683278d00579a0526340019))) (pickBlockF p 16 (pickBlockF p 15 0x77f286ee64d1de2293bc34d7784a4ef0579de0a93bc01977325cee9149dd02f3ba03e7730320024eddc11cbb803974f8a4ed5161db5a63b535876b298ed4561d3d2fbb3d607674b8e9e94dd85af3b0b527614bcec2949d8414ba7a417548a4ea8d79d76283aa35275449aeb2939d65213aa24c755498eaa531d549e3aa12274f462ea0d05d402f3a803e74f0820024ddd30a2ba60496c28bcd8514dd1d253a3a46747092d85149d10ac3a21546c26bee7ed71cfd1c39f93873f268d84d4db09a7b9d45e73a6a4e74125b09a6b9ac5273529ae6a531cd420b613456c2686e5c8f5cc49e39723572e28ae5c125b092f36125372b488e48d35ca22839414c72468ae48935c9122b920296c24a4e440e5c51a138f94871f288e2893dc722838e24c714486e2ed39c5d1d38ba36717072e284f5c542738a0316c2488e1d181c3930387b5070f680e1c911b08afb84b51709492e12545c2424b6115e707298e08d51c10ae38213c6c22a6df8575bf0a737e14d 0x7fe2a8ffc4f1fb89dbf71377fb278ff2911fe49e3f71337ee036fea139fd41f3f70197ef0b8fde151fbc263f78447ef078fdc04c004a1bf61387ac8a6fd0d45fa124bf40497ac6bcfcb161f95aa3d625f7e2488fc44a1eb129bf01387ac49efb7179f6d1f3ee34e7db250f58925f649a3ec1287ac486fa5179f49af3ea3447d26a4fa44a9eb120be535e7ca6a4f94d39f29a13e525e7ca4a4f940a5eb11cbe41387c0686f8093df14943e02437c3258f808cdf0015be00237ac470f7c90deb11a3da2497b4482f74491ed11cbdc1267b4470f684d5ed51c3da0197ac2a4f648e1eb5a4bd6b417ad4a4f5a179eb41f3d603900127ef52519ea424bb9c527a64b0f4c551dcdafbd1b5c7a3268ee6d4de7e2f3cfb5279f092ee6d35e74ae3b9a53799492f32545e6424bb995e797488f23149e45af3c8b527914bcf22949e4414bb993e78e46af1c0e5e05a13c0a4f78b498f0290de21a73c403978147af0c531e04a1bc092b781246f020ade0411bb993c) (pickBlockF p 17 0x87d47b0fa4a61f414c2825287b4990f515214097c3c14c8768a90ec8f214095c3a1448678bd0cf14a1c4a2433b5e8676a50d4d0a1a89ec3513c86a25d0d40c619da243395e8670330a04a61962a4281278632990bf152181a243012c85f4690a048e170a042e04085b8a90a00ae1522f42a4528546bd0a8d4a1502f42a02e8500530a41321462a42802300146709a8e61341cc18b4984a49d0940a60c524c234588466a908c4e20c51fc213588424a90844a20c51dc1dc5883f699076d620f52641da5883b2810628de0d5a241c3448354b106c8d20d52a418a3383209d0640fa0c42480094f82d49105a5220b4a23f734f8294710524e20a49a3f734b824ac1048942090ae4121507ee68f043142084a640f45481e27103c4d1fb9a1bf714f81b25102e92605d20c0ba39817072fdc53a0452e40a14c8112990225120449e3f714b7ee28f01c5320312a40613c7ee286fdc4fe0249c40234e80468500893a011214020297ee27cffc9320049e3ff15c (pickBlockF p 18 0x8ff04600290e3f51c46fc538f96a31f25263e424c6fb5e8f646b1ec0a637d2947a1348f16a51e257a3c40cc6f9398ef4711ccd0e3b092c760298e64851cc53e398a1c731338e60371cc04e37c9c4723438df2691c0d4a3802f47002e8df0720028fe3712346e0498b98a51b49722e5a9c6b2518d62931ac1262e52f4684528d06a51a097a341294680298b947d19c51232e2946595e8cb0331724a63209ac640398c068518c93230121c6014f8c028718048e3000dc600138b925117c90e2e49245d4528ba0bd1740ba2e414800a3b8b627316c0e62be2945995e8b303315e5062c02f45802e8af0820028de2b122c560498508bd0a114e29da5453b468a70930a114a29122c520498506bd0a0d4e27da6c4fb4589f0730a0d4a2741cc4ab4289869d1304ea2609b44c03989547b12c13a25418c2834488f8c111ed82241a844834088f6890a097e229a8c4525188a2931141261412f44424c8858a910a9722152642825387d4bb0fa93a1f526c3ea3e 0x9622532c40a656d24caf93e95f0332b65265701f4ae02e95b092002d3e55dae4ab9389572692648fe5549c4aa34c9324772a24a654414c9923993246f29c8f2531a24a625c932467290d725211c4a423493227f28c8e25152649913b94227d2840664c89cc9913793f27927a9124f4ae4991339320772720fa4e4174990399330b92660f24cc1a49982c9330492640cc005a1c9793992f073250d264b0a749601992829325213a4a41749404900149f1fe93e4909cc920398ff49d23cd724792649024c91e25123c4923fd25c7fa4791b499232d524652647fa439154b922a9524552647f92f9134992248f23fc95c8794e90f0331fe4a63fc93c8612c90a4692145323fc91c7f82b90609d20c0ba3fc14c8005c9000a920013240016480024))))))) 11
def l_2293 : Nat → Nat → Option Nat := unpackIndexedLinksF
  (pagedUnpackF 19 7 (fun p => (pickBlockF p 9 (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0x6c800d7081ae0034c4069800d3001a6003442068800d1001a2003344066800cd0019a0032c2065800b948172002d8305a820b50016a002d0105a000b400168002cc1059800b204164002c80058820a434144102880050820a1001420028400508009b1813600260304c000970412e0025c00498809300124082441048800900411e0823c00478008d0811a0023400468008d001141822800450008a001140022800450007c380f8001e4303c80078040f0001dc103b80077000ee001dc003b02076000ea081d4003a80074040ce68194203280064040c800190003200064000bc30178002d8605b000b408168002d00056100ac00154102a02054000a608148102900052000a010140002800050000a00013430268004d000980813000260004c0009800130001f1c01a90002c80001 0xd4861a9003520067ca0cf8019f0033e0066070ca86194043260864c00c4161870430c0861800c3001850430a0060440c080177282ec085d800bb00170182da185b400b60216a082d4005a410b480168042ca1859400b202164002c800558e0aa82155002a80855000a9821530029e2053c00a2941440428800510009f0c13b0c276004e8109c041380026e084dc009b021330c266004c810990013200262084c01098001223824208474408e021181023000460008c00110202200044000870410e0021a0843400858410b002160042420848010804210004182083001060020c00410207a9e0f5001ea003c83079000f2001e4003c80078820f1001e2003c01078000e6281cc003980073000e6001cc00398006f8e0df001bc08378006e040dc001b80036c106d800d9081b2003640) (pickBlockF p 3 0x153002a50452e70a54214a802940452800a50014a0028e1851c00a2c31458028a0451400a28014308262904c400988012f0825e004b228964012c80255104aa009405128002500049820930012600248104900092001208e23e0c47c008f4111c8823900472008e401190e23200464008c801190023008460008c001178222f0045c088b8011196223004460088c01118022108442008840110022200043e0887c010f0221e004265884c010980213004260083461068020d0041a0083401068020d004161082c0105802012840200804010080201003fe107fc00ff801ff003fe007f810ff001f4283cc7079800f3001e6003c22878400ef841d7203ae0075c00eb801d2143a40074020e4101c70438e0071810e00c1bf0437e006f810dc0c1b80036a186d010da001ad1c358086b00 0x19e0833c0067800ce8219d003390467200cdc219b803370066e00cd421931e3260064c00c8c3191803230064600c881191003220064400c841190803172862e00c5c018b803170062e00c5c01880e3100061e08c3c01868430d0061a00c3011860030a0861400c280185003080861000c104182003040060410c080181003020060010c000180003000060000bf0417e002ea485d400b9c3173022e6005cc00b941172802e4045c800b900171822e3005c600b8c0171022d5345a610b4c0169802d2045a400b480169002cc1859800b243164802c80459000b200162082c40058608b081161002c10458008b000160002be0857c00af8015f002be0057618aec015d802bb0057600aec015d802ad3855a00aa83155002a90455200aa01154002a80054e08a9c0153022a60054c00a980)) (pickBlockF p 6 (pickBlockF p 5 0x21e8043328866010cc02198043300866010c422188043100862010c40218024252c82e7105c020b80417008242904802080440820810010200204004011c7fc18ff411fe023fc007e258fc011f8003ef047de00fac41f5803e1287c200f8011f0003da187ae18f5c01eb023d4087a800f4c11e9803d30078a70f1401e2803c50078028f0001df043b62076a08ed011da003b40076608eb461d6023ab0475600ea811d20c3a40074800e8431d00239d0c73808e7001ca8e3950072808e5001c8863910072200e1ca1c3023860070030dfc11bf8037e046fc00df411be80379106f200de401b79436c0c6d800dac11b484369006d008da001b3823640c6c800d8c11b180363006c408d8411b080353386a408d3841a70034e0069c00d1881a3003460068810d1001a1823430068210d001 0x283005030ca060140812810050104a0201400128000500009fe093fc027f804ff009fc093c0e277044ee009dc013b41276804ed009ce3139c0272064e4009c60938c0271804df109be01370326e004db049b601368126d004da009b209364026c024d8009b001360026c004d7049927131c2263804c70098c093180263004c018980012f4325e804bc04978012f0025c084949092801250024808490009162922c02458048b0090839210024200484009080120c12418048204904011dcb23b80477008e6211cc02370a46e008dc011b802350846a008d401198423300466008c811190022e8e45a0c8b401164122a88455008aa01154022a80453088a60114c022902452008a2091440228024500088a591140222804450088a010fc621f8043f0087e010fc021f8043f0087e010f42) (pickBlockF p 7 0x2e5005c904b920171442e2805c500b76516e032dc005b704b6a116d402da025b400b6801698e2d2825a404b460968c02d1805a204b383166c12cd0259904b320166402cc0259218b240164802c78658f00b181962c12c5025870cb0c0961802bf8e57f00afe015f812bf0057b0caf6015e812bc8257900af2015bca2b78056f00ade0159c82b30256210ac40158802b00456000abe0957c02ae8455c04ab02156002ac0055608aac0155412aa8055308aa60154c02a98055108a847950802a10053f0ca7e014fc029f8053e04a7c014f8029f0053d04a7a014cca2998053300a66014cc02998053300a58394b002958252b00a52114a402948052804a500149822930052600a4c0149022920052208a4401488028f0851e00a3c01478028e0451c00a3801470028e0051810a30014192 (pickBlockF p 8 0x358806b100d6201aa87355006aa00d4c21a9803508a6a100d4201a840350806a004d4001a7c134f806942cd2801a5003480869000d1629a2c03458068b00d1601a2813450068904d12019f8b33f0067e00cfc019e8433d0067a00cf4019d8433b0067600ce8119d003390467200cd6399a033340066704cce0199813310866200cc40198803310065c18cb801970032e0065c00cb801970032e0065a08cb40193cb3278064f00c9e0193c03278064d08c9a0193403268064d00c9809904b3199c63300c66018cc03160e6290cc500989c13138061c2cc3801870030e0061714c2e0185423069060c04c180181863028260500c0a0181013020060010c00017d8a2f9865f300be4097c022f8005ef04bde017bc02f09c5e100bc20178402ee0a5dc00bb41174882e8825d100b96317281 0x3d8807af08f5e01eb423d5847ab00f5211e78b3ce8279d00f3a01e6c23cb8879508f2a01e5403c90679200f2401e3c33c39078508f0611e0c03bf0a77e00efc01df803be0477a08ef401de803bc0477608eec01db883b70076a10ed401da023b30476600ec811d9003b18276300ec211d7c23af8075d08ea459d4413a88075100e9e11d2c43a5807480ce9001d1823a30074600e8619cec839c8473708e6e01cc853990073200e6401cc803980472e08e5c01cb803960472a08e5401c8883910071e10e3c01c70238d0471a00e3011c58238b0071408e2801c4c13898071108e2201c4013829670404e0801c100381046fe10dfc01bec337d806f80cdf001be0037b046ee20dd811ba82375006e514dca01b940372806e500dc611b842370806e100dc201b7c236e846dd00daa41ac64)))) (pickBlockF p 14 (pickBlockF p 11 (pickBlockF p 10 0x45d048b905172022d8345a828b5011680a2cc1459808a9291500a29c1453808a70114a12278744e0489a091320a260144b82892151201224004478288e05114222280445008880910e0a214243c1a877050ec0a1d804339e866050c61a188143100860090c00217c142f0285e010a8521482428828510109c1a13414268084c050960a12c0420948400507e0a0fc041f8083d0906c3a0d0241904831050600a0bc14150a828090500209c141302822110440208804100481f0503a12040d4078280c0d0160a02c040484809010100a01c1403807fd28ff611fe813fd007f70cfec09fd803fa827f404fe801fa8a3f4827e804fd001fa003f3047df1cfba11f6c23ed027d904fb009f4c53e8847d100fa009f3c13e5887cb00f9601f2423e4027c608f7269ee403da887b500f6611ec42 0x4e0809c1013820270014e0009c00137c126f804df009be0137a0a6f404de809bb09376026ec04dd809bb01376026ec04da8c9b501340aa68004cf0499b0d3360266814cd00999053320266014c98a9910931c1a63804c70098b0d3160262c04c4069880130a1a61404c280983093060260814c100981052f43a5e414bc02977052ec0a5d414ba80974052d64a5ac04b50296a012d20a5a014b382967012ce0259814b300965052b84a57004ad8295b012b40a56804ac82950252a00254004a78294f0129c0a53804a68294d012980a53004a58294b012940a52804a48294901260ca4c004980092e09254224a804950092a01254024a804950091e3123c02474148c888f1a11e00a3bc1477808e03d1be0a378146f008cf3d19c0a3302466008c90d1900a3200463828c60518c022f0a) (pickBlockF p 12 0x57600aec015d802b98657300ae6015cc02b8c356c16ad6095a812b4c156980aca2557e5aaf8155e82ab91157202ae4055c80ab90155e52abc055780aa52954612a8c055180aa30152a72a48354900a920152402a24954384a8605500329f8253996a6f114de029bc053684a6d014da0298ca53084a61014c00a97c152f80a5c0d4b802970052e00a4e394961a92c052580a4b014940a928052500a412547e128f4251e02a390d472028dc251b02a360146c028d805180ca2e094465a88c051180a210943a22874050e80a1a0d4340285c350b02a160141c42838050700a0e0141c02820650400a00213dc927b804f7009ee013dc027b024f4089e8013d0027a004f4009dd2d3ba0277014ee009dc013b02276004ec009d8013b00276004ec009d8013947272414e4029c80138c127045 (pickBlockF p 13 0x60480c08058100301c160380c07017f85afa145f400be8017c822f8c15f102bdc197b802f6c15e894bd00579e0af3815e38ebc60578032efc15de84bb61d76c02ed805d88abb10175e12eb035d600bac017560aeac05d502ba12574202e8405d080ba00574002e8005ca96b95017280ae5005ca00b94017260ae4c05c902b92017067ae0c05c180b820570402e0805bf08b7e016fc02df025be00b7b056f602dec05bd02b7a016f20adb4c5b680b6a0d6d402da805b500b6a016d402da805b500b5e316ba0ad7405ae02b5c016b802d7005a896b3d5167a02cf4059d84b3b0167212cc8759882b2a1d64e1ac9c059302b1d2563a02c74058e80b1d0163a02c54858984b100d61e0ac34258602b0c0161802c18658300b060160c02c0c357c16af6095e61abc8157804af0015da1abb01 0x68e00d1c01a3803438e68682d0d01a1613418568300d0505a0a03414068184d0301a060340c068180d0205a0403408068100d0201a04033f0667e00cfc019ceab39c067380ce5099c41b388067082cdc159b41335c366b80cd7019a81b350066886cd1019a203338366700ccd0598c3b318066300cc40998023300066000cc00198003300066000cb431968032cc165788c87a190e0321c064188c82059020b1ec663d02c74198e4131ac763580c6b018cc2b198063204c610d8c203184063002c5f058ac4b158062b00c56018aa0b154062a80c4a2d89403124162480c490189203120162400c393d872030e4061c02c380186e0b0dc061b80c360586c030d4161498c290184c1b094161280c25018480b090061008c20018400307c160a94c140582413048060882c11018200b0247))) (pickBlockF p 16 (pickBlockF p 15 0x72d06e5a01cb403968072d00e5a01cb403938c72682e4d01c9a03908b71728e2e01c5a0b890971200e2401c4413888071004e191dc2c1b85417070ee0e01c1c03838070700e0e01c0c43810270104e0105bfc1b7f416fe80dfd01bee337dc06fb80df701be81b7a4b6f384de605bcc0377496e916dd201ba403720a6e304dc601b8c0371806dc1cdb705b6c0b6c846d900db201b64036c806d414da50db4a0369406d280d9c25b341366416c98cd9109b0c5b60846c100d8201b001360006c000d7629ae8135d006b982d7205ae4035bc36b780d6f01ade03584e6b080d5921ab20356406ab06d5505aaa0354836a900d5201aa40354806a60cd4c01a88434c9269900d3201a64034c8069804d2c11a58034b0069600d2c01a425b484069002d2001a4003470468e00d1c01a38034700 0x7c980f8d19f141be2807c482f8901f0a23e0837c100f8201eec63dd807bb00f7601eec03dd807b78ef4b91e940bd1067a200f4401e8803ce4b79c80f3901e6a23cd0179982f2d19e5a03ca0579382f2701e4e03c94278f0ef1e01e3813c64378c80f1901e3203c60178b82f0e25e1c03c34178680f0c05e1803c30078600efd3ddfa03bf0177e00efc01df60bbec077d02efa01df20bbb4c77680eea0ddd20bba4077480ee805dd003b90477200ee401dc60bb64a76c80ed805db003b5c176b80ed701d985bae1475c00eb705d5a53ab4075680ea911d500ba9c17508cea005d3e0ba78174b8ee9605d2033a40074800e9001d0a5ba14074202e8401d060ba0c074180e8301ce87b9d0073a00e7011ce0039c0073782e6f01cde039b4273680e6c05cd8039a8273500e6905cba639740) (pickBlockF p 17 0x865010ca02178742f0085d050b51616a042cc2858070ab16156042a81855010aa021520c2a40854810a902152042a40854810a31a1460428c08472b08c0a1121c2240843070860210c04208483d8f07b020f6041e4283a89075020ea041d4083a81075020ea041a4c83481068060c8240f2881e0103c020625c0c40818810262e04c04098081301022120440408808110101e1203c04078080e0501c020341406808098f0100e0200403c18078100e060142402808050100221fe873fcc17f980ff205fd833fac17f580fea05fc833f8437f080fe005fc003f6477ec02fd801faa1bf5407ea80fcb29f901bf2007e382fc701f8e03f1817dc9afb709f6e03ed817db00fb601f6033eb437d680fac05f5803ea047d286fa501f480be9007d200fa401f460be58d7ca04f9401f260be4c0 (pickBlockF p 18 0x91cc923806464348c80919012320244e5c89c09130321c2a4380486c190d8121b024187c83009058320b024160481c49038120606408148100901831f7323ee047d038f9831f3023e6047a0b8ea291d4023a60c724a8e4031c21a3840470808e1011b72e36e046dc08db811b70236e046acc8d5811aa06354046a808cd9f19b023360465c48cb811960632c0465418c985193023240c618c8c3011830e3040c60808c1011772e2c6a458c08b103159262b20456408a891150062a00451c989e1713c02278044c8a8980513002260044c008911d1220224404460a88b051160222c0445808841d108022004440008800110002200043e8687d010f2221c0943800870010e0021c004378286d090da021b404368086d010cf2e19e043381867010ce02194243280865010ca02194043280 0x4e4c09c9813873270e04e1c09bd9937b026f604dcc89b29d365026c80cd9009af0d35e026b814d6439ac813580669474d1c39a3813460668c04d0849a1013410668204cec699d813390a66c1ccd8099a833273a6481cc900991833230263e24c70398e0131c0262064c400988013100262004c4009848f2e5925ca04b94096d172da025b404b38c967012ce0258c44ae0e95a872b5025680ca9cd952852a50254a04a9019520129e1a5361ca6c094d0329a0252c24a54194a812950251e34a3c09468528a0e51404a24193d9d2780e4f0049dc193b81273124e01c9c0093801264324c804990093201264024c8049747)))))))
  (pagedUnpackF 23 7 (fun p => (pickBlockF p 20 (pickBlockF p 10 (pickBlockF p 5 (pickBlockF p 2 (pickBlockF p 1 0x80640780b80ec1681d01d03848004e1200182001b13800d4900541400b4a601515003569c068d080cd2f01925203149c0609080851f00323d02f2bc05c5480b09c8159310290a404c1300741a01303c02729804a1700902a01183c02205804207007d1800384c01c06003a0f0018a600e14401b0780340b006022009150015088022540049a8008a5000e09801a0f00301600485c0176bc02cd480512f009a520102a401e17802c2900504e00808400e0f80181e80282e00405a0060744622f88ac531116be21cd4c429a788334b10168e1f6d0c3dd2f07b2530f24a41d2938395258722430d748419c8f83291d864a330b946413c54826c2f84885e08a0a60da1481ac2782e84e0550960a611c1382181c84203707e0500f80801d80f0370190660040ca569a7c98b4392749f1fc90e3791fc5c23b8ae46f09e8ce0c0a7bf69437ab27eee44edd389bb6093367725ec4a4ad7c093a889233ff08675c0ecb041993802b16d04623806c0040980001f 0xae49c15490829d1f051a320a225a13e4942702e82f04e0450840520f80401904ea6009c2c00fe18025c9404a13c07f8ba134d241a5a084ca490324821305442589f04a93209325c1244881fcb604805c08f0a811c1302342204603c08b0581120902211c0438340840681069302081203c83c0750680861301e01e03a0340710580f21301e02203a84c07408801a0f01c01603884407006810c93821521040a3e0804640fe1741f82703e84d07c0980f61141002103d03e07707a0ec0f01cc1a80583207205c0de0b41b80e83625005c0b007c14010da403412805f0a00c44f017ca803535e0696a40acd380f9a6833a490664820ca8e40c11883215e0632a40c2524180a082f0520520880b60f016c2602e15c05a0980b21101601e02b82c0560380a89000fc2e02884005209807c570144aa02803c04f05809a11011ca80250440462a008f1401192802184c0420780820b01322f025c520494bc090948114a902205e0400a407e1380f82681e83e) (pickBlockF p 3 0xe669c1e09243bd20876a390eb47015c5482582f0430520ea06a0c41303a126073a440e64780ae4a01842e02b02804f2500c0170158100568400ac2a01c41103802205ea300de4981788c0374a00559500e38bc1c314837da686e3450db4bc1b49483651f05da320aa2a41b04a82542f04285206c09a0a811430d1a0549500d3068150508250270418420d106c1acd38355a106a25e0d249c1a093032d1f0539520930bc10214833c1281683c0cd4b819895032d1e01112802c0980420a00689401584c02104014c100294a80638340c506817a8c030d2605e2300c22801485402f49805e3440c86bc18cd48311a5060b460c04bc17e9482f92705da420a32a41744a82482f04005203807a03e0d42b4a00562500ab48008e1402e0220531300a54801488c00482005b0340b349c1569082c91f05223205f09c08c1080a81f0088320b06b815e8e02b4220564500ab4a01529702a1260530340a56a0148940285200502300b78a216ad442d128858a50 (pickBlockF p 4 0x120460240d104a1af093b52126694248d1848d2f09125212149c23e908478a901082116a8be2d114c595af8b1b5316069e2bad2c569a38ab3431524a428c9084e11909985e12909c23a0f846d2c071a4011a0b0232150130200711400b80a01c29403692005b96004b0a00d213045c2408b044040080228960321180898581120a802e0c031c9805b0500c648017e8c02d4b000b0400320782200e043c1a0058300360781c050037d28086a480d647821812042c2201a83c06809818a4c03c12e0622401094700ce1704201c0838341006801ba9003091807fa300fe68020a94037120060a301042a02061704082805ea300bc4602005003fc2607f4540ef4b81aa9302ed1803305c0340980600f03f41c07e0340080601f4d243e52487c04506407c0920c80bc1700a0220b42c01164a0260360599500b22a01ea9383692107a23e0bf4641625403cc9504e85d06309c0901080b81f0098320b02a01bc9103b81205794209709c1101083b013078b5e 0x2556964a8d0c931a112425f2454a647e93c8e92591924722b4864508fc8791c90ea3320d4623e45487bc2f8f285e1de0a63821486fc278d884e1a909634e11c688218c684218b05e2f80b85d4158b982716e0460040885b12c0a8a4016b0a8264130541280a52401310b825e1305a4220b3a581454602cc1504a01e0a224013e46024e1304881e0b203414f4a02c49204b82e0b08441434802be8e0498260af0341596802b8940535200a0a3015b0b82581304901e09da301200782b00d0561a20acc5413a46023e0f055c1a0aaa4e14a4842a88f84f91909504e11e07c2a60985392609da3014b0482920905462f0a845214f69a29ad145312f0a525214847c2748c84d42f0a38260e603c2849304ed1809f82413d068276d10515af0a2352143694282d185012f09f25213c49c2749084d02f09c8260cb03c26ed244bda089b24912248226a4c84d091096b4c1204602651784c62909835e12f6a425c9344b122895a3911f46225454815818892a4c))) (pickBlockF p 7 (pickBlockF p 6 0x1c609838a1107101e00602c1da69c3b2d087551c8ea2311d30ba3a4138744268e804c1cf08a3281087381f0e603d1cb05c3900b471c160e182500b044384074701a80d80581920a032ed206cc280dd1281b72783669406f9af0deb521aa69c324d346f12f0dda521b94923709046d8a48da9411b42722fe4c46c8290d30441ae05835c1306c0ae0d784c1ad0783580d06ac160d501c1a8680326170694200d304c1922b834a550690260d182c1a1088336540678220cd15019b8a0334d4065c260cb03c19505834117867e290ceb5e19c6a43325486602f0ca05219309c3241346441f0c803d18f05c0100886380e8c634017b0700080c05f8280c42381854980185205f9a80c535e1896a430e938619210c223e183464304578604a90c014e17f2840424b8010968be85201b0422f41305c8120bd02c17b2782f21705e02a0bb84c1760580420705d12000283c1710402e40b00109e0b89341700982de0b09b22f934c532656bc4c8d4c981a912cb4e 0x2174683fa5408901a0fe1421e809c3ae1088881b113b4e22668444a97888d27110a4c22047c3f654879c2f0ea85221f04a2de4a060c1e0108201fa0803f254086c1a10c83421146042e9308411810b1401f82a04224c0841a210e35e21a6a4430d28855a310a25e2134a442493883d210fb95220e2543cc178750290c603d17406a406900809a8100b4019b0a0418110825a7100b422084723f08c46cc270cd04217e05c024088819ae102a38203088405140805a80fd2301f96803f0900044180ff8241fd4b83f89307e81a0fcb501f84a03ead007d118105c5120a6a240ed40811a71003421fe4a23f68e47dd188fb13d1f326a3e01746c8270cc84217d05c0200887c5b00f81601d30c03d84a07a09e0e9c5d1ee69237ad047b5288f5a3e1ea4643d2524604a08f39291e62423a65b07902e0f18541e20983c20f07801a0ef82c1dd0483b88e076c1a0ec0341d74983ac090728160e302419709839a0f0724160e28241cd088388090728260e4844) (pickBlockF p 8 0x1df2703da1b0824a810415026369c49ed089891c909a312072a04c24e87c42e8dd84e19c0843120b80581110315025e04840a5087b0270ee04225c04c4bed78961a711f2492314824ba8e496d1c1021521eb0bc3b41489681a8dd04c2586984ae8e09591a0d59381b90b83540e068c9c0dc05c1aa060406100808a81290442012a04a71789462912835e24f6a44889348dd2292723920f4624005489349d0f505e1d90a43801346a022925b5821c4604941609242a00a02021b4603fe140869a0109a401fe2c00260c060416123828246048016080904220c402c241480488d4090da4113a3824209048011061c1611c2441b70984328c08fa2e10c34023d49836c1708f01411d8242386984208c08d8a0108a30236680460900859181179302396a046ed008b92010aa302352a04681708cc28108a302104604605008bc26118c5c22e6a844cd2083d200da85c1860782fe0b08b41411602400804030a0b08a9ae114b542206982ec4e00841c0c202c (pickBlockF p 9 0x2b56bc566d48aa5269502452b147251c8c4a282f15803625803c55cd60a651815685427b058530d00a492013d03c275058556090aa5a81543482810b854e110a5da0152a4c279078548090a85a6147a302a26a0540d00a752014aa3029f0b84fe1309dc16147a30273058538090a712214eb5428e4804e40b0a6c1214b24c28f460526090a441a147b442996bc530d48a5da514ab462944bc524948a41271472422880bc51a0988800f145b492836825148c8a24a493a941288242500d309cc9814345e2858a4508d78a0da914125228129a4fe5149f89c9391311aa0624f05309cc98139a4427c6a44f69789e92913ca4a27748c4ec5789d4a913a14e2722840460840840895f45f2bc8a6570d48abda115625f2aa4a654c93ca8d2594f24729a4865188c4a1c2f13e84e27105c4ded6094da013705826d0a8340100949201060502516a049ed0082cb00cf8501bd0984d61209a8220ca0402686924ce924998228de03e19d0643140b805c11105160 0x2f52985e3140bf22f17dc522f969c5f0d08bdd2f17b2521aa47c3208f4bd09c9799312f22525a6484bc0290d20312e50685d80b0bb01e17714c2ed0b85d60f0ba81a17482c1aa0385ced40644261720302e5078320530b90a217185c2e20585c0d40b3c1c01d8302d20a05b88e0b65260209482d28a05bd178b762916da4e2da4845b08f8b5d1916b15e2d52a45a84f8b4c9902b12e03b25a5a21481401096683c2c604859a0b0b3c9e16705c2cc098596110b281602b01c2c84a00780f0b141016302c03b27858a4d0b102e16182c3aa8bc75314ce96291d0b5f39e6a6736d3ce4da49c934338a68270c97ce0d299c024f3784926ee90cdbd209b423f3614766ac8dcd2d1999815232d0be646178c702997f8522fd07e5de0f8ba01d9730372e106631a0c8b7c1796802e2c905658e09cb081181c8222c06b056ed00afc2a14304c2b66a0566d00a142e14184c2bd088576d38acda115d239292462504138ae41b13e02e2b4068564090ade2f15b452)))) (pickBlockF p 15 (pickBlockF p 12 (pickBlockF p 11 0x3570806a08c0d3d201a99303520786a04c0d3da21aac583546b06a2d10d392817984c2d70785a60b0d34141a6024008040692d24cfda09a42493364825e20f866c1916902e047044682d00d022819fb5019a08068c0d0d11ae1a1a38341088681140cfda819c2403376a066c9401181819e82433b4b8674930ce01a19bb503364a0666d00cc9201a54513478a068ad44d09a499f34133c4a2672924cd52099a14d33128a65c174bc01f0cc8322d105c08a088cbe301971603110c06544a0c989e188c5d32c6a2656924bd920994a3932846264e524b54a09929393242626225b0c882e19084c32008863e0f0c781a18e82c31b0486348e0c641a18b034315498628090c2c1a182024308058606090c2c260cb03c307058604090c201e1838343040986060f0c081a02082c31869262ed04c4d249892413110ba620138c3c2698703e30d07a6180f0c281a8ca03230905c60c0b4c1416180825040044600074bfa281770481900805e2140be89c0cb248 0x39a6bc732d38d9d249aaa4139747272a8e0d08a919485e3180a47280d4b889c17c04c1aa060682100d00a81c804433f2a0723178e3e291c735e38d6a46dc934d79229c623934e46267c548e2c9d19405e3170a45fc134b9c229c4c58376480710160e1c2a02482037548067a140dd1a81b925033c2c00900c0b54161c2828384048080080b70161bd45c382690702d10b28a402b0482db058676540df81a19d14232609c62a108df01b1b634e3546846fe978df5271bda4c37a47c672548c942f18985237904a5864a0b681e02b02033808066e540dd41a19b1503766bc6e8d48d99a51ae3463734bc6e4948dc5271a72423352a46e04a8c902f1890522e007a5900d4da82216c82c35d4686d4d00dba281b6b5c36c4b06d60e0da41a16c02c35f4886c60d0bd41e1b1a403678b06ccd40d952e17a04c3640506c4090d7da61a7a3035b2806ba930d3d181ad1403504606a08c0d6da01ad2403534606a4480d82281af35035c4a06a28c0d64a01ac04c) (pickBlockF p 13 0x3e004c6f4078f7a281eeb5c3bf0987b80d0f69a81eca5c3b70787b0090f55a61e72303d349879c8c0f5a281ea3503d24a079e8c0f44261de83c3b505879c900ec4161e60243ce6887988d0f3da21e6a503b0058796090f25249e02413c846278e524ecca09e31313be478762480f12291e1b5e3c26a4782978f01291df93d3bd26a7784a4ec0908d78311aa04276c4f0ec4901d8a343ba8a4772978ee1291dba3a3b546c768578ecca91d913e3b02640b0084158089fdc523f86be7ecd4cfb5a09f525f3e84a67be904f6d1f9eba3b3d046e7948ccf142f1dd83e3af05c75ad24eb1249d58452fc07c3400c8b781702602234a2c063a520cb0361a49503482a0750d24e35a09d3a4937248268e540e98a519785d2fb07c33e0c8b74170258223a48b0722d00e8c2c1d105419d060720d00d18281c7c5038d6a068a5806702017b03c3a007073e0d06501817d03c3998b873a920e71221749481aa0905f20f0d10a81cc024343284654138c68211cb026 (pickBlockF p 14 0x41b058834071051a8050930410060826d40280982078304146a0826d01061ac20bb5041669082ad010493004f92007207881a0810141a20502440906880809104120207a304080888060d1038162051304092400e20b1020122029304042400e00b100c1203793c40d2688181b102c2e20385440609880411100416286c515096a29fed3d3d5a5a77b474de6869b494534127a6324b4c048e95e90d2951fa4da3b49546e9088cccc0a10f913209e24490413d1dc2723904b46a08e8b610cbfc2122c83f44c07c88e0ed0fc1ba178331c106485a0bd0781720c82b41104e80008c1b4111ff3493f16827fa924f8d209fe0463c407c7740b8fea2c1fab403f90a87860f0fd2281f8b503c20987800f0fdc1a1f90343f00487eb178fd2291f9b5e3f16a47bc934f51229f7a393cd462790178fb81b1cc81e3ec8b07ce900fac2a1dc82c3e66a07c6940ee01e1d982c3e90487c8090f881a1f3b5e3e66a47b4d28f49a31f2a5e3e34a47c2938f35211e305e 0x4620688bc0910e11823193030b0988c411117d182051303040988bc110c3cae2331544650d88c81311842223003c45d0688b80b116a300fb14044b0903981006591a22c1241db4988a68c06591c22a9384536888a29100351a0eb23c42024089c5300349e22bb4a45668c8a89391492122423e1cc47a8a04f513c9aa2692941f2423c40c50f01a0cb84c00c0588965311283622482c4480388891407d4a021f0404448a0882901105a80fa13043d06088d16111628221b604424988809007cc980e704c43b0608700d10cc1221b83440404887cd010f51821b04443c0788640910e11821b9201cd07886c0d10cd182021201c40788640d0730a621d94443a0d88721710d42a21a03c4310688600b10b9b005113041d0700de0c10b09a0209240872988484c10a4a20061240822788404810991c0209384244888449300309421023442b4948549190a11d213a3642529c8465090849f20f93241a25c0de4b423010a0702404309801a0f10749e20e06c))) (pickBlockF p 17 (pickBlockF p 16 0x4a707094c0d02041025125c49f2503fa4c1289a80fe1301d70608520b127da800602c4a48c09469b12852e2502541fb28093c4a07542021403c49d05093809124920248a3049046092e13126a30247a304992809301312582022783c42705814a4c0048900fc94001124091809122c922020244926a09224c12401821002c48a0483f05002909824493048824091890121c9820212048b0409128c122010243a3448a46890c50125230249b6048f68891c9807dca00519300102403a81002001820f82c48d05090a09002c10241d603342a08ec160c3c280cbb44481268632d3114d180cba4c47e250086d111f11a18a34c4242600865311e49e239b4e30f69a9009351fd22a3ea394524628f65351e8a2a3c13942326264410519c220cb03c0410588ec5711d43623a02c4730388ded411b128237c503332808d21011b2281991404680808e31811c1ae23735046d4b88d6940cc4a018805c4660808700d117c1223183440a0488d2d011a12023384c 0x2002803324c0c5c280ec8404520789ce0e137c1a0ca0300b3240164481355af25f3524aa69c926d093752f25ca524dc49c91c908cf0a90ff1420b42641624c136c9521703d41206a160481359280579200880408f80f1359a426a1484d44a00861313663626c3484d76889aa98134ca405712047b0b89a4121344220430204cd4989944a0ceca0266c5033a28062a1010b01626545004105899f5813393626624c4cb4886725413249418985042b0789900a131c1225ea504bc4809769013081e262d604ba48098854130c2e26085047a0988540b02b0980239203372a008c4812dc1225b12440a04897b1412f0a025d84042405896a090cd8a80559304b42409664812dda02051304b224096c0c12d1182598204b246896a9112c49825fd604be6c0974d512e53019a9500aa26008a480c48280428304230589700a12c0120200200a92409569402a090041820451078956d712a49c254a5000d07895cdb12b5ae2563544aa4c09504e029c9022804c) (pickBlockF p 18 0x54c286a40509210299e504b34b0865180e48741990683113805219208c2e410a8e01b515032a2404c008089a49503482a09fcd653b9a8a883494e868299e9652fd28a87a494b9482694548d1ca828714a20b26416e48920c2ea3885520926041050141e2f276c5250c6bc9d0d4929124a4a24150b47291c8c4d14a9105142207280a144e82d49122d04d44308a40c4c1419242819485066a040a4c07701824084c5036a032e13142236283b60505490a08911408a41021304800b8a02121400220ed0304fc4709f24e0d10a027e4503432806341011601e27cc501960789fd5813f5b627da384fa4686845413e09c18c0504570989ee0e13d81a2763504eb6809d4d013c41627a5604e96809e65413c82e27805047f0988ac0f0808a00cd9303402a03344c13981a2729344380689d91413aca02750404530789c80d0cfca81009404e32409c4481399a021c2304e12409ca0c138d182710204e14689c8d11380902775604ed8c09d31513a1b019f150 (pickBlockF p 19 0x5566a8aa8d114a92e2a8a5454f298a9a4f14dd1a29b23453d468a769115052005e930547684a86939501212a313d52525ca464b55141889d8290bc042a868d1505a02a034453c480a78d008449829f34253d49ca769094e89ea9492e52725aa720c4a3c14908021535480a6ad00d409829bb4e536684a689094b49f29593d53325a79c0e4d3c18a9902152f030a5a4914ad1a294944527488a4ad1148da22a5c5e54a8a4a92d79521a92a23445424bca7e9494e122298a345302bca5c5494b0a729514d52827ca4c4f54909729112d3cd09269c104a381c90783113a0521760854840c80401151f260a3c0c1475a21071400ba26000648146daf28d3525194bca309485bc9900d1225170bc91a149458271a684202103c0060754501e289b4400325005613060c1e2f6c5f5e88a6bcad79791a9af03525df696bb6d29759a32eab435cf4bcb9c94d715292e224b5bd494b609196b121ace2345962beb22579630a9ac215257f29ead0539578a5aae147 0x5a969eb4ed0d691212cb94f58f286b004fd5a89f2b313b55d26eaa84cd4c4992cf92d48f08679e0ecd4419ace82151d036a2604d665282cc24059b6c0b3498165d1a2c596058b8bab2ad255f5a0aca2515932a2b241252342094a02921404228006430008ac813c58f688b169b1638a62c693c58b2bab145394b8a12c493e58827ab0e4b961896a470512920724260c44f81485f821585032016045569a22aba44581470a5650160dac2c1258580468aca5614a8a82be244579488ac44a15d5222b9144564278ac08f94ad1eab714256d254ad84a15ac08abf35e57d6a4abed394a9a6abda5e57a4a4af09255dd20abb23a5742bcae65495c4a4ab814156f274ad44915a41c9a68312900524240844f00c85f011567278ac04b1548a22b213c562258ac8531588a62b0234566688aca97158ca62b093c55f258a5a53154c982aea3452c2b8aa250156d262ad14c54e278ab093155ca62a813c52b498aa69115549e2a9a34552298aa0911539a22acc54))))) (pickBlockF p 30 (pickBlockF p 25 (pickBlockF p 22 (pickBlockF p 21 0x5454801844c176a292e925e5c94a4b5a8c5764a6aec14c559262a884c175c208a08290c1042b6e9515351c2bb95c55f260ba64f150c902ea23a5d246cba25155d09f2a11325d00925320a487010a8c819014022b1c93164cb62e6a34541280b97141728a62a01305cc694b92d197211eae3a3559a2baae65394fca12498512980724340c57181484002151803202604558d262b895c55f250b828d170e292e135e5c06a4b7e979608a69aa0412970724300c56f814add25053e280b6a4f14f49029e1405ba8a0b685314ec982dc24c5b3298ab04c15611d2da94e5b4284b66484a580c90b81153948042c4c16f2292dda5e5b94a4b6e8c56d8a6ad914c556262a704c16c42094a829215042b5e9316b8a62d6c5454f498ae057157c902d59485aa288a6e4c1699282d4238536280a6a501699a0acc94d56e27ca684c966096a490415a505292008568d272cc2425a247ab428d568014a8f02156b47ca648c9244a11a993251f254b3c1392402128f02a 0x60e47ac168f1800a13039225312407a8124d7820afa8315fe278a6e48180da82fe93c536240a6a4c180e2829a130601478bf84f1580902fd1205fe69cbfad097f0992fd12a3d30726ba0c57e91e2fc94c5f8278c0b17981229301352600484bfe4f57ec9e2fb9215312407a4124d7020afa0315324606b65014c9181ad14059e240bead097d1212cea304992a46b25097cc2f24b0525f209c6ae10987e2fb0ec536196a4c26d09819212fb14259c24092a14cf40259ab0435f1062b568d16a8922d4a345ef2b0bdc55152ca02ef3585ec690b869617ad242d3a3454a2a0afa5317a8a42f494452e280b848e96ed1b2f394557b27ca924c9798248a28290c8042a3606405c08ac6a385942d8b809296e5232f1a3a5e246cb365755e8a72a41424940a2bc20e4750188a20290c6042a3406405808ab0a385782b8abe4e177a292eeb5e5d44bcb9894960ca69aa8415dc0722860a431010ae5a50547280ab64c156d1d2e994e5ca284b5c4845080c861811) (pickBlockF p 23 0x6430523ae0859052732002963e278c764f0bd41e323b4f645686c849098fd1d31e94363c276c744cd28421b1c83b63806644208433409b1b1434a008619804d8d1a9319b4a6324a4c629298c0af31795252c29cabe5088801886582162e03204204527ca8315a3862c6a4c549398a52124f152022244c501792742931384e36408400a0b80841133a45f6718a6cdcd499a9a533425366549ccc492d97d21b2ca426522bcc905398dca631a94462d25c93614cf5c259b084321e06219408d8980cb11a3c5ab240c424f16ac90312358618680c4496184920310158605280b524816a09830e3606176a0c3cd21855a0308a506042a0b4e481841a83019505a6260b4a8c187228b07b4261b49cc2a909808a12d213049a0a2c340a525810b0c45e6178a4c2c979855291eb049360082c280a4d5c10b06a3c537240c20d418311e29b120535240c211414d09030512060d69cc18d098049930512a3d50726be0c58291e30494c608278c2517984629307b52 (pickBlockF p 24 0x67909c6d610801c1f0108326be8bed7714dae5a9b5bb4e6b4696d62d0dab1a1352a5e69d49cd24931a4122316a3e6862a4cfe529294299ed84b3680864500cd9e0148670116764b0cbc9019d4aa32894c646298cba5019b5ac339b4865c4a0ca0571938a6339144643498cce93996d2132614e642298ce04d98d09725205166f0723aa0c58b00cb06134641278c809319b62933635e63f298c164d18cc971b384166b072c7c53195d3631ea5c6364a8c648f19a4a63179285b4268cac5398ac0cb31b4e6674a4ccc8e1954af2d9134227042c5406592d2e318a3c664298cc64f14909231d94c661268c94971980a62af92865d488bf08d197a2f32e45265b6a4ca89799689e9ed04936608244c0c58a414b2b128658692c9cd0595ca8ac394962f282caa4f99509925185165309293a10489410b2323864d468c764f19462f32845264f6bcc9cd499312931fa4864b292c945054909caaf9313d90926ca1059241c9b2031223042c8c8e19111b251041 0x6a34b8d42931af5223429586bc290d32931aa9b634c35c6916a8c68d318bd1c35d1286a949ccfc0a5ad9a735425e5d8468d1e549ae09c33e8290d6022d40d718cda635b24c528468d6a4a1a592635992469f6b8abe8e1ac894357b44608268d61179aba29353b5e68e2a4d5a4a8f78249b704167c0721aa045aa494355b496a1682d5494562524b17a416a847cd4e8c92b828b530494a70821a8045a6c9c34b1286a48bcd47149a89af350b526a0492d3e9054a11caafa3168c2a4d08520f74249b684169e0726d60c434808b4d938699250d2c4b0b641634e34f69a686d3090da5d1db4aa3368a284d084e92b421b4a03b69306645408c34008b48a434ac08645208d7291a34693468b26c956105a200c841811688498d1ed39a39a134624e68a498c648f9a2492a5505167b052d0e06420408afe92468329cd02065a0c9e340a4c6858a4d089318c51f34115e5fb2486d8105a000cb3f2384a92a0cfad399f1a133da524a82a42ec4c99e82f253852))) (pickBlockF p 27 (pickBlockF p 26 0x6e9278dc44b949c96b740316f58bcde9149bc9a7378b426f04bcdde949a5d26aafa3e52647adda579bb0a9373944660272a9e4c5b98951f0849371082dca0a48b4108a40190d9022dc6531b889631d94c6d4268dbe4b1b7c9e370b546e0498c94571b789e2af92c529278daa481b712a29414c6d3260db4931b64a636913c527478daa8d1b5ca636aa44560468da84f1b49a236c4546d66a8beed1149926369a445702b8da24f1b3ca03670406cd6a86e05403609801d1206cb8bcd95149b252f3642522c328409e489b1c2f25c0526c607c45a0c81580f01d01d6c4098d86d500e89403005c2da078e97179d2a29ba34527436bee7cd4dcf5a7b9cb4d73468ae66d0dcb52f3962537234a4e2691197d1db2ca3a5f646cb588cdc34afb8415e7032a6df6549bdc9fb7213e6dd276db64ddb4099a901324af0a67be124ddc219b784129a0764560cc518148720230d7042d9806db140cb61013039022d80d61ac1a035fa546a4498d5e901a6d26357350 0x73247ae608d5cbca2b7692e542244e5c124f9c1c9bb0316c9032092045c152e38516c72b488a824c1ca62839414c540260e54d35c9da2b9324d72548ae22575bb09f29f9324be0a27cc124dd020b92029085042d9006412008b8ea4171029ae1e4f5bac9729f1224bd082e440e52ec18b9014871f288a7a4814f09838ec5071c498a764c1c69a7387b42719474e308d9c5c1cb670316e847ca728c92f0a11181326cf254e2a1392ec2136702a721684e3c93dc6d21b8714f706286e2c4f5be097b7392e6e1256db849db5891a9c1224ba086e280c4a74159170236cd036d8604dc41a8387b407128c0e22981c39223811607028bae18d45c2d24b77a4170a2a2e121252e0209f283937306229806436c08b8394c7066a8e049b1c14ae38213c7022bae02539c00a6b7f93e52e264dfc4b9bf496a5c8513e30926e41045281486d0216fc032080045b65a237ca4c527260df5171be12a32d2486e0290a4c501bd922379a346df270ddc511bada137513d) (pickBlockF p 28 0x759498a76481d5c903ad24e759484eae4e96e091150829238042eae931d58a63aa93c75f8a4ebcd79d71a93ada4d758498b6e4c9d509129c1207520825400e48dc18a9ca30236280e2a4c1d49a0b8a2405b14649885488d4993a885e4c10a4ea00f88cc193b7c527694beecc94dd8120ba9a31713260b6048930029ba784129e05646408d9791d302a3674d28adea4f952c993a60491510521c6085b2c0c826011704490e185b1d25253a424665c474c088d9c48aeb7a13e54a26497e145d1c249890411500521c2085b280c825811720488e3e4d1c79223a29587442a8a924c1cee2e3a135c71b4a8cb6921d051c2a41406ef278e804e1cfc9a2971306de490abe521bc89e39e45e73b6a4e64979ca92937d13d73a0924620c453c1486f8217294a0a8e4c1b689836d23a73129ce505096bc908a70190de022a8a9003749839c4527304bce4e9496b518b9b94d736298db04c55109839a84114d0521b808580122368a386f1298abe4c1cc49e2a1920 (pickBlockF p 29 0x787698f26979e4929332139563262a484a557c909be8412a507247a0c5e441491e02178f46a99a105e381c98a83178b498f12d39e201cbc314c560468ac85306dc263c6b4278c49ef1490de1d1ebc2943784256f0648d330219bd831782056f0208c3a009bbf9434cb0861ce04ddf6293be34d77b4a4cc68e9de8af3bc95252827cabe4c8de8208730217780320ac045328a83bb45268047cb7c8c9324a902b9227750bc990149dd01f11e03203c05c0ac089ea2293d2b5f7a26a6f3cd35e7129b3fa3e662476b888cd6f5193cc15e79027cf004f1df89a3bb92e4c60a66f0104a8c1d91d0330e5046ee6065c89203b425175f482ee28e5d8918b909405bc24498a145dc01ca6083176d698e404c1daca639013076e8b0ed8d61d95203af23076a2b0e3c4c16ec903aeb5071d2a0b744c1c70a03b45607646a0eb8d01d9d2e3b125071b280b724c1d95af3b23527634bcec4948a881c91c831761052466085d75a829f12075a478a7a4814f0903aec50 0x7ca0524840843b408be41387c5250f864b0620163e3b437c649ef8890d5d91fbe12337b7284ccc4a9360219c10337c1056f8008c3ac08bdf2434d708670208dca1223dd1247b824c9ac105ed40c8440117b5470ef6d39ef124bdda417b9472f6e8e1ed89aa6a8517af072f6806421808bd92384d42a0f62d25ec1a0bd7a524d32a4594509eb82f26905203f09c0ac109eb41f1210327eb8a6fced79ddda73f225f7e14a6fbe93df6924beba437d1482f928e5efd1c3dea347b32a4cca4a9340299c00437ac07254c0ac8fc1187481178e498d0a8f970d193d514679627cf1a4f1df4972678517a9092626105dd80cbd3a585c2460f4c551e549e3c593c5c1260f41171e91ae2e0240794298f244f1e8c9a3c493c759288f10931e862f3d0352758288f0e4f1df0973cf84923e062f0c4f1e69363c2a4c77f488ef68f1e74ae3bc92879b492f24905e68a8b7f149779282d044b96fc91267051799092990104dfc18bcba4478b498f2d149e55af3ca352)))) (pickBlockF p 35 (pickBlockF p 32 (pickBlockF p 31 0x68747cb8c8c9004a90459227f609c70a109fd41f12383241a03c0dc0741b89404c06c7f30b8fe4151fc4263f80447ef079058d3e0a1a5c11b4781d686f66939e7125b96243723484d0c8f99a11dae72335c546503853e058a740814b80f28f01650dbeca140513f80327cffa4edff09bbfc1335842649b4144fa0259c18432aa07648a0cc5481487b0230f2042fee06dfd00cbf701306d022f908e1faa363bec5c779690f8e921ef9223f61387ea6a2e02d25de5a0bf4a497cb482fbc8e5f5918a6c8517e80929a41043c408bf34587e56a8faa901f411c3ea2307c5470fa6d41f3da43e5a487e3488cce4e1f88943be45c7dd6b8a58d11f39243f01387dc250fb8d39ec81cbef45e736488fba8f9ef0a93ed9287b10921e0045f0d1c3ec9347cd690abe921f60943ea344756288fad179f55af3e9b527bb2a4fa44a9ec0249548392440621de045f14943e19287d06bcf9ed49f39a73e6b427cc4bcf969494b1272afa427b92a4ccc4e0aa01c921831 0x84547f0828ee0e91bc1a23372d264b9e48a0c4249f503b3860665580ac9201187b811809278e56501ca928417a4868f47905c5220b4a240413c81b298b9a4c1ef12e2e624082b4710345720a89c4149348226a0e5294172d18410a30827ac1040d0209928393a405c946104a572090a82a0a308228a0a808c2084a64104547bb4b8d1c9314fd1840c95c80729900a4f207c9c40f13452e260e4c942054ac38015081b250086131de5a738034d81a4930329060611cc02a3179d292e0a50537428c0b8393850622aa0643d408c071448142790285320552e3cd16c8132990245120449e3bc92c725480e02572034a040714c7004b901a951c28b640613c5c8481004521620a040493800d079010d3a01da140324e805484c5e8f96211eb3493958e2629b8146010149238211540321e8046004a63fd93480127900493195cb640015c7ff2a8ffc4f18bc962e3a30589298ff44c1fec9e2c424c7fa488b265b1fe49e26d9600f32600dc481ed127392242) (pickBlockF p 33 0x607488a448e217d1a2bb95c6f12990ba5021702042dc5438b2a049a5006389842cc5e8588a50aed7a159a91711421a32650aa17939c2942a02e0fd0443540786380ec2904c8518a831c4e06e02e17c04c8ab8bd15514e29a29451b5e8a26a713cd4a251a244725f8894bd10894e1f12941a15f81d2a6fae53df44a6ba9945733286d624fdab09eb031355d52670f24be1d495c3312986424f0bc48d48090a6f0533ed09272410ce28209578392540664980c616815c2982985004631a0845580d87d81377a6bcef2d4a12126c1f24584e47306e8c4fb0249c484184d0727100c43e808c2234a83c68cc609798bd29425a4e83748455c0e492c18c2502924a0421f20461222c423b5473228108c4e2111ac421a545d42610844a20fda641c23083d4990708c21022c41f35883c4b10728c20eca03981305d22410709220d9222a192083868906c8d20e5a241ba588354a8a84481cb9212e823241b2a483414a0cc271c404283207c4940ca131a4c24a49 (pickBlockF p 34 0x89b69d120d0a2689d44c9368980730b80c61a91caa2a314eb2850ba4e84009144b04e4ea0850b80ea271a1447a4f88748712e8f60e4a7c1014387a25f0ee4ae1a494c32927862246a884853a421c4a83185b0570a208c5640d87f0138916a1120d0224e3044936088f68910698220e2ec46b5188c4a311652607ca0c450494e70827e60e4e381895a82925004311093221e2a441b6c8864b910a93220d2ec4124e88149b1008fa1fd1ec3f12952e2429d0144fc4249c68412b307249e0c61f4148ca02187b4990d68f21ea2a34fa5c7cd498abe8f21d89c291a30878298d2c931f0d1e4301248778a8fa4971ab52643b23c5224610e85121c4a243734286d27b0d84f21ac9729192d86a0630e717a1ca2943835e86f6a50d2d11f6127368a426b247ca9a8ca1a0af40f95263c29af084f557c9729112d3ef092718104ac41c9270318670321fa0454951e4309208658a8a488f217c90291a388614690c6532185a23712445604690c04b218a2a3aa254 0x5dc4629f05486ac9945d85e4f70a43220f86a81945d02e1080451b714a365a9c6aa5e8cf47d08257e0a0a9bed14d6b427ecd44e577c99aed9318ca25317e4a22f49227a8533930824aa0ce2e4148ae81b10602713ad022712041395173828316e4e609098aed1214f40a316c0e53c018c1da5e8264a516857a090a90ae02910504316606440808c4b230895680e6a90575d18a799521042451621793c02945802e10204516b14a2511841d15f8232a7164505cd098aeb1214ef0a715e1045680d8808138ad48ad604f58489ac3992954b243158124adc1c929831859052340086215a4446a6c8a9695150d1a24d2eb5713d61126b0e44a552890a770518a709262e104ad81c92883185805233e08629522bea93d75e26b0e04a552490c520493f50727220c615c148ce8218866b91189b2285a6c503458924bafa6535d70a2c379295482429da144fd0249c784189f0723b20c6158148ce02189149b1208f6088a0c371295472429d81062741ca75031))) (pickBlockF p 37 (pickBlockF p 36 0x8e9286ade4fe3a099b5c12d50508673a0cc96c10c7381b8e60271c8d0d410219ce0335032a11c4d49e7d24b9d2415022a45d250a3842f28085219309c35410a380170860228fc8a71f0d7a33da747aa528452bf05854df7ca7bcf14973d286e725063c09cc729388e3268d6e4b53fc299cd8438df0724b20845800d8850138c84711ba91a3511f3369395de26319a4a631c9427f0518dc0926301062f014c631288d86d91a6d323692e468a388c527117c4d236128c402498d14831ae5260a8a0b361295dd2429fa14635824a7b84139a0631a914a34da946925e8d14a4fba535ad89ea9212955f24273210496018c680291aa04319c5123362942125e82b4a4fb6931ad51f2b0a328cc2bd0545494a09f2af9323970822be0a442410c658191080231924d53f020c6403931a06318c93206ca62b02345622980d013231da1462a438c429f18650df6c9eb7312f8c22469f610ce541892b8238c103718004e2f921a7d0432560469f25422f229335a39 0x50b0a25740e498818c87819110022b0e8f1788a048592090c258b0c8e242d1a2ca16c90a298a14580984a00e11308f669d13ed099bd1caf0a314302a43be4ca41c271d004290605c2200891200f0e101d1c22703da1b24102e4818549020992020b24001247ab4e8d9697144d0e279a149324f92349d23a92e47123c8c24387c484fc253de88a5bb314773e286d724fd9b89caf21335e02632284be44495c8712990d24f21248d61090a848513f609673c10cae01c9320332600632100ae41414c7f8231c10422c606c43809c779388fb8d91a9172345a447ea388ee2911c85123eda8c413498d16831f45260b8a0bd093973c262a101463e424a8084125f0431d88e234da747ba357a0292e765063cc9cc759385070a31c40e63d8148ed0218f42691e6d4a1192f417a527e049cdbc909ae11e47915e82e2a4a5853957ca112e83116205221a0863c40c8860118ef4711da49541820c760291dc0430124f1b892236f93c0360791dcd0e3ad2147514f) (pickBlockF p 38 0x87c462fd653dea0a4ba514374628328e4fe5109dca093994026f2784cdbec98b5d92f671256c3a49d7a091a868513fb09275210ce9420c9d83b9380732640ccbfc1895e02b2690462d006c45409c6935e8d16a4fcc535db0a2c981397452627f4124e9020c978393a30624d0085ff9293d3a4a76a48cc605798bca949694e7452844ce0c459c1488a02192c032226046291a12f32314492a489014a4a8271d184292905c22608a4b9a4c51a3292b292fc84fde949dbb4937743266bca4864a0249fc03b3a10664ca0845940d8888138a16a1244962205280cb84c8d169d102d3636924c432417a4292e845064949cba013150c0a32480e4e801895d8292630432369124809449024c9226b91b09b248526468a3c91f25123c492281a044125c91a481236932205ae48d35488c4d923293244c9435526c9174b922c95245526317a3c912271226932430922f1a40912478b0c8c0030163fca527e249ce82909ae91f2c6a3291029ce805098bc972c312d (pickBlockF p 39 0x3ac0822d80a446c10caf81911a023158d05d3120a3a1524730a52ba0f89b8194ae02e11a0452c29262ad18caf14974b262d7c4bd9d095b0f9275ed2472b6124ea81895f02b26c0462d406c46009caaa388fb6d92b2d72345a64aa2489582712ae4d25391a4aa9388a96a12a8d321fda00cb03c9196a51fad3a215a1468a3e87f47ace64e57b098ca91295ea242a20144ff8249d40419510524d6086201a645425094d46129c8f21fda44a6b4488d4d92989725189c3f536c94a6b8ef2d325251c4a423494529128c8e24fc9a3a4a50945498dfa900104164062527ec49ce08909af11f2f5a3294327cbd44c9de49737e92d50f0a27fa124e9c20ca1019117022dfcd31d20a849f13093f278dfa9224f92238616c93d2b8a1c580e98a81801408dc69314ed05ea524ba3a4145c2a463a50a4e81f13583293905c22e0891cc0f18001d3002906581b24dc2e49b03c9350692680b24cc1247e24f8db49315490e29920cab23f9534772a08e653d1bca5a33 0x1242d4a3492f468a526c027ac444d658c94af79213ad0825800e49bc18cb102926e0430229499d91d31023677a2bcef254a5809f2f7932))))))))
  6 11 7
def m_2293 : Nat := 0xaaaaaaaaaaaaaaaa
def s_2293 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_2293 : Nat := 0x20222222a
def bds_2293 : List (Nat × List Nat × Nat × Nat) := [(m_1806, s_1806, 5, g_1806), (m_1761, s_1761, 6, g_1761), (m_1947, s_1947, 5, g_1947), (m_2026, s_2026, 6, g_2026), (m_1871, s_1871, 5, g_1871)]
theorem kn_2293 : KnownBin bds_2293 := by
  intro b hb
  simp only [bds_2293, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_1806
  · exact lb_1761
  · exact lb_1947
  · exact lb_2026
  · exact lb_1871
theorem sub_2293 : ∀ b ∈ bds_2293, m_2293 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2293, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2293 : ∀ b ∈ bds_2293, canon b.1 g_2293 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2293, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2293 : dagCheckRootsF m_2293 g_2293 bds_2293 (dagRefF 2404 (dagTraceF m_2293 s_2293 8 f_2293) l_2293 0) s_2293 8 = true := by decide +kernel
def node_2293 : Nat → Bool := dagCheckNodeF m_2293 g_2293 bds_2293 2404 (dagTraceF m_2293 s_2293 8 f_2293) l_2293
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_0 : treeBlockF 0 128 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_1 : treeBlockF 128 256 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_2 : treeBlockF 256 384 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_3 : treeBlockF 384 512 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_4 : treeBlockF 512 640 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_5 : treeBlockF 640 768 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_6 : treeBlockF 768 896 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_7 : treeBlockF 896 1024 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_8 : treeBlockF 1024 1152 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_9 : treeBlockF 1152 1280 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_10 : treeBlockF 1280 1408 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_11 : treeBlockF 1408 1536 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_12 : treeBlockF 1536 1664 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_13 : treeBlockF 1664 1792 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_14 : treeBlockF 1792 1920 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_15 : treeBlockF 1920 2048 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_16 : treeBlockF 2048 2176 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_17 : treeBlockF 2176 2304 node_2293 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2293_18 : treeBlockF 2304 2404 node_2293 = true := by decide +kernel
theorem nc_2293 : ∀ j, 0 ≤ j → j < 2404 → node_2293 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_2293_0) (certBlock nb_2293_1)) (joinChecks (certBlock nb_2293_2) (certBlock nb_2293_3))) (joinChecks (joinChecks (certBlock nb_2293_4) (certBlock nb_2293_5)) (joinChecks (certBlock nb_2293_6) (joinChecks (certBlock nb_2293_7) (certBlock nb_2293_8))))) (joinChecks (joinChecks (joinChecks (certBlock nb_2293_9) (certBlock nb_2293_10)) (joinChecks (certBlock nb_2293_11) (joinChecks (certBlock nb_2293_12) (certBlock nb_2293_13)))) (joinChecks (joinChecks (certBlock nb_2293_14) (certBlock nb_2293_15)) (joinChecks (certBlock nb_2293_16) (joinChecks (certBlock nb_2293_17) (certBlock nb_2293_18))))))
theorem lb_2293 : LowerBin m_2293 s_2293 g_2293 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2293 sub_2293 gl_2293 rc_2293 nc_2293

def f_2294 : Nat → Nat × Nat := unpackForestF 0xe9498cea7c5334a72508a4601f 3 10
def l_2294 : Nat → Nat → Option Nat := unpackLinksF 0x288a06986121c1 0x3a52921a9f24c9a9c942d19c4cca4601f 6 2 10 3 3
def m_2294 : Nat := 0xaaaaaaaaaaaaaaaa
def s_2294 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_2294 : Nat := 0x20222222a
def bds_2294 : List (Nat × List Nat × Nat × Nat) := [(m_1761, s_1761, 6, g_1761), (m_1806, s_1806, 5, g_1806), (m_1871, s_1871, 5, g_1871), (m_1947, s_1947, 5, g_1947), (m_2026, s_2026, 6, g_2026)]
theorem kn_2294 : KnownBin bds_2294 := by
  intro b hb
  simp only [bds_2294, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_1761
  · exact lb_1806
  · exact lb_1871
  · exact lb_1947
  · exact lb_2026
theorem sub_2294 : ∀ b ∈ bds_2294, m_2294 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2294, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2294 : ∀ b ∈ bds_2294, canon b.1 g_2294 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2294, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2294 : dagCheckRootsF m_2294 g_2294 bds_2294 (dagRefF 8 (dagTraceF m_2294 s_2294 7 f_2294) l_2294 0) s_2294 7 = true := by decide +kernel
def node_2294 : Nat → Bool := dagCheckNodeF m_2294 g_2294 bds_2294 8 (dagTraceF m_2294 s_2294 7 f_2294) l_2294
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2294_0 : treeBlockF 0 8 node_2294 = true := by decide +kernel
theorem nc_2294 : ∀ j, 0 ≤ j → j < 8 → node_2294 j = true :=
  (certBlock nb_2294_0)
theorem lb_2294 : LowerBin m_2294 s_2294 g_2294 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2294 sub_2294 gl_2294 rc_2294 nc_2294

def m_2295 : Nat := 0x3333333333333333
def s_2295 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_2295 : Nat := 0x111111313333333
theorem lb_2295 : LowerBin m_2295 s_2295 g_2295 9 := by
  refine lowerByRows [2, 61, 2, 60, 2, 57, 2, 56, 2, 53, 2, 52, 2, 49, 2, 48, 2, 45, 2, 44, 2, 41, 2, 40, 2, 37, 2, 36, 2, 33, 2, 32, 2, 29, 2, 28, 2, 25, 2, 24, 2, 21, 2, 20, 2, 17, 2, 16, 2, 13, 2, 12, 2, 9, 2, 8, 2, 5, 2, 4, 2, 1, 2, 0] (by decide +kernel) ?_ (by decide +kernel) lb_2293
  intro w hw
  simp only [s_2295, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2296 : Nat := 0x3333333333333333
def s_2296 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_2296 : Nat := 0x111111313333333
theorem lb_2296 : LowerBin m_2296 s_2296 g_2296 8 := by
  refine lowerByRows [2, 61, 2, 60, 2, 57, 2, 56, 2, 53, 2, 52, 2, 49, 2, 48, 2, 45, 2, 44, 2, 41, 2, 40, 2, 37, 2, 36, 2, 33, 2, 32, 2, 29, 2, 28, 2, 25, 2, 24, 2, 21, 2, 20, 2, 17, 2, 16, 2, 13, 2, 12, 2, 9, 2, 8, 2, 5, 2, 4, 2, 1, 2, 0] (by decide +kernel) ?_ (by decide +kernel) lb_2294
  intro w hw
  simp only [s_2296, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2297 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2297 : Nat → Nat → Option Nat := fun _ _ => none
def m_2297 : Nat := 0xcccccccccccccccc
def s_2297 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_2297 : Nat := 0x404440004044c
def bds_2297 : List (Nat × List Nat × Nat × Nat) := [(m_1765, s_1765, 7, g_1765)]
theorem kn_2297 : KnownBin bds_2297 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1765
theorem sub_2297 : ∀ b ∈ bds_2297, m_2297 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2297 : ∀ b ∈ bds_2297, canon b.1 g_2297 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2297 : dagCheckRootsF m_2297 g_2297 bds_2297 (dagRefF 0 (dagTraceF m_2297 s_2297 7 f_2297) l_2297 0) s_2297 7 = true := by decide +kernel
def node_2297 : Nat → Bool := dagCheckNodeF m_2297 g_2297 bds_2297 0 (dagTraceF m_2297 s_2297 7 f_2297) l_2297
theorem nc_2297 : ∀ j, 0 ≤ j → j < 0 → node_2297 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2297 : LowerBin m_2297 s_2297 g_2297 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2297 sub_2297 gl_2297 rc_2297 nc_2297

def f_2298 : Nat → Nat × Nat := unpackIndexedForestF (pagedUnpackF 22 7 (fun p => (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0xfe4f0361530f6d603db480f69203614f0f25303614b0ecd403b3480d851c3994c0e64f0361430dad2836a5e0da918369560da5183613100209c3515407117c3414407116c3316c07115c313480c4d103114407114c30154070d7c2f134070d6c2e16c070d5c2c35c0b0d502c134070d4c2b144070d3c2a134070d2c2915c070d1c28134070d0c1c24a098d68263560709182435d0904e82413607055820c5a08315820b5a082d5820a390828c41c146072d581f234072d381ca560729181c94a0725181c13e00207c1b25800517c19a480665200145b06298001457058d20163440589201614800514c15258004d7c14238004d6c12a6004a58001357040d70103540408e010138004d4c0ea4803a5200134f0368e00134b0329400134702c8e00b138004d0c0a1460049680645e022d1006452018d34063450185680615600492803b5e00ed180395600e5180123200696801a320064b40114a00205c0001f (pickBlockF p 2 0x1fa9107e9281fa4906b2531f4d787d2561ac9046b23b1ee9006b2371eb1606b15f1e65706b15b1df18077a6c1de9806b1571d4570751441d44f0751341ac54c73a5e1ce5586b1411ac4ec721401ac4dc7125c1ac4bc7015c1ac4ac6e3501b89406e1501ac49c6ba341b24906b95c1ae5106b1230020dc6a25414517c6924414516c6826c14515c662441985206614414514c5134a190d6864356144d186235d1888e8622361449585fc5a17f1585fb5a17ed585124617a9505115f1764d05115b1729b05115716a5705a95416a4d0511531669105114f160d505813414452c5725c14451c55b541564d051143146d2851b461469585313414693851956146518511290020bc503580d917c4eb4813a9203645b136d803645712cd204b24812c5204b1440d914c4a2460d8d684745e1225104745211c968472560d8d2845b5a1168f43624a112d603615f10e5303615b108d80422600d855c3f95c0fe5503f94c 0x2fe128a00172fa110a0b4d2f6170a0b45282978a0a522828e8bab502ea910a0a36282578a09522824e8b7b502de910a09362da0d0b3a3d2d6500b3a352ce508b392a2ce074a0924282178b2034282148b1124282134af1242be050af044282128ae014282118ad1402b2490a0845290934a41422904f8a41322904a8a4126290108a403e2900c8a402a290098a48322920c0a4822292068a4014282110a30442820e8a1350284d10a12442820d8a001300211887b5627ad5087a5f27691087a5b26edb09b96c26e58087a57264950992442644a09912421e94c9815025cd589725621e8e49635421e57c9514421e56c9336c24c9b09326021e55c909542425109093c2424d08795323e9408ea5623a558879392349108d14821e4bc8bb4822e5108792b22ad20879272268e0882342205508814421e48c0083f1ad168864681acd7c854581acd5c844581ac97c8325c1ac96c814602045b0811601ac95c7ea5c)) (pickBlockF p 5 (pickBlockF p 4 0x3fc0d8ff02e2800ecf725d3f4930fd0503dc8d4fc1353dc570f71513ea100fa2353dc540f89403e2140f71353de540f70422800dcedb463d6938edb443d2910eda5e3b6918eda443b64a4ed9283c44d8f11343b6490ee3443b8910ee1283ba4d0ee0243b6148a002f39cd78e735239cd34e734539c528ea15039c518e705e39c148e704a39c118e702e2800acdcb52372d40dcb4a392d40dca4d38cd40e3244372928e2240372918e1340372914dfa3237e108dca4437a510dc931374d40dd244372128a0027358d78db034358578d6152358178d604635e8f8d783e35e0c8d60443580b8d601e28008ccfb4d33ed14cfa4a34c570d305033e918cf95e33e518d124433e4d8cf85233e0e8a001f322d34c8b45322948c8a3a322528cb95032e170c8946322178c8846326910c8836322078a001b31e920bfb4d31a940bfb452fe948bfa4a3124d8bfa4830e520bfa3a30a4b0bf94a3064b0c01483020e0c002c 0x4f811d3f1404fa5513e0432808d53b24d4ec9153b2354ee1113b03928053d36b514dad3536b454ded4137a504de911369364da064a01434cad1532a5e4ca94933b504ce911329364ca064a013b4b097530a4c4c25412c2354b05092f1254b01712c0514b65012ca354b25092c0502804dd22b464aa93922b444a691122a5e48a91922a44498d112624449a4d12612448a549228294925092282848c8d92323448a090a012f470d791c352470d351c3454709291f0504709191c15e4705491c14a4705191c0192804ad11b52446d4111b4a466d4111a4d460d4118244446929172404469191634044691514a3245250911a4444cd4113244446529120444460c4a012742cd791013442c9790b25242c5790b1464328f90c93e4324c90b14442c4b90b01928048d0824d420915082354225110813928013d03b5140ed3503b45412d4104a504129110383640e0b8a00433fcd14ff2493fc578ff152400d4100244) (pickBlockF p 6 0x5fed515934b5fad7159347564d157d2465649455924b5e89417a16c5ea9417a16056491d754545d4db1753545de8d1752605da941751385d6d11751345648fd73c6c5ce9b15923b5c9181723545648dd7046c5c09b1702545648cd6f1465645455914b5b09b16c2605b29416c15056451d6745459cdb16735459c8e16924459c8d167a3859e4d1671605644fd65c6c5965b15913b591181643545644dd6246c5885b1621545644cd60a6c5825815912f57cd815f16c5644ad5db60576d615912757294159a345665b15a94056a4c15a1245665515912300211d5814455a4e55704455a0e4a024f54c4a55312854c4915302954c0a15302428090d5134e546d715124f2808f54e35e53e8f94e2445384a54e0292808ed4aa4e5304914c02452a9094a95152a144a02374f8d0d3e23f522d093e23e51a9394692451a0913e2324f853d3e14b510171440504f851d4304050a9513e1434f813d3e04b50057140150 0x6088fdbcb5a6fa541bcb566f2969bca566f24a58223b6df169b7b5a6ded59b7a5a6de505b824a6e0919b814a6de131822376d6959b5a3e6d64a5822336d2131b39466ce4f98214b6c4d75b125c6c4945b125060851dadc566b6d59ada396b68e1ae2466b68d18213f6a8969ac2506a8959aa15a6a8559aa13e6084eda545a694d69a5356694905a515a696929a5a46696129a504c6084dda315668c4f9a312e6084cd9f35a684971a115067cd599f25667c9199f14a6084bd9ab4a66a9699ca506725719aa5666a5599a94666a4b98212b65cd699734a6628f19725a65e4f19715a60849d8eb4a6561318eb4663a9299404c63a91992a3a64a4b58ea346468d18e95a6424918e95663a5298f04c63a5198212362ed118ba4462e0a18c23462e0918292f60a49d8a14460a48d8734461c9118712861e4d18712460a0bd828276161118282360a07d8281b60c9218301060a05d820460021295935d564d357fc6c))) (pickBlockF p 10 (pickBlockF p 8 0x7d6d75ff0447d6d35f5b457d6949f5a3a7f0d41fc2447d68d9f59527d64e9f9b507e6911f59367e20d1f623d7d88d5f61427d8501f612a7d6491e99567d0921f42387ce8d1e994f7c8559f21467a6529f0a487c28e1ef2347be491ef05c7a651deb45a7ad159eb35a7acd59eb04e7ae151eb0427a6519ea3447a605c009237a3179cb35572cd15e724672c925e2c6478b151e2b6478ad51e293878cd51e334478a4d1cb23f786951cb23b77d161df36477cd51df25872c8dddda64776951cb233772519cb149761191d8454760d91d83547608e1d8a54762911d823472c4fdd715472c4edd4c58752d91d4b54752561cb13774c591d315472c4cdd225472c4bdd115472c4adceb6873ad61cea5873a561cb12772e8d1cd12472e591cc12472e551cb12300213dc9a397264e58234b720945c8151608d1dc704c718919c612960892dc3b5d70e571c395170e54182247701159c03567004e5c0138702d19c0134 (pickBlockF p 9 0x8f4d623f23c8f49623e13c8f45623d0548bb17e3c3488bb16e3b3608bb15e38b488e2922389488e21122ec538d9166370448d9146362468bad6a34a5a8d295a2eb4a8cad2a32a3d8ca8f22ea5a8bcd2a3123c8bc96a2f13d8be52a2f13c8ba568009278b45522d0547a717e2c1447a716e2b16c7a715e299448a6111e9c5389ed162794589e511e9b5e894d1a25a3a8968da253447a6d49e9b4a88ad6a22b5688a535e9b46878d161e23a8829121e2368785161e92a87a49a1e1447a697a1d234864d2a1934686c8e21b23486491a19a3a8668da192447a694a18144854d7a16b4485a8d215352854d2a153467a692a0fb5a83ed5a12a4484a5120fa5e8468d20fa5283e8ea0fa3683e535e9a468385120e044820d3e0d238820d2e0c250820d1e0a2388284d20a034820d0e0823a8228da0812d7a68d20623481a492060547a657e0234680891a0423a8088d20312480855a021467a656a012508028d1e9957 0x9fcd7a7f2569be9067e1289be8ee7ba409ee5427c3489ee1726fa379e2d6a78b569e25367914c9e24ba6f95a9c0d1a773449c093e702479d6d127014f9c052e740509c051e721449c84d2720189c050e7012b9c2d32701279be130009379b85526e054994d7e6d134994d6e6c16c994d5e6a3549a84d26a034994d4e690449a09366824599455a66b5699a95a6513e99655a6512e0024ce63a5498e1525345f9889126214894d16e60a6c9825825345797a9125e94897a1125345394cd6a5d15094cd5a5c35d94c95a5845a96115a5835a960d5a5825a9625425825694c91a5694695a5125315294ed6a53b5695257253a5694e4965314a0024be5195494615240c5f940d225014490316e4eb6093a5b240c57932d224c94493211240c5392cd1a4b344902d4a4a136902d2a4934a90296a47a5091e8ea40a56916d764625c9168ea4095690716a41c56906d6a41b5690656a4215090655a409469024b80092b)) (pickBlockF p 12 (pickBlockF p 11 0xafe91ab893eaf48febe04caf48debd027ae24f2b8934ae24bab923fae48eeba040ae48deb9233ae205000943aded7aa9456aa4d5ab5454ad4d52b5054aa497eb4244aa496eb2b6caca582a9257ac0952b0244ac04a2b0024aa494eaf044ab6d7aadb56ab695aa9239ab2112aaa4faae542aaa47aaa09ea9238aa691aa92340024fea8054a5117e94457a98552a6054a50d7ea5134a50d6ea416ca50d5ea2354a884d2a2034a50d4e9434ba8217294347a7e4fa9425aa7a4929ba51a728f69ca35a7249a9ba50a6e57694256a6a1529415fa5056a94157a60d3698345a5055a9413fa56d5a95b46a5695a9413ea504de940170024ee93254a460fa92054a460ca6fc5aa3b1a28ec58a3a5628f340a3a1526fb5fa36d5a6fb5aa311628c1609bed5e8b1529bed5a88458a20d5288158a22d02880549be97e86d68a1a9726fa5ba15182851609be95e81568a0497283358a0491281128a06502810249be94e80244 0xbf3162fcb54bf2962fe144bf2502fd344bf2132f6a37bec992fb254bda8cefa028bdc4bef712bbe2d02f7127bde552f7123bda1100094fb9916ee6457b98d6ee6357bce512e634fbca4d2e634bbc35a2f095cbc2172e6347bbe4d2e6343bb8d22ee344b9853eed05cb9851eea35aba8d5aea04ebaa152ea042b9851ae613fba2972e7b56b9e91ae613eb984dee601700252ecfb5db911b2e4138b3ed2ee2b5cb8a582cfb47b8492ee1247b3e972e0246b3e946df138b6ed2ede150b6ed1edba3fb72132dba37b6e09ecfa50b6a572da128b3e92ed8a50b62582cfa47b58db2d6260b5a942d6138b3e8fed4a6cb524a2cfa3bb49182d2260b4a542d204cb3e8ded026cb40952d0128b3e8cc00947b3a512b8b4fb364d2b8b4bb2d5a2cb15cb2e112cb05cae2d1eca134ae2d0eb894cb1a8f6c6a39b1e132c6a35b1a8c6b8946b088fec223bb11162c404cb088dec2233b080fec2037ae2512bfb4eb02132bfb46) (pickBlockF p 13 0xcfd1b33f238cd8d2f3db5ccf698336347cf08ef3c237cd85733b146cd85473a238cdad2f39250cdad1f3693fcde13336937cda05f3615000291f2ba4ccae91b3113fcc44ef3304ccc44df31133cc40ff31037cae9132ba3ecbe51b2b929cb44ff2e04ccb44df2d017cae4a32b924cae09000a43caad7b25456c94d5b29156c944e728044c9a53f26947c9a05f25138c96d1b251340028ff24054c6117f18457c8a4a71835ac7a97721134c7a5471f13dc7c4d71f125c7a54318356c761531825fc6096b18257c6cd371b345c6095b1812bc6655b18129c6049f180270028ef17254c560fb16054c560cb0845ac4b1a312c58c4a96313340c4a1530835fc46d5b0835ac4116310260c20d5f0f252c20d5b0c35ac30d5b0c24dc325330c129c2096b0b156c2050708b46c26d1308a4fc2291f0804c0028df05256c1a95b0523ec1655b051290028cef6b45c0e91af6a49c0715301b54c064e2f6a3fc02952f6a3b 0xd9692765949d9611000b4fd8ed5b63a39d8e4e400b4bd5097f6236cd5096f6016cd805836006cd5095f5ea5cd7a5435e364d5094f54251d5057f5c26cd5056f5a26cd689835a06cd5055f58a50d6257358264d5054f54151d5017f54a6cd529835496cd5258354057002d1f4d239d464af51927d4609f4d238d348d34d139d3a4bf4e927d3a05f4d138d344d34d034002d0f4ab45d2e51b4a949d2a11000a4fd0516f41457d2052348144d0493f4705cd0491f4435ad10d5b4404ed1215344042d0491b4112bd0a51b41129d0449f4102700292f3635d)))))) 11
def l_2298 : Nat → Nat → Option Nat := unpackIndexedLinksF
  (pagedUnpackF 18 7 (fun p => (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0xc21030800c20030800bf0c2fc00be042f800be002ec30bb002ec00b9082e400b9002e400b9002e400b41429100a40028c10a30028030a000270409c00270009c0026430990026010980025c109700254209500254009500248309200240209000238208e00234108d0022c208908224008900214408500214008500204408100204008100204008100204007b181ec007b001e8107a001e8007a001e800741818d106300184206100184005f0817c005d08174005c04170005c0015c505700154205500150105400150005208148005200148005200138404e00138004b0c12c004a0412800470c11c0047001142045001083042001080041041040041001040041000ec603b000ec003b000ec0036140d80036000d800330c08d0001880001 (pickBlockF p 2 0x15d00574015910564015900554415500554015404550015208548015104544015100544014e0c538014e00538014e00528414a0052801461051801460051411450051011440050c11430050c0143004fc413e044f8013d044f4013a0c495512500490112400484312100474411d00474011d00468311808460011800450411400450011400440411000440011000440010a1842801090442401080442001060841801060041801030c40c0101084040101003fc20ff003f810fe003f800fc083f000fc003f000fc003ec10fb003ec00f51839110e40038820e20038800e00838000de0837800de0037800dd0436050d80035430d50035400d40435000d40033860ce0033800cb0c32c00c90832400c80432000c80031820c60031800c6003180 0x2102483c120d0883402071881812050481012040081002010c80011ff047f811fe007f801fb0c7ec01fa047e801f9047e011f7047dc01ed287b401ed007b011eb047a421e8047a001e70479421e50079011e40078c11e20478801e20078801e20078801e20078801e20078801e20078801e20078801e20078801de10744d1d10074011d00074001d00073431b95067da19f0067c019e04678019d04674019d0067011981066001980066001980065041940064c11930064031900063c118f00638118e00638018d0462441890062401890062401851061401840461001810c6040181005fc217f005fc017d085f0117a085e80179045e40179005d831673c59421650059011640058c116300584216100580116000580016000574315d005740)) (pickBlockF p 5 (pickBlockF p 4 0x2cd00b04c2c004b0002bf04aec42bb00ae812b70cadc02b604ac452b100ac402ae0cab802ad04a9092a304a8c029e14a78029d04a74029c04a70029b04a6c029b00a64229804a60029800a60029704a4c428a24a28028a00a28028904a24028900a20128800a20028800a200288009e8e279049cc6273009cc0271089c40271009bc226f009b4226d009b0126c009b002690c9a40268049a0026800998225a3096412590095c22560495802560095802560095802530c94c02530092c824b00928124a00928024a0092022480092002480091c12470091c023d288f4023c048f0023c008f0023c008f0023a088e8023a008e80239048e0122e288b8022c088ac12280c89c12270089c022508894022308888121f0c87c021d08874021c048643 0x3ac00eac13a908e35c38d00e34038d00e34038c04e14738308e0c038108e04038100e04037e0cdf8037134dbc236f00dbc036f00dbc036d08db4036130d80136000d7c135b10d68135a00d6413560cd58035504d54035014d1c934604d18034114d04034004d00033f04cf8133e00cf8033d04ce4433900ce4033804ce0033800cd8232d24cb4032d00cb4032c04cb0032c00cac132b00cac032b00cac032b00c74e31c04c58631600c58031408c50031400c48231200c40231000c3c130f00c3c030c0cc30030c00c28230a00c2412fd30bf012fc00be822f904be402f900be402f900be402f60cbd802f600bb882ee00bb802ee00bb802ed04b9872e408b9002e208b8802e200b8802df0cb7c02d234b4022cf04b3c02cf00b3c02cf00b342) (pickBlockF p 6 0x472091c41470051b0446c011a044680119c14670119c04660518c346205188046201188046009180045f0517c045e05160645801160045609158045601150245401150045401144345101134444d01134044c05130044b0512034470511c0447011181446011141445011140443090f4643d010f4043b090ec043b010e42439010e40439010d83436010d80434090d00434010c82431050c4042e0d0b4142b090ac042b010ac0429090a014250d039740e01034140d0103013fe38ff803fe00ff023fc00ff003fa08fb8c3ed04fb403eb08f70f3db04f6c03d80cf6003d800f4863d200f4803d200f4023cf04f3813c038efc13bf00efc03be04ef803be00ef803bb0ceec03ba04ee803b904ed443b500ed013b208ec803b104ec403b004eb04 0x5430150c0542055080542015080539254e40538054d82535054d40535014d40535014c445282549c15270149c05231148c052205488051a21468051a01464151709444650f09438150e01434150c0542825041941005040140c15030140c0503013e894fa013e414f7093dc04f6053d804f6013d804f2113a494e8053a004e80139044e40139004e40138824e20138804e20136c74db0136c04db0136c04d90936404d90136404d21d34414d00534004ce0933804cc0931864c60131804c50531404c50131014c40131004bf152fc04be052f414bb092ec04bb012e814b0292bc14af012bc04af012b814aa112a024a80129c14a60529804a60129804a505284449f0927c049e05278049e01278049d0526c248e351ed3475191d01474011d00))) (pickBlockF p 10 (pickBlockF p 8 0x6460591026410d900163f058fc063f018f0363b058e8163a018e806370d8dc0636058d80635058cc2632058a0a6184186006180185826140984c16130183c460f0183c060c0d830060b0582426090182016080181c16070181c0606057f0a5fc017ec15df7177c05d81d75045d40174435cf0973815cd0573405cc0572c15cb0172035c11d70405bf096fc05be056f805be016e455b8056e005b50d6d405b20d6c025af056b815ae016b415ac056b005a90d68875a20168025a00167c159f0167c059a15664159901658359601650259401648259105644059101644058b196203587056142585016101580115bd156f015bc056b115ac056b01588956201584156101564855901564055805558255019538254d05534054c0552c15490950c6 (pickBlockF p 9 0x75d01d70175c01d6c175a05d50675305d40374e09d28474905d24074901d1c274119d04074101d00173f05cd8973505cd4072e1dcb4172d01ca837231dc88172105c78371e01c74171a0dc4c77043dc08270009bec56fb01bd856f505bb486ec05bac16e80db9c16e701b8c46de15b7026dc01b7006da09b5846cf1db3c06cd09b3406c22db0416c005b0006be09af806be01af806ba11ad456b501acc26b205ac806b201ac026b001ac006ae09aa846aa01aa416a901aa406a709a9c06a701a8076a001a78269e01a78069c09a70069b05a6c069b01a6c06902da3c168e05a28468a01a24168805a14368501a14068501a08367a219e806761198d36600d980065f0596c465b0196c065b0195c465605950265401934764c0592826480991c1 0x85706144685102138384e02138084e0213418471a11c084606118084602114183e1e0f8083e020f4183d020f4083c060f0083c020ec183b020ec083b020e03838020e00837060b8981662058081506048381202044181102038380e02038080e0202c380b02028180a0200c78030200c07fe15ff807fb0dfb8d7ee01fb807eb0dfac07eb01fa037e801fa007e315f8c07e301f8c07e00df7047d90df4c67d301f3857ce01f3807ce01f3417cd01f3407cc05f1087c401f1007c10df0407c005f0007bf05efc07b919ea117a801ea007a50de9407a501e8837a201e88079d15e74079d01e74079a0de68079a01e5c379701e44679101e34478a0de24178319e0c078301e08177d15df4077d01df4077c05df0077c01dec177321dbc475e45d741)) (pickBlockF p 12 (pickBlockF p 11 0x9581256009580255c19570254859500a53c194f0253c094f02538194e0252849384a4dc192f224a8592a024a809290649449250249019240248c19200e480092002480092002470491c0246c191a0646809141a45009130644c091206448090b1e4185901163c8f8f2023bc38ec0e3b008ec023a438e90239c28e70239038e30638818e20237848dd0637408da0e36808d70e35c08d60635808d60235808d11634408cc1633008ca0a31848c60231808c60230848c20230808c20230808bd162f408bd0227de89f02278189e0227418942625008940225008940224c188c1e22c18851a2140885022044880061dc9877021d81876021d80875061b8786e021b8086a121a80869061983865061940865021883861061840860061647859021601 0xa570695c0a57029581a56029541a4e1e9341a4d029283a4a029241a49029240a48069200a470690c4a37328d42a320e8c02a2f068bc0a2e068b80a2c0a8b00a2c028b00a28128a00a270689c0a27028903a240288c1a23028881a22028880a210686c6a1b0286c0a1a068680a141a8500a14027e1c9f3167cc09f2067b459ec067a829e51679409e40677479dd0274ca9d30274819d10673c29cd0a73409cb0a72c09be366f809bd066f019bb066e819b6126d809b5066d409b4066c439b1026c409ae0e6b809ad066b409ac066a439a9026a409a90269839905a640098c1262c19871261819860261809830e5f0797c025e439770a5dc0976065d809730e5cc096b225ac096a065a8096a0259c39670259c096702574a95d02574095c065700) (pickBlockF p 13 0xbd706f485bd106f3c2bca16f280bc906f087bc202ee0abb802edc1bb606ed02bb20aec80bb00aec00ba336e356b8b0ae0c8b8302e081b8202dfc3b7f02dfc0b7f02dd4ab7406dd00b7012dc00b7002dbc1b6f02da85b680ad904b524ad441b4922d105b4402cf86b3e02cf41b3c06cf00b351ecc05b2b16c70fb1c02c643b160ec580b130ec4c0b1302c481b1202c480b1202c345b0816c200b060ac084b0202c080b0202bf84afe02bf80af916be40af902b6deadb02b681ada02b641ad026b400ad002b400ad002b3c1ac81eb1c1ac11ab040ac102af44abc06acc9ab302ac81ab202ac80ab106aa87aa906a8c6aa302a8c0aa206a880a9926a058a7a1e9e80a770e9dc0a7216994da620e9880a600a9800a600297c1a5b1296c0a580e9600 0x33dc3cf40f3b08cd94f3544ccf1b3246cb5532cc2cb2072b84cad072ac2cab032907ca40328c1ca00f2743c98172582c95072444c90072382c8e0321c7c86072180c830f2003c7b171ec0c7b031ec0c7b031ec0c751b1329c490f1240c49031240c44171082c3f0f0fc0c3f030fc0c3a170e02c3413094fc220f0880c200b0704c10330382c0b0f02c0c0b030203c080301c1c07030181c06030180c0506ffc6bff02ffc0bf91afe40bf902f75cbd816f600))))))
  (pagedUnpackF 22 7 (fun p => (pickBlockF p 13 (pickBlockF p 6 (pickBlockF p 3 (pickBlockF p 1 0x8b1582235a086d58212390828c41f23407ed581eb4e0789581da460745281c9460d317c33c5b0cb15c30c530bed7c2eb5b0b6d5c2bb530aad3c29b4b0a2d1c27b4309c92825a4608e558201460704f81b2580249201a24806652006a6806298008a4805ed201734402096016a48058520152580148c01423804c98012960046d70113540428e01013801e9600f24803a5200da38032940072480128c00ba3802c4e002a4a01a5280a146022d100945e02114807b4d01cd140695a0185580535e012d180224a0105580394600a968022320064b41ac5f06516c1845705714c14b5f04ed6c1235703ed4c0e34f034d2c0c34702ad0c09a5a0169280323200452b6534fd8cd2f53b47d32d0f4a24fd0292f35a47cac90f24a3fc5e8ef07a37c128cef614fb9652ecf147ae050ea893fa4e4ee6f1379924ce5292f9004ae2e1277a448dca84f6061295884727e1188703f1aa0dc5082f0d609c1b81f00205c0001f (pickBlockF p 2 0x1604d05725c158d505593414c4d054b4a150d1853a5614a9385215614651869c5f1a316c67c5719714c6534a18ed1861a5617c9185e15f17456c5c15716854c5914f15e52c5694715450c51129140d604934813cd204ea4811eda04db6012292048358132d204c24812e5204b144118d2847a4a128918489441251784845211e968472560fa5343b145118d6845a3d0e24c444b580e04c04394c10ad8042260104570409541005303f93c0fad603e3480f69203c94c0eed403b3480de4c03a14c0e64f038b4a0e097837a460dc5583694613f17c4e45b13515c4ac53126d6846b4a1149284415f10c56c419570fc54c3d14f0f052c3a9470e450c361310d455026a54088550341440989103316c08a590219440c8d2031b440c4510301540bc4d02e16c07e4f02d35c0b2d502c1340ac5101e93c0845502a1340a4570209540a04d024a560748f826b5a098d58241560724b82535d08ad542493a0904d82345a 0x2345208c34822e5108993022ad20891202268e0892342225508814427cd589e25f27496c9b25726294c96a3925657c9495b24a55c901532384e48c92f22c4ac8a12721e48c8645d21515486468215160844581f69008325c2091808196c2045808025c1fe9107f1281fa4907db5e1eed187d2561ba4d47ba401eb160741401e657078c601e09b077a601da570761441d64f0751341d0978722461b88d8739561c85007125c1c05706f3501ba9406e1501b44806c94c1b24906d2341b05706b94421b16885b5f212d5c83a5f20a96c80a571f894c7ca411f08ec7b2371e857c7915b1dc55c749531cc5047293b1c64dc7092f1be4ac6d9271ac48c6a254192d50602541a4910643441a09b060a6417e9106724419a5206614418ad5854939192d68643561889585412918cd7460b5518a8e86223618516860c56180d685fb561624e45613117a9505d9341729b05392816e5705b15416a4d059a4414a4a058b54)) (pickBlockF p 4 0x29e110a70442e0d40b7a4429a110b68342d6500a50342920d0b623d2d48d4b49422d04a8b103d2c00e8ae0362b20d4a40342ce074b20342be0d0b11242bc110af8342be050b01242bc110ae0142b4500ac9242980c8a5830294088a481a2ae934a1a452ac508aa93e2a84c8a992a2a4498a88422a00f8a783229c0a8a6826290050a3044288d40a1b44284910be34d2f4d14bca5e2f0948bba3a2e88d8b995e2e4548b893a2dc4d8b31242ca178b18522c2134ae84a2b6118ac04528e110a283a2820d95624f54a90d50a3d5368ed4a2374f68d53a94f4d850d3213b4ae4dd2212f46e4ad1112742a48d0784f40c10cfe83b3da0dced02f39a0acdc02735608ccf01f32006cbf01728004c9eb5427691098238272db097a382705b09b96026a9509a2442664a09912426054097b5625c9588c139258d509514423e4e09436c24e9b09326023c4e0921542465109113c2424d08fa5023c9588d23e23a5588da44 (pickBlockF p 5 0x3a4178e88523a0128e784639c0b8a2822380d10e4b4d38ed28e2346384d14dd84a2e0048e4b5038c910e3b5038c910e22403740e0e13403808c8df8422de048de944376d40dd244398d48e5b50394d28e424d38a928e1a46382914df2443588f4de131372128b7012362110d804436c0d0d78443628f8d803e35e0c8dbb5e36a578da152366178d904635c110d682e358078d113434e570d3050344910d534d352d14d424a34a918d215e346518d09363224b8d005233e0e8c9834330540cb85c326910af04433ad34ce345336948cd23a332528cb14632a178ca0463240d8c881e31e920b60102d6080c3a5831a940b50102d2080c393a3124d8c39482d0080c183830a4b0c10482c0040c192c3020b0c0838304520c002c2c0040c734d318d14c5a52314928c424830c8e8c214a2fe128b30102da050b61242fa110baa342de4d0b51242f6170a18542840d0aa8442a8110a98442ecd40baa442a4110a8044 0x44a529118312e80450d944434511101344325110da3e4344f90c932442d790fa5e43c9490e95e4385190c14442e4b90b0194225110a24d426915092354204e50184a36a088b9812414111058343c04f104834416d41052504129110735141ad3506345404528f71463b64f8da1323404b8b91223a20e90403640e0b8b18223744d1000343044d100b5040091102b454089250195e404548ea93a3724d8cc92a2fe498e803a3fe0d8ff02e2ba088fda443ea500fda4c3f0530fa1403f4140fc1353e4910af1443300a0fa8403e88d4ab1353de108ea02a330068af4503e4500f88503de540fe25d3f28d4fb95c3ec544f99503e04d4f70423a60a8cb01a3c6490f5a4e3d28f8f11243c00c8e30253d2910ef8323bc108f19363c44d0ee8243ba4d0f03443be910ef1283b8090f63463d4d10f425e3ce918f32443ca4a4f21283c2490ed85238c0d0ea1503b2d78ec3523aed34eb3453aa528e994633e4b8b8922))) (pickBlockF p 9 (pickBlockF p 7 0x4e094137a444e8d4539b4d4e4d1534a4a4be91925a3e43c8c91d93a4dc4d8cd8292f0085368192c6045132344ce4d1343504ce91135b454d497934a5247e8e912a364744e933136408124d402d308095328192ba045312444b61013124c4c25412f04c4b41012c8504bc494f894434c4b0af0444b65012d2354b25091f12a2a20d4d301d4c6975302354be5091e92a4ba1712e0514b0140f803534a075238244aa93929a3e49e4c91812548c09129a4449c4c92692449a4d127b4449c911261244920a12494248e8d9232344acd192a3444a497928a464a0911259524940a52402848a0911813447c14121b5e484d4920b4d480d151fa4a47a9191e15e4765491d14a472518cd0292ee0851c01928a04515344466d3518b4a45cd191634544e528bb011466d4118244462d411824445c90113138458d0115232452508ba81144ed41132444481111b35246ad411a34a46493517a4a45a91915a454509110ba3d (pickBlockF p 8 0x3b20a4db8215328d9472345308d946a3452ed19463444e8545211395564a555128552491070513b00e55402954e0a153024546d3551b5c53e8d15234e54493d4f2354f453d399434824ad1912742813d068433ae0ace402735407cce81b31c05cbe01353e9114fa3e460494e3025540d794f24445e4d54e92938a0d54e0295324914c0244c2910fd1445349394ba424745654b1514d64e5301354ac4b5169253a01654a85140a0e4fc8353d80b4e182552293148b4251e9394712451a0913393450c5013125c50a5014485c5101414304050a95114a344000d13f0403f69714095c5005413e8404fc5013e95437e4d149b435248fd4823e5188c94594f51452d4394750850d3c93f4e44cd2a12d4804ad159274504954184f50412d3f8474f810d0983f4180ccf502d3ac0ace082737c094d481f33806cc60172f404d3b8444f49353ca454f08d53514a43e4893b0392f2045381444e24d127a3c4de4d138b50 0x67a4bd9a12b65a49d8e1236081198035a5fad59742395c48c56613958c4c57fb456011b17fb5453e1117eb5c5e48f5722355ac4f5641355eed597734e5f49195f9395ea5417aa505ee9417b16c5e8581759345de8d1769385da94175b445e515178b6c5e0d51772605d84e1751345d11b173a6c5cb181723545c51b170a6c5c09516c25659c93960a3e5bc5196c9505b29416da6c5b49816c1505a48d1681505a49116823859e4d16b4545aadb16a3545a68e168a3459c5816646c5965b164c60590d516346c58a5b1621545849b16096057ed815f16c5724c15e360576d615c12056a5115ca505685115b14056a4c15a1245708d15b96c5665518135d602d357f34b5f8d1d7db455f29457c24b5e691d74a3f5cc8ed71a375be8cd6e9515b852d6b94759a4fd6513b58e4dd619335804bd5e92b57449d5912356051157044544d055124d5409294d2465249154824455e4e51d9314864a51092155a0e4e8831)) (pickBlockF p 11 (pickBlockF p 10 0x6528c9ab15a6aa559aa13e63e4c8d605669a130e30446980f1a584c69a929a6246696129940126a5169a8b5a6a0d59a334d69e905a715a64e4898605669413185844690559a393e68c4b985056686971a1150688d69a0b566809599fa4666a8f99f14a6121599d2506725719e34a6769699c25666e5599b14666a4b98405660e151931306628f19192065e4f191920666d699934a6609699715a648481828566561319404c64c8e99194a6425199292d60c11991a342be0d1909242bc1118f04c658d299534665292993a466488d19115a6405598f94a63a518c88566300918c234636d118d2446320a18b8244e2d41182446285118792461e4d1893446229118812861c49105b5038c911858442be0d183a4860c0414f23562c4bd0b92b62a49d8992361a0bcd602b61809d8502361207d8401b60a05cc8813724d2dc7b4771692dc32476fe8fdbc23b6dc8ddb52336cc52db09476b44fda993b6924dda2933 0x7a0d55e7b4579a925e223f7848eddea377748cddc14975e4fdd693b7504ddd29337464bdd092b73849dcb123608111bb2457288e5a89457264e5bda59722945c2a3d6ea8d5ab159720545b013d6a04d54f04471c131bf34a6e8d19bda4a71a919a213d6604d5c6129644485a123c6fa8e9a112d714d75be23a712571c415170e541a092d7024d18d8446341118c8466300d1c0b4662e119c2c56708d59c19397044e1c013462c159be9506fcd69be3566f6969bd2566784e5961316f24a58f92142e159b904c460111b883c6e0131b924a6e2919b814a656045bbc5a6ecd69bab566d8d35ba25a6e65059512162a159b784c628111b6a566d88f9b5929626159b484c6b2929a72466768e9972366ac529b41466ce4f9911326744e1ac13a6744a9b2b5d6c8971b1a516c4941ab93a6704a9ae23462411188844620119878346b8919870466c1159afb566bc8e5aea386b68d1868566b0941aca5a6ae9599f23e) (pickBlockF p 12 0x7b0139eb0422220f46b8357a8d122cc5f8af16e2ac578a514e2735e892d4a2434a888d1a1da5e86294a14a4a83c91a07a3481657e0195a80055df51567cc53df194a7ba51dea94672c17d8e05a56415ca005621e13c6b0477a605de8c5e7988f5e023576e4f5d59355fe1154f0447968f5dfa3576c4f5d513577cd19e724673c4d5e3934636111e31346341118c8446300d1e3b5478cd118b844799191e5c54794d91e4b547904e1e293462c151e1a5442e15118044783161e036477ed51df25862a1518a044778991dda54626151d4a4673a8d9dc9467648d1890447628d18884462011187834764951d8a4461c111dbc6476d151dab64768d51d9a387608d18685475c550d605438c111d6458756d91d535475256186054616111d396474c55185054748951848547445518405460e151d036873ed61cf25873a561cd92060a151cd154730511830442be0d1cd1242bc111cc1247368d1cc96472e550c8854 0x7d24f5f09357c44b5f412564c128b40467c48ea08a3664a128b3846836d3e0cb4b82ed1e09b438248ea0714f80e52a009477d6519f393f7c04de0812d73613d9204a57011cb30462240fc6d0377a805e031442c41520684481a4920723480a550b08648181520423a80c5199184a2c0118af83480c490af044814d1a04a4680e8d2029568085199105a2ba158ad044804940ac8448028d0ac0542ae151f88147e0491ff0447f08d1f99347de490ab0442a6111fcb507f0910a90442a2110a70447e8d41f9a4429a111f88342980d15b0352960d0a48347e08f5f7a357dc509f69407d84a9cd03d6420e8ae0365680d4a40347fed75edb557fad35fe3457f6949fd23a7ee8d9fb1527ea4e9f91367d6491cc84d640128ad846566114a38447d2921f42387ce8d1f214428c111f29567c85198f85a28a159f12487c28e1ef84c7be491f02347bc170a1844284111eb8547b9169edc567b4d69ecb5663a168a0856)))) (pickBlockF p 19 (pickBlockF p 16 (pickBlockF p 14 0x8368d1fe9648b6550be0648b415223b548509520ca347b45522c1442f61122334484e9120ba348ac5b1ed9647f8551ec9442f41520a92482849209a348a85122984484c8d21812a84a499a184a34e11a28b4585e8ea122368a05162794485c8e211a348988ea25a3689ad1a2534485892a1124688497a1ca5285692a10a467f45599605a2ee159fc1442ea11223b5a88cd5a2025e87094a1523a8408da0515a7ee55a2294d654168ba0568828d21f1448829121e94487c4aa1e926672128cb846886d162123a8808da1f9458785121ba448748d21b23486e8e21b2348688ea19a36872d2a1c34686a91a192448605121734485a8d217b5e858d4a15b4a854d19fa956652168b88567e6510b784484c912129448468d21435a84ed5a1225e84494a10a3a8408da0495a7e455a0f94d64e168b70562da111f88447e05520e9442d81520e0448348e0b5844830941f79442d41120b23882a4d20a034810529f6146 (pickBlockF p 15 0x9168e99b84a328118c984490854244c5a91115a43b5a90cd5a4295a9065599b05a32415a029567c85199a85a32215a5145f93f16e4e45793114e4ab52926d2a48a5a91c95a4515690451a4092e74217d9a05a57a15cc805622c13c6f84731e1523f23c8f84f20e0108fed623ea588f65620d92031c1923d0548344c237b688f0d220c9208304c0c68548d4da23b36082e480c605482c4c23725882804236b688e8d2239a488e4522099208e21123704431215237c598db1463524a8d8919d005d666168c5056576154c405430e15233b5a8d496a34a568c656a09130664168c30568104823114a662128c28468ced2a3323d8ca8f23095a80e4819805a30815a041303061123123c8be4f0c10543021122f94a65e128c00468c6d2a30a5a8c04f62f13c80e4819705a2fe15a3cc5f8ef16e3ac578e114e35b5a8d0d2a3225a8ba56a0792073817d9685a57415cbf05622813c6d84783a490be854838491ff054 0x35a15839835996559a305a35815a6db5f9b2d6e6bb579a6d4e679569984fa6512e74a17da285a58615cd58561540fc39037990950d506498e1525a25498a912621489849b25aa64966912609603521525fa4497c5225e844964d1a5594a688168d40569628d9a104a34c11a27a5c9608da5d1509544e9a084a34a11a5c35d96ad565413a680128d18463441125895096d16a5ac56968d6a59b5696496a5825667e168d085695c51a569448bc4921825c95257255b5a954d5a5425694e4959f05a33e15a6345f98716e6045797914e5db5a972d5a5ba5695e91a40a3e95854a5314a74617d9e85a58015ccf05623213c70847948550ce86494615250b4890e5525014493cd824e96c910592431443381524db489345124c84492ed1a4b3448ca4d24925a91e95a459569284d99e05a33415a4934a90a9199d85a33215a42136674128cc04687c5724825091e8ea1e15c9064d99c04a32c11a4625c91ad7644355)) (pickBlockF p 17 0xa2c54a7a14a84e489d584d6a0128e1846590114df04409807613120a22d028a458a26d527fa40a2456212120a201527504ca1d5a286a5c8124827485c9d013285c60a145827384ca0c952833588464827283c9c813281940a115a283a5ca0a91211130a084a27185ca040928024437a1127fb5e9f4d1a7f2567c8919a785a37815a109309f84a27105c9f0d21f24509f49027c9508404827b85c9c0130dd0449e45327ab5a9e8d5a7994d9e24ba0492269c168dc8569dcd1275b449d0142731449ca4d2720189c2d3277b469da93e762479d453e7494b9ce51e719439c44ae70127a4516a8e35fa34d6a8bb57a2ad5a6534da1e97e8625ba1295e80a539fa9067da3b9ec8de7815a83c489d405f6921696385737015a6f84c1c60dc5682f0ea09c2581d9a4152689649ba5526e0549b44d26c16c9a05526713c9acd526a9349a80d2690449a29366824574e135a404a3641196204535c1126735699a959a385a (pickBlockF p 18 0xadad5ab4a5face96eb2257abe94ead239aa88e2a923475e17dad05a59a15ced0561640bc3d027a62590eb864aa015298154a36510eb05485e8c2a6954a9815255a4ca944d25523ca905b29693c85c8c216930a8cd5216240a8a4d2a203485690215230a584f2a085ca7e4f9ac85a3aa15a9e924a768f69d235a72499ac04a3a811a9e251a709429b95d6ae128e98469965529a85499655a901466ac168e8056a62d36983456aa128e7846a5ad5a96346a56959aa05a39c15aa7c5fa9d15ea5b5fa92d6ea3b57a86d4ea134ba80d1e9f25aa6c95a5323e8528ca9a15fa6656a99157a5e55a9713fa544fa949377c64c9d685f6a61696505739a1587284715e0fc3c03709c0b401025a5005e93254a4815290c5da3315690346a1c966842516a4168e5056a4a0fa91832a3cd0290c68a411628db54a3e560e4064a3a1527684c38c1128db569ea56a141226a2168e285609a0768cc58a30580e08549d8130df844 0xb1c512c013cb2c172b9814b1a552ca134ae40505b82f10409e1b930b131621b120b1e132c8a3db208e6c7235b1a8c65712e86a4889203d1d80d61a130b1316219920b10132c5a3fb148eec3a37b0c8ce5692e86448ac283fb080dc5b02f10209ec084cb04d3ac0346afe9183f835af8132bea3faf68dc9103f1d60debd0272420fc75037a4051aba040aec8febaa3bae68deb9233b38d3ecd34bb2ad1ec9b439588fa18a32b24532c6146b06512bf13eaf24f2bc134aee4b89004f1d211c5a03f0fc0deb88143d6112b7b5eaa68d28d93576e135b004a3d81196b0453d4111da84d6be128f38465a8114f3044abc4a2b6454ad6d52aea38ad4152b4244aae8e2b336cab88e2b2960ac6952b1244ac24a2b0024abc112ab950abad7aae356ab6959af05a3ca1583d835ab2112ab950ab093eab24776613dae84a5a611cf2046aaa09dd903d6b80e8f18365a40d4f1034aa6919d804f6b6129688473c211ab7456))) (pickBlockF p 22 (pickBlockF p 20 0x6cc1696e0573fa1589484f1e411c5d03f10c0dee601799715ae4b5ab8cd59b285a3f815adf250b931b265b6cb869b2dea60b904e0fd844b78940fd044b8cd72e125cb76942e29603f2110fc044b8692ee12476c81296d8473ee1189382f1e009ed9356b5cd3ad334680a95ae0246a7852a481386c6168fb0561080d6df1383ea112de1503e81129d948b5a4e29d138b72132deb4bb76d1dfda47b748fedc237a704ea4812a6c41296d0473e61189303f1de0dedb827b6a572da1283e4110f884480b582d9250b62580f8044b5a4e2d6a50b5edb2d7260b584e2d526c91e4e2d4928b4a132d2950b4f182d3260b48132d126cb42952d0128aef176e535db8ed2ee2347b82972dfa51b6c942d9a4bb6091ed5a3fb508eed1a37b3e8ce9b13a91c4a9b084a5ae11cf684624a0fc770371700bc41827b22552ce944b044f2bb0148744c21ca40b20552cd934aea052c4954b2e112c7834b020b2ccd688708c2cc15c (pickBlockF p 21 0xb42515de04d6da1290e0465c01150c044c1a959b605a42e15ad0256c16559b585a42c1580b025c1c95b0623ebea57eef15bb3e55ec9953c144a5dd05f6d41696f85742a1582781f02a05f02a3dbfc8d621922bfad1b03a46be811302c54c08d5301938be615300a548844c2f9054882482fe144bf4d12ffc58bfcd52fea58bf650220120be0152fc84cbde112fba64bec952f7054be80a2f8b40bde552f992fbe44aef8127bdc48f04345c0c9270123fc008eefc237bea8ce1d922bda1109583f1e80dc5e02f11009e7aa54bb05527a244bae511028548c291102064ba04f2f3944924922f2934bc75a2f115c8144c2f085cbbe4d2eeb48bb8d1290144bb417100044baa152ec35abaed59b405a3fe15aeb04eba810ae8a5cba0d5ae7a46a7e52a789466ce168ff056bd716ef5457bd2d6ef4357bccd3ef234bbc0d1eef343a7c92a782469228ea2ea36bb653e9994abb251ee9946ba44fee713eb9a4de01932 0x6f41291c846b5295a7e246c66559bc85a47015b23c5fc8d15f2235ac78d5b1d25fc7296b1c257c6a95b0015fbc856ed4157b3454ea114b9f651e499398904c71a12bc644a7189277c6485e105f6f01697305746e1587c0471940f445035c6009c2981f03405f17254c5815314c5dc4315714346bc6566cc9516ee1691a056c5a0fb15832c4cd0314c68c5116311b54c4e96119064c4a1530904c46011311b56c3896a239216ec169178561920b710c58c4098115854c2213114844c3c94b0da4a88c485e004d6ea129168465c8115140441900b513044c325330e35ac36d5b0d24dc304a6051216e816912856448112fda5e9f291b0b1567c8519b985a44615b09b44c28d1b0924fc2291efc84fbc212ed2047b2c10ea082b9ee09f1545ac48d7f1135ac3ed5f0eb56c18d370ba5abf057ef015bb4655eca953c2a506a013b9ec4de2212177a17db705a5c615d11056c201307b03718e0b42881f03005efb94d)) (pickBlockF p 24 (pickBlockF p 23 0xccc1333413fcce4ef32937cc84ce4b1298944873183fcc40dc2c81f04405f14246ac293a82246cbe51810025cb81332e93fcb64dc9983f1fc0df2d0172640fc7e837ac00fea203ba040de6a033cd493334a46cc29133023eabe53ea194ba0251e6994392a4e624931cbc4a72c928cb04909884f1f811f2b8240ae07c0f8174aa1132ab5ec468d725934798135c284a4ac119790454a8111e504d708129288465e011528044c0697ad6256ca4559c185a4941580e825ca0112d6a50c9e53f2714779013dc104a5d811d24046c9a05de383d7020e9238365d60d523034c96d19e284f7001297504748a11b2a456ca6d5b0115fbcc56ed5957b3854f28939c984e32513478817dbf85a5d215d220560aa07c0e017c6e99120864c901531b254c4691120054c8a4a5bf05a47e15b21134c804f71f935c7c495be84a47c11b21a5dc825471e9506f81291e846c1a9531d854c1a95b142466f61691d056c6ed371b345 0xd1010b22b4ac30d1ada256d0a519c605a4ca15b49c5bd2515f2234ac2ed1b47a4fc7292b46a47d0e91af495bb6655eb394fa9252e861479b250e5d93d8c84d74312bd084a741927806485c585a5f015d3205627413c82847d0409c2e81f04e05f06c56cfed6b3e35671416931856ce85433fc6cc1adb33f238cf25b3399604c4113391504c21133e35ccf69833c15cce2541300444bc0d33ca3bcf08ddc483a5ec0dd2e8362700bc81827c82d2ad8a56aca93a852469748f202956cec519c405a4b815812825ce88e12d844ce49412d044c80922aba38c7e8e33784cce6d2f38b47c7a8e9fb147ce04ff371379744b5c384a5e811d2c04626e0fc81037cda05f3045dd00d773eb4bcf4d1f1e23acee5733a951cd8542f414bb6051eb213fa8e4ee849379ae4ce5c92d70c129798474ae1189b03f2020dc2d81f04805c2d01f04605eb193da8c4e6829359ac4c64b92989a4849a83d1fe0d626230a0d16225920) (pickBlockF p 25 0xb8a95a8c2469828f9c805a52a1588546c5fadb35626cd569835516cd5258362a5fd8696f1ca59d7e95f5da53d749474924bcf491f2a23dc8c8ef0fa37c3a8d75c95fd6e56e99959d6655f57953d5c546f514bb8851eb713da9c4ee8b937a2a4d66012f9384ae3a9278aa48f5685fd5015de804d71e1297e0475281197d8454f61108483719e0bc4d0270ca07c180179364e6399351300d75292bd4849f518270c807c178170c607c1701797c8fa392360580974f92fd3c49c6682f12e09f4e81719807c4b01797a07e4c81b8e205e29813d4c8e751238d428d350139d384e34d9349784be4c12b8e049e29123d340d06582f12a09c3081f05605eb613da264d628921a2491b4b946ad40bea602ba2009e6e023d30d174b149ad24fea593ba1e4de6d93389c4874a8442780fc838370be07c14817c38d5346254c36d1345a444d615314244d2252348144d1c17133844d121534635ad16d59c685a4cc15b4504e 0xc4ed1b142468fa4d68fa468f68da90146c904af12927aa00ae8e82798e07e5181b8f405e2d013d92d1766a49c8e8ef12237d98526a793ba384de6312f9444ae3c9278b248d80855542153658442160dc6982f13e09c3481f06a05f11a35a364d57f84553c1133f356c1a95a509397281694e85613a0d6e42569888fa659567261694e05606609764b56d2696f3ea57c4491764239bd656ee3957a34517639399864be4f92b8ee49e2b9237241697f0575361586882f13809c3381f06405f622685161135f254d88db31b254d16911450545120d35ea5051011310c6ccf8db35e250d845b360960d801b14384450c1135f25cd7a54142844d78d930f3445081533db56c40d1a4f1397221694b056d705a141844d625535c26ca60552eb94450415140834d6454140044a331b2e336cd6c9b35aa60d605435a06c4fe1113f044d649435895c4fa11358264a2c9113e054)))))))
  6 11 7
def m_2298 : Nat := 0xf0f0f0f0f0f0f0f
def s_2298 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_2298 : Nat := 0x10505070307070f
def bds_2298 : List (Nat × List Nat × Nat × Nat) := [(m_1986, s_1986, 6, g_1986), (m_1745, s_1745, 5, g_1745), (m_1776, s_1776, 5, g_1776), (m_1963, s_1963, 5, g_1963), (m_1828, s_1828, 5, g_1828), (m_1978, s_1978, 4, g_1978), (m_1947, s_1947, 5, g_1947), (m_1984, s_1984, 4, g_1984)]
theorem kn_2298 : KnownBin bds_2298 := by
  intro b hb
  simp only [bds_2298, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1986
  · exact lb_1745
  · exact lb_1776
  · exact lb_1963
  · exact lb_1828
  · exact lb_1978
  · exact lb_1947
  · exact lb_1984
theorem sub_2298 : ∀ b ∈ bds_2298, m_2298 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2298, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2298 : ∀ b ∈ bds_2298, canon b.1 g_2298 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2298, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2298 : dagCheckRootsF m_2298 g_2298 bds_2298 (dagRefF 1742 (dagTraceF m_2298 s_2298 8 f_2298) l_2298 0) s_2298 8 = true := by decide +kernel
def node_2298 : Nat → Bool := dagCheckNodeF m_2298 g_2298 bds_2298 1742 (dagTraceF m_2298 s_2298 8 f_2298) l_2298
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_0 : treeBlockF 0 128 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_1 : treeBlockF 128 256 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_2 : treeBlockF 256 384 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_3 : treeBlockF 384 512 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_4 : treeBlockF 512 640 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_5 : treeBlockF 640 768 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_6 : treeBlockF 768 896 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_7 : treeBlockF 896 1024 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_8 : treeBlockF 1024 1152 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_9 : treeBlockF 1152 1280 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_10 : treeBlockF 1280 1408 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_11 : treeBlockF 1408 1536 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_12 : treeBlockF 1536 1664 node_2298 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2298_13 : treeBlockF 1664 1742 node_2298 = true := by decide +kernel
theorem nc_2298 : ∀ j, 0 ≤ j → j < 1742 → node_2298 j = true :=
  (joinChecks (joinChecks (joinChecks (certBlock nb_2298_0) (joinChecks (certBlock nb_2298_1) (certBlock nb_2298_2))) (joinChecks (joinChecks (certBlock nb_2298_3) (certBlock nb_2298_4)) (joinChecks (certBlock nb_2298_5) (certBlock nb_2298_6)))) (joinChecks (joinChecks (certBlock nb_2298_7) (joinChecks (certBlock nb_2298_8) (certBlock nb_2298_9))) (joinChecks (joinChecks (certBlock nb_2298_10) (certBlock nb_2298_11)) (joinChecks (certBlock nb_2298_12) (certBlock nb_2298_13)))))
theorem lb_2298 : LowerBin m_2298 s_2298 g_2298 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2298 sub_2298 gl_2298 rc_2298 nc_2298

def f_2299 : Nat → Nat × Nat := unpackForestF 0x1d1e323064b7cac18edaa3054b5aac14ed0ab21460a4628d4495882b1888204c223001f 5 10
def l_2299 : Nat → Nat → Option Nat := unpackLinksF 0xb9b8b1b0a2a099988a81806b6868686861440f01 0x30891919f2b14566a8cb55882b0c444aac851842b0c44346a54ac8158813968f092dd1db14b5276748c223001f 8 3 10 5 4
def m_2299 : Nat := 0xf0f0f0f0f0f0f0f
def s_2299 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_2299 : Nat := 0x10505070307070f
def bds_2299 : List (Nat × List Nat × Nat × Nat) := [(m_1986, s_1986, 6, g_1986), (m_1776, s_1776, 5, g_1776), (m_1745, s_1745, 5, g_1745), (m_1828, s_1828, 5, g_1828), (m_1963, s_1963, 5, g_1963), (m_1947, s_1947, 5, g_1947), (m_1978, s_1978, 4, g_1978), (m_1984, s_1984, 4, g_1984)]
theorem kn_2299 : KnownBin bds_2299 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1986
  · exact lb_1776
  · exact lb_1745
  · exact lb_1828
  · exact lb_1963
  · exact lb_1947
  · exact lb_1978
  · exact lb_1984
theorem sub_2299 : ∀ b ∈ bds_2299, m_2299 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2299 : ∀ b ∈ bds_2299, canon b.1 g_2299 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2299 : dagCheckRootsF m_2299 g_2299 bds_2299 (dagRefF 19 (dagTraceF m_2299 s_2299 7 f_2299) l_2299 0) s_2299 7 = true := by decide +kernel
def node_2299 : Nat → Bool := dagCheckNodeF m_2299 g_2299 bds_2299 19 (dagTraceF m_2299 s_2299 7 f_2299) l_2299
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2299_0 : treeBlockF 0 19 node_2299 = true := by decide +kernel
theorem nc_2299 : ∀ j, 0 ≤ j → j < 19 → node_2299 j = true :=
  (certBlock nb_2299_0)
theorem lb_2299 : LowerBin m_2299 s_2299 g_2299 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2299 sub_2299 gl_2299 rc_2299 nc_2299

def m_2300 : Nat := 0xf0f0f0f0f0f0f0f0
def s_2300 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_2300 : Nat := 0x10105010303070
theorem lb_2300 : LowerBin m_2300 s_2300 g_2300 9 := by
  refine lowerByRows [63, 61, 62, 60, 0, 0, 0, 0, 55, 53, 54, 52, 0, 0, 0, 0, 47, 45, 46, 44, 0, 0, 0, 0, 39, 37, 38, 36, 0, 0, 0, 0, 31, 29, 30, 28, 0, 0, 0, 0, 23, 21, 22, 20, 0, 0, 0, 0, 15, 13, 14, 12, 0, 0, 0, 0, 7, 5, 6, 4] (by decide +kernel) ?_ (by decide +kernel) lb_2298
  intro w hw
  simp only [s_2300, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2301 : Nat := 0xf0f0f0f0f0f0f0f0
def s_2301 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_2301 : Nat := 0x10105010303070
theorem lb_2301 : LowerBin m_2301 s_2301 g_2301 8 := by
  refine lowerByRows [63, 61, 62, 60, 0, 0, 0, 0, 55, 53, 54, 52, 0, 0, 0, 0, 47, 45, 46, 44, 0, 0, 0, 0, 39, 37, 38, 36, 0, 0, 0, 0, 31, 29, 30, 28, 0, 0, 0, 0, 23, 21, 22, 20, 0, 0, 0, 0, 15, 13, 14, 12, 0, 0, 0, 0, 7, 5, 6, 4] (by decide +kernel) ?_ (by decide +kernel) lb_2299
  intro w hw
  simp only [s_2301, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2302 : Nat := 0xff00ff00ff00ff
def s_2302 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_2302 : Nat := 0x1500570037007f
theorem lb_2302 : LowerBin m_2302 s_2302 g_2302 9 := by
  refine lowerByRows [0, 1, 2, 3, 8, 8, 8, 8, 4, 5, 6, 7, 8, 8, 8, 8, 16, 17, 18, 19, 8, 8, 8, 8, 20, 21, 22, 23, 8, 8, 8, 8, 32, 33, 34, 35, 8, 8, 8, 8, 36, 37, 38, 39, 8, 8, 8, 8, 48, 49, 50, 51, 8, 8, 8, 8, 52, 53, 54, 55] (by decide +kernel) ?_ (by decide +kernel) lb_2298
  intro w hw
  simp only [s_2302, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2303 : Nat := 0xff00ff00ff00ff
def s_2303 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_2303 : Nat := 0x1500570037007f
theorem lb_2303 : LowerBin m_2303 s_2303 g_2303 8 := by
  refine lowerByRows [0, 1, 2, 3, 8, 8, 8, 8, 4, 5, 6, 7, 8, 8, 8, 8, 16, 17, 18, 19, 8, 8, 8, 8, 20, 21, 22, 23, 8, 8, 8, 8, 32, 33, 34, 35, 8, 8, 8, 8, 36, 37, 38, 39, 8, 8, 8, 8, 48, 49, 50, 51, 8, 8, 8, 8, 52, 53, 54, 55] (by decide +kernel) ?_ (by decide +kernel) lb_2299
  intro w hw
  simp only [s_2303, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2304 : Nat := 0xff00ff00ff00ff00
def s_2304 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_2304 : Nat := 0x100150013003700
theorem lb_2304 : LowerBin m_2304 s_2304 g_2304 9 := by
  refine lowerByRows [63, 61, 62, 60, 0, 0, 0, 0, 59, 57, 58, 56, 0, 0, 0, 0, 47, 45, 46, 44, 0, 0, 0, 0, 43, 41, 42, 40, 0, 0, 0, 0, 31, 29, 30, 28, 0, 0, 0, 0, 27, 25, 26, 24, 0, 0, 0, 0, 15, 13, 14, 12, 0, 0, 0, 0, 11, 9, 10, 8] (by decide +kernel) ?_ (by decide +kernel) lb_2298
  intro w hw
  simp only [s_2304, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2305 : Nat := 0xff00ff00ff00ff00
def s_2305 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_2305 : Nat := 0x100150013003700
theorem lb_2305 : LowerBin m_2305 s_2305 g_2305 8 := by
  refine lowerByRows [63, 61, 62, 60, 0, 0, 0, 0, 59, 57, 58, 56, 0, 0, 0, 0, 47, 45, 46, 44, 0, 0, 0, 0, 43, 41, 42, 40, 0, 0, 0, 0, 31, 29, 30, 28, 0, 0, 0, 0, 27, 25, 26, 24, 0, 0, 0, 0, 15, 13, 14, 12, 0, 0, 0, 0, 11, 9, 10, 8] (by decide +kernel) ?_ (by decide +kernel) lb_2299
  intro w hw
  simp only [s_2305, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2306 : Nat := 0xffff0000ffff
def s_2306 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_2306 : Nat := 0x15570000377f
theorem lb_2306 : LowerBin m_2306 s_2306 g_2306 9 := by
  refine lowerByRows [0, 1, 2, 3, 16, 16, 16, 16, 4, 5, 6, 7, 16, 16, 16, 16, 8, 9, 10, 11, 16, 16, 16, 16, 12, 13, 14, 15, 16, 16, 16, 16, 32, 33, 34, 35, 16, 16, 16, 16, 36, 37, 38, 39, 16, 16, 16, 16, 40, 41, 42, 43, 16, 16, 16, 16, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_2298
  intro w hw
  simp only [s_2306, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2307 : Nat := 0xffff0000ffff
def s_2307 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_2307 : Nat := 0x15570000377f
theorem lb_2307 : LowerBin m_2307 s_2307 g_2307 8 := by
  refine lowerByRows [0, 1, 2, 3, 16, 16, 16, 16, 4, 5, 6, 7, 16, 16, 16, 16, 8, 9, 10, 11, 16, 16, 16, 16, 12, 13, 14, 15, 16, 16, 16, 16, 32, 33, 34, 35, 16, 16, 16, 16, 36, 37, 38, 39, 16, 16, 16, 16, 40, 41, 42, 43, 16, 16, 16, 16, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_2299
  intro w hw
  simp only [s_2307, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2308 : Nat := 0xffff0000ffff0000
def s_2308 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_2308 : Nat := 0x115000013370000
theorem lb_2308 : LowerBin m_2308 s_2308 g_2308 9 := by
  refine lowerByRows [63, 61, 62, 60, 0, 0, 0, 0, 59, 57, 58, 56, 0, 0, 0, 0, 55, 53, 54, 52, 0, 0, 0, 0, 51, 49, 50, 48, 0, 0, 0, 0, 31, 29, 30, 28, 0, 0, 0, 0, 27, 25, 26, 24, 0, 0, 0, 0, 23, 21, 22, 20, 0, 0, 0, 0, 19, 17, 18, 16] (by decide +kernel) ?_ (by decide +kernel) lb_2298
  intro w hw
  simp only [s_2308, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2309 : Nat := 0xffff0000ffff0000
def s_2309 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_2309 : Nat := 0x115000013370000
theorem lb_2309 : LowerBin m_2309 s_2309 g_2309 8 := by
  refine lowerByRows [63, 61, 62, 60, 0, 0, 0, 0, 59, 57, 58, 56, 0, 0, 0, 0, 55, 53, 54, 52, 0, 0, 0, 0, 51, 49, 50, 48, 0, 0, 0, 0, 31, 29, 30, 28, 0, 0, 0, 0, 27, 25, 26, 24, 0, 0, 0, 0, 23, 21, 22, 20, 0, 0, 0, 0, 19, 17, 18, 16] (by decide +kernel) ?_ (by decide +kernel) lb_2299
  intro w hw
  simp only [s_2309, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2310 : Nat → Nat × Nat := unpackForestF 0x647151c5279d82127111db60555c4273980b57105c01f 4 10
def l_2310 : Nat → Nat → Option Nat := unpackLinksF 0x7971696861595851494841390e01 0x205d427815e760849db60555ce602d5f247b51e927711d027105c01f 8 3 10 4 4
def m_2310 : Nat := 0xffffffff
def s_2310 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_2310 : Nat := 0x1337377f
def bds_2310 : List (Nat × List Nat × Nat × Nat) := [(m_1770, s_1770, 6, g_1770), (m_1742, s_1742, 5, g_1742), (m_1743, s_1743, 5, g_1743), (m_1765, s_1765, 7, g_1765), (m_1768, s_1768, 6, g_1768), (m_1745, s_1745, 5, g_1745), (m_1761, s_1761, 6, g_1761), (m_1752, s_1752, 5, g_1752), (m_1771, s_1771, 6, g_1771)]
theorem kn_2310 : KnownBin bds_2310 := by
  intro b hb
  simp only [bds_2310, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1770
  · exact lb_1742
  · exact lb_1743
  · exact lb_1765
  · exact lb_1768
  · exact lb_1745
  · exact lb_1761
  · exact lb_1752
  · exact lb_1771
theorem sub_2310 : ∀ b ∈ bds_2310, m_2310 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2310, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2310 : ∀ b ∈ bds_2310, canon b.1 g_2310 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2310, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2310 : dagCheckRootsF m_2310 g_2310 bds_2310 (dagRefF 13 (dagTraceF m_2310 s_2310 8 f_2310) l_2310 0) s_2310 8 = true := by decide +kernel
def node_2310 : Nat → Bool := dagCheckNodeF m_2310 g_2310 bds_2310 13 (dagTraceF m_2310 s_2310 8 f_2310) l_2310
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2310_0 : treeBlockF 0 13 node_2310 = true := by decide +kernel
theorem nc_2310 : ∀ j, 0 ≤ j → j < 13 → node_2310 j = true :=
  (certBlock nb_2310_0)
theorem lb_2310 : LowerBin m_2310 s_2310 g_2310 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2310 sub_2310 gl_2310 rc_2310 nc_2310

def m_2311 : Nat := 0xffffffff00000000
def s_2311 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_2311 : Nat := 0x115155700000000
theorem lb_2311 : LowerBin m_2311 s_2311 g_2311 9 := by
  refine lowerByRows [63, 61, 62, 60, 59, 57, 58, 56, 55, 53, 54, 52, 51, 49, 50, 48, 47, 45, 46, 44, 43, 41, 42, 40, 39, 37, 38, 36, 35, 33, 34, 32] (by decide +kernel) ?_ (by decide +kernel) lb_2310
  intro w hw
  simp only [s_2311, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2347 : Nat → Nat × Nat := unpackIndexedForestF (pagedUnpackF 23 7 (fun p => (pickBlockF p 14 (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x68ade0f69641ed2c03da5507b4a80d158c1a1378342630754fc0ec9501d53903425f0726da0e4db01a12d83425706f4c80d2df81a5b903626c0696ca0d49701a5b2034253067068004d0c1943202e26f0630480b898c1841202e23b05f0980b88dc175a202e2330022bc01517414daf82c46c0536b60a6d5c155ae02a4640536a60a51f00292782535f04f8d8094d6c129ab82636c04b8c8094d4c1253e00524b04169e08d170105a5820b47043698085150105a182057000a48e070d7c0f63601c35b0386ae074db00e63201c3530374f801490c0b6b681745f033ad805d16c0ba2b81846c02fac805d14c0b53e00523b02b8d00415b4085af81446c0216b6042d5c095ae0124640216a6044d480841b01047000a46e03c99004eb680e45d01368802917c066b600a45b0148ae02d1b0056b200a4530134f80148cc044be00592b00f48a01cdc002c9380623400b24601413800833001a6f0034c60068ec00d1b8023440034660041780040980003f (pickBlockF p 2 0xff0ec1fb5d03f43a078c7f0f90dc1f21b03e43307bc640f70881e31cc3d63207936f0f36a81e4d8c3c42a00135f0ee6e81dc1d0396bf875b540eb0a81cb5cc3a53207346f0e74881cd18c3941a00135b0e2cf01c41d03663f86fc7c0df0881b31cc376b406d36f0db6d81b4d8c364360013570d50dc1aa1b035433069b740d30e81655fc33c2706784c0cf08c19ad503342a0595730c94d019299432532059c6f0c549018a91431522059c630b34de16698c2fd3f0602440bf4e416693c2f1bf05e35c0b34961729f82e539059a470b74c8168df82d52605a3540b34861640d0009a9857b740af0e814d9fc2b1b20560640a6ce615499029eb78542540a7ac614c0d0009a585104e0a208c144110282bc050074096cfe13c138272b404e064096ce61351a025eb784c458097ac612c170009a384906e0920d8124198241ba048074067cfe11c158231b2046064067ce6114190216b78440460866a810c150216b1833c540804d21009a020132840264 0x17f4e42fae305f5400b867717b4d02ed5bc5e5210bbc701774e02ed59c5c22a0ba168171ade2e45c05c6b38b823810b6862d2d6c5a5ab8b4b4b16968e2d51505a5a1885a6a11fadc2c0d7c596360b035b1606ae2c4db0586320b035315f2c823edbc55d278ae35c1574962ae91c565260ac3541574862ac4d047db58a736f1538f829cdac539b38a836c14f8e829cd8c534be08fb6714549e294d70515258a2a4714749828cd50515218a213411f6c62759f84ed378a037c13b4d627699c4f53609e37413b4c62744d047da589c56812fcfc2611bc4d6be09846b1308ce264db04c6ba09846312f2b823ed1c4b5b209067e12badc2411504853789437c1214d624299c495360923741214c62441984841109013411f6862169484751c08635b11b4c0218d5c4651c08634b10c68e22b1504551c08634311326821ad2c435a388745410f05c21c4d0435a188625210b0d400205c4243200156f1070a800558c4143200136f103068004d8c3fc3f07f87c)) (pickBlockF p 5 (pickBlockF p 4 0x1fa28e3f69a87ed330fe14c1fb4a83f450c7e538085b671f7470216d8c7d1ba0fa2781d9afe3e09287c1210f82401ee6a83dc960766bd8f527a1ea4f03d49c8799c60f39391e72683cca00766bb8f1b541e34b03b35cc784b40ed46f1df2903b51ac774b80ed4671db2903b518c7651c085b5b1d6cf03ac9e06ee3f8e925a1d24b03a49487423e0e82481bb8f63989687312c0e62521c8d003925b0724b08e42801bb8ee38b1f0715240ddc731c32d03791bc704a40de46b1bf2e037919c6f4a40de4631bb4c0216d5c6e1ba0dc2781afcfe36ae306d5400d7e771b32d03615bc6c4b80d85671af470216d2c6ad250d5a481ab4843535e06a53c0c3e7f1a748434b600695400c3e771a02d23405a0680b28d0164188ade3365f466cbe0cd97119b2e031159c620b78cba7d1974f83105ac620b38ca17c1914ea3245b06453a0c416318d4f431c5f06353b0c415b18b2d83125e8624bb0c41571874a0216d1c60d350c1a621834c0302dd06053c0b867f 0x27f0cc4fadd09f43a13667f27b0ac4f2d909e4321366732770c84e55bc9d423139b542730a84e558c9b22a13826826dade4dc9609b6b19360342146864c892c9a6b81322472644764c88dc995a21322332142cc4b8d7c9863612e35b25c6ae4bcd709763212e35325b8f843893c94daf92c46c2536b64a6d5c955b612a4642536a64a49f08712592534f24f8b8494d2c929a392634c24b8a8494d0c926b810e2472416be48d1b0905ad920b572436d8485190905a992027c21c48647117c8f6b611c45b2388ae4751b08e6b211c4532374f84388ec8b9af91a46c22e6b645cd5c8c5ae11846422e6a645c0d88b63810e23722769e44ed2c89da3913b4322706c44cd80875a210f45f223ad843d16c87a2b91046c21fac843d14c8753e10e2332140cc42a9bc8553190aa3b21546e42cd108551990a05e0010364249a042eb790827010bace41c9a042db790623810b6d63f456c7e8ab90416a1fa29e4069a8814b6101a662034b83f452c804ae10016a) (pickBlockF p 6 0x2ff6a65fc950b693197b56f2fbcf85ed5acbdab397c46c2f7ce85ed58cbd52a16d23b2ed6de5e51f0bb5b5976b672ef6d85dd1d0bb5b19764582da46e5b6d10b72b797467c2dcad65b959cb96361726742dcac65bf17cb7e2d96fc572df8a65b88d0b751a16e0522db4a85b48ccb44af16936f2d70685a4d8cb49a59693472d38a85a4d0cb442900081f2cf0c84295bcb342a10a5632cb0c8428dbcb241a10a3632c60fc58c1d8b12ba1620742bb8fe5821b8b043315fc642bf0885771ccaf1b795e3632bb0a8428d7cae1ba15c0742b1afe56ad50ad42a158d732b28de56518cac41a10a35b2aecf055c1d0a9e3f955c7c2ab08854f1ccaa1b79543632a70d8428d5ca90371520662a26e85441d0a66bf94f84e29f08c53ad50a742a14cd7329a8de53518ca641a10a3532966e852c1d0a3f3f949b642930c851f9cca42b794856328f068428d2ca302714604628aaf05141d0a0b3f94404e286ad050c190a0b39941d6f283ac6504170851a393f86e 0x37f2e86d95fcdf0a71be14637a6a86f4550db2bd9bb97e3772ec6eae30dd4c61b65773726a86e4550db2b99b6c6f36d8d66db19cdb6319b61342d16b66d39e0da4ba1ab47f3662bc6cc558d923e1b21443568f66c2578d84ab1afe8035f3186ad1dcd723e1ae1443568e66aedbcd5db59abb673576c66ac5b0b45ab9a9b743532e86999fcd41c61a818c34ccee69b5bcd36b39a61342d1696692538d24a31a3d783472e867b9fcd14a71a1d8034331867b9dcd063219f56f33f8f867d59ccf4ae168b4733a2dc674598ce1ba19c174329cfe66c5f8cd1c619a18c329cee664590cb6b799814e32e8e065c5f0cb6b3994c5432aade65559cca49a168b4332249664491cc891d9912373236886448ccb44b318d36f31f8f8634dacc69b398e36c31b8e8634d8cc663216d26f3116be62d1b0c45ad988b573136b8625190c45a99882542da4d6610d7cc363618435b3086ae614d70c26321843533078f85b499cbfdaf98246c2ff6b65fed5cc05ae180464))) (pickBlockF p 10 (pickBlockF p 8 0x3ff6887ee9c8feda21fe2343fb2b87ee954fe11a1fc14c3f74a87ec50cfd4121c72333f22f87e4050ef4959f4a4f3ef0487d292cfa5239f53543eb4887d4090fa5219f43703bd24e7bc8fcf94121ef23b3e32987bc8dcf7da21f02343df0487bc8ccf75301df2343d725e7ae4acf5c939ec2343d72467ac540efc921e8b7c3d24d87a4580f44921df83f3cf4c079c8d0efc1d9e4c703ca6c0794580f24921df8373c64c078c0b0f011a1e0b603c24a0784540f04921e01443bf06677c050ef4919c716638f2ba774590ec6369d935f3b78d8764d6cec9ab9da36c3b38c8764d4cec4be1c792b3a68da74e93ceb5ae1d3a4b3a748e754930ea5aa1d3a433a704c74cdc0e3c939d205e3a32c87211b4e65ae9cd23f39a47673c530e691b9ce34439a466734098e65301c82343916be72d1b0e45ad9c8b573936d8725190e45a99c817c38f24671c198004219c61642d1ade7145f0b46b39c41642d16de70c4d0b45b59c217c2d16ce7044d0b45b19bfb74 (pickBlockF p 9 0x47f04871c98d1f13a23e074473afe8f29511e42a239d734772c88e91bd1d4a223a46347304871c8ed1b49f23683e46d06c8dc0b91b41a235c7846b0e88bb5fd1949f23283e46506c8cc0b91941a231c584630a88bb5cd185b422f46f45f6908bd18d174261c72374582dc8b01b91603622c0664564e88ac1d0fd6bfa2894e45109c8a213114423227a5444f0a87eb5cd13432222c6f44827c8900f91201e22403644648888c111116319fab4443f2d287e5a10fcb2a2005e43f2c87ed1bd0e4a4a1c94843928a8740f90e4a21fb4634362b286c5550bdafa181394302708604d50c41721813442f6a67ec8d10b51a1fb16f42b05c8544f1095a22142344252b884c8d1094aa1fb16341d468844491074bf20f23441f24883c511074b91fb14f41a4a8834551042b920ba4441728882d189041a220827e4104e4824d110412ea0825c3f62968188d1030bf2061723f628e812991024b21fbd7e4072a880b1b90149e1fbb44401468804491004b21fba7e 0x4ff4c29fcd212ea39a7ca694f94d09f29953e53225dc6f4f44929e89213d122a7a2444bb8d69de9f53bd3e277a714ef4e097719d3a924a752484ea48a9d49112ee31a5da6f4e66fa9ccdf12ed35a5da674e34f89c0dd5385362703744bb4c69bcd913653f26ca7a4db6f89b29d93653925da4f4d06fc9ac8d1341bd2683764d34689a0dc9341aea6835c4bb49699d1a13213f26625c4c84f49951c13213b2642724bb48e98c9912f1bf2622344bc6f4978dd93051a25e3724bf4b8978d552f52625e3544bb486974d8120c93a4267a4b3cf09695a92d2b125a5604b32e89091fd2b63e25736d4ae6c295cd812b4a224247b4a7d009515e92a2bc2545724a73189091dd2863e25136d4a26c2944d81284a224247348ead493d5a1239b7a4cb6c49a4ba9349452651c24736b494ae092b1a92563124a17c48e6ce91edb12412ea4825148f26891cd8d2111a2464684856de914d71215b5a444704856ce90cd71215b1a4216c48324600211d204321c726f)) (pickBlockF p 12 (pickBlockF p 11 0x57f8c8adcdbd5e9aa2bda4957b48aaf48e15b9b5abac7c5766dcaecd995d4be2b736756f6a8ae09255c122ab802256f268adcd8d5a11a2b4b6f5696d6ad2d9d5a5b1ab4154562246ac64ad58c93ab2234563246ac41a800427a9ea6f53d4c6abc9d156ebfaae25455bae6a7a8ed5601f2ac0365578f0aa55fd5501f2aa0365538b0aa55cd4f51baa786e54f0cca9c9d150ebfaa584e54b08ca9495150eb9aa246f54607ca8c0d9515222a2463543688a7a8cd4f895a9f12753f468a7c48d4f43300084b483ad4a755a120cb7a9c16c4832d6a6d5c120cb3a9a16c4832c6a2f9e94c33c2981745178fea551f14adb6a95b6152b6c0a5451145e3da92680525af4a4b5e1496b929218c5178eea431f1484a228bc7351f8d0a30dbd475ae28c36b51b8e0a30d9d465ae28c3635172d89064ad2eb3d2886785114daa229b144530a883784ba8fea151f142d36a85a6c50b4c2a14d212ea3da826805054daa0a9b141530a823804ba8ee9fd1f13fd36a7fa6c 0x5ff248bf29a97e5332fe1245f94c4bf29757e52e2f214b5f78b0be25b97d4ae2f896a5f38c0be25997c4b12f21475ef2a8bca9b97b4922f2a6a5e54ccbd4491795312f415c5e54aabcc5317952a2f21435e3048bba8cd77895aef1275df468bbc48d7742f0008535628ccbb5191588b7aec1545622d6bad1f1588b3aea1545622c6b795d9742ba2e81745bc8feb97191731acae63555cb288b791ed724b22e2d8c5c68fcb8d1d9714c62de4775c28c8b845116f239adeb6f5bd6d6b7ad9d6f5b1ade154562256b355d96d6ba2db2595b64aab6c0896d5bc2cd47f5b08c8b629656c52aad834859a8f6b5cda16aac62d5a595ab4aab54e0166a3bad24645a54b2b4a955694112d234859a8e6b4499166e37ad024459b8d6b3c9f166e33ace24459b8c6b34d6158893ab4576593ae8b291b9652332ca0625932e8ad11fd63a322c7b5958f6aab1c5115a23dac6164588b18b131f96263b2c418c5688eeb0519160dacac1b55583064b045115a239ab7466) (pickBlockF p 13 0x67f08ccfa9519f42a339d6367b2a8ce917d9e4a233a45b6772d8ce915d9d4a233a453673048bba8ed9bc1f33783666f068cdb1a19b432328d6f66907ccd20d99a41a333c586670a8ca35ad98c1f331836663068cc31c19843e328d6765d07ccba0d99741a32dc5865b0a8ca358d965ac32945f657690ca516d955b0329457653690ca514d944262eea3764d0bcc9a1719342b325a6464b0c8bc75bd91c2732384c64708cc8a9519142a2f1d6b6410dcc821999043231fa7c63f0f8bc759d8ec2731d84c63b08cc729518e42a2f1d6363609cc6c1198d12a31a0546278bec6411189e2db1783e62f06cc5ad818b436313c5762a07cc540d98a1a43140446278a6bc6d11888acb111586222aac445517922fb0e94961d290c3a515874a22f245b6182dac305b1860b0b0c1605e48aec2652584ca4309945613288bc914d790afb07a6d60f4d8bc856d790abb0616c6094cac14571825322f21536076a8c045b9808b530236c6022ccc04589790a7afca6e 0x6fe8b8dfc921bea3537e25c6fa4d4df4999bc923b79b6a6f36ccdec971bcdaab7a24c6f36a8de490dbc5b834b9276e869eddd171ba1a5b743476eb698dd5151ba1a1b740426e72a8d315c5b7b4036f48c6df6fadbedc5b7db83703706df074dbc511a622db6b6806d7afadaf5f1b5eb8b6c57c6d70a4dac5b1a622bb6723f6ce476d9c8ddb41a23681286ce466d9c0c9b34a234f4616caae0d94df1a79a5b61d706c44dad889b1b1130b6202a6c34a0d3cd1db011cb6023569f696d74975ae92e35d2516bb054d74941a7da3b4fa4b6b46b8d68d41ad42135a15c69f48ed62d71ac52835845669f47ed56d69ab52e355b566ab69ad3e8edaa5a635235a6a7498d48969a912b35214c69f46ed44931a81a2b5034469f466d3c981a611a34e36c699696d35581a65a3b4c17c69724600215da542a2eea5f693048bba96da44362eea5768f048bba94da2c2f34585c68b0acd12991a2432339d6f6864a8d0c1519ceb5b41a7c6830f8ce759d9fc2733f84c)))) (pickBlockF p 21 (pickBlockF p 17 (pickBlockF p 15 0x77f0ccefa9f1df43e3ad56777a09cef4119ddd2a3bc14c7770a8eb558ddd0273ba0467724a8ee4151d922fbb80447648b6ed84d9db01f3b603676a6c0ed41b1d922bbb383e76706cecad21d94223b245375a688ec4561d6e2fbb014875b8b6ebc581d6e2bbae14875b8a6eb4091d5119baa92b75524eeac8d1d5491baa05e0010b6d2f185d42b83a817c697296e9d5c1a5ca3ba334f74b8b8e8cd2dd19a3ba434c7478a8e8cd0dd14aa39bd71740d00e81231d06b83a01447378b6e7ba01cf4b639bc5773b6d8e70d2dce6b039c3477372f8d2e4adcbd27b9a35c72f496e5e91dcc52639835472f486e5cd61bc6b8b92680724918e4b5c1c953eb92a7c7254e2e4d5c1c94153923486f18b6e3ba01c793eb8f27c71e4e2e3c0a9c75b0378c57717492e340a9c5d2438ba45717488de516dc4536b88a6c7114c2e240a9c45303794576f24b6e1b1b1c363037925770a8d8e14981c1eb3383a6a7074ccde493dc05b538226c7016cce02d75c05ae37924b (pickBlockF p 16 0x7ff6f8ff4d2dff6b83fd3477fb6f8ff4d0dfbcb33f85667f78c8fe0dbdfd5aa3f836b7f38f8fe0d9dfc5aa3f83637ef2bc00248df2a2cbe514b7ca28efcd5a5fa4a23f345b7e72d8fcd15df2895bee5697e24d2fc4995f85a43ee45b7de4d2fbc995f75b03ee4577ca24ef975a5f61b4bec3657d7288f9716df52b4bea5657d32d8f9715df322cbe634b7ce4b2f9c955f35283e63477cb468f9448c0042fbe40547544bef8c091d512dbe206c7544aef84091d5129bdf85e7bf0acf7a991ef4323d5d6f7ba4a8f74151eaeb5bdba7c7b70f8f5759ded0273da0467b14a8f64531ec42a3d5d637ac8bef5916deb22bbd64537ab048ea88edea01f3d40367a68d0f4c191e3ab7bd11367a207cf440d9e822c3d005478ead6f384d9e701f3ce03679a8e0f341f1e3ab3bcb83e79706cf29161e55a03ca05478eac6f1f17de3e2dbc7c5778f8a6f1c131d511bbc585e78b0acf12991e24323ad56f78528cf0a139e14233c1a547830a8eb55addfcb73bf86e 0x86149f0fad761f51f430a4b879ad10f21721e428430a478774b90e8d561d12f43a25d8614870ded6a1bdab43824886f4bd0c20be1b09f43605e8610570ccd4a1992d433a508674810cc95a18413c3203c86226d0c417a18411c2f13485e0710bc0d200da9c2e2608468cd0b416211dafc2bc6d8576cd08ed6e145acc2a56c8514c50a4982144b1423b5784f6d909b196135a7423b5384b0cd08e0ee124b042406684706708c51200da7c223668036970415aa08d2fc1fb6d83f4cd04696e0f52cc11a5783b4d906cd960d92e41b23e83605106c09208d29c1a26682305f05cdba0b9b141713e82f4d905c19a08c15c1636a82304f048dba091b141403c82426d04a982095284120668230470409420802e41005080368f008d9a074aa402a5f81b2c9032db606533402a5b8174b300a95e055364083658134bd020d920411f4080288054a7016dba02db140586680b04900a0ae019b74033628074a100c19a01411c02238803686fde8d20063e3fd34f)) (pickBlockF p 19 (pickBlockF p 18 0x8ff0b91fc1da3b82dc7ce7a8f9af51f55c23e6bb4770578efcfd1df9ca3d4364779668f30b91de5923c2b84785608ef0ed1dc14e3acb647586c8eb0c0fdf15e3a4be465c768cc6df1c71f6395b2c71c7c8e36ed198dae3823f4703698cc6cf1bcdf235e3ac6d46e8da6dd1b4db235e3a46bb4e8d7071198d8e34a3f4694728d36d91a41da3301dc66c7e8cd8e519cd823343b4660338cb288fdf14e3202c4640548038bf18ad2e315a3c01c5b8c047718497230119c6002f8bf4c100715e2e22f45ca3b8bb8d11728de2e41dc5c1448038a716d16600dafc5a14489e6bd13e93e2bdaec57a3e8af04913e92e27d23c5625c8a56ab14a97a2952ec5425c8a548b14c5122949344fa438a34bd13e0be2849245035289f04f13c8e200dadc4146189b089106d7e25a3744c3458968d912cd3a20dadc4a1608836af122db2244b044746688e69d11cd3620da9c44b6d8896cb1151b2225acc4185f8846c3108d76211aac421608830af1045b200dabc2f35e 0x9778dd2fc1125de314be04c97728d2f2d4a5e41e4bb9449770dd2ec0ce5cca24b9848973088fdf18e5c4be4a6d7696f0d129d1be5aabecb646596aaf92d51da53a35cb1c69967cf92c6dca591384b217c9632fd29d19e5863e4acd7595b8dd2b71b256db14ae26095b2dd2b35d25662f4a7463954afd2a95ca556364aa07694e09729f5fa53eb94a846094f0ed29c10e534aa3f7c5f91d8ed23cdbe51a3eca43659468f928cdda479b5ca236991e6cf284df24ee3ac9fb6e93f6d92771d24eda749d83893b06923cd8e4e5a249b47a9368ed26cdda4781fc9747e92e8e525c53a4b8a6497b7c92f6d925c1da4781dc9547a92a6f5254dda4781bc8fc7e91f8e524c13247ca349203c91f289240dc2481b049003491f0ed23c0ce474a23f7c5b8ebcf52321a24643247756f914cfb22d1964533e48a4768eead72255a63bab3c8847c90bceb21b1ba43636485e7490b8dd1dd58e41f3d483e76907aed1dc17e3fb3f47f6728fe2dd1fc5b23febe47fd6c) (pickBlockF p 20 0x9fc8cb3fb5b27f6364fe4599e40bf3f41527d6b4cfad619f52dd3ea5b27d42f4f205b9ef8c33df1767c2b84f84509ef8ab3c815e796b4cf60549e5ac33d41b2794b34f3c519e70b93ca5927942f4f20539e32c8fdf1be784aa4e2c6e9c66bf3b71b6775ab4edc6c9db69d38cd6e764364e33579d76d93a3196751aecea35c9d18c93a2dba745b6ce33539cc8d539919a735b44e636e9c607f38f18a71db54e43509c76cd38c0de714a23f7c6b9c32a934f5c67042a4d446f9bcafd37d1566f2be4de45e9a88d735119e6e63e4d9d769b68db36d1b26ceba4d9c5e9b38bb35118e6ba3ecd74759afaf935d1a66a037cd4c719a98db3551826a632cd40679a72f8fdf19e5ce374bb35f9a08db344d5a682364d034e9766b73399e2670364ce0609766af334db265232ccbb5d9976b9329192651b74ca36d9766a731d1aa63a334c7b6898f6b131cdba5d81fcc60549878dd30f18a61ca74c394c9870dd2ec0ee606314c0b6a9826c1304d42605b34bb037 0xa7f0c149b15e9f5b8530c76a624df4eedf69e532d3bb7ca774ed4c49ae9d534d31267a734f94dadd69c13753826ca6d6e94da8fa9b414531263a686fd4d0dca9a536534076a620574c6dfa98db9532260a630ed4c408e985a4526c53a57ac34bc95295e2fd2e244a578b74b49b295e2bd2c244a578a749adaa9553252746fa5348949d1ae9453e527467a4f48949d18e935a9000927a2b6bf4931ba92636515b5ba2b6af48cdb290e3352235ca438c9456d4e906b251fb6da3f6cb45617e8f42251cc69a398c34725ba8e4b651585ba348c1468d768d6b051a355a2b0af4591a68c422516461a2f0d945859a8b42e516164a2b0a74505928a0345140647efadf44c51288a2dd1216ca228af444551fbeb5d0eb6fa1d6c743cdf687437d0e17c7efacf4295ba855a5d0c578a1568f42d16685425d0a1547efac73c75a67922fd06d6ea0f8ab41b5b28362f4f245ba0a0f94141c27922bd0447ca02acd40b1b681636501564a028bd40517679229cfe46d))) (pickBlockF p 24 (pickBlockF p 22 0xae4aed5ca9bebe9bed7e265afa6f95f49dab9535d7c269ae54cf5ec9f2bc1bad79a6eaf34d95e0dd2bc11f578028ae54c75d6dfabadb957626caeb0ed5ca0aeb99bf573372ae74c15cc1dab9411d72358a4d8bf5671daad137d6eb7dadf4cb5badf2b753b55a26badb4d356899eb653e569375ad64dd5ac9b2b49ba56923ead20515a4092ad131d68234acd6f559addab353b55a02fac56fd58adcab149f56293cac64f958c9b2b143b55a02bac06f55809eab0538560276ab404f56adfaad5b955e03cab526d5740b2ad49a55b270ab64c156c092ad43b55a023ab369149b16e9ff3d54126faac6fb55c996ab1be556276a824d75549a6a0933d5427caa06eb54a9baa9536550374aa04d95408faa8014550024a824c753c8d2a6dbd54db76a9b4ed5040bea4dbf549b72a9327d5264f2a513e54a26ca930ed5040aea39bd54727aa8f4e151c9daa0813d41b7ea836e55140f2a0c9b54402ca832695089c2a1130542024a830ed50408e9fdb053f86c (pickBlockF p 23 0xb7e4a56fc0b2df09a5be06eb7b0476f4da293637dbc358b548dd6aa97edc5b6dba256b716d96e28fadc4125aaa5bb554af6dc9b2d81b2db5a5db6b4b96c0d92d81375b026db666c96cc9b2d812adb0b64b634a96c2952d85265b012ab554a76b6daad6db35ae268b5b4dd6aa0bed59b15ab26ab574a16ac99ad5413daa348a4d8d76a4d62cd2b8d9aa5fb4c6db69c95ad31b65a623eb354b76941b2cd52bda426cb406cb68a976d152e5a0364b404dd6809b6d05b25a025db354a7676daacedb359e268b3b4dd66a0becd9b159b26ab374a166c99acd413d9a370a4d8cf6051bac152fd96b6db2f4ad65adb2cb51f582a5bb2a0d9654182c152bd9426cb226cb64a976c952e591364b224dd6449b6c1529d8e36ab1c6cd63a9a2c752c58e26eb0505f634152c55b758ab62b1527d62a4f2c543758282bb0f6c561e9aac4130588250b0f4cd60a09ec19b7583362b0b07960c4dac212958402cb0626960c1bac1411d81348b0209160411293631d80370 0xbfa8eb7fadbaff5b65fd474bfa69d7f40e2fbdb1dfac7ebf58e57ecdb2fd43b5f783bbf08fd7e11cafc5b05f8076bef0677dc512f8e29df4b4fbe96977d2d1efa5a1df1966be46df7c8daef91b3df2363be32bc0024aef0527defb5dbdf6b978292ef0523dee25cbd96ab7b4932f65aa5e0a43bd74697aad6af55ab5e082fbd308979ed7af3da95e793ebcf2797820aef2d2d5e6250bcb4ad78209ef09af5e4034bc26a578c0f2f089b5e202cbc22697841d2f0411ddf368bbe0d177c192936b7dde348bb88b7774d82ee22bddc358a4dad776492eed5365d9243bb36b57640beec5b8526d67baaadd75692eead21dd6352bab047754d62936b1dbd569b7b4bf746db6e952b5d1b6cba347d6f696ee80365d0060b7b4af73c9b2e61b2dcda5db9b4b9730d92e61375cc26db7b4a7724daae49b35c9a68b934b17249badec17dc8054b8b6dd716d8ae2c9f5c593cb8b0dd6f60aee15b15c2a6ab864c170c942e15335bd827b7c6dd6f8d8ae041e5be136)) (pickBlockF p 26 (pickBlockF p 25 0xc7f2a97c75af1f4be5f1d67c7aadd8f4552f8eb1e3bd69c772c97c71bf1d4aa62bc6ec732ad8b0d7f1b636e37b56c6f2ad8db1b31b5a762c35bc6b0d98b0d5f1a5b6631c65c666bb8ccd7318e32631b6ec636db8b0d4f17a3562f466c5f6d18bcdbb1601fe2cc62c596d58b4d43165b362c037c572897c71af154aa61cd71c3a8df89f5fb1462ae27d7cc4f8bd8751af1343e61d467c4b8f988b5db12236e2446cc45ae988b17b1162ee1d463c408fb8811d7106be620469c3a0df8771c70ee36e1e460c3b8cb87419f0e4be5f1c67c348dd8685130d02461a044be38c78645f3052bb618068c158df8575f70b632e15d7cc2b8ed82b1af0a234e14272c158cf84d1f3082bae1146ec228d984498b082ba61045ec158c78375fb06eb960e46cc1b0ed82a12f05abf60b572c178c182c1db05421e0a154be38bf8231db044a25f1c5bc0ccf58185b303036606060be38af8145f2fba3b5f7b6fc048fb80cd970123e602376bef6d7804da6fbdb3e0037c 0xcffad19909bf3b9a7e7dc5ecfb8b99dcd2f3b9a3e7c36ccf58ad9ecd733d62a677343cf26bb9e4d573b827e77b4dcef68b9dc11f3b53666426bcdc69f9d317b3a62e66e34bcdc68f9ccd7338e2b67234cce38a99b8d0f381aee70355cdc09f9bad37375a2e6e047cdbae199099f34f3c669a6ccd34b99ac17334c1466a150cd304999098f334afe6695bccd2af99c553334a9e6405ccc94bf99409332529e6405000128f96ed7f3123766246ccb76b796ed5f305be65f466cbf6d997d1932dda9e5dc69cbb8c396e16f2e234e5c461cb70a796c593225b7e55a4fcb26bb964d732ad25e55a47caf4b9958d572b526656354cab4879544d3225b5e4fb6fca68fd94d1f327db5e4fb67ca36f99411db285b6650474c9f6c793c5f3225b3e46a4fc9a6bb934d7323525e46a47c974b9928d572552664a354c8d487922d7b245a964682bc8e6bd91cd4b23411e45934c8b071912d8f224b3000943c852c990a1a3214325f1d6fc832898ff16f204b663fc57) (pickBlockF p 27 0xd7f0a800317f5f0a5ebe1470018b600315f5e62f000c53d778b200257f5d4af00095bd738c200255f5bcaf6b7818d6f02800254f4be336ae36fd6a8fdad51f3571b5eae367d676f9ac71db595296b236cd638e9ab8d8f5823ceb0471d5c0d7abb1e757638eae063d5b8c9a5e9bf541afeabc6ed578d9aa0d6f541abeaa36cd518cdaa4d73546326a8353d4f4a9a5e9af511afea5c6ed4b8d9a88d6f511abea436cd458cda8cd73516326a2353d438f9a5e99f4c9afe9fc6ed3f8d9a64d6f4c9abe9e36cd398cda74d734e632699353d368d3a6d1874c82de99c69d338c3a6414f4c12a698028d2f4c600253f4b4b268136fd1b49fa52d774a5ae68da4bd1b48fa4c973489aae92136d23499a44d5346d21e8fb5ad1f6ada360bf4712d68e256d1b04fa344d3409b5e84b6fd168fda2d1f3425b5e84b67d136f9a211db445b6688474d096c7a1adf7435bae8486fd0a6dba14d9742433e8417cd026cfa084d34101c682034d026c7a04598004a5e6456a 0x6bf858))))))) 11
def l_2347 : Nat → Nat → Option Nat := unpackIndexedLinksF
  (pagedUnpackF 19 7 (fun p => (pickBlockF p 14 (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x8900112002240044800870810c08214104280085001090420a20410108182101081fe103fc007f020fe001fc003f4107e800fc041f0203c080748e0e9001d0083a00073820e7001ca103940071060e1041be103589069080d1041a00833c1067020ce0019a083301064080c70418c083141062020c304186003081060820bd10178082ec105d020b904170082e0005b820b604164202c41058020af0415c082b41056800ac041560829c4053020a60014a082901051820a2041440028410500209b1413018260004b04095041280824c104902092001220824010480008f0411230214404280083081060020420400207f040fc081f4103e8007c040f6081dc403988073000e4081c800388206f080de001b810350805c380b800170002e0005b040b60016810291003d54003e00001 (pickBlockF p 2 0xed081d9043ac1875800eb001d6003a42074410e7061ce0039a0873400e6021ca0838c2071410e2021c10c380086fc10de061bc00376086ec00dd021b808368206cc10d9021af0c35c086b410d5061aa00352086a400d4021a6083442068800d1001a20033c2067410cd0619a003340066800cb08195043241864800c9001920031e1863c00c78018f003181862040c3041860030c0061410c10618200302085fc20bf8017f002f8185f000bd8217b002f4085e020b81016c102d6085a810b308165042c80858430b080160042c00057c10ae06156182ac0055800ab001511429e1052850a5001480828c1050840a1001410428200500109e861361c26c004d8009b001311425e104a85094821260c2481048040900011e0823c00474108e8011b0822c28458008b001160022c004484 0x168842cf0859620b2c0164842c90059008b200163042c11458200b001160002bf0457818ad4715a802b50056a00ad0115a002b30455640a9c4153022a50454808a8c1151802a20454208a74414e0229b0453408a64114c022980052e08a581149082910452008a3c11470228d0451a00a301145822871050c08a141142022830450408a08014082280044f8209ec113d8027a044f2089e0113b82277004ec089d411380a26d0c4da009ac213502269044d00899c113380266044ca08984412e8825d004b61096c012c84258044ae08958112a82255004a80894c1129802520449830920411d1c23a00472088e4011c022380046c108d021198223300460188c001178222e0445c008b801168222b0844e208789104aa205103fe307ec40fb0a1f1143d43879450ef0e1de003bc007780)) (pickBlockF p 5 (pickBlockF p 4 0x1d3003a60074c00e9411d10639a2072c20e5021c80838f0471c08e2c31c58038b0071600e1c41c3023830c70600e0c01c18037f106fe00dfc01be063790c6f008ddc11ba06374006e608dcc01b902372006e208dc401b80236b146c838d8c11b10235f0c6be00d7c01af8035b106b408d5c31ab80357006ae00d4c41a980353006a018d3431a60234b0469018d2001a3823470068c08d1801a2823450068808cfc519c0e3370466c08cc84198823300465a18cb401960232c0065608ca031910c3220064400c88018e8a31b0862c28c541189063100861820c3001860030c0061800c204184003080061000c200182083020860208c00117e082f8105f000bdc117b802f6045e810bd0017a002f3045e210bc40178022f0005dc10b98816f8e2df005be00b7c016d0a2d8085a628b4c0 0x24404487049062120812400447f048f6211ec023d0247a008f2091e4023b84472148e4011c4123880470048dc1119c723380467008cc09198023282465008c809170822d8245a048b209160122c00457048ac091484228824500489e0913812268244d008980912c1223884460488a09110122182442048840110412200243c10876090e8121c824380486e090dc021b0243504862210c012178242e0485a090b012160042b04854090984212824230884409080220f0441e0083a0906c220d024141882411048020900412008240104802068a40c0481609028120482408048100101c1203024021080010fd0c1fa003f4007e800fcc11f9803f2047d440f5551e8883cb1878e20f0851e0043bc1077410ed841d9083b00876000eb821d7003ae0075a08eb011d4863a90075008e982) (pickBlockF p 6 0x2b58856a04ad2095a012b38256604acc0159412b20256010abe0957812ae8255c04ab60956c02ad0255904aaa2154c22a90255008a9e0953422a58454b00a940952022a40054800a900152002a18a54300a84094f0629d0452e30a5c014b802968252d00a58094b002958252320a1ca942842828a501109f8293e042790c4ee109d0313a00274004e6089cc0138c3271804e3009c211384026f064de009bc01370226c084d8009b001354326a804d5009a4193480269004d0089962932c0265804c80c990013200262864c50098a0130c225f0a4be0097c012f0225e004b90c972012e4025b844b700968192d0025a004b20895c212b80257004ab0c956012ac0254064a8009500129822500c4a00094001278224e824991093201260124b82493109260124c02488448a1c914012280 0x30c0661800c3001858230b006130cc260184c03088461100c1c1983803070060b0cc160182c03058060b00c0e2180463008060100bfc197f802ff005fc08bf8017e432fc805f900bee117dc02fa065f400be8017c432f8805f100be2017c402f6885e718bce0179c02f2065e400bc80178432f0805e100bbe1176462ec805d900bae1175812e9085d104b9e1173812e5085ca00b920972402e4025c608b7e396fc02df805bd08b78096e042dc005b704b6c096c842d9005b104b62016c012d8005ae08b52296a402d4805a708b403968002d0005a000b3e0967c02cf0259620b2a0965012c98259204b240164412c80258c10b160962812c48258804b0e0961c02c30258504b022160012bf8257e04afa095f012be0057b04af4095d842ba8257404ae6095c812b88257100ae0095bc1))) (pickBlockF p 10 (pickBlockF p 8 0x39b0273504e6a01cd013990473104e6201cb833938e71d28e2c39c58038b0071408e2609c4813880470e08e1811c2c1384847060ce0229bfc237f026fe00df811bf0037c866f708dee01bd81379866ee14dd811bb00376006eb04dd601ba81371106dd14db809b70036e006da08db011b60036b826d604da811b4c1369026cf0cd9819b2c1365806c80cd8e09b1c0363806c508d8611b04235e0a6ba08d5c61aa84355006a904d5009a9c1353026a504d4a01a9013518269f10d3a11a70134d0469904d2e11a54234a8069308d2211a4013450c6870cd0e01a1813420468400d0801a1003420068208d0401a0413408067c14cf4119e4133c0267704cec099d8033a8267404ce0219b4332f1e6475cc86218f8531d0863514c66118b853160462810c4c1188843100461b14c360186c0 (pickBlockF p 9 0x4168e82b090540a098441282824050421a0840410028200103e0a070340b0c8150502a02050140a008130501c2a03024038a8060500c0201414028080404ffe29ff423fc887f900ff009fe003fb827f508fdc39fb023f6007ec00fd609f9463f1847de14fb811f6c13ed027d808fa431f4023e6087cc00f9219f2013e4007c800f8e09f0853e0827be0cf7031edc13db807b508f6a01ecc23d68c7ac04f5609ea423d4027a50cf3e31e7c03cf8079c0cf3801e7003cd8279b00f3211e5053c59278908f0829e1003c18277e14efc01df413be8077c04eea39dc443b88077004ede09dbc03b70276c08ecc31d9413b2027610cec201d8403af8475c0ceb801d7003ad8275908eb009d4473a70674e00e9c01d2063a40074704e8819d1003a18274204e7639ce8139d0073904e6e11cdc0 0x48d089161122c02458048b009160122422448048900912012240243844870090e0121c0243804850890a012140242804850090611200323fc147f028f8191e4323c80478828f1011e00a3a86475008e9051d2023a40474028e7051c2323840470808e0051be0a37c046f028dd051b80a358646b008d5051aa02350146a008d3051a6023346466808cc051980232c1465808cb011940a3280464828c9011900a308645b188af1d15c0a2b02456008ac01158022a04452088a2091440228804510089e1113422260244b828970112c0a24454468888b091140a224144480884151002220004400087f050fe021fc043f8087d090f6121ec043d8087b010f2121dc243b80877010ee021d424398486e150dc021b414368086c050d8021ac14358086a050cc2217c74233284211074420d06)) (pickBlockF p 12 (pickBlockF p 11 0x51a82a350146a028d4051984a3109462028c4051880a2f0945a128b4051680a2d0145a028a8351404a211d44202884051080a210143a22850950a00a1305426028481503189e9753ca2278444f0809e0053c00277c14ee069dc013b80276824ec049d8013b00275824ea049d0113a00274004e7049cc093960a72814e3869c50938a0271404e2809c3093840a6fc34dd889bb013740a6e804dc829ad313349a638c4c50898515302225f054bc08973152de225a854b500969052d00a59434b202964012c80259004b00895d0d2b80a57004ae0095c012b02255434aa02953052a01a54004a78294f0129c0a53804a68294d012980a52044a10c9410527e124fc049f8093f01276224dc449a8493405268024cc14970a92a11250124a00494009280124822480448f0491e0123c024780 0x59d02b390567202ce0159b82b360566032cc0059782b2f0165c0acb8059682b2d0164e32c9c059302b260164a0ac94059280b240564802c8c159180b220563832c40c5848eb09016100ac20058382afb315c4cab58c56908acb1d58e22b08555f08ab91556a22ab8755700aae0155c02aac355580aab0155602aa4255306aa60154a0aa94055280aa3095401aa80055000a9d0d53a02a74054e80a9d0153222a44854802a8f0551e02a3c054780a8c0d51022a1c154302a85055041a9f8453f00a7c094f8029f0053d04a76114ea0a9d4053a80a75014e41a9b8453700a6d054da029b0153600a6b054d6029a8153308a5d254b80a96c152d80a5b014b602960352a08a53054a60294c052884a4d1149a0292c252502a490548c1a908452082a400547e0a8f8151d08a361146c028d80) (pickBlockF p 13 0x5fe08bfb057f01afe005fb82bf7017ec0afd805fa82bf5017e80afc045f50cbea017d402fa805f308be4097c022f8005f000be0017b822f6825eb08bd5057a80af5005e78abcd0979222f2015e382bc7017842af0025de08bbc017760aeec05dd02bba017720aee405dc02bb41175a3aeb015d600bab0574c2ae9025d008ba00174002e8005ce08b9a0972c22e5805cb00b960172422e4025c608b8c0171802e3005c408b860970422e0805c100b800970002df825bf00b7d056fa02df405bd84b7b016f212de405bc80b77096ee02dd425b80ab70016e002dc005b800b6c116d802db005b600b6c016d022da005b400b68016d002d9045b200b64016c802d9005b008b5a196b20ad6015a90cb4c1969802d2c15a580b4a0568832d1005a182b430168602d0815a082b3b1967602cec0 0x68500d070da0c0b410268182cfc1d9f8033f0067d82cf9099f2033d836780cce6299be3b374266e02cda099b013360066b04cd4099a60b334666506cc90598e1331c066302cc50598a03310165f8acba15970132dc165b02cb60196c032d416580acac11958032b0065582cab01956032a4265480ca41594413288065100c9f0d93c0b278064f00c9d059380b25c564a06c940192803244364880c91019200b240064704c891590e1321c064380c870190c0b204564080c81018fe131f0363e00c7c018f60b1e8163b08c76018ea0b1d4063a02c74018e60b1b0763600c6b058d40b19c362f12c58198b00315c162b80c56058a813134761b2ec321185a2b0a446120ac20118362b05c46090ac120182403048060708c0d058141b024160402c050d8080b00c160006c0001800030000)))) (pickBlockF p 21 (pickBlockF p 17 (pickBlockF p 15 0x71586e2a05c4c23898071300e2409c4803888270f08e1e01c3c03870270e00e1a09c3403864170c80e1901c3203858370b00e1409c2803850070904e1201c2013824770480e0805c100381c170380e0605c0c03814170088df825bf0037dc16fb80df605bd463735d6df1edba11b6c236b886d40cda11db400b67c16cf02d9d05b3a0367016cd82d9711b2a1365016c982d9301b221363446c602d8b05b101b62006c382d8701b0c0b60c36be8cd7c05af60b5e816bc82d7901af00b5dc16b988d700dadc135b026b582d6b01ad6035a816b500d6809ac43357456ad84d5a05ab20b55c26aa84d4f19a962352426a480d4709a8c0b51806a00cd3f05a7c0b4f0269d82d380da64334b4569602d2b05a483b48c169102d1f0da3e0347c068c0ed1705a2c0b450268904d1105a16334281 (pickBlockF p 16 0x79882f3101e600bcc0079782f2b11e5603cac079502f2a01e520bca4079402f2801e4e0bc885783b6efb31dee23bcc477980ef301de40bbc8077882eee0ddda0bbb4077680eeb09dd213ba0177382ee40ddc413b78476e82edd01dba03b6c276c84ed901db203b5c276a84ed501daa03b54076a80ed309da40bb3c376588eb84dd6823abc575588ea41dd4023a64774a88e9015d2003a40074704e8e01d161ba2c074580e880dd1003a20074286e8501d0a03a0c274180e8205cfe1b9fc073f80e7f01cfe039ec473990e7301ce6039c4273802e6c11cd8039b0073600e690dcd00b990473182e6205cc20b974472e02e5811cae0b958172986e5301ca213934472680e4d01c9a03934072488e4025c7e0b8f8171d86e3a05c6c238d8071b00e3601c661b8c8171708e2e01c5c038b80 0x80e0301c0203024060080c01018020223c044080803010020200403048058300b020160402818028b0040600804008280005000020000400007ff04ffa11ff403fe417fc80ff60dfd463fa807f500fe221fc403f8417f080fde0dfba0bf7407ec88fd805fb003f5827eb00fd505f9e33f3c07e702fce01f9813f3007e582fcb01f940bf2417e090fbd11f7a03ee057dc00fb411f660becc07d788faf01f5623eac07d502faa01f5403ea807d500fa31df4603e8427d002fa001f3e0be7c07cf02f9915f3203e5837cb00f9409f2803e4c17c980f9301f2213e3447c098f8101f0203de487bc80f7805ee62bdcc07b884f7101eda23db407b40af6801ece0bd9c07b302f6601ecc03d8067b000f6001ec003d8007ae08f5c01eb60bd6c07ad02f570de9e43d2c4799b0f3301e640bcc80)) (pickBlockF p 19 (pickBlockF p 18 0x87e070f7161ee043dc087b810f6061e22c3c40877850ef021dc0c3b80876830ed021da043ac28728d0d9321b00c35c1866950cd02196143185862830c5021861430c085f0b0bd0617a042dc685b810b60616c042d8085b010b30e166042cc08568d0ac06158042b00855830a80e1500429c1853810a6061461c26c884a8d0950212a0423c68478108f0211a1423408468108c061180421c584189083021060420c084103082020fa2c1e4483c81074160e8041cc18378906e060dc041b80835870690a0d2041a0183401067060ce04194283281064060bc34178082e8305d020b80c16c18299104f1209e0413c08248d048060900411c182381042160820c0f0581e0103c02074140e8081d010361206a0c0d4081a81034060621c0c408188103102062040b448129102112042040744 0x903812060640a0c80c290181203024021480018fc8f1ec363d60c7a818f0151e0023bc1477418eb0f1d40a3a80474828e8831cb1a3921472018e18b1c206384046fc38db131b506366146cc08d9811b10a362046c018d58b1aa063483468c18d1811a3023421467448ce8119c063380466828cb0918d2630e3461818c08b18006300045f828bf011771e2ee045c078b80116f062de045bc08b68516d022da045b408b30f166022ca0c59408b281160162bc1457808ae8315c062b80457008ad051541a2a80455008a98314d1a29a0452c28a58114a062940452028a401148022900451438a00b13432258444ac18958112b022483c48c1891811210a24204468788d011131e22604448188901112022201444008858b10a062140442808820d1020a20404404187f850ff021fe043fc0) (pickBlockF p 20 0x98d0131a0263014c486989013110662204c4019878330f026142cc1c3983813070260e04c1429800b3000260004bfc197f812fe065fc04bf8097e052fc025ec34ba8c971112e1065be14b68596c832d9025ae14b5c09690b2d20259834b300965832cb0259604b242964812c9025882cb0c1961812c3025840cafc395f032be0257c04af4195d072b22255834ab00955052a9065443ca80294f8329c0e5360ca5469478d28e0651814a3009460128a0a5120ca2019410d2800a4fe0c9f8193e05278124ec149d4193a812730a4de2499899300d25f064ae44954292a812530a4a40c93069258324a064920c900991f8323d0a47a048f4091d8523a064720c8c489170722d0645a048b01914872221e4440488419108121f0a43c0c874190b8d213124240c84419080320d0e40e3481c0 0xa10154200283c150606a0b05416028281504c1a068d40c0680c350141a01854020680404ffc39ff033fd067ec3cfd029f9833f3027e214fb449f6033ea0a7d20cf9c29f1893da267a834f5009ea013d3067a604f4819e9013d1067a204f4019e58b3cb027940cf2809e4833c9027900cf2009e3833c312750dce9049d1833a20673c24e6849cd013990673204e6019ca09394027260ce4c09c78938f0271c0ce3809c68338c0671024e2009c4013880270e0ce0859c101382027020ce0409c003380026fe0cdec49b79936e066da0cd9489b2813630a6c604d8429b08135d126b80cd7009ae0135b066ac2cd4069a78334d0a6980cd2829a5013480a68434cf4599e033371666c0ccd8099a053340265a3ccb40996813261e64c04c941992813250264614c8c09918131c1e63414c680))) (pickBlockF p 24 (pickBlockF p 22 0xa948b52806a50054982a930152116a42054705a8e0151b06a360546c0a8c8551902a320544c6a890351202a24054441a870750e02a1a0d4340a86035090ea02453ec6a7d034f5169e80d3d00a79054f2029d63d3ac0a720f4e4029c60d38c0a71814e10a9c2053840a70814da1e9b4053641a6c814d9029a82d3482a69014d1069a00d3400a68014ce0a990353200a64014c80298e0d3046a60814bf0a97e052f81a5f014bc0a978052f00a5e014b90e9682d2a0ca501149f069323525c2a4b814950a9280d2308a4583483229040d2002a4001480028fc151f41a3e0347b068f40d1c49a3881470068e0051bc1a348d4660e8ca0d18c2a3103461068c2051783a2b8f456068ac051580a2a8344e1e89a0d1283a24834470a88e051142a220344306886050fc4a1c8d42c368560d0a81 (pickBlockF p 23 0xb1e8163b0ac76058d46b149962122c420587c2b0c8d6170ac2e058542b0a0361306c183d8186b02836030ac060580c0aff0b5fd06bf6157e42afc035f316be40d7c80af8835f102bdc1d7949af2035e402bc8057882aef095dc0abb8057700aed835d712b9c4d7206ae4015c60ab822d7001ae0015be0ab7c056e45adc815b31ab66056c81ad9015b202b5e1d6bc0ad7815af02b5c0d6a06ad3835a702b4e056981ad1875a206b44056880ad08359e0eb2c456406ac7835881eb0e0d61c0ac28558502b002d6000ac0015791eaf2055e01abc0157802aec155d80abb0156f1eada155b40ab68156d02ad6155946ab28156406ac80558c1ab10356202aba2d5683aad0155a02ab4055602aa98b55302aa40d5480aa88355102aa20553c2aa7815491aa7a654f01a9d835312aa600d4b82 0xb940172802e4c15c980b93017201ae3e0dc7c0b8f8171e06e361dc6c0b8d0371a02e320dc583b871170916e1205c240b848170902e0a25c140b828170502e0a05c044b73b56e312dc40db841b6e896d912db205b601b6c016d706da625b4c0b69036d202d9c25b380b66836cd02d980db2c1b63896c702d8e05b181b61096c202d8405b041b60816c006d8005afc1b5f816ba16d5c65ab41b56036a422d4805a882b51016a00ad4005a704b4d0569906d2e15a5c0b4a8568f1ad142da241b448168806d1005a1c1b410b67c1acf60d9d07b398367302ce2159c40b360b66c02cd8059947b328166406cc8059900b310566202cc40596c7b2c8565902cb2059640b2b856511aca2059401b280164f06c9c0d9380b248b6460ec8c059180b23016440ac7e2d8fc0b1f0363e02c7a0d8f40)) (pickBlockF p 26 (pickBlockF p 25 0xc0b8b8150b022260440c078580b130160601c4c000f80002ffe0dff81bfc0d7f706fee05fdc0bfa077f402fde2dfbc0bf48d7e902fd00dfa00bf4017e60afcc05f980bf08b7e006fc005f800bef837dc0efb60df6c0bed817da06fae1df3c8be50b7ca02f920df105be1837c302f8215f040bde0b7bc02f6c35ed80bda837b502f6a05ecc2bd9817b302f5c2deb41bd6817ad02f580dea43bd4037a802f5005e9c1bd20779c22f2e2de5c0bc98979302f2605e289bc50178906f1205e0c6bc10378202f0015e000bbd8b77b02ef40ddd06bba0177306ee605dcc0bb9817700eee005dac5bb50376a02ed405da41bb30776602eca0dd940bb2037610eeb245d505baa0175012e923dd240ba28974502e8a05cf09b9e0173b06e6c2dcd41b9a817330ae6605cb85b970172916e5205ca01 0xc918f91f1323c0e4741c8d859171322e064581c8b01915072261644c0c89819110b222064440c878590723206263fc4c7f038fd071f6163dc4c7b818f6071ec063d41c79858f3031e6063c42c78818f1031de1639c8c71898e3031be2637c0c6f818de071bc063741c69178d2031a4063480c69018d10718a663140c62818c40717846285bc4f8589e0713a0e2644c4b858970312c0e2580c4a8389113122062440c478588f0311e062342c42918820f100161fc1c3f0387c0b0f4161e80c3c83879030f00e1d82c3909871070de161b81c368386b0b0d2161a40c3403868030ce0e1942c3089860070b82616c1c2d038580b0ac161580c2a83855030a80e1404c28018500309c161380c270184c0b088461100c200983c130529e0944c12818250303c3e0780c0e8381d030380e0700) (pickBlockF p 27 0xd74b5ae5135c226b3d2d5e27ab03353a9ea644d4033a7c134d29e9944d2927a4c1b480668e08d0eb7a191342e168581d0a83a111341e1683c0d0703a0e0341a0e8301d0409a0803410068182d0301a0603408167f08cfc879f70b3ec0e7d41cf9859f10b3e2067c01cf8019ef073da167a44cf4039e60b3ca0e7901cf1059e00b3c00677c1cef819de073b8167604ceb839d50b3a80e74c1ce7899cd0b39a067301ce6019cb0738e2671c0ce3819c50b38a067140ce1859bb23376066dc4cd2279a0133362e6642ccc03997073262663c4cc78198e0731c066341cc60398a0b314066280cc40598803310066182cbf1197b0f2ee265d81cba839730b2de265bc0cb70396e032da0e5ac2cb58196b032d2165a40cb4819670b2be465703cac09958032b0065447ca6899346725c364a84 0x361e66c0cc)))))))
  (pagedUnpackF 26 7 (fun p => (pickBlockF p 27 (pickBlockF p 13 (pickBlockF p 6 (pickBlockF p 3 (pickBlockF p 1 0x16115006456c015114005846c015159006845f018116c05c457014114c07456d01b0d1004c27c00b017804417c00f091403837000c048003023401024bc04012b00d049c02c12305a1174144b4f0482d2c0fcb470362d0c14424f048092c0fc247036090c0b0a3f02c08ec07c23701208cc02804e00408c00103440082dbc01cb6300809bc01c26300628fc01823b00508dc00c23310815bc41856310431bc408c630f0317c390c5b0d8315c2c4c531040dbc4083630f00d7c39035b0d80d5c2c43530a52d3c29434b0950d1c19834305b0578024066002017b5f845fd7b116f5e8457d78114f5d935fd744d6f5c9357d6e4d4f4b934fd014d2f31d347c884d0f5d9a5fd74696f5c9a57d6e694f4b9a4fd01692f31da47c88690ef8923fbe288ee9312377ee48cf5d815fd74056f5c8157d6e054f4b814fd01052f31c147c88050ef8a93fbe224ee9309377ee24cef8992fbe204ae9301277ee048df2405f753016da580575dc014d58404f53c012d20804738d010cb4103f21340ec42903700140ccb4182f21360ac429827001608cb4001f213006c428017001004c00003f (pickBlockF p 2 0x6909401bc26406c09b01a825c06e0df81b437206b0d941a436407f15bc1e856307909bc1e0263074097c1c425b070095c1a025308f19fc22c673084115017016e01201d800c06e06700d01940640630090040076061009017423000d01d817c04c00c019817434400b01d8190b6f0622d8c19026f062098c180a3f06008ec17823705c08cc02806603528fc0d423b02a08dc0742330580da015435405811b01503500550d701504640590d7c15c35b0560d5c14c35305211f013c36804c0d5013c46c04b0d4013036c04b119014035f04e0d6c13435704a0d4c12427c0460d6010c34404611701083400430d301084540470d3c11434b0440d1c10434304015c00f436803a0d500f446c0390d400e836c03911900f835f03c0d6c0ec3570380d4c0dc27c03311a00c045403315b00bc45003011b00bc564034117c0c845b031115c0b845301101380d456d02d09f004005e02b11a00702300280da009435402811b00903500250d700904640220d480a435f0270d6c0983570230d4c03805e02100d80a856d02011c006c23000d017807034401e099007045d00c0138064468 0xbc0d702e827e0b909c82d02400b709902d424c0b60df82d03540c811bc3104630c309bc3082630be093c2ec24b0b8091c2cc2430d215fc33057303601d82c80340aa01902a82640b00dd00d40840af01d02a40340a801502a02540ad0d902b00640a700d02a82640a809502a456f0a7158c18405e0ae19fc2ac67306005b80b007600601b829803402b01d029004e09a013028c0460a2011026846808a08c02845780890d000a80840a001d026405c09e013826004c098116021823009d15a021434009c019025c05c09a11a026045809915bc25c56305f017827c67f09b19cc21034005e05b807c07600501b825805c01e01d025006e09301b0248066080019022834408009902244540910dd007408409001d01fc03408808d021c34408e01581ec0540860d101ec254085115023436408c01901e803401c01d0228064088011821c354086015022456f085158c17415e01b019801005e08309a4208268081099420026407e09641f425807c09541ec25407709781b82520750db81b436207609501dc27e07509c81cc26907209a01b026406a09501cc36d0720db01ac251)) (pickBlockF p 4 0x10901902b0a3f0ac08ec27023708c08cc2acb4f0ab0d2c26c34708b0d0c41c0540fd2d3c3b8b4b0e22d1c34cb4306501383f0c5f0ed316c384c570d2314c19015e105019002005e0f7317c3acc5b0df315c334c5306301783d8d6f0ea35ac378d670cc358c18816e00701b840c03410101f840007c0ff01d83d40740f511903f85740fd01d03d00540fb01b83e806c0f901983cc0640f30d503e04640f201903dc0440f511903cc3540f40dbc3c83630fc11fc3d847305101d83c40540e901903a42640ef0dd03b80740e800d039c0440e709103b03540eb01503980340e9099039c2440e811bc3984630ed15fc3a857304801d83940340dd01703745680e319e03880740dc01b036c05c0db0db038047c0da01f037c0440dd15a036c36c0dc0dbc3683630e111fc37847303f01d836406c0d701b835806c0d501983240640c909903503740d301d03200340d1013834004c0cf01183140440c509103383540cd01503100340cb09a03282650c9099031c2480c609143142440c109382f424a0ba09182d82420bf0d782e43560c0091030427e0bf09c82f02580b509102f437e (pickBlockF p 5 0x14b093c52424b148091c51424314404d050027813d099050037c13c09804f426c13c0dd050426f13f09ac4f826713b098c44c06a14219f84e813411201e84e056812b0d004d44781320d904d457c13111804c836c13115d04d846f13411ac4cc467130118c4dc67e12a0d004bc15c11101e84ac45412d0d904ac56e11001a84a027812509904a037c124098049426c1240dd048806612909bc49c26b126099c48c26310e01a848402212c19f84a845412004d043407a16715b8578c6f15531ac530c67143318c57836f1550dac5303671430d8c4e4b4f1390d2c4b834711f0d0c43006a11d08e046c26011209884642381160d00444262110094845845410d098845423811304d044034010f00b844045410e04d0448b4f1120d2c44434710d0d0c470c5b11a315c47035b11a0d5c460b4f1180d2c45c3471140d0c43025221115bc83c56720d31bc82cc6b1f8319c7d8c631d8316c6e8c5720d0dbc82c36b1f80d9c7d83631d80d6c6e83571ae2d3c6b834b1860d1c5bc34316809a847825210b01a82bca3f0af08ec28023709008cc2b8b4f0ae0d2c27c34708f0d0c168074 0x19809f465c27c18f09a8628266193058464416018d056862415619405f064816c19309d464427418e05f063c27a18d09d862c16c18a05e862417619f15bc66856719905bc65816b195059c64016318c056c6201571a819fc6906771750d005ac27a12e098861c25011701e861426a17409a061026218309804b425017b11505d013817a115060837418109e04b026017308e05fc27217209c05dc45417204e05d845417e0e305f428017108e05ec26812b09405e424217811c05dc27017a15bc5d856716a09a84a825211601a85d016817205c05cc56f171159c45406a18019fc5f067717511505a427a11f09885c023811401e85a834016a11505b8c5b16d315c5b835b16d0d5c5b0b4f16c0d2c5ac3471690d0c508b4f1420d2c4dc34712c0d0c5943681620d5059446c1610d4058836c161119059835f1640d6c58c3571600d4c57c16415c096056424415c0d70560240159093056035415d093c56c24b15a091c55c24315604d054c3781500d5054c47c14f0d8054036c14f11d055036f1520dac54436714e0d8c53417c14a096051c24414a0d705182401470930518354))) (pickBlockF p 9 (pickBlockF p 7 0x1dd09c07a01391dd04e079c1341e90e307982801dc08e076c2481db04e07903541e309607682381e105a077c1481dd05c076c1481e011bc77846b1dc119c76846311d01a87cc57f1ed15ec7945771e215cc5b827a1d908e047007a1c3094070c1601d719e07582781c2098075025a1d309607482521c109407041601d111f07002701d0092073825a1cd09607302521bf094072816c1c905846fc1601cb1a007202801be09806f42501bd058071847c1bc09c07142481c305a07041481bf05c06f41481c211bc70046b1be119c6f046311b01a875447f1cf11ec71c4771c411cc5b427a1bb098046807a1b309a06cc1381b90dd06e027814209806c82381b109c06c41381b60e306d42801b008e06cc1681b105c06c856f1b0159c46406a1b719fc6d067716c09e84e42621af08e046007a13809806b424a1ac09206ac2421a209005ec3401a205406a857817a0d006a4278137098067c2501790d405e03501a7090866c2401770d0066c1501a616005d83401a50a006682501a305a46881681a1059468016419e05f467417c19c05c466c17019805e465c17819405d0648164 (pickBlockF p 8 0x25a2d3c944b4b2482d1c8fcb4325a093c94424b248091c8fc24323628fc8d823b22c08dc87023321608c085834421a2dbc864b6321a09bc86426321828fc86023b21708dc8542332ce15bcb305632ca31bcb20c632ba317cac0c5b2a6315ca60c532ca0dbcb203632ba0d7cac035b2a60d5ca6035328e2d3ca3834b2810d1c9ac343263059886c06621401786e0b4f1b80d2c6a43471810d0c6dcb4f1b70d2c6a03471800d0c84826816709406d4b4f1b50d2c69434717d0d0c6d0b4f1b40d2c69034717c0d0c8402701f4316c758c571f3316c754c5720e09a05782521ee316c740c571ed35ac73cd671550988830238208097881825a20009587f825220405287f414220805a880c15820505b07f014420609a8810266203097080415c20005a87ec1401fc05307f826a1fd09987ec2541e6316c720c5720a056c824157207053c80814b1ff051c7e81431e5316c71cc571f909c05302521e3316c714c571e235ac710d6714309887dc2381e109a07841381f50dd07d02781e008e07c824a1df09207c42421f0090077c1381ef0d507b82581de08e07b027a1eb09e07a8272 0x2730d109c845427a0d909e406426d00d09dc06427501189d035427301509d856f272158c994166225019885805e27009a09b825826f15bc9b456327c19fc9e0673271115099017621c01d885406e26c00d09a457026508c099434426a2d2c9a0b4726a092c9a024726728fc99c23b26608dc9902332610da097835426111b097435025e0d709744642620d7c98035b25f0d5c97035325b11f09603682550d5096046c2540d4095436c254119096435f2570d6c9583572530d4c94827c24f0d6093034424f117092c34024c0d3092c4542500d3c93834b24d0d1c92834324915c09183682430d5091846c2420d4090c36c242119091c35f2450d6c9103572410d4c90027c23d11a08e845423d15b08e445023a11b08e456423e117c8f045b23b115c8e045323709f08d036822b09008c435423411b08a82502300d408a42402310d708c0464228094089c1402350d7c8cc35b2320d5c8bc35322609008b803622d11c089423022b0d3c8a834b2290d1c8a034322700d889836022311a088045422315b087c45022011b087c564224117c88845b221115c8784532250d1087427c)) (pickBlockF p 11 (pickBlockF p 10 0x2920d2ca143472780d0cb340542c42d3cae0b4b2ae2d1ca88b432c3317cadcc5b2ad315ca84c532cb019086805e2bf317cad4c5b2ab315ca74c532be35bcad0d6b2aa359ca70d6321901b8b240342c701f8b180762c515d0b100742bd0150b0806e2c10198b004642bc0190afc0442bd0dbcaf03632c311fcaf847325a01d8aec0542b90dd0ae00742b300d0ad83542b50150ac80342b311bcac84632b715fcad057326a05d89440762b100d0abc6782ae01d0aa406c2ac11f0aa007c2ab0110aa436f2a80d8cab447f2aa11cc9a017624801d8a9c06c2a501b8a900662a30dd0a8807429b00d0a8004e29f0118a7835429d0150a6803429b11bca684632a115fca7057323f01d8a640342970dd0a5807429100d0a503642930190a4003429115bca4056329519fca4867326705d88d807621801b8a3c03428d0138a3004627708c0a2c5782760d00a280742840170a2004e27308c0a1c5682720d00a180642830170a1056f283158ca2467f28519cc9c434026605d88b007621701b8a0805c28001b89fc0662770d109d845427e0dd09f407426f00d09d42342740d109ec056 0x30d0da0c2835430d11b0c2435030a0d70c2446430e0d7cc3035b30b0d5cc2035330711f0c103683010d10c1046c3000d40c0435c3001190c1435f3030d6cc083572ff0d4cbf82542fb15e0be04642fb19f0bdc5602f811b0bdc6742fc15bcbe856b2f9159cbd85632f50950bc83782ef0d90bc847c2ee0d80bbc36c2ee11d0bcc36f2f10dacbc03672ed0d8cbb04582ea08c0b782442e815e0b882342e51190ba067c2e108d0b905602e008d0b9446c2e419d0b7c2342e2117cb8445b2e0115cb7c4532dd0108b742342e915bcb9c56b2e6159cb8c5632de08d0b700522ea0d10b6c2543182dbcc3cb6b3062d9cbf4b6331809bcc3c26b306099cbf42632f428fcbd023b2eb08dcb682332d700d0b4c3402d31150b60c6f2d6318cb6036f2d60d8cb54b4f2d50d2cb503472d20d0ce2c56f389159ce1cc6f38531ace0cc67381318cdacc5b355315ce1c36f3850dace0c3673810d8cdac35b3550d5cd2cb4f34b0d2ccf03473280d0cc841662d90578b4405229628fca5823b28a08dc9f42332952d3ca5434b2890d1c9f03432cf0190a4ca3f29308eca1823727908cca48b4f) (pickBlockF p 12 0x36905d0d6816c3670578d9815636511f0d6417c3640510d8815e3610558d8068035f0630d6016c35d11f0d5c17c35c0510d6836f3590dacd603673570d8cda047f36311ecd7847735b11ccc9817635605b0d5037435305d0d381343510e30d4018c34d04d0d3856f34d159cd4867f34f19dcc941762f405b8d301342d50188d2814e3490518cc823034815e0cc434034705d0d0015c3300940cbc3503450538cb82303441600cb43403430630cf815c3411190cfc47c34015bccf856734619fcd0867732c0d00c901762eb05b8cf415c2d40188cec16e33a0598cc83443311150ce437433805d0cac13433605f8cb834432d1150cd438c3340630ca81343320590cc014e32f11c0cb817c33115bccb45673230598ba815e2d30148cac56f32a159ccdc67f33319dccb045432205d8b6816e32904d0b4806232308c0c8c3443272d2cc98b47327092cc9824732528fcc9423b32408dcc8823331f0de0c7036431f11f0c6c36031c0db0c6c4743200dbcc7836b31d0d9cc683633191190c583683130d10c5846c3120d40c4c35c3121190c5c35f3150d6cc503573110d4cc40254 0x39f08ece7423739b08cce680263a10d74e642603960da0e4c35439611b0e483503930db0e484643970d7ce5435b3940d5ce443533a211b4e6023439005f0eed35d3bb6974ec123f3b088ece9523738f48cceec15d3b0a4fcec093b3a524dce3c9333b064bcec012b3a5049ce3c12348051bd1f94634806dbd1f9b634724d3d1ca34b45c4d1cfd134348009bd1f8263472a93d1c8a4b45c291cfd0a4347268fd1c823b45c08dcfd02333bc0598b4514e2d164f8b4412e38e0198d4ca3f35308ecd1c23733808ccd48b4f3520d2cd183473370d0ce3016435028fcd4023b34308dccd023334f2d3cd3c34b3420d1cccc34338a05f0dfcb4b3692d1cdf8c5b368315ce201643180578b6005237a316cd90c5737935acd8cd6730f05b8e181343752d2cd7cb47374316cd78c5738405f0c1815e372316cd70c5737135acd6cd672fd05b8e081342d60188e0037437f05d0dc013437d0538df014637b0d50de815436f04d0de017e37705d8dd838c3750630db81343730d50dc815436d04d0dc046f36f11acdb846736d118cdf857f37915ecdd057737115ccc9c17636c04d0da8678)))) (pickBlockF p 20 (pickBlockF p 16 (pickBlockF p 14 0x3dc0480f6c0143e50090f680143e108c0f8c14c3d90050f800243d80050f802343e10d10f7c0243d70050f9823f3e408ecf882373de08ccf580143dd0980f540143d80480f602343db04bcf6812b3d9049cf5c1233d200bcf3c02b3ca009cf1c0233d60540f4402f3ce00acf240273c5008cf4c1243d309b0f481603d40df0f441243cf0980f382343cb0490f100403c300c0f080203cb0d80f281603c10080f304703c90490f000303c204d0f1c2603c104d0f1802c3c30490f0c2503c20540f103603c10490f142343c00510f541243d000fcf3403b3c800dcefc0333dc08d0ef80143f148fcfc623b3e748dcef52333f1a4fcfc493b3e724dcef49333f164bcfc412b3e7049cef41233b948fcee623b3af48dce892333ba0590edc3683b40d50edc46c3b30d40ed036c3b31190ee035f3b60d6ced43573b20d4cee446d3b105f0e841203ad0960e801303aa0910eb435c39f0500ea424039d04c0ea824c39c04c0ea435439b0500e680303ae093ceb024b3ab091cea024339904c0e9c0263af11b4e983703980480e9005e3a108d0e8c16439c08c0e7814c39c0d10e8023f (pickBlockF p 15 0x42605110a813c42808d10982344290d1107425e41309690302563fe094909c15c425055108816e42005890481493d1019908812441f04d107c12442008d107814442308d108417e41d05c90441594100560f4007641808d105c2344160d1106c25441a055106024441705110584624120934f380663fc05110483443fb0550fe014441915c905434441409f904c272411097504025c3cd01d8ff41313f904c0f2406640e08d103417e40c05c8fe81413f70500f2007640708d101834440a09910241644070550f1805640611b900c26e3ff0988ff42453f9091101413c3c50199008154402049100c2344010590ffc3443fc0530ff02343fd0d10fec15c3c10158fe42343f80530f0006640815f901034440009f8ff82723fa0954fdc2543bf01d90f846f438118d0b823442c05bd09016341c053d03c14b40b051cfd81433be019915457f44e15cd1103443bd05d8b4915e38f01d8fd40243f305f0fc80143e604c0f940303e40500fbc0243ec0900f881303e104c0fac0243e00080fac2443df00c0fb03543de0500fa80243f0093cfb824b3ed091cfa42433dd04c0fa0370 0x46500d117c348446048119045844508c118c05445e013118436845f0d2118046f45e118d1a857f46215cd1102303e705d8b5115e3a501d917404c3a401d1100064440017116c16e3a301d116806e45901b116006643f019113423443f059113034445709d0e8808445601d10f802444b04910e804444a049112412444804910e803c44708d115014e453013914804c45101190e404444608d10e41444450d1114025444f01510e00243a101d113406443500910c403443100b112c13e44a00f912403c44800d90c003443004d111c24444601110bc02444c11bd1144633dc0598b4d14e39801990b80244370d110d823440a050102835244001790d423444305a510816844105950fc16440805050d034443308d10c823441b05610c401441b0d250c012443a00f90bc23441905650f414943c05210ec14543905110dc1594360555018131418052106023943100b905814943404e50cc13843204d50c01344350d7d0bc35342d057d0a415342304fd05413b40e04dd0101333d5015908813e40304c90b4234421053905014a40d051900014242b00b908024e3ff09090a014c)) (pickBlockF p 18 (pickBlockF p 17 0x49e15a126c25d49a094527036c49908e125846a495118925c57049405f124425d490094524836c48f04d127c56a49d0dbd26036b4930d9d23836348c11a122835c48811c121835c48b0dbd22436b4870d9d2143634b819e92c847f4ac11ed2984774a011cd23423448405b14ec56a5394dbd4dd36b5354d9d4cd36353969bd4dda6b535699d4cda6351648fd45a23b4b948dd20d23353905bd4dc16b535059d4cc163516a4fd45893b4b924dd20c93351664bd45812b4b9049d20c12347c48fd1f223b46b48dd15923347b4d3d1ee34b46a4d1d1553432d8a538b6193e3bb01d12040644794d3d1e634b4634d1d13d3432d7a138b5d83e478517d1e245b462515d1394532d6a578b5994e47f0090ee807447701911dc16447d09d0ee408447c01d11d802447501111d414447a09511e405447400911dc16447505111d846f474118cfc806647b15fd1e05733f105d8b5695e3b001d91cc02446e00d11b802c46e00b91c413e47000f918403c46f00d91b40344610da113412046c11e11302303af02111ac074460013119803446600b119802e46904f91a003e45f00f119c036 0x4e309d13842644e70df539837c4dc0d7935435a4cb0d5930c3524e209853802604da093935024a4c909193082424e309f138426c4e20dd53803744d90d7934835a4c80d593003524de0d9136c37c4cc091137427e4dc09e93682764d909c93442594d009613582344c609f134c2344bf09512f42444d70df935437a4d40dd93483724d10d7534035c4ce11a133025c4ca11c133427e4cb09e93242764c809c92f82414bc09013182644c408d13042344bf09712f424c4c50df930c37a4c20dd93003724be0d552f03544f811bd3cc46b4ee119d3a44634e809bd39426b4e4099d37c2634d8093d33c24b4c7091d2ec24351519e943c47f50911ed40c4774fd11cd2e836048d048127c23449e08d123015c4b615a92305684b515892d05604b719e12742344b305d122c16c49c08d122815c4b00db522836c4af0d852b83604b111f126023448905f12b414449708d122015c49604912541244aa15e92a45784a815c922057049404912ac68049308d129c18c48705b12482344860571244124490049129036d4860db128c3614a20d8123c1244a511f123823448505f1284144) (pickBlockF p 19 0x5298d2d4253474ac4d0d4e016c52848fd4a223b50848dd2ad23353615c148d23f52388ed40d2374a648cd48923f52288ed4092374a548cd48134f5208d2d3f53474a04d0d4d016c51f057147c56853119e14c017451e05b147415c52d0db547436c52c0d854ac36052e11f147017c52a051146c15c52715e949857852515c946c5705281a0149018c51a05b146415c5190db148847c51805f148414451f11a147435c51b11c146435c51e0dbd47036b51a0d9d46036353219e94bc47f52911ed48c47752011cd45c16c49f04813ec35049e048144c26d51209b14442614fb09814506785100de13e036049d04813d835049c048126c13049a050143426d50c09b142c2614f6098126413050e11f13cc37050a0d212601204ef0d4125c12050709b541826c50509853bc2605081a014103804ee0d8124c1204ec0d4124812050109b540026c4ff09853b026050211f13a43704fe0d212381204fc09a53ec2684fa09953e42644f709253d82484f509153d02444f209f53c427c4f009c53bc2704ed09253b02484eb09153a82444e709e53982784dd093935c24a4cd0919314242 0x5d769ad755a675d3698d6ed23f5bb88ed66523756748cd76416f5d705ad7541675d3058d6ee93f5bb24ed66493756724cd6ed92f5bb04ad664127567048d58806a05b40c816d82205b004957534f55d8d2d55934754d4d0d56d45f55b916d549457549514d57827455c095157457f55b15cd50407655900f956003655711e152023055500f9550036553116151023055615fd54857354308c150007655001b953c0665480d11538274547049151812454508d153004e54b011951034454a095151c03e54600d951424454811bd51046353f019953457f54915cd50c34453e01d94fc12053f08d150523f54188ed50123753e48cd50693f54124ed50093753e24cd50592f54104ad50012753e048d58146f55f518d581b6f55f6d8d56934f55a8d2d5453475424d0d58026f55f098d56aa4f55a292d544a47542290d569a3f55a08ed54423754208cd4f406653248fd4ca23b51548dd2e1233532a4fd4c893b51524dd2e093353264bd4c812b515049d2e012353148fd4c623b51448dd2dd23353a15a14bd23f52f88ed43d2374b248cd4b923f52e88ed4392374b148cd4a534f))) (pickBlockF p 23 (pickBlockF p 21 0x5b00d215e41205ae0da15e01205ac09656ac2555ad16316a838059d0d615d0120573048169c2595a609556940225a8119166c3685a40d215b81205a2099168024459e09f16702445a111bd67c46b59d119d66c4635ba15d96d047f5af11ed6a44775a311cd66835856d048159407a05e410960023457f08d165846e595119965006259715d15f823459305d15b015457d08d164035958f0d5564446457908d15ac16458e05115e023458c05915dc124576049162847e58911d95d412458b16315d023458806315a815457308d15c812457104915c01245850d6561035556f049160c03258611915b8234569059160814457f11915f024957b09155f435457a08e15dc36e5760d995e047c57505f15c824957109155c00225730d515bc13458011995f836f5790dad5d036756e0d8d59006a05d40c95b036f56b0dad5a83675690d8d66057659211fd63447b58711dd60447356d08d15a015456301e8171042564048159023456648fd59a23b56548dd58d233566a4fd59893b56524dd58c93356664bd59812b565049d58c1235db119976536f5d74dad7553675d34d8d765a6f (pickBlockF p 22 0x5de24cd78592f5e104ad7801275de048da5145f692516da4145768e514da51b5f6926d6da41b5768e6d4d9c934f6728d2d9413475e24d0da5025f692096da4025768e094d9caa4f672292d940a475e2290d9c9a3f67208ed9402375e208cd77405e5d248fd74a23b5ba48dd6612335d2a4fd74893b5ba24dd6609335d264bd74812b5ba049d6601235d148fd74623b5b948dd65d2335da119173d23f5cf88ed6d123759248cc192832064608973923f5ce88ed6cd23759148cd72934f5ca8d2d6bd34758d4d0d7601545c848fd72223b5ad48dd62d2335d611f171123f5c488ed6a523758748cd70d23f5c388ed6a123758648cd70534f5c18d2d68d3475814d0d750154062a1081898325d115d17401745c005517343595cc0d557384645bf059172c1445c9059171c47e5c611d972058c5c506316f81545c311916f41645c2051170036f5bf0dad6f83675bd0d8d7485765cf11fd72847b5c411dd7044735bc055159807a060a10960012057f04816e02595b709556d80225b915d16d43785a10d615f812057d04815f014057b04c16c82595b109555e81305b3119167c368 0x63509518d005463201118c003e62f00d98b836062d01b18ac03e62a00d98a434862801118cc45f631116d8b0457627114d77c05e62505658901586230555888154620052587c14861e051587414461b05b586816c61905858601606160525854148614051584c14461005a583c168606053980014a5f605197b814260c059182815461009b583c26c60509797f825a5f409597b025260b054582415060305397f414a5f205197ac14260c05b182815c60b099582426460209797ec25a5f109597a42526070d5181036c5f5051181816e60505a980c16660205897e81595f905617fc1245ef05b17f01245e8055179814460009b97f826a5fd09997ec2625fa09757e425c5f711617d415c5f311817d816e5f405a97c81665f1058979c1415e505017bc1545ed04917a81245e8057179814c5ee09b97b026a5eb09997a42625e70955794254621117d87045b617115d848453611057d83815b60d055d820153601053d7e014b5f0051d79014364a15bd91056b63e159d8e05636260d1177806e5e3009177c1205df08d178523f5e188ed7812375de48cd78693f5e124ed780937)) (pickBlockF p 25 (pickBlockF p 24 0x6810139a0004c67f01199d404467505119f825467d01519d002467b05519e414467705b19d414467a117d9e045b676115d9d045368815bda1456b682159d9f05635e101b99cc02467100f996403c67000d99bc0346590d618d012066e11a18cc23066d019196004c66b00f995c03c66a00d99a40346570d218c812066811618c4230667015195804c63005018bc14062e090199403e65500f199003666300d195436062d048198847062c08c198407c65401318ac14062a05018a424065f00f994c03c65e00d99740346530d218a012065c116189c23065b015194804c6590d6195c3486550d8194c348658117d95845b654115d94845366c15bd99856b660159d96856362608c178006e65101318dc12463604918d423464f017993805c64d015988805463408d18881546330d1193026464b0191884024649013992004c647011987404463208d18741446310d11918254645015187002464301b986806c642019990406462d08d186816c62c0d1190027c63f01f185c02463d01398f004c63b011984c04462808d184c1446270d118e8254639015184802463701398d8046 0x6b10941ac04566ab0924f980526ad0971a882446ae0d69ab03566ab0d34f900526a90d31a9c24c3e30109aa035a6a60969a942566a108c5a802306a40530f880526a20930f840426a10d15a803443de0149afc34b6b90d1dae024b6b3091dabc23f6aa08eda8c23769f08ccf740426cc1185b2434b6c20d1da782603dc010899503a69c0db1a6856069b0d2da643476e615c5b7445b6d5115da7423469805f0ef40522644129d4846174f4d2dd3534774f692dd35a4773648fdcda23b6f048dda5d23374f052dd34147736a4fdcd893b6f024dda5c93373664bdcd812b6f0049da5c1233bc010898d03a26360a898c01a68948fda2623b66d48dd92d2336884d3da2234b66c4d1d9293436950151a1934f6868d2d99d3476454d0da1545f685916d999457644514da4c02468348fda0e23b66148dd8fd2336824d3da0a34b6604d1d8f934369101b19f534f67d8d2d96d3476394d0d9f145f67c916d969457638514da3c02468d0179a3005c68b01599ec05467b0551a2826468901919e802467901119e41446870951a1805467800919dc06c67705b1a1027c68301f19d8024) (pickBlockF p 26 0x6f50905bcc2406a304c0fb40626a204c1bd825c6a10501bd024c6a004c0fb00526f80da9bdc3666f50d55bcc35469f0500fa4062716116dc4045770f096dc30257706093dc0024b6f9091dbc824369e04c0fa005272d15c5c8c45b71c115dbc437069d0480f9c0522664129bb83586d40491bac3446ee1171b4c1246ea0d01b481246eb0d31b441246ea1151b3c1246ce0491bbc34f6ed0d2dbb03476e90d0db341246e80109b944696cc08d1b9c1546cb08d1b2823469c05b1b800486e000e9b803706e30df5a7037c6e20dc5b843706df00e9b946806e41231b2423469b0631b781446c808d1a6815c6d80141b6005a6d815f1b6c57d6da15f1b6457169a15c1b5c0526dc1a01b082346990631b5816c6d108c1b443446d004a1b5023f6d308edb482376cf08cdb380326cb0d65b341446cb15c1b2837c6bf09c1ae82406bb00e1aec2606c709b5b1826c6c50985ae82606c400a9b205706b909c1b0c2506a80915b042396c008d5ac434c6b108f5aec02a6be0975af425c6bc0945ae82506b008f5ab834a6a60d19ad40426b70d71ad83506ac08e9a942366b40571ac835c 0x73705f0fc4052267a129cd02587310911cd035c7300901cc424c7300d51cd424f733092dcc824772f090dcb046972e0d61b3012072a0d21b2c1207190d81b2812072600a9c6803872615c1c6827072a15c1ca427d72809f1c9c27171909c1c9402a72c1a01cac48c7160e01c903486c90481c443506c80481b1c1306c60481b1414071200e1c482706c404c1c8427d72009f1c7c27171109c1b0c13071e00a9c886807100e01c743606c20481bf83546c10501bf824571a00a9b001306fd0955c6c2497190921c602457170911afc1306be04c1af412070a0d71af01406bb04c1c2824d6ba04c1c4802a71509b5c5026c7130985c442607090935ae41307080d79c1435a6fb0d59be03526b80501adc1306b604c1c3846c70d1181c1c24e7030929be82466f70909acc1306b204c1ac413070b11b1c282606b004c1c2456670809a9c1c2667020965c042586af04c0fc00626ae0501ab412070409b1ab01306f60951aac1406f40911c1436a7030d99c0835d7010d71aa81403ee0189aa41306ff1171bf82486a804c1a9c1206fc0971a981306a50481bf446a6fb09a9be8266))))) (pickBlockF p 41 (pickBlockF p 34 (pickBlockF p 30 (pickBlockF p 28 0x78215addf0567776158dd8c34456305b845115675501b9d680247560481d5823475848fdd6223b75748ddd55233758a4fdd6093b75724ddd5493375864bdd6012b757049dd541237c7517df1545b7c3515df054537c76d7df15b5b7c36d5df05b537aa4d3deaa34b78d4d1dd653437c7097df1425b7c3095df042537aaa93dea8a4b78d291dd64a437aa68fdea823b78d08ddd64233562057842d14610b64d842c1267540179d453597516965d1123f74488edcb52376e648cdd44159744a4fdd1093b72d24ddb9893374464bdd1012b72d049db981237434d3dd0e34b72c4d1db9534374248fdd0a23b72b48ddb9123375115c1cfd34f73f8d2dc8d3476dd4d0dd4017c26aa1289a983a73e48fdcfa23b72248ddb71233269a0e89a582a74e15c1cf123f73c88edc712376d548cc9a283a26860a9d2c3587480d11d2c45c7470d01d2034c7471151d3034f74a0d2dd243477460d0dd0c4697450551d0414473b05b1d0457073b0df1d0c6807421231ce818c7400511ce415c73915c1cf86807380631cf416c73b0db1ce456073a0d2dce03473f30109d1057173f116dcf0457 (pickBlockF p 29 0x7ac0091ebc45f7ae116deb44577ac114def056f7b915aded85677b0158d59816e118a559d6006e7ab0091ea403e7a800d9dc81207a711a1dc42307a60191e4804c7a404d9e8c03e7a200d9dc01207a11161dbc2307a00151e4404c76e0501db414076c0501dac24079e04d9e7403e79c00d9da812079b11c1da423079a01f1e4004c7680501d9c1407660901e6003e79700d9e543407650481e5845876408c1e5005478f0131e4845f791116de4045778f114de9456f79f15ade64567793158dd8c23056505b845d15675701b9e3804c7750491dd012477308d1e3005e78b0159dc82347710d11e282647890191d840247870519e1804e7850119dc023476f0d11e102547830151d7c02478105b9e0006e77f0199da82347690d11df827c77d01f1d7402477b0139de804676508d1de014c7640d11de42547770151d6c0247750139dd00467730951dc80547700111db813676d00f9db003676b0d81da806c76800f9d9c0367660d21d94044771117ddbc45b769115dd9045356405784591467560179d881587600521d7816075c0521d8445f75f116dd7445775b114de2056f 0x7da24cdfa992f7ea04adf901277da048dfa134f7e88d2df813477d64d0df9923f7e688edf712377d248cdfa41447e705b1fa85697e8116df984577d10481f8c2697e20995f843487d00481f3c1407ce04c1f7c2697de0995f341307dd0d81f301207e415a5f8045b7dc115df2c1207d108d1f643697d80d95f402347d70511f545697d41595f302347d305b1f3c2597ce0955f342507d11165f4034b7cc0d1df685697d6116df484577cb08d1fb44597ec4d2dfad3477ec692dfada477e548fdf9623b7db48ddf292337ec052dfac1477e5a4fdf9493b7db24ddf289337e564bdf9412b7db049df281237bd48fdef623b7a648dde252337bc4d3def234b7a54d1de213437c80151ee934f7ba8d2de813477834d0dee545f7b9916de7d457782514c47295611c6519f180247b748fdede23b79a48dddf52337b64d3deda34b7994d1ddf134311aa5184699367c401b1ec534f7b18d2de513477774d0dec145f7b0916de4d457776514df080247c00179efc0567be0991ef40647af0091eec2547ba0151eb80247b809f1edc07c7ad0091ed404e7b40119ec814c7b30951ec4054)) (pickBlockF p 32 (pickBlockF p 31 0x8220941f3006f76901adb0806762c018e08405c820014206c15981a09a606425581d0552038029809008605426481b059206836d8170d96064266817099605c56e81115b605c259814094604825081509b204c25e8140d9604836481108fa03403980800c604002880e0dba03436280c019a02c024807019201c2508090dba020362806019a07025f818096e05825780f094dd9805b629014e02802b805008e07836680408e1d9006b627018e31c45f8c4116e2f84578b7114e2d435f89d0d6e20435785d0d4e11434f8430d2e07c3478030d0df2c05f763016da74057626014d5b404f543012d234047444010ccb103f27140ec5d503708440ce00447c7ff0df1ff45707fb0df200034f7fe0d2dff03477fa0d0dfdc4647f50d51fcc47c7f10d51fe05667f60dbdfd036b7f20d9dfc0363a2715be88456ba1b159e84c5639e211be71046b9a6119e5c846394c117e47045b8ea115e32845380208d1fe41667ef0579f2806f75901ada5c0675e2018d59c05f542016d20c0573f4014cca104f26b412c5bd047066410dfa923f7ea88edf912377da48cdfaa93f7ea24edf90937 0x868094219c24086a0d4a1a425a866095a18c02286400f15c015e86304da18805e87f093e1f024b878091e1cc24356f013d51404b48f011d11c04386e00be1ac02b865009e1840238800d7a18013456e017d51005b48e015d11405385f00e217803485c09821603698570d5616805884f0d9216046d855119615c3668550d9615026085415b2148160852098215456e84d15b615435984e0d4614c262851058a13c36c84e119613434e84b019a124160848019a16435f8560d6e14035784c0d4ddcc05b635014e12803b84700ce16c4668460511dc406b633018e1103667d001bddbc06b6c9019d8c406384009a60fc25583200a60a802183b099210036d83d0d960fc26683d09960f456e83815b60f425983a09460ec26c83a0d960e425c83808fa0c403982900c60dc02883600920d026683000ea0bc05482800920bc26c8320dba0c43626c4059a0c013e82e019a0b036a76e01aa09c022825019209803482800f209826082509420a836e8290d8a09c136824019a10425f83e096e0f0257835094df3405f76b016db0c05762e014e0cc02f82d00ae0ac027823008e10856a) (pickBlockF p 33 0x8b900ec9d102b087408e2f445e8b805109c903b08540ce2d845957e013d52004b49d011d1300438b405122c045e8a911762c42598a909462b02548b10d762c023e8af00922a825d8ab09062b025c8a809122a025c8a604922981448a90d762ac3558aa097a2a425d8a709162941268a3097a2841248a00d4a2c824f8ae092e2b42478a4090d5e804f499011e28802f89f009e2cc35e89e08e15e405f498015e25846e8990daa25c36888c01b621806589b01122483448980d1626446e89711b22384628960d3a23834d8910d4a23c56d8900d4a25016088b01762140558920db224416088e11aa24046688f0d3a23834d88a0da222846c88c0db622c3658890d6621c3618860d76214355884058226835f8950d6e24c35788d0d4e22005f883015d5d403f49400de27046188205b15d004f493011e1f445e87411761f825987409461dc25487e0d761f423e87200f61a403587b15a21d425d87609061e805c87901421c402d86600961dc25c8740d761d8355875097a1d025d87008d21c02488720d6a1c435686f097912c05286d00ea19002486d04fa1b005e8670d521a0234 0x8f3015240457c90015b23fc05c90519fa41067290305ba40816c8fe01da3e85708fc19ea3ec57a8f915da3d00528f201423c00748f101523d406c8f301723c45708f015823dc67e8f619c9b5c1768f4059a3c81648ef01da46056f91315ae44456790a158df4c06f77e01adb58067640018e41805f8fd016e3e00578ee014e08412482008d246c67a81f08d1ff01768ed05b1f4807f77c01edb5407763e01ce3b006c8eb01820782348e905f23983798e40de238c3658d500e63400318de0dd23943658da0d9239847d8e411f23804758e30dda3803758dc0d8238067e8d819f638447e8e00da63743618d90d8237837c8dc11ba36c36e8da0db23744758d911d236034e8d4012633c0418d700e234c0748d30db235447e8d411ca3480768ce01d23383608d011fa33c4728cd01da39c36f8e20dae37c3678d60d8dde406b63a018e34403b8cc00ce3a047680308d1fe81768cb0511dd807b63801ce3240588c80150cc503f27640ec5e903708940ce31834b8c50d1e30825c8c308ee30423332f40fc5e10378c000be2f456d8bf0980cb503f17640de2ec4688bc08ee2e8237))) (pickBlockF p 37 (pickBlockF p 35 0x9480d964fc36494911f651c47c94411d65183769440dd64e004d92b011651067e93d19f65103699410d864f836093700f64a80359420df250036e93f0db250447593e11d24f434e933012649c04193c00e24ec0349390d124e047a93711da4d8376932012a4c404892f01d24c006492600d24900349300df24bc36c93411fa4cc4726df05da4c814e93105324b80765f70dc24b047a92b0dea4a837678701ea49403292300c2484074922011249804c920019a49003c9220dc248436092000d24a047e92711ca494146923051247c07694a0dbe51436b9430d9e4e83637d701bde1006b6de019d91806393500fe4b403b92900de47803394b11da10c2347fe05da4741447d601fde0807b6dd01dd91007384208d245c57991515e245056591a01a246406490501663dc05191011d245846590d119245c67d91519f244867591411da44847590901b63ec06591219fa42c67d91215a643c56190c158242005d8f9015644047c90e11ba43446c90f19d643067490b11ba4100698f6018581c46490919ea42067690715d9e0407a90301aa40806890001d24040648f501523fc066 (pickBlockF p 36 0x97f11ba5f446286108d160c16e97b051a5e014497701ba69035f99f0d6e66c3579930d4e180124582017d52805b4a1015d14005398d00fe61803b98000de5d803385f08d21781249a511ba1742347f005ba5d414458101bd52406b4a0019d13806397401225cc04485b08d25c417c85a04925b447996b11e25a846585904925bc068957012654804196111d216012496c119657846485704925b457d96b15f25a057596a11da5a0475856049259c370855049215012496719f257446096569f259417c853049257035095b0d4259427096405f25a067e95919f65a046996011865684609660dca58da7e96305fa14012484f049258447c84e0492571a6c95c05b257026095f11ba57846c95d0d8a56da6e95b05ba13412496015d6568574959117a130124956016654405195501d255446c84b049255c57e95615ca12823495401da540074950118212012495215fa54457284708d253c07696e11be5a446b962119e5604638460491e2806b64c018e54c04b94e010e5c057684508d200017694d0551e2007b64a01ce1102349490de651c3789460d964d003992800c6508374 0x88b04922281249af15f22241249b111f66c04759ae11a62201249aa15d221c12488604926a846088504926b04719ab11b66a4465883049270046f9bb11ae6e84679b2118e2081249ad01be6a0067588013d29c0479c215c62042349a705f1fc815e587017d29805788008d268056e99415b668c3699a10da265036187f049262c03997f00c666836487e04926883569970d521f41249a311b668446c9a00d3a1f0124992013661004587b04921e801487904926786789950db66643519960d421e012499d01b267006099100f6604035877049266836c876049266035d9970d721d4124874049265046d99911966584649950dba65036d873049262804997d010664046c98f0d121c812487104921c01249900da263c35886f049264846a991119a63836e86e0491150062989012a62004898c01521b412497c00d25e403486c049262c46e98a118a1ac234989053a62014c98701ba6084649830d121a812497a01021a4124868049219c1249830d8260835086604926144629840daa60436686504925ec03297800c25f8044864005218c12497c01325e835297900f2188124)) (pickBlockF p 39 (pickBlockF p 38 0x9ec01527a806c9e8114679c05c9ed15a67ac5619e9059a798164594057a79405ea11117e83045ba09115e8044539fb017e7d005b9ee015e790053593013d53804b4b3011d15c043a1215a62d42349e30591fd815e592017d53405b4b2015d1540538b404922cc2349e1055276c56e9d115b67783699dc0da27443619d70d927743569d40d5277846d9dc11b276c34e9cf01367240459d20db67583519d30d4276406c9ce00f671c0359d70db275435d9d40d7274446d9d6119674c4649d20dba74436d9cd11b27343689cf11aa7384669cc0dba7204649c80d427284629c90daa71c3669df0d7e76835b9d80d5e74035358e017d2b40579cb00fe7180379e011ba2742347f405ba71414458d01bd2b006789c08d270c15489b00526f057e9bf11ea6f447889a04926c407d9ab01d67040549b9115226412489804926f84559b6115225c12489604926fc57e9bd15f26cc5729bc117a6cc45d89504926d067d9b8118a6d446089304926c006d9a901962481249b911f22401249b711b66d846c88f04922381249b315ea6e05769b515d26d045e9b311762341249af11e2230124 0xa2d01728c8469a3011868b8166a2c059292c35fa480d6e91c357a420d4e8f805fa38016e8cc057a2b014cce503f27e40ec60903709140ce3242348c8049231c234a2a05928a4068a280190cdd04f27c412c60104708f410e318234a260512314234a2405b289445ba23115e310234a22055287807da1e0df688036fa1f0d8e87406f33540fc5f9037a1a19f62f8234a1c05f1fe015c333413c5f10478bd08d22f0124a1601662ec124a1815e22e8124a1611662e4234a190d2e85c3478b8049285404b27a40ec235033a1a15ba2dc234a1405509e104b08b410e2d8234a0d15ba84046aa0e11a280006d9f20196820454a0f1156814454a1015ba83856ca02158a83445ea0211767e40699ed018680c57da07114a810450a0b01f28280709ff01767bc055a0811f281846da0511b280856aa07159a810564a03117a80845d9f801a67ac0619fd15927f84689fe15b27f446ca0011b67fc4659fc11667dc06a9f601a116c0429fa01527a80549e701527e45699f815867dc16e9f605b27d405e9f015927c44649e801827c45709f011427cc4619f211767bc4559e9014a798050) (pickBlockF p 40 0x81204c204414081004c29c8375a6f0dd29b823e80f05029a8039a6500c69b402880e08c29a407480d09029a426c80c04c29ac37ea6a0dca028240a6801da024230808090299007480704c299026080604c299837ea650dca014240a6301da9ec26fa7609ae9d0267a6c098e01013079601ad970063a6700ae988023a7c11da95c37aa610d2200c12079301ed968073a5e0952970244a5a09b2960244a5f158697445fa5b116e964457a57114e954264a53091294427ca4f091295046fa5211ae940467a4e118eef456fbb715aeec0567ba9158ede446fb5311aeccc467b01118eb8c45fab2116e9f8457a60114e95836aa4d0d4a0081207db01bde3406b6f0019d940063599017d54405b4b9015d17005333c413ca0504b186411c255043a4a0daa924368a4001b68d8065a460d52910354a4a11ba92446ca3c01a68c8061a450d4a90c350a3f01768d0055a460db291035ca45119a90c464a3b01a68c0061a41159290036da3f0d968e806aa3901a28f4044a2f01528b4054a3c11a68ec461a3a05ba8e416ca3515828dc460a360d768d0355a2e014a8b0050a3101128bc06c 0xaa609baa9426c83904c20e014083704c20d8030aa70dd6a90374aa309b2a8823e8350502a60039a8b00c6a84028aa00092a7823483404c2a7437aa9c0ddaa6c2768330502a5c03aa9600e20c8230a9401d2a5406483109020c0140a8a0092a2002482f0482a5427ca9409b20b8130a990dfaa6037282d0901c78176a9704faa5813ca9301da0b0140a8f09c2a4437aa9009eaa3827682b0501e7807aa89008aa1c02082a08c20a4240a8501d2a1803482800c209c140a8a00f2a10066a8800b209813082504c2a18270a850982090130a840092a3037ea8b0dca08c240a8904daa1c134a8301daac026faab09aeaa4267a9f098e0881307dd01bde6c06b71d019d988063a9a00bea4802ba8d009ea080238210042080120ab119ea96437aa810d8207c1207dc01fde6407b71c01dd980073a8001b29fc060a7d0dc2078120a7a09e69e0278a770996070130a6b00a6998021a7309d2068140a7909969c026481904c29e837da780df29d4375a7709da9d4275818050205c140a7519fa9b867da7509a69c8261a6f098205813081504c29cc27c814050204c120a7109ba9c026c)))) (pickBlockF p 48 (pickBlockF p 44 (pickBlockF p 42 0xa5d0deab903588450481e9407b66c01ce110120ae009e6b78278add0996b2c029abe0086b64274adf0996b58264ae00df6b7837cadb0dd6b74276adb09d6b3c03dac200d6b6c67ead419f6b6c269ad80986b54260ace00b6b00025ad909f2b5c26ead609b2b60375ad50dd2b5023eaca00e6af4031ad300a2b48024ad008d2b3c37aace0ddab34276ac900eab20038ac601d2b1c064abc0092ae8024ac709f2b1826cacb0dfab2837272505dab2413eac804f2b14076ac109c2b0c37aac209eab002767a401eaaec022ab90082adc074ab800d2af003cab6019aae802cab809c2adc260ab60092af837eabd0dcaaec136ab904d2ad4076ae109beb7026bada099eb442637e101bde8406b724019d9a0063acc00beb1002babf009ead0023ae211da96c37aab30d2210c1207e001fde7c07b72301dd9980738420482abc279aad09e2ab026584104c2a64029a8c0086aa02748400502ab8265aa509920fc130aaf0df6ab437caaa0dd6ab0276aaa09d60f8140a9d00f6a4003583d0502aa867eaa219f6aa8269aa70986a9026083c04c2a7002da8e00960ec130aa809f20e8140 (pickBlockF p 43 0xb2309b6c9c251b240942cac06cb2a0182c7c02db0f0096ca026cb260976c9425cb220db6c9c365b240d92c8c26eb2209b6c60039b0c00c6c7836cb1d08d2c78268b1d0962c8036ab1f0d9ac7026e469018ac5c03ab1600e2c68054b0b0092c20024b190dbac60362b1704fac5813cb1501bac40364b1108d2c24030b110982c40250b130d8ac4826ab0f099ac28022b070081358034b0b00f2c24252b0800b2c3436eb0c0d8969416eb0a04dac1c134b0601bacc425fb2c096eca4257b21094d69005f553016d3f8057464014ec6c02fb1400aec38027b05008e17c12085e0042cc846ea4e0d8ac1034885d048168c06f55201ad3f4067462018ec0c048b020112170130b000dc216c120afd09e6bec278afa0996bb8029ae90086bd8274afc0996bcc264afd0df6bec37caf80dd6be8276af809d6be067eaf119f6be0269af50986bc8260af609f2bd026eaf309b2bd4375af20dd2bc423eaed00e6ba0031af000a2bb0074aec09b2bb837eaed0dcabac076ae701d2b9c260ae90dfaba0372ae601dabf826faf909aebdc267aef098de9c06b66e018eba802bae5008ebfc576 0xb6468f6d9012a8aa04c2d982548a90502d8da3cb6304a22a0130b670d92d9826cb62693229c140b6204a2d8c244b630952d90364b620952d8424cb680db6db4365b6a0d92da426eb6809b6d94255b606936290140b6004aad7036cb5c09a228c130b5e0daad74366b5b09ba288140b570d92280140b570942d64362b5809aad5826689f0502dd825fb70096edbc257b5f094e2781305b0017d428057b5a00bed54027b7711ba948362b540d222741205af01bd424067b520d62270120b4c15bad0856db4f09a6d34268b420986d20264b4e095ad14254b4f0db6d3436cb4c08facf803db3800d6d0c26db470946d10250b4a01b2cf402db360096d2026cb460976d1425cb410936d04364b420db6d1c365b440d92d0c26eb4209b6d0025db3c0db2cf0268b3e0daacf4366b3b09bacdc364b370942ce4362b3809aacd8266b50097ed2c25bb49095ecfc2535aa017d410057b3a00becd4027b5115c6cd0370a500d4a2041205a9017d40c0578800482cb456eb2215b6cc0269b2e09a2c88261b1900a6c34021b280992cbc256b250952cc036db2e0db2cb423eb2000f6c48035)) (pickBlockF p 46 (pickBlockF p 45 0xbaa0d622dc120285412c26d0438b60482e8c56eb9815b6e98269ba409a2e60261b8f00a6e0c021b9e0992e94256b9b0952e9836dba40db2e8c23eb9600f6e20035b9909b6e74251b9a0942e8406cba00182e5402db850096e7826cb9c0976e6c25cb980db6e74365b9a0d92e6426eb9809b6e38039b8200c6e5036cb9308d2e50268b930962e5836ab950d9ae4826e471018ae3403ab8c00e2e40054b810092df8024b8f0dbae38362b8d04fae3013cb8b01bae18364b8708d2dfc030b870982e18250b890d8ae2026ab85099ae00022b7d0081310034b8100f2dfc252b7e00b2e0c36eb820d896d816eb8004dadf4134b7c01bae9c25fba2096ee7c257b97094d6d405f557016d44005746c014ee4402fb8a00aee10027b7b008eea0569b7a0da29503528b504816d005f556016d43c05746a014ede03588b30482dc856eb6815b6dd4269b7309a2da02618b204c2db82648b10502dd0256b6b09522c01408af00c2dd436db730db2dc823e8ae0502d7803db5800d6dc4024b6909b6db4251b6a09422b4130b5d00b6d580258ac04c2db826c8ab0502db025db6b0972d9c245 0xc7e15af1f0567c79158f1d846fc5611af0e0467c33118f04c45fc10116f02c457bed114efa0166be30579f9406f7aa01adcd8067672018d6ec05f55a016d458057472014cd2e84f28ea12c6ba8470a5a10ef80259bdf0962f48029bc90086f70254bda0912f8035dbdf0d72f5803dbcd00d6f6c241bd90902f5402dbcb0096f7025cbda0932f6c355bd90d52f44039bc700c6f5c234bd60d6af54356bd000eaf3c038bd30112f18024bc40092f4835ebd10d4af4013ebcf04f2f30250bcd096af2c256bc5008af0c020bc800d2f1803cbc400b2f2435ebc70d4af14136bc304d2f08074be1093ef7824bbdd091ef60243348413ca2d04b1aa411c285043bd400bef3802bbca009ef040238c90482320010bc00da231c120bbf01a2ef8064346413ca2504b1a8411c27d043bbc0d22318120bba0d82314120bbb116eee4457bb80d623101208c30502ecc03d8c204c2ed426c8c10502ecc35a8c00502ed824bbb4090e2fc130344413c699047bb200beebc67dbb10dc22f8120342413c6910478bd0482eb0031bac0d4aeb824bbad090ca1d04b09d410eeac023baf15ba97c378) (pickBlockF p 47 0xc2e15f70b057cc2915d70ac476c2911d7088460c2919fb08067dc2911a7094461c2111830a0272c2611f309046ec2311b3088262c2515d7084574c20117b074059c180147070074c1c11b307857ec1d15cb06c076c1701d305c460c1915fb060572c1601db0bc46fc2a11af09c467c1f118def806b68a018f06804bc15010f0c4576bec05db0501547bc01eda200737e901bdeec06b740019da1c063c1211dafac176c110511fa007f7b901edcfc07768501cdf9c06f7b801adcf4067684018f03c67abea05db03816c7e601fded807b73c01dda08073c0d01b3030060c0a05f301c379c050de3010365bf800e6fcc031c000dd3018365bfd0d9301c47dc0511f3008475c040ddb008375c0219fafec67dc020da6ffc361bfc0d8300037cbfe0dbaff436cbff11d6ff0474bfb0d3afdc049bf20106fe8038bf601d2fd836cbf811fafdc472bf501dafc4074bf10d82fcc47ebf211cafc0076c080dbf00c36bc010d9efe43637b301ad9f8063bf400eefbc033c0911dafa4176bee0511ec007b67c01cefb034fbeb0d2efa8347be90d0ef9c36fbe60daef94367be40d8f21056f 0xc7505531bc268c6d15bb18c56dc710da71b8368c630d871cc156c690d931c0356c660d531bc156c7111b71b846cc6d0d3b18404dc5b011719036dc680d47194350c6b01b318003dc5900d71a436cc670d7719835cc6311b71a0465c65119319036ec630db717c46cc5f0da318446ac60119b17836ec5a1193168350c5c118b16c36ac590d9b1c835fc6c0d6f1a8357c620d4d72c05f52a015f17403fc5800df1d046ebe605bb15c1445ca01bd4a4067c55055313c57ec5211eb140478c4301f70f4075c4b1153144455c48115314857ec5015f3114572c4f117b11445dc4619f7128462c47118313407cc4201b70ec065c4b11f312446dc4811b311457ac4a15db11c574c46117b11445dc4111e310457cc4311f7108475c4011a70f0574c3c11830f8471c3d11b70ec465c5311bf13846bc4c119f110463c3f01bf0e80675c5013d490047c5415c70e417cbe5057971005f523015d70805f55c016d48405747a014f0dc46ebe405bb0d81445c101bd56c06b520019d1e0063c3501230d0044c3205f30b8479c2c11e30ac465c3001a3078049c190107098474c2d119708c464))) (pickBlockF p 51 (pickBlockF p 49 0xcaf09532b4244cb30d772c835ccae09072b0240caf09732b424ccae0d572b0354cb4093f2c424bcb0091f2ac243caa04d329c37aca60de328c354ca10d5329c47eca611f3288362ca00d8328c37cca10db3288476ca011d32a036fca50daf290367c9f0d8f27817cc9b0967268258c9200a723c021c970953254244c9b0d7726835cc960907250240c97097325424cc960d57250354c9100e7238031c920d7b244352c8f0d7b238352c9c093f26424bc98091f24c24329ea12c33a843c9000af234023c8c04d0a7285b0cca14f22c038c0948ff02623ba7c48de3a1233cb531bf2a4c6bc9d319f228c63cb50dbf2a436bc9d0d9f228363bed4d3efb634ba604d1e329343c890599f0406b68e018ca6284b0b1a10ca6183b0b160ccd5283f297a0ec6e68370b0a0cf21c164c8601a3214064352a13ca5684b1b7a11c2ba843c83051320416cc82116f200457c7f0552ebc136a1a04b8d4683f1b6a0df1ec67dc7d05f0d3e84f1b4a11ca5283b0ada0cf1ec56ec7a0550a4a84b0aba10d74004f55e012d4c004747d010f1e0569c770592f9c15e5cf017d57405b52f015d1ec053 (pickBlockF p 50 0xcde0157398344ce40d133a845ece91173394342ce30d0338004dcdd011739835cce40d33394456ce3115338435dce00d5737834dcdd0d173ac34fce80d2f39c347ce20d0f37c04fcdc011cd8283f1cba0df36c570ccf0170d7a83f1c7a0dcd7683f2aca0ec71a8370e0a0cf35805ccd40543364678cd809b335c25cccd01b332406035ba13caaa84b1c4a11c37a843cd500a334c024cce0553344a5fcd0296f33ca57ccd294f34415fcd0056f33c157ccd054f03512fc0d84aea011278ec448f328024ccb2d7f324b53ccb097f324253c0c48ff03223ba7f48de3ad233d0015ab3f8b6fcec2daf368b67cd22d8f3f826fcec09af368267cd2098f02d23fc0b88ee9f92378ea48cdfac06f7c301add34067690018f33005ccc80140d5683f2a6a0ec6ea8370d8a0ccd5582f2a660ac6e98270d8608f31436acc40da3304354cbf0d5331446ecc411b32f0069cb90187300352cbe0d4330437ccbf0db3300466cbe11932ec069cb801872f0469cbb11872e4469cb8118731835fcc30d6f308357cbd0d4f2e805bcb7014ca8e83b0d4a0cf2d81642a1a12c34a843cb309672c8258 0xd1e00bf46c027d1a04d0de685f1eda15f45c37ad160de343807dd0b01d744c354d110d5345c47ed1611f3448362d100d8343406dd0a019744c37cd110db3448476d1011d343837dd0d0dd742c36dd0a0d9746036fd150daf450367d0f0d8f43006fd09019cdda83f1e9a0df42017c374a13c796847373a13cada84b1e4a11c3b2843d0604d0dc685f2b4a16c78a8570eaa14f414038d0400d304923fc1288eeb8923794b48cf4b0c6fd1931af41cc67d03318f4b036fd190daf41c367d030d8f04134fc108d2eac934791c4d0f4081667ec01bdf1406b74f019da4806336ba13cac284b1d8a11c39284336b60fcac183b1d860dc391833cd92d87364261c0f48ff03e23bab148de46d23336aa0fcabe83b1d7a0dc38e833cff15a334405cccb0140da283f2ada0ec7568370e1a0cf3f035acfb0d633cc05dcf001573e0344cf60d133f045ecfb11733dc342cf50d033c804dcef01173e036ccf60d733dc456cf511533cc35dcf20d573c034dcef0d173f434fcfa0d2f3e4347cf40d0f3c404fcee011cd9683f1d1a0df3b426ccd001b0d8e84f1cfa11f3a835ace90d6338405d)) (pickBlockF p 53 (pickBlockF p 52 0xd5f01af5700632c5a0ec3fa833d5b1190b0e83b0fca0cf56036ad570da3550344d520d1356046ed5711b354c352d510d4355036cd520d7354c466d51119356435fd560d6f554357d500d4f53c254d4c0dab52c368d480d53518354d4c11bb52c46cd470d4b514350d480db351835cd47119b514464d4d0d7f52835bd490d5f510353d4311f350036ad3f0da34f0344d3a0d1350046ed3f11b34dc069d3401874ec352d390d434f036cd3a0d734ec466d3911934d8069d3301874dc469d3611874d0469d33118750435fd3e0d6f4f4357d380d4f4d405bd32014cb0283b0f8a0cf4c42542bea12c3da843d3000a35b4466d5a2dbf538b6bd422d9f4bcb63d5a09bf53826bd42099f4bc263c1348ff04e23bae348de5312337c701ada500632baa0ec3c28332ba60ac3c1823380a0fcae683b1f5a0dc3be833d2d0590dfa84f2b7a12c7ce8470eda10f4a8259d290963498254d2309134a835dd290d7348003dd1d00d7494241d22090347c02dd1c009749825cd2404db48c24cd250d57488354d200d6b47c356d1d096b470256d2b093f4a024bd27091f48424337ba13c7be847 0xc7448ff1d223bb7748de781233d4eb17f466c5bcecb15f2a6c53d4e6d7f465b5bcec6d5f2a5b53c564d3f15a34bb534d1e711343d75057975c05f537015ce1684f20ba11ce1583f20b60df15123fc5488eed452379c248cf5cc461d42ad3f41eb4bcdaad1f276b43d42693f41da4bcda691f275a43c3848ff0e223bb3348de6992335d5013d4d4047383a0fc7e283738360bc7e1827cd7ad5735da55c3748ff0de23bb3248de695233d30ad3f416b4bcd5ad1f22eb43d30693f415a4bcd5691f22da43c3548ff0d623bb0348de5d1233d04ad2f34eb47d04692f34da47c3448ff0d223bb0248de5cd233d2fb17f40ec5bcd2b15f22ac53d2f6d7f40db5bcd26d5f229b53c334d3f0ce34bb014d1e5c9343d71057974c05f55f016d4cc05747e014ce0684f2c8a12c7da847102a10ce0583f2c860ec7d983710260cf5c0018d6f00530c523fc3188eebfd23797048cf5ac37ad6a0de359c364d640d935ac47ed6a11f3584079d5e01c7598362d630d8359c37cd65094b59036cd6611db58c474d6001e7574071d6111e7580471d5e11e7574471d6c0dbf5a436bd680d9f588363) (pickBlockF p 54 0xa2748cf21293fc8424eeef4937a2724cf21192fc8404aeef4127a27048f600058d7f0150e2d03f2ce40ec84503710840cce2d82f2ce60ac845827108608ce2c01f2ce006c844017108004f20934fc828d2eeed347a254d0f20123fc8088eeee5237a2348cf5f534bd7c4d1f5f5a4bd7c691f1f923fc7e88eeedd237a2148cf5f414bd7c051f1fa93fc7e24eeedc937a2124cf1f992fc7e04aeedc127a21048f5e456dc7c48ff1f223bbb048de86d233c7ca4ff1f093bbb024de86c933c7c64bf1f012bbb0049e86c12338940fc83d03738960bc83d827389007c83c017c7b48ff1ee23bbaf48de869233c7ba4ff1ec93bbaf24de868933c7b64bf1ec12bbaf049e868123d79117b1e523fc7988eeea5237a1348cf1e693fc7924eeea4937a1324cf1e592fc7904aeea4127a13048cb3103b10640ccb3182b106608cb3001b106004f1e123fc7888eeea1237a1248cf5dc459d5aad3f4b2b4bcfead1f2d6b43d5a693f4b1a4bcfe691f2d5a43c7648ff1da23bb7948de7892335d9013d58004b539011d200043387a0fcb2a83b20da0dc41283338760bcb2982b20d609c411823 0x321923fc8688eeefd237a2948cf21a93fc8624eeefc937a2924cf21992fc8604aeefc127a29048f21512fc8584aeef9127a28448f21682fc8520aeef8827a28208f21581fc85006eef8017a28004f21123fc8488eeef5237))))))))
  6 11 7
def m_2347 : Nat := 0xffffffffffffffff
def s_2347 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_2347 : Nat := 0x11515571337377f
def bds_2347 : List (Nat × List Nat × Nat × Nat) := [(m_2311, s_2311, 9, g_2311), (m_2310, s_2310, 9, g_2310), (m_2302, s_2302, 9, g_2302), (m_2304, s_2304, 9, g_2304), (m_2298, s_2298, 9, g_2298), (m_2300, s_2300, 9, g_2300), (m_2295, s_2295, 9, g_2295), (m_2297, s_2297, 8, g_2297), (m_2296, s_2296, 8, g_2296), (m_2309, s_2309, 8, g_2309), (m_2306, s_2306, 9, g_2306), (m_2135, s_2135, 7, g_2135), (m_2301, s_2301, 8, g_2301), (m_2307, s_2307, 8, g_2307), (m_2305, s_2305, 8, g_2305), (m_1902, s_1902, 6, g_1902), (m_1986, s_1986, 6, g_1986), (m_2070, s_2070, 6, g_2070), (m_2149, s_2149, 6, g_2149), (m_2139, s_2139, 7, g_2139), (m_1993, s_1993, 7, g_1993), (m_2293, s_2293, 9, g_2293), (m_2299, s_2299, 8, g_2299), (m_2041, s_2041, 7, g_2041), (m_1861, s_1861, 6, g_1861), (m_2292, s_2292, 8, g_2292), (m_2294, s_2294, 8, g_2294), (m_2303, s_2303, 8, g_2303), (m_2152, s_2152, 6, g_2152), (m_1936, s_1936, 6, g_1936), (m_1765, s_1765, 7, g_1765), (m_2145, s_2145, 7, g_2145), (m_1768, s_1768, 6, g_1768), (m_1770, s_1770, 6, g_1770), (m_1761, s_1761, 6, g_1761), (m_2154, s_2154, 6, g_2154), (m_2190, s_2190, 7, g_2190), (m_2155, s_2155, 7, g_2155), (m_2026, s_2026, 6, g_2026), (m_1799, s_1799, 7, g_1799), (m_1750, s_1750, 7, g_1750), (m_1862, s_1862, 7, g_1862), (m_2125, s_2125, 7, g_2125), (m_2045, s_2045, 7, g_2045), (m_2196, s_2196, 7, g_2196), (m_1798, s_1798, 6, g_1798), (m_1937, s_1937, 7, g_1937), (m_1787, s_1787, 6, g_1787), (m_1797, s_1797, 6, g_1797), (m_1802, s_1802, 6, g_1802), (m_1812, s_1812, 6, g_1812), (m_1751, s_1751, 7, g_1751), (m_2094, s_2094, 7, g_2094), (m_2308, s_2308, 9, g_2308), (m_1756, s_1756, 7, g_1756), (m_1795, s_1795, 6, g_1795), (m_2113, s_2113, 7, g_2113), (m_1771, s_1771, 6, g_1771), (m_2146, s_2146, 6, g_2146), (m_2131, s_2131, 7, g_2131), (m_2262, s_2262, 7, g_2262), (m_2096, s_2096, 7, g_2096), (m_1827, s_1827, 6, g_1827), (m_2057, s_2057, 7, g_2057), (m_2211, s_2211, 7, g_2211), (m_2150, s_2150, 6, g_2150), (m_1946, s_1946, 6, g_1946), (m_2136, s_2136, 7, g_2136), (m_1749, s_1749, 7, g_1749), (m_2255, s_2255, 7, g_2255), (m_2240, s_2240, 7, g_2240), (m_2256, s_2256, 6, g_2256), (m_2241, s_2241, 6, g_2241), (m_1805, s_1805, 6, g_1805), (m_1870, s_1870, 6, g_1870), (m_2027, s_2027, 7, g_2027)]
theorem kn_2347 : KnownBin bds_2347 := by
  intro b hb
  simp only [bds_2347, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_2311
  · exact lb_2310
  · exact lb_2302
  · exact lb_2304
  · exact lb_2298
  · exact lb_2300
  · exact lb_2295
  · exact lb_2297
  · exact lb_2296
  · exact lb_2309
  · exact lb_2306
  · exact lb_2135
  · exact lb_2301
  · exact lb_2307
  · exact lb_2305
  · exact lb_1902
  · exact lb_1986
  · exact lb_2070
  · exact lb_2149
  · exact lb_2139
  · exact lb_1993
  · exact lb_2293
  · exact lb_2299
  · exact lb_2041
  · exact lb_1861
  · exact lb_2292
  · exact lb_2294
  · exact lb_2303
  · exact lb_2152
  · exact lb_1936
  · exact lb_1765
  · exact lb_2145
  · exact lb_1768
  · exact lb_1770
  · exact lb_1761
  · exact lb_2154
  · exact lb_2190
  · exact lb_2155
  · exact lb_2026
  · exact lb_1799
  · exact lb_1750
  · exact lb_1862
  · exact lb_2125
  · exact lb_2045
  · exact lb_2196
  · exact lb_1798
  · exact lb_1937
  · exact lb_1787
  · exact lb_1797
  · exact lb_1802
  · exact lb_1812
  · exact lb_1751
  · exact lb_2094
  · exact lb_2308
  · exact lb_1756
  · exact lb_1795
  · exact lb_2113
  · exact lb_1771
  · exact lb_2146
  · exact lb_2131
  · exact lb_2262
  · exact lb_2096
  · exact lb_1827
  · exact lb_2057
  · exact lb_2211
  · exact lb_2150
  · exact lb_1946
  · exact lb_2136
  · exact lb_1749
  · exact lb_2255
  · exact lb_2240
  · exact lb_2256
  · exact lb_2241
  · exact lb_1805
  · exact lb_1870
  · exact lb_2027
theorem sub_2347 : ∀ b ∈ bds_2347, m_2347 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2347, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2347 : ∀ b ∈ bds_2347, canon b.1 g_2347 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2347, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2347 : dagCheckRootsF m_2347 g_2347 bds_2347 (dagRefPermF m_2347 g_2347 63 3457 (dagTraceF m_2347 s_2347 12 f_2347) l_2347 0) s_2347 12 = true := by decide +kernel
def picks_2347 : Nat → List Nat := unpackIndexedPicks
  (pagedUnpackF 19 7 (fun p => (pickBlockF p 14 (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x62740c484185b830a1060320bd34174602ddb05b280b64016b182cbb059240b1c815de02afc055e00ab84153b82a70054a40a94015028294c050fa09ef013858265b04b56093b0121d8238b045b6088ac10d4020ec040b207fd80fd281fa003ee607d0c0fa001f4003dae078700eae01d1403a20073c80e6901cd0039a0071d80df481b4a0364406c800d8101aa60354006a800d0501979031b4062c80c5801892030a8061400c280181402ef405af00b1c015f402be0057480aac0155002aa0053d80a34813bb026ac04b600942812800246a045f008b8011700219604288080c80f7a01d780395806ec00d67019b203250064800c720182c03040060800bd401674029b405030096a012c002418042d807e700e5801a6402f58052c008d800eb001760024a002fa002f0000580000 (pickBlockF p 2 0xeda21d8ac3ab6074bb0e9421d0a03a088736b0e5581c7ec38ad0709c0dff41bcf0373686dac0d9f61b12c35d506afb0d4961a6a8348c8686b0cfb219cac3336065bb0ca161916c31dd0630b0c4b61867030848605b0bf7417bf02f1e05d8b0bae2173e02e7085c3b0b6f816b2c2d5885a290b422165ac2c56057fb0af0e15dc42b6d0561c0ab30156042a750542c0a6f614af0293a052700a486145f428a9051140a0b81405027ea04f0d09e0013c00278004ea609bd813474262e04bab095f61296824ce048dc0905611e64237d0466908b58113b0221d844210882210e9c217d8424b083541064420758401d07eb80fb241f1503d990799a0f0301dad83b41075720ea841cf60392c070f60e1841bd6036dd06c380d69c1a8c83510069300d09c19c5032f9065c20c9dc1930831d9 0x15e822ba3056d70acfb158f02afa455f00ab77155f02a9e054fc0a95a151382a02453ad8a68d14b982946c522e0a39c1459a288e450b68a0ac1406e28048500809fd413eec27dc04fb809f5213d56277b04eca89d9013ac6273dc4e7809cf013986270a84dbd89b341366026bd04d6909ad0135a026ac84d0d0996b13284265004c910989913120262404c1b0978b12d982586c4aea095d012b64255584aa809550129b0250e849c58933512516248984910091e4123842470048e009184121d4240ec47eb08f2b11d502386446e288dc011b08233e4467808cf0118782304845bd08abc113f82252c444d887eb10e76219f042e58851b108d620fa041960826c1042a205ac405d88038100601ff1c3f8d87e7a0fbd21f5283e4607bdb0f61a1e9303cc6078db0f0381ddac3ba8876e7)) (pickBlockF p 5 (pickBlockF p 4 0x1e0163bf1077c20ef801de4c3b9b076dd8ed0b1d87a3adf0755e0e9fc1d2963a4c474908e8a81d01439d6c735d0e6a11cc503984472bd0e5611c9d0390ec71cd0e2dc1c438385ac706c8e01c1bf1237b6c6f248dd9b1b9d6370b06dbd8dacb1b418365306c4d8d8811b02e360046bb50d6ac1abf6357846abb8d5611a994351206a188d38b1a5d4348b068b60d0ac1a03233d7067648ce1b19b123336c660e0cb5c19556327ec649e0c87c18fb431cac63360c5ca18a54311ec61f48c33b184f83072c60d88c147182623022c5fe60bf2a17e222f9ac5ed60bd1917a022f1e45e308bbe8176942ecc45d5c0baa1174322e6245c6d8b8b2171242dfe85bad0b75016e642dcc05b728b63b16bca2d7805ae88b51c16a202d38c5a340b3ac165f62c92c59188b221163322c37058068af5b 0x248c248eb0916e9223a2444248574904691fcc23e9047b208f6011e4823bcc475288e6411c572375646cdc8d2f1198d231984606c8bbd116cb22c36455e88a7c1143c2277044d5889a811323225aa44b40896811285223984446c8879110f0221a4442508848110902204e43e64877d10ed221da043ac8872390e4021c8043720869c90c8b218c443180862110be6217c042f8085d210b0a21498428108500109e2213844270084e010984211f2420b483f2107e020f2a41c9c83901071120cf44181c82b5104bb2096041248822a103f6207a440e14817c902a52054040a08813110260204c04090880d5100ec200763fdf07f5e0fded1fa3a3f1e87dcf0fadc1f4743e5f07c658f80c1eed43da747aee0f51c1e8d63ceec797e0f2d21e4563c79078f00f1b31e2e83c2f078580f0b0) (pickBlockF p 6 0x2d38e5a430b426168042d00059f88b3d2167a02cf4059e08b36d9662b2cc0459800b2f1165c22cb8059700b2ba964cb2c81858da8b18a963102c5c658964b128162412c3ae586c8b0d8161562c22858260b03195fca2bdfa578f0aebe15cbc2b81656d30ad46159cc2b272561f0abf49573b2ad16557a8aa9d9547c2a79654c6ca935951bb2a34254644a86e1500d29eb653d04a79894e7c29b5a533eca61694b5d2953852734a4861484c28f5451bb0a3161458a2899851030a1a61429b283b850470a03d13fbc27dda4f8b09eb613cac277d84ecec9d9093b11274b84e6349c6d938c1271624dff09b969367b26b5a4d37499ff1332d264d84c6b0988c9304d25f184bb6c971592d5d259384afac95e892bc1256364a97094e4929b1251f84a0f093be126cb24bdc494ec924592471 0x3577a6ac2cd5789aae1354766a5f0d46d1a8c1351626a02cd3a61a6aa34bba69434d22d9a38d3459868830d09e9a07c33f9667bf4cf1699d7b33ac267544ce5599bec3367666c84cd8899a6b3335866428cc1e9976d32d5865774ca8e1945c326fc64af0c9059913d320da63f28c78618e3d31b3463370c60e18b3e31516629c4c530989ac311ba620e8c4109876c30d3a61824c2c4184db308b060ee8c1769823b3044260844c0a69806e2ff765fe84bf6e97dfe2fa965f35cbe2497c402f7ae5edd8bd7c17a692f33a5e370bbff1773c2ed165d76cba8e1745c2e7925cbf4b91e172122e4205c7c8b8c3971802e3005c510b84616fcc2df265be40b79b16ee52ddc05bb80b74a96deb2da765b3d0b67816c962d8e45b1c0b63816c522d7565abecb56916ad02d5645a8e0b51816a30))) (pickBlockF p 10 (pickBlockF p 8 0x3ac067565ceac09d5803aae27550cea731d4e03a8d074eece9769d22c3a2f67432ce80d9cff239fc273ecce7ab1cf3239e4273c08e75a9ce2939af6735c0e6b81cd5239aa073450e6791cce1399c0732cce6239cbb93976072ec0e5c91cb72396a472b60e5339ca51394a072940e5191ca033940072800e4f11c9c23938072688e4b99c9253920472400e4621c8b13914272208e4311c84238fcc71d28e34d9c5eb38ab271414e2351c4423888071088e1e31c3c03878070d5ce15d1c1fc382f0704d0e0981c0d6380b070140e0209bf9b37e306f9acdedd9bda137a8c6f320de331bc60378666f0c0de109bc023772e6ed50dd7b1ba69374846e900dd111b9c6373806e700dcba9b8da370386ddacdb561b5dd36a566d174d9dd1b2cf364186c4f4d8459afbd35e166b87cd6ae1ac8d (pickBlockF p 9 0x40f9a81c31031ea057c4097880ff1019e2028b403f2804f1004d1ffdc3fe1a7f930ff099fe013fbe27f784febb9fcbc3f7f87ecb4fd799fae13f5a27eb04fd2b9f99c3f1b87e070fbc49f6cc3ec727d5b4fa561f3dd3e7827cec4f99c1f3033e4987c630f8661f0b13e1427c064f7f19ef3b3dcf87b72cf6ab9ecba3d9607b2c0f6419ec533d7ce7ad64f5649ea2a3d3e67a61cf4a99e9413d1727a02cf3e21e7393cde879b84f3251e59b3cae47950cf25c9e4833c88879010f2001e3c43c67278b1cf1151e16c3c2c0784ccf0549e0643bfd077e54ef8c1de6b3bbb277704eeba9dd523baa077504ee7a9dc4b3b86277084ee011dc003b80077000edc41db353b57076ac0ed419da353b316763e4ec4b1d8273aef675d84eba89d7323ae6075c84eb811d6883ace2759c0eb309d633 0x46ce28d72d1a86234f1468d28d14519ec2332b466228ca251938a31f8462b48c5051864230b1460528bded17b0a2ed945d828b92116cda2cfa459a48b2c9160d22b7a456e08ad4915a822b05454d48a981151222a11454208a71514d12290a451e28a3c1145a22883451008a0991401227e244e9489d0113822270044e0089c01134ba266344b948970112e0225c044b088958912b02250644a00893891270224c24485488e29116da222b442d88854510a0a20c84403687dad0f5da1ea143d22878610ebd21cda43856870450dcc21b81435d4869290cc621971432c2863a10c1da178b42e1085a5d0b04a159742b20856410a93a14a842850850810a10213c64269084b5d0968212d0424b08472508a4210b941ff883da5075da0e2941af6833a5061620b6c415768286904ae2089c)) (pickBlockF p 12 (pickBlockF p 11 0x4f24c9e2293c0ba78014f0009de5d3b84a76974ed029da013b13275994ea309d4413a80a75004e9109cfa939aca727e4e35a9c37537ff26f2d4dcd89b639365ea6c1a4d69a9aa3134eda692b4d0d899eb1337da663c4cb16993313258a64a14c7f698d2d3198a63214c4f6986f1307e260e14c1a2980ad2fbda5f614bea297aad2efda5d694bac0975812e7ba5c694b7b296c712d35a59ac4b250961ed2bed2572b4ad14957312a862545b4a75694bed292d2519c4a1d6940ed27be24ebc49c169356d26a0a4d314998e930a925c524adb495829295d2520a49aa492149213123c6246db48c9291631227ca444b4877290c2d213ca41bc481f89012d1fc623ecc47d628f91d1f18a3d8b479b68f0ad1e08a3ba7477228ebe91d2d239ab473228e49d1c88a387a46f968dc311b78a3687 0x57320ae5515c992b930571caae3095c512b80a57000adf115be02b7c056f80add995ba12b69b56d20ada415b482b65456c46ad8815adbab5b056b24ad6415ab92b4da56838acd715946ab1bd56234ac13557c62aedb55c56ab575564e2abdc55638aa97154d5aa8dd55038a9d71533f2a59e549b8a903551f8aa3d254638a89ad50f42a12c54222a83c9501e29f8b53d5ca77394e8629c2e536baa6a354cd7298dd53038a5d714b3f2966152c84a58894aaea949c5279aa4e8949c8a92dc52456a46a14876290d152164a3ff1479e28e5e51c82a3889470128d3d518daa2fa1458ea8a98513b8a25614446a880850e5ca19b142d6284ec5081ca0fc541e9283b2505daa08b140aea814150244a01b13fdda7f384fcf89f9493f20a7d8c4f9b69eff93df0a7bc24f7449eb753d0e27989) (pickBlockF p 13 0x5e822bcd717946af1cc5e272bc1b577e52ef0c5dcd4bb6b176852ec3d5d6dabaab17548aea815d410ba531743eae7ad5cf22b9e0573842e65b5cb1ab936d7260ae4b15c870b8e2d715eae20b5c3e2b878570b42e0ac5bfbab7c716f44addae5ba32b71716de4adb0c5b4f2b66b56c762d82c5b022b5e256bb8ad6bc5abdab54b16a88ad4985a902b4f6d6986ad25b5a482b48c568dc2d10b5a07ab3e2d67b8acef859dc2b38b166aeacc9c59920b32416613acbb759634b2a9d650caca1059420b269d649bac8a959140b228164142c7a858e14b19e56330ac5f758bc2b1565624e2c48158810b0fc561ad2c2ab58522b07e960f0ac16858176b028560142c01157ef4afaf15efe2bdd257b64af42d5e262bc4057844af0815df22bb3b57660aebd15d70abae05750cae94d5cd5ab991 0x64b22c960592b13255164a46c92dd920d323b66468ec8cc59181b23006452ec87ad90963206c64048c80818fe331f2a63e40c7c458f4c31dfa63a78c71f18de5b1b0c635e2c6b858d3431a5163446c65ed8c65b180c62fe2c5de18bb0b175162e46c59ed8ae5b15c062b26c54d98a893151062a02c52998a143138a6262ec4a9d890cb118962300c454d8891b11206218cc40e58801b0fe261eb2c3c8d877230ea461d40c399186ecb0d4961a08c32d5865830c83617f2c2fc185f830bf0616d2c2d4585a830b3261660c2aa5855030a9161520c2a058529b0a3261352c268184c8b093661152c20dd83cd3070960c98c16e5827e3041e606b8c0a7180ee3010d6005cbfdb17f4eafddc5fa1abf0f57e10afb995f702beb317cfeaf93c5f0f8bdeb57b7daf63c5eadabd2ed7a50af428)))) (pickBlockF p 21 (pickBlockF p 17 (pickBlockF p 15 0x6c0e4d7ef1af76b5e3b6bc24d7805ae9735cb76b7dad6cb1ad9035b116b530d689dacc5359266b132d6241ac40b58806b04cd5ea1ab8cb57016ae00d59e5ab03b556a6a9b2d519da9ceb53276a4d8d47dda89e350c769ffad3cb5a73634d9d6999ad30a9a5aeb4a9c693d6d24b1a445347bd68df8d18f1a2c5b456268ac0d1509a26bb44d0689a0d11d9a1de342fc68496d0631a0933406c67f76cfbf19f1e33d8b679f2cf0f19dd4b3aec6741cce5319c73338e06712ace1c99c3833870670a4cdead9b763363b66af8cd4959a88b34a7668e6cd1859a28b33ab665f6cc8f19910b31b766306cc5c59865b301b65fc6cbf4597a4b2f1365d30cb7ad96d232d28659c8cb345961d32b8b65598ca95d94f3b293b65242ca4459479328a565050c9e29939ab272164daac9a8d932ab25ab (pickBlockF p 16 0x75554ea829d4b53a8bb75016e9d31d34dba60974a98e9231d1e63a30c74498e8631d06639fee73e3ae79e9cee5b9d0c738b6e6e71cd6e39a2b732d8e62edcbfe3973c72e42e5c45cb35b95bb72b42e5645ca75b943b726f8e4af1c950b9291723d6e44edc890b9111720d6e3eedc794b8e9971d20e3a41c71b38da971a14e3131c5c638acc713fae24b5c4363879d70dd6e1875c2a6b853170a24e10f9c1af3829c7039ae03f5c025b7f7d6fd5adf7edbee937dc16f9dcdf1ddbdd6b7aec6f41cde4f5bc36b778e6ed5cdd7b1bae1375b16e9bcdcff9b996b73026e5c4dcb45b90e3714d6e136dc1c9b829370416df18dbaf5b705b6de26dba2db3f9b643b6bbd6d5f8da879b4a6b687d6cf3cd9b35b306365f16cba4d93f9b20f3635c6c664d8c49b180b624c6c2fad832db05136091 0x78cd0f1981e3213c5d778b46f15cde29a3c49a78920f1241e2483c48178810f1001e1f13c3e0787c0f0da1e1b03c360785eef0bc1e170bc2e0785a2f0ac9e11c3c23078460f08c1e0e3bc1757820ef0299e0143bfc677e72efc85df4cbbe9077ca8ef79ddee8bbdd077b64ef6c1dec1bbcf9779e0ef385de703bc77778e0eefe1ddf83bbe1776d0eebdddd2d3b9d8772b0ee361dc33bb86077084edf5ddbe0bb74876e80edd01db89bb71076dc6eda91db0cbb61076b4eed681dac13b58076b00ed601da8bbb5107694eed245da393b470768e0ed1c1da30bb460767eeece95d9aabb30576510ec7e5d8f0bb168762c0ec581d8a8bb0d876164ec11dd8203b04076080ec011d8003aff175eb4ebd05d798baf2175e04eba21d7403ae7175ce0eb985d6ecbad6775994eb289d5fdbab4b)) (pickBlockF p 19 (pickBlockF p 18 0x7dde0fbad1f70d3edc57db62fb6c1f6ab3ecba7d8e8fb10df6203ec227d840faf19f5e03ebc07d6aefaaadf4fdbe9697d1b2fa0e9f3c5be6cc7cc36f97c9f2f83e5e17cb48f93edf2693e4b27c816f9001f1f13e3e07c7a2f8f41f1d1be3737c60ef896df10a3e1b67c360f85d1f065be0937c04ef8009efdabdf0b7bc7af75f1ee8b3dcc57b890f6ee5ed94bda7b7b3b4f668dec853d8977b06cf5ea5eb8cbd65c7ac46f55edea74bd4777a7b4f4d25e9643d2397a352f44a1e8903d0e47a1a2f4125e7e43cfc079f62f3ec1e7d0bcfa079f04f3e01e7a9bcec979d80f395de7283ce4179b90f3599e66cbcc4979862f2ea5e5d03cba0796c8f2d81e57bbcae1794d0f2981e5303ca60794a2f28c9e4dc3c9a179340f2681e4c8bc92779222f2405e478bc8d2790cef2019e3bcbc6e9 0x82927052420a1b4143082825050420a08413d48272904bae091dc118b821b7040ae07c540edb81cb1036ae06c140d8081ac50341a062640c228184102f9205e8c0bc18170902b32056040a93814c702982053040a60814c10289204f9c093c811e90234a0460c087580f9701e4e03a2c074080d9101832029ec047c8079700c6e0179402f0805a500aca010d401f2802b50054200994013080261003d20061c00577ffecffd2dffa03ff047fde2ffa95ff053fdd37fb28ff5c9fe8b3fd107fa20ff38dfe1dbfbf47f786fee11fd6dbfac17f508fea01fd313fa607f42afe805fcf8bf9f07f368fe469fc35bf7ca7ee36fda9dfb1bbf57c7eaa4fd541fa82bf4a67e7d8fce91f97dbf2f07e568fca85f9503f2557e446fc575f88a3f0c57e108fbf6df7ca3ef817dec4fbc55f780beef1) (pickBlockF p 20 0x878090f0021e0043bd3876570ec821d7243ad1875650e9d21d0b4397a872690e44a1c79438e1871490e02a1be9c37d086f290de421bb94377086ee10dd0e1b824366a86b770d42e1a1ec337c865790ca4a194843263864670c66a189b4308b861010c18a183043060860670c04a17f942f4b85e090bb12176042e8485bd50b65616c0c2d7185a4b0b22a15e642b1b854b90a6721493c287b850a50a1421402c27e284e59099ee13384265284ca109942130a425f284ba509472126a424a3849230911611d5423648462b08c42115b4220b842990826e0fe6c1f0c83dc507b820f68c1e7683b790755a0e6c41c588373906e420db941b61836c106c920d8141ae28343b0678e0cbbc1970832e10650e0c4641880830890604e0bf9417a582e8d05a6e0b2a4163282c25057ca0ac3c14cc 0x8eb311d3ea3a25c739b8e5d71cb0a3960472758e4a51c63638b1470bb8e1611c24a3848470908e0a91c08e37d446edd8dced1b896371046de48da771b40e366246cb18d8cb1ae76356e46a1c8d34f1a42a342dc67c98ce3719a2632e64652a8c8f718f2e31954626c8c39518432303545f9d8bdf51787a2eae45cc98b83716f522dbb45abc8b417168022cf1459e08b32b163722c68458948b10315f6e2be8457768aec315d0a2b7ac564b8ab911568a2ad0455558a9391518e2a30454248a84114fce29f8453a58a6151496e28dd4511a8a0d713eb2277644e3b89af91327a25df44afc8945b12756248e4484d88f3711b7222f7c45868893f1111621bec42ad883bb10436202dc40328806110086200143f4c87daf0f99e1ed643da087b050f6021ec043d6287a850f48a1e3dc3c43))) (pickBlockF p 24 (pickBlockF p 22 0x933f72652e4c9149920931e72634a4c0e497f292e9725d024b914972092e4125bce4b61c965792b39255524a8a49510929a9250ae4a08c93c59276324d964956491ec9223b2417247d5c8f8291f0123dc647a948eba91d25237ea46f848dd291ba12374246d948d8391a112325e45f5c8be09174922e4645a2c8aaa914e7228d24509489d4913a12274244d1c890a911892224e44484885490f7521e4a43aa4875090e6521cc24381c86e290da321b42434a485fa90ab5212ea41fe4833c9062520c424180c82a6903d92070a40954812090205203c64078480a59008d2004e3fc4c7ef98fc3d1f8423eea47da38faab1f2ae3e39c7c078f7c51ee563dc847b908f6c71eb2a3d4247a538f4a11e7da3cad479328f18f1e3023c51478a08f0c91e10a3c11478208efc91dcee3b4d47618 (pickBlockF p 23 0x986a130d426182cc2c498437305ea6065cc00c97e992fa6e5f394be7097ca52f79e5ebbcbcbc978352f0425df1cbbb3977612ed965da14bb22976412ec825d724bae0975c12eb465d60cba849735d2e5925ca14b931971cb2e0ee5bdc4b78396f012dcd65b4d4b5eb96a772d22e59e64b31b965e52cbc25970cb295963d72c61a58754b0e0961852c2c658584b083960c52c10a58204b02295ed92bc9257634aec095d092b7aa56cacad6395a852b35e561d4ab8b955992a7f654a5ca904951e32a2d25441ca7cc94ecd29c1a532dca65094c65298c253184a5f494b4b2959252564a47394869290c252184a3c79463728c42515b4a2a1945052889a50e34a12a941c9283465060ca0b1940e927f6a4fc2c9f4493e8127c8a4f9049f2093dab27a524ef5c9d4a939552702a4da649aaa 0x9ee053dc027b804f6d39ed293d8627aae4f5149e98b3d3027a334f3ac9e6e73cc5a7980cf2b59e3f93c4b678364efac9ddf73b8b676b64ecbb9d7db3ac767526ce95f9d11b39faa739dce6f49cd4b397b272a54e5409ca4539482726ace41c9c82138eda71d0ce2ec9c5c138a927148ce2729c44b3862a70a9ce1509c229381ea70294e0509c00b380026fe9cdfd09bf0b37c9a6f364ddca9ba73372a66dfdcdb5a9b51b3676e6c86cd83d9aebd35a726b22cd57d9aa4b351b269d64d2fb9a45b3453a683ecd02599ebb33a7266df4cced998773304a66084cbf29978732c6e655b4ca56993573268264c14c980993013251264914c902990b73208e63f24c7e098fc131ece6385cc70098d8931ac663494c63698bad314ea627a4c4e1989a33130662424c3ea9876730dd261b84c352)) (pickBlockF p 26 (pickBlockF p 25 0xa579d4abf6950f5296ba515949f3a937ed262da4ad9492ee91f6d232ca4605488f6910952201a44014878a90d2520fba410f47f6e8fe851fb2a3f4347e828fb9d1f34a3e25479728f0a51de3a3bc14761a8e7551c77a38c3471468e0a51b7aa35794682e8ca65188ca2fb745eca8bd0d1773a2ea545a368b045154ca2a814548a8a9051520a29c9452ce8a49513dca272944d1689a0512e6a2495447d688e1d11b1a22ad442ae87f650f3ba1cdb436b2867dd0c4ba173742bea8525d09b9a12174238a8468d08a3a10e741eb683c150762a0d7741ac2834950681a0d0141a02833150624a0abb414528280d04f1a090f40f3281c9d0354a06a140bda8116d015da01393ffae7f964fe8a9fb993f4327e3ccfbe99f6953ea6e7cf5cf93b9f2253e4067c69cf8b29eff93df4a7b95cf720 0xad4175a56eb455d6882ad06b59e2eb375566e0acd4959a0ab3225657daca4b59392b21dd6421ac75158c2ab12dd61abac1f75830eb04255fdbabe7557cc2af8955f10abd6d577f2aed2d5d73ab9975728aae1455b8aab5b7568aeace35591bab11356022abbcd5707aacf3556f2aa8d5547aaa7b554d62a95d55283aa3f35461ea87cd50b4aa05353db2a7a154f04a9c99535f6a6b854d52a9aa1534caa645d4c35a984352db2a599d4ac7a93fb524f2a42f5477ea8e6951b96a3165455da8aa1514caa298544e5a885950d76a13f541bca832550516a04653fcca7f814fe8a9fd053f55a7d1b4f6f69e6f53c1ca77c74eece9d76d3a1da74214e7ca9cf8539a5a71d94e2569c39537ada6ee74dbe29b0f5355ca69394cefa9985d323da62f94c36a981d52f8ba5db74b87296b5d2cac) (pickBlockF p 27 0xb510769faad3965a66cb4b3b693aed21dda37cb4597688e6d0b6da0acb3fd967ceecf3e59e25b3bab674aece3dd9bbcb372566d8ecd56599ddb33a166652ccc859981b32a7662aecc2ad9832b2edb65d46cb7b5963cb2b17652bac9f6593c2b26eb64ab6c8eed91d0b2365646c2c8b2d90acb1fd963c3ac71ed8df4b1b4b633eec625d8c40b184563082c5ead8b0db1499625bac45658882b104d61db2c34758680b0c896188ac2ead852bb09ab6128ec1eed83c1b06af60a72c0f5d813bb00bd5fe72bf6e57e1cafab95f452be62d7c2aaf6f75edc2bda957b50af6835ebd6bd25d79e6af3a35e4eabc89578c5af0375dd72bb4e575ebaeb855d612ba7557459ae8a15d0caba1857412ae6b95cc16b978d724bae4455c71ab8955706cadf595bbb2b71dd6d8bad9995b06eb5b5d6abb 0x5a8b4)))))))
  (pagedUnpackF 7 7 (fun p => (pickBlockF p 91 (pickBlockF p 45 (pickBlockF p 22 (pickBlockF p 11 (pickBlockF p 5 (pickBlockF p 2 (pickBlockF p 1 0x8a890e2c5050c101810008487162828606040090e2c5050c1018100088890e2c5050c1018100088890e2c5050c101810008895121c58a0c101810008895121c58a0c101810008a890e2c506060400222544871628286080c08004544871628286080c080045448b14143040604002 0xe2c506080c0800478a890e2c506080c080042458a0c0c0091628304060010916283030008487162830302001070c040070c1c286080c1150e180090e2c5050c101800478a890e2c5050c101810008486080c080121c58a0c10181000848608040022a2438b141820302001091418181) (pickBlockF p 3 0xe2c5050c1018004544871628286080c080042458a0c10180041c301001c3070a1820302001150e18180042438b14182030008f090e2c506080c080042458a0c001091628304060011e0e180804c1c30100984871628286080c0800478a890e2828606040024c0131e12282030200109 (pickBlockF p 4 0x782840200f0508782843c14304060401e121c58a0a182030200115121c58a0a1820302001150a100050814205080c080042458a0a18203000848b141430406040020a10284122c5050808f1512282840604002122c5050c10180042458a0a182030200105081420914142050804009 0x80c080043c48716282860604002121c58a0a182030200113121c58a0a1818100088890e2c5050c1018100088090e2c506080c0800454487162830406040021e2438b14182030200115121c58a0c10181000848714181810008a890e2c5050c101810008487162828606040091628301))) (pickBlockF p 8 (pickBlockF p 6 0x2a2438b141430406040022698f15162830406040022698f09161430302001150e2c3030200f150e2c506080c080041c31e0c98f15121c5850c0c0800498f150e2c506080c08004009871618181001c31e0a181802678a890e2c286060400226544871628286080c0800478a891628286 (pickBlockF p 7 0xc1018100091a5121c58a0a182030200115121c58a0a18203020010714181810008a89162830302001120e2c506020010714181810008a890e2c50606040022a2458a0c0c08004184871614303001838b141820302001091628286080c080041c4871614303001c38b14182030200113 0x121c58a0a182030200107162830406040021e2458a0c10181000838b1418203020010f2a2438b141430406040021e54487162830406040023c5448b141820302001001628286080c0800400a890e2c5050c1018100088890e2c5050c101810008a891628286080c08004009090e2c505)) (pickBlockF p 9 0x14182030200110122c506080c080041c58a0c101810008815121c58a0c101810008815121c58a0c101810008f15122c506080c080040000b14182010008a890e2c506080c0800444487162830406040022a2458a0c101810008018121c58a0c1018100091a52a2438b14182030200115 (pickBlockF p 10 0x60402f2a2438b1414304060400212143040601795121c5850c101810008995121c58a0a182030200115121c58a0a182030200117121c58a0c1018100088890e2c506080c080045448b14182030200124382438b141820302001234a2438b14182030200115121c58a0c10181000838b 0x42438b0a10180081c58a0a18203020012f121c58a0a1820302001090e2c286080c0050e2c5050c1018100097890e2c5050c1018100089871628286080c08004bc9890e2c286080c0800454585080c0805e544871628286080c080047c1890a101af2a2438b0a182030200115161421f)))) (pickBlockF p 16 (pickBlockF p 13 (pickBlockF p 12 0x80c080043cf091628286080c080043ca891628286080c080045448b14143040604002001c58a080c08004004871628286080c08004404871628286080c080042438b14143040604002001c58a0a1818100080090e2c5050c101810008f890e2c5050c1018100084871628286080c080 0x200111122c5050c101810008895122c5050c101810008a891628286080c080049848b14143040604002202458a0a1820302001091628286080c080049848b141430406040023e2458a0a18203020011e2a2458a0a18203020010b141430406040021e2458a0a1820302001261628286) (pickBlockF p 14 0x43c4871628286080c080043ca890e2c5050c101810008a890e2c5050c1018100093091628286080c080044048b14143040604002122c5050c1018100093091628286080c080047c48b14143040604002122c5050c10181000858a0a182030200111122c5050c10181000858a0a18203 (pickBlockF p 15 0x122c5050c101810008007162820100080090e2c5050c1018100088090e2c5050c1018100084871628286080c080040038b141430100080090e2c5050c101810008f890e2c5050c1018100084871628286080c080041c58a0a18203020010f121c58a0a1820302001071628286080c080 0x8040022a2438b14182030200115121c58a0c100800478a8916282010008f1514143040604002222438b141430406040022a2458a0a1820302001234a2438b141430406040022a2438b141430406040021e2438b141430406040023c2458a0a182030200113121c58a0a18203020011e))) (pickBlockF p 19 (pickBlockF p 17 0x9415122c506080c0800488a891628286080c0800484f150e2c50406040023c5448b1418203020011e2a2458a0c101810008a891628181000901e2a1c58a0a101810008f15122c5050c101810008a8a0200115121c58a0c101810008a890e2c506080c0800454487140c0800448a8a (pickBlockF p 18 0x140c095121c58a0c101810008a8716283030208a87162830302001124c2c080242c080242c506080c0800449aa60e2c505080c08004980a61628286080c0800448a871628286080c08004544871628286080c080045438b14143040604002425448b14182030200115122c5050c10181 0x141430406040022a2438b141430406040022a2438b14182030200115160401516545850c04115161420302001150e2c506080c0800454487162830406040022a1c5010454487162830406040022a2c2840608a8b0c04a8b2a2c0802a1c58a0c101810008a890e2c506080c080045438b)) (pickBlockF p 20 0xc10085080c08004142150e2c5050c101810008a890e2c5050c101810008585080400b0a10a8b0a10080042c2840e2c5050c1018100084871628286080c080041420100d45050814205081c58a0a1820302001090e2c5050c1018100082840a1058a0a1820302001350e28284065438b (pickBlockF p 21 0x402458a0a1820302001203c5438b141430406040023c5448b14143040604002442458a0a1820302001222a2458a0a1820302001223c2438b141820302001223c5448716283040604002121c58a0c0c0800488f090e2c5050c101810008f090e2c5050c101810008a8716283010014205 0x2a2458a0a182030200101242438b141430406040024ed8f090e2c5050c101810008f091628286080c080045438a0c0c080045448b14181810008c0b1418181001c58a0c0c080042458a0c0c0800478a8a0c0c0800454487161820302001202a2458a0a1820302001090e2c3040604002))))) (pickBlockF p 33 (pickBlockF p 27 (pickBlockF p 24 (pickBlockF p 23 0x478a8b141820302001151654584020931e2a24586080c0800478a8716180a63c54487161820302001010008f150e2c301000931e2a1c58a0c101810008f150e2c506080c0800478a89162830406040020204a890a182030200115121c58a0a1820302001222a2438b14143040604002 0x6040022a2458a0c101810008098121c58a0c1018100093b6121c58a0c10181000848b14182030200106121c586080c080041838b14182010008a89162830406040020c1c58a0c10080041848716182030200109162830406040024c78a8b14182030200115165459e2a24586080c080) (pickBlockF p 25 0x200117121c58a0c1018100093b6121c58a0c10181000848b141430406040022a2438b0c101810009095122c506080c080042438b0c1018100090891628286080c0800484f150e2c506080c0800478a89162830406040020254486080400202544871628304060400244544871628304 (pickBlockF p 26 0x2a2458a0a18203020010916143040604002502458a0a18203020010916143040604002502458a0a1820302001262a2458a0a1820302001282a2458a0a1820302001282a2c5050c101810008a891628286080c080045ca890e2c506080c0800488a890e2c506080c080045448b1418203 0x122c5050c101810009015122c5050c101810008a891628286080c080040448b0c10080040448b141430406040021628304060400204c048b14143040604002122c5050c101810009315122c5050c101810009015122c5050c101810008f15122c5050c10181000848b0a182030200128))) (pickBlockF p 30 (pickBlockF p 28 0x16143040604002422458a0a18203020010916143040604002422458a0a182030200115122c5050c101810009095122c5050c1018100090951628286080c080045448b141430406040024c5448b14143040604002445448b141430406040022a2458a0a182030200101122c2860200101 (pickBlockF p 29 0x402458a0a1820302001091628286080c080040448b0c1018100080891628286080c080040c58a0c1018100098091628286080c080042458a0a1820302001262a2458a0a1820302001202a2458a0a182030200115122c5050c10181000848b0a1820302001212a2458a0a182030200109 0x3c14304660400216282840009b9e122c5050c101810008f071628286080c080047848b141430406040024278a871628286080c0800478a891628286080c0800498a891628286080c0800488a891628286080c080045448b14143040604002020448b0a18181000848b14143040604002)) (pickBlockF p 31 0x122c5050c10181000911e2a1c58a0a18203020011e2a2458a0a1820302001213c1c58a0a18203020011e122c5050c101810008f090e2c286080c08004dcf071628286080c08004cc1373c2c5050c101810008f050c10080042828404dcf091628286080c08004dcf0b14143040604002 (pickBlockF p 32 0x1628286080c08004444871628286080c0800444f15121c58a0c10181000889e2a2438b1418203020011e2a1c58a0c0c0800444f15121c58a0a18203020011e2a1c58a0a1820302001151628286080c0800488a871628286080c080045448b141430406040024ed838b14143040604002 0xc013070c040354c1c58a0c0851e2a1c5050c0c0800498f0a080c002121c58a0c101810008f090e2c506080c080040403516281242a28181000c00b140c002121c58a0c0c080045438602003860e18386121c58a0a182030008f090e2c5050c1018100084871628286080c0800444487)))) (pickBlockF p 39 (pickBlockF p 36 (pickBlockF p 34 0x141430406001091628286080c080041420508d458a0a101822a282840604002122c5050c10180045448b141430406040020a102846a28284060828402004871628286080c0022a2438b141430406040020e180800e183860e18182121c58a0c101800478a890e2c5050c101810008f07 (pickBlockF p 35 0x122c506080c08004e448b14143040604002727848b1418203020011e122c506080c080047848b140c08004e4f091628286080c080047848b14100800478a85080401e0a10f05080c11e0a100803c2438b14143040604002121c58a0a1820302001050814205080c1150a10181000848b 0x6040020e2c5060604002122c5060604002241c58a0c040020e181810008a890e2c50606040022a2c50606040020e2c5050c0c039122c5050c10181000838b1414303004dc95121c58a0a182030200113725438b141430406040023c5448b14143040604002722458a0a182030200128)) (pickBlockF p 37 0x1628286080c08004e478916283040604002723ca890e2c5050c1018100087950e2c506080c0800478a89162830406040020001c890e2c5050c101810009c91121c58a0a1820302001091628286080c0800400939121c58a0a182030200125722438b141430406040022a2438b1414304 (pickBlockF p 38 0x162830406040022a2438b14182030200139202458a0c101810009c902a2438b14182030200139205438b1418203020011e2a2458a0c101810008000722438b14182030200139222438b14182030200109162830406040020061c890e2c506080c0800495c890e2c506080c0800454487 0x47dc890e2c5050c1018100084871628286080c08004f1c890e2c5050c101810009e39121c58a0a1820302001137278a871628286080c0800478a890e2c5050c101810008bb9121c58a0c101810009c91121c58a0c10181000848b1418203020012438e4487162830406040024ae4487))) (pickBlockF p 42 (pickBlockF p 40 0x80c080047dc95122c5050c101810008f15122c5050c101810009c8f122c5050c101810009c8f122c5050c101810009c8f2a2c5050c101810008a891628286080c0800400039121c58a0a182030200139202438b14143040604002121c58a0a18203020010000e44871628286080c080 (pickBlockF p 41 0xc101810009ca6122c5050c101810008fb9122c5050c10181000848b14143040604002724448b14143040604002724448b141430406040027244a8b141430406040022a2458a0a1820302001394c2458a0a182030200139202458a0a1820302001091628286080c08004e53091628286 0x121c58a0a18203020010000e44871628286080c080047dc890e2c5050c1018100084871628286080c08004e47890e2c5050c101810009c8f121c58a0a18203020010f2a1c58a0a18203020011e2a2438b14143040604002729848b14143040604002724048b14143040604002122c505)) (pickBlockF p 43 0x200f151228286080c080044438b14143040604002122c5050c1018100092871628286080c08004544871628286080c080043c38b141430406040023c2458a0a1820302001130e2c5050c101810008f091628286080c0800400039121c58a0a182030200139202438b14143040604002 (pickBlockF p 44 0x60400224544871628286080c08004544871628286080c08004544871628286080c08004f84871628286080c080044c487162828606040027c2438b141430406040027c54487162830406040027c5448716283040604002121c58a0c0c08004544871628286080c080042438b1414303 0x2a2ca8b0a08a8b2a2438b14182030200115121c58a0c101810008a8b2a2ca8b2a2c3010054487162830406040022a2438b141430406040022a2438b14181810008926160401216049091618203020010924984871628181005c48602001090e281890e28303020010100093091614304)))))) (pickBlockF p 68 (pickBlockF p 56 (pickBlockF p 50 (pickBlockF p 47 (pickBlockF p 46 0x604002161420b0a18201002c2840200585080c1090e2c5050c1018100084871628286080c08004142010024505080c10508142090e2c5050c1018100084871628286080c08004142050824286080c080042438a0a101822a2438b141430406040022a2438b141430406040022a2c080 0x478a891628286080c080048848b14143040604002442458a0a1820302001223c2438b141820302001223c2438b141820302001090e2c506060400244784871628286080c08004784871628286080c0800414205081430406040020a101822a2438b141430406040022a2438b1414304) (pickBlockF p 48 0x80c0800405f12121c58a0a18203020013646f84871628286080c080047848b141430406040020e283030200115122c5060604002302c50606040070c0c080042458a0c0c0800478a8914181810009f202a2458a0a18203020013e402458a0a1820302001203c544871628286080c080 (pickBlockF p 49 0x121c58a0c101810009b237c2438b1418203020010916283040604002121c58608040027c5448b141820302001090e2c304020013e122c506080c08004f8f15121c58a0c101810008f15122c506080c08004040be2a2438b141430406040027c88a890e2c5050c101810008a891628286 0x6040022ef8487162830406040026c8df090e2c506080c080042458a0a18203020013e425448b1418203020013e422458a0a18203020013e4278a890e2c506080c0800478a89162830406040020205f15121c58a0c101810009f222a2438b14182030200115122c506080c0800404c3e))) (pickBlockF p 53 (pickBlockF p 51 0x122c5050c101810008f15122c5050c10181000943e2a2458a0a1820302001287c2458a0a1820302001287c2458a0a1820302001287c78a891628286080c08004a0a891628286080c080045448b141430406040022ef8a890e2c506080c08004f9115121c58a0c101810008a891628304 (pickBlockF p 52 0x6040027c98a891628286080c08004f9115122c5050c101810008a891628286080c08004040be122c5050c101810009f20122c5050c101810008a891628286080c08004040be122c5050c101810009dbe122c5050c10181000848b141430406040027c98a891628286080c08004f9015 0x76f848b14143040604002122c5050c101810009f262a2458a0a18203020013e405448b141430406040022a2458a0a18203020013e425448b141430406040027c8448b141430406040027c8448b141430406040027c84a891628286080c0800484a891628286080c080045448b1414304)) (pickBlockF p 54 0x80c080047848b141430406040027c84f15121c58a0a18203020011e2a2458a0a18203020013e4c5448b141430406040027c88a891628286080c080045448b141430406040020205f091628286080c08004f90091628286080c080042458a0a18203020010102f848b14143040604002 (pickBlockF p 55 0xe2c5050c101810009a950e2c5050c101810009115121c58a0a182030200115122c5050c101810009b23121c58a0a1820302001091628286080c08004f911e2a2438b141430406040023c5448b1414304060400242784871628286080c080047848b1414304060400276784871628286 0xa182030200142401c50606001090e2c5050c1018100084871628286080c080040038b080c0020e2c506080c0020e2c2030008a81000df867e54386060400706001071618180041c5850c1018100082840a1048a0a101822a14201002438b14143040600115121c58a0a182030200109)))) (pickBlockF p 62 (pickBlockF p 59 (pickBlockF p 57 0x60048716283040604002121c58a0a1820302001350e2c5050c1018100084871628304020010716100020e2c5050c1018100082840a1048a0a101822a2828406040090e2c5050c1018004544871628286080c080041c58a0c1018004802840108a850804042162828406001066a80a87 (pickBlockF p 58 0x400280041c5050c041070c1c2800e14300041c58a0a1818100084871628286080c08004001070c041070c1c386001c58606040020e2c286080c080041c3070c1c33f0e2c3030200107161818100080830210181080c2012a2ca8b02545840604a8b2a2c180162ca8b2a2ca8b2a24584 0x1628286080c080041000400101802a1c585080c0020814284002c203262c284060400000142002a2c2840008a8b14142030008a890e2c505080c080044ca890e2c5050c101810008a890e2c5050c101810009c890e2c5050c0c080043c48716283040604002121c58a0a182030200105)) (pickBlockF p 60 0x8584060010916282030200113121c58a0a101810008a8b0a18203020010b2a2c28400101840a10181005448b141430406040020a002802a1c585080c0023e14201004c48b0a1018100142002a2c2840054487162828406040022a2c286080c0800454585080401f12142030200a89 (pickBlockF p 61 0xa0c080121c58a0a101800414181000048b14143040604002121c58a0a18203020010100100800e2c286080c080040c080160c0020a0c08016140020e2c286080c080041c586060400226545850c101810008995122c5050c101810008583004c38b0a101810008583000848b1414181 0x8004871628286080c080047c4871628286080c080042438b14143040604002161420302001150e2c286080c080042c2820a1000b0a182010008f8b0a182030200107161430406040022a1c5850c101810008201002438b0a1018008040001628286080c080042438b14143040604002))) (pickBlockF p 65 (pickBlockF p 63 0x161430406040021e2438b14143040604002122c286080c08004d47890e2c5050c1018100087950e2c5050c101810009a95121c58a0a1820302001000024586080c08004142002a2438b14143040604002202438b141430406040022a2438b14143040604002000048b14143030200105 (pickBlockF p 64 0x20010f2a2438b141430406040022a2438b141430406040021400100000058a0c1008004d44871628286080c08004404871628286080c08004d4a890e2c5050c101810008500040000016282860200135121c58a0a18203020011f121c58a0a182030200135121c58a0a182030200109 0x6040022a2438b1414304060400280544871628286080c08004404871628286080c08004544871628286080c08005004871628286080c080047c4871628286080c080042438b141430406040021628286080c080043c4871628286080c080042458a0a18203020010f121c58a0a18203)) (pickBlockF p 66 0x42c5050c1018100090891628286080c080042c5050c1018100090891628286080c080042c5050c101810009095122c5050c101810009095122c5050c101810008a891628286080c08004d4a8a0a18203020013e121c58a0a182030200115121c58a0a1820302001432a2438b1414304 (pickBlockF p 67 0x14143040604002161430406040020a182030200115161430406040021614203020010b0a1820302005850c1018100085850c1018100085860804002161430406040020a18203020011516143040200115161430406040022a1430406040021628286080c0800484a891628286080c080 0x122c5050c101810008a091628286080c0800404089161430302001091628286080c080042458a0a182030200114122c5050c10181000808916182030200101122c5050c10181000848b14143040604002405448b141430406040020204a890a181810008a891628286080c080045448b))))) (pickBlockF p 79 (pickBlockF p 73 (pickBlockF p 70 (pickBlockF p 69 0xa10a89161430406040022a2c2842a2c505080411f0200a8b141430406040022a2c2843e04a8b0a100800a102842a245850c101810008a8b141430406040022a2458a0a182030200122122c5050c101810009115122c5050c1018100080812a2430406040022a2458a0a182030200115 0x1628286080c080041448b0a182030200105162828608040022a2458a0a1820302001151628286080c0800454595165448b0a1820302001151628286080c080045459516280822a245850c101810008a8b0a10f9516142010200a8b141430406040023e5458508280822a2c2840200284) (pickBlockF p 71 0x604002405448b1414304060400202545050c04002025448b141430406040026a5448b1414304060400208245850c10181000820b14143040200115122c5050c101810008289161430406040020a2c5050c10080042458a0a1820302001041628286080400208245850c101810009a89 (pickBlockF p 72 0x14143040604002445448b1414304060400202545060804002025448b141430406040022a2458a0a182030200114122c5050c10181000808b141430100080891628286080c080042458a0a182030200114122c5050c10181000808b141820100080891628286080c08004d448b1414304 0x141430406040022a2458a0a18203020010b14143040604002725448b141430406040021628286080c08004e448b141430406040021628286080c08004e448b141430406040021628286080c08004e4a891628286080c08004e4a891628286080c080045448b14143040604002445448b))) (pickBlockF p 76 (pickBlockF p 74 0x1628286080c0800500a891628286080c080045448b14143040604002282458a0a18203020010102245850c04002122c5050c10181000848b14143040604002282458a0a182030200101122c3040200101122c5050c10181000848b14143040604002405448b14143040604002805448b (pickBlockF p 75 0x2001352a2c5050c10181000848b14143040604002445448b141430406040026a5448b14143040604002282458a0a182030200115122c5050c101810008a091628286080c080042458a0a1820302001222a2458a0a182030200115122c5050c1018100091091628286080c0800488a89 0x1628286080c080040001e122c5050c101810008f091628286080c08004785850c1018100085850c1008004785850c101810008a8b0a18203020011e2a2458a0a182030200126122c5050c101810009315122c5050c1018100085850c1018100093091628286080c080042458a0a18203)) (pickBlockF p 77 0xc101810008f091628286080c0800500f091628286080c080047848b141430406040023c5448b141430406040020000f091628286080c080047848b141430406040020000f091628286080c08004d4f091628286080c0800478a891628286080c080040001e122c5050c101810008f09 (pickBlockF p 78 0x444a890e2c5050c101810008a890e2c5050c1018100091112a2438b1414304060400244544871628286080c080045438b0a1820302001112a2438b141430406040026a5438b141430406040026a5438a0a18203020011e122c5050c101810008f15122c5050c10181000a01e122c505 0x1614304060400716143040604002161420302001011618201000838b0a1820302001110a1820302001012a2c28608040022a1c5850c101810008a870a18203020012122544871628286080c08004848890e2c5050c101810009091121c58a0a18203020012122544871628286080c080)))) (pickBlockF p 85 (pickBlockF p 82 (pickBlockF p 80 0x80c080041c58a080c08004444871628286080c080042c081222438b14143040604002121c58a0a18203020012022544871628286080c08004048812204895121c58a0a182030200115121c58a0a182030200107161430406040020a101810008a871614304060400216142030200101 (pickBlockF p 81 0x6a44a890e2c5050c1018100088950e2c5050c101810008a890e2c5050c1018100091090e2c5050c1018100091112a2438b1414304060400202440910244a890e2c5050c101810008a890e2c5050c101810009011121c58a0a18203020010116048890e2c5050c1018100084871628286 0x4d44871628286080c0800480895121c58a0a182030200101220488122544871628286080c08004d4a890e2c5050c10181000838b14142010008895121c58a0a18203020010716282840200111121c58a0a18203020010716282840200135222438b141430406040020e2c5050804002)) (pickBlockF p 83 0x121c58a0a18203020012222544871628286080c08004048812204895121c58a0a182030200115121c58a0a182030200120222438b141430406040021604091121c58a0a1820302001090e2c5050c101810008487161018100088890e2c5050c10181000808b02444871628286080c080 (pickBlockF p 84 0x141430406040024044a890e2c5050c10181000a0112a2438b141430406040022a2438b141430406040027244a890e2c5050c101810009c91121c58a0a182030200139222438b141430406040027244a890e2c5050c101810008895121c58a0a182030200115121c58a0a182030200122 0x121c58a0a18203020012222544871628286080c0800500895121c58a0a182030200115121c58a0a182030200120222438b14143040604002022c091121c58a0a1820302001090e2c5050c10181000838b141018100088890e2c5050c10181000808b02444871628286080c080042438b))) (pickBlockF p 88 (pickBlockF p 86 0x141430406040026a5458a0a1820302001090e2c5050c101810008895121c58a0a182030200115121c58a0a182030200111121c58a0a182030200115121c58a0a182030200111121c58a0a1820302001090e2c5050c101810008895121c58a0a182030200115121c58a0a182030200122 (pickBlockF p 87 0xe143043c1430402019803c5458a0a18203020011e0a1823302004870a1820300142050878a890a182030200115121c58a0a18203020011e2a2458a0a1820302001112a2438b1414304060400222544871628286080c080045438b0a1820302001112a2438b141430406040022a2438b 0x1628286080c08004544871628286080c0800478a871628286080c080041c31e0c78a890e143040604002287838b141430406040020e18f060600f15121c286080c080041c28608ccf050c10080120c01e2a2c5050c10181000999e0a18201001c28608002840a10f1512143040604002)) (pickBlockF p 89 0xc101810008a87161430406040022a2c286080c08004109890a18203001058a0a182030200115121c58a0a18203020010526544850c101800a5458a0a182030200115122c5050c1018100082151628286080c080041091512143040600a891628286080c080041499512143040600295 (pickBlockF p 90 0x14143040604002002438b0a0c0800400a890e2c5050c101810009e95121c58a0a182030200115121c58a0a1820302001150e182010008286080c080045438b0a1820302001140a101810008a8b0a1820302001150a182030200a05080c08004545850c101810008a870a182030200a85 0x121c584060400200544871628286080c0800440a890e2c5050c101810008a890e2c5050c101810008009161430302001002a2458a0a182030200114225448b141430406040022a2458a0a1820302001000024586080c080045448b141430406040022840a891628286080c080045448b))))))) (pickBlockF p 136 (pickBlockF p 113 (pickBlockF p 102 (pickBlockF p 96 (pickBlockF p 93 (pickBlockF p 92 0x200115121c58a0a182030200109161430406040026a3ca890e2c5050c10181000848b0a18203020010f2a2458a0a182030200109161430406040021e5448b14143040604002122c286080c080043ca890e2c5050c1018100087950e2c5050c101810008f15122c5050c101810008015 0xc1018100080002a2c5050c040022a2458a0a182030200114225448b141430406040022a2458a0a182030200100005458a0c10080045448b141430406040022840a891628286080c080045448b141430406040020000a8716282810008a890e2c5050c101810009e95121c58a0a18203) (pickBlockF p 94 0x6040021e5448b141430406040022a2c5050c101810008795122c5050c101810008a8b141430406040021e544871628286080c080043ca890e2c5050c101810008f15122c5050c1018100080002a1c58a08040022a2438b1414304060400220544871628286080c08004d4a890e2c505 (pickBlockF p 95 0xc101810008a891628286080c08004fca891628286080c0800450815122c5050c101810008a891628286080c080040048716143010008015121c58a0a18203020013d2a2438b141430406040022a2438b141430406040021628286080c080043ca890e2c5050c101810008a8b1414304 0x122c5050c101810008a112a1c58a0a1820302001352a2458a0a18203020013d2a2438b141430406040023c544871628286080c0800400a890e2c30402001002a2438b1414304060400220544871628286080c08004544871628286080c08004fca891628286080c0800450895122c505))) (pickBlockF p 99 (pickBlockF p 97 0xa18203020011514143040604002425448b141430406040022428286080c0800484a891628286080c0800484f15121c58a0a18203020011e2a2458a0a1820302001353c5458a0a18203020013d2a1c58a0a18203020011e2a2438b141430406040022844a890e2c5050c101810008f15 (pickBlockF p 98 0x200a8b0a1820302001010008303020820100083040604a8b0a18203020011e2a1430406040020c0c0820a1818104180823c2c286080c08004785850c101810008f050478a850c1018100082853c1410104785850c10181000809e0a182030278a850c101810008f15160c0800478a8b 0x248486080c08004040890604a891628286080c080045448b141430406040020c0403f161808004fc3020e181810008a8716181810008a87161430406040020e2c28406041050c101810008a8b0a1820302001332a1430406040020c101850804a86080c0802a2c286080c0800414080)) (pickBlockF p 100 0xc10080202c5050c101810008348121c2840604148201c58a0c0c08004544871628286080c08004544871628286080c080045448716282840604002405448b141430406040020204a890a1818100080890604a891628286080c080045448b14143040604002665448b14143040604002 (pickBlockF p 101 0x141430406040023c14304021428402001050804f050c1009e2a245050c1018100080850a042050804f050c10080047858a0a18203020011e0a1820100cc505080400202142013c28286080411e2a245050c101810008f150e2c5050c101810008f15122c5050c1018100088050806405 0x200095121430406040020a0400b14143040200115122c5050c101810008201000858a0a18201000820100080921228286080c080045448b141430406040023c54487141430406040021418203020010a0a181810008f071628286080c080040420402cc2840200f0a0a182010008f0b)))) (pickBlockF p 107 (pickBlockF p 104 (pickBlockF p 103 0xc101810008a890e2c5050c101810008a890e2c505080c0800480a891628286080c080041c5850208095141430100082840204095122c5050c101810008a891628286080c08004cca891628286080c080040490a0c100800414201025448b141430406040022a2458a0a182030200105 0x80c08004cca891628286080c08004fca891628286080c080045448b141430406040022a28286080c08004e4a891628286080c08004485050c101810009c95122c5050c101810009c9e2a2438b141430406040023c5448b141430406040020e282840608286080400508142150e2c505) (pickBlockF p 105 0x80c0800478a891628286080c0800510a871628286080c080045448b141430406040020a102840a1820302001090e1420304544871628286080c08004544871628286080c080045448716282840604002405448b141430406040020e2c2830209f95122c5050c101810008a891628286 (pickBlockF p 106 0x488a890e2c5050c101810008f15122c5050c101810008895121c58a0a1820302001112a2438b141430406040022a1c5850c101810008895121c58a0a182030200115121c58a0a1820302001352a2c5050c101810008a890e2c5050c101810008a890e2c5050c0c08072544871628286 0xc101810008a8b0a1820302001003c543850c10181001c28406040022a1c5850c101810008a8b0a18203020010916143040601115121c58a0a18203020010916143040601115122c5050c10181000848b0a182030088a891628286080c08004245850c1018044544871628286080c080))) (pickBlockF p 110 (pickBlockF p 108 0x80c0800441115122c5050c101810008a891628286080c08004780004478a890e2c5050c10181000838b14141800488a890e2c5050c101810008a890e2c5050c10181000801e2a1c30402001070a101810008a87161430406040020a101810008a8b0a1820302001002a182030200a85 (pickBlockF p 109 0xa18203020010f445438b141430406040023c5448b1414304060400200780223c544871628286080c0800441115121c58a0a182030200115121c58a0a1820302001220088000445448b141430406040024444a891628286080c080045448b1414304060400244000220088a891628286 0x141430406040022088a891628286080c080045448b141430406040023c000223c544871628286080c080042438b0a0c00244544871628286080c08004544871628286080c080043d115121c58a0a18203020010f445448b141430406040021e88a891628286080c080043d115121c58a)) (pickBlockF p 111 0x141430406040021e88a890e2c5050c101810008f15122c5050c101810008f000088f15121c58a0a18203020011044544871628286080c08004d4a890e2c5050c10181000910044000222a2458a0a182030200122225448b141430406040022a2458a0a1820302001220088000445448b (pickBlockF p 112 0x1628286080c0800441115122c5050c101810008a891628286080c08004780004478a890e2c5050c10181000838b14141800488a890e2c5050c101810008a890e2c5050c1018100087a22a2438b141430406040021e88a891628286080c080043d115122c5050c1018100087a22a2438b 0xa182030200115122c5050c101810009115121c58a0a18203020011e2a2438b1414304060400200780223c544871628286080c0800441115121c58a0a182030200115121c58a0a18203020013f445448b141430406040024444a891628286080c080045448b141430406040027e88a89))))) (pickBlockF p 124 (pickBlockF p 118 (pickBlockF p 115 (pickBlockF p 114 0x80c080041c5850c101810008a8b0a1820302001150c1018100545850c101810008f15161430406040023c5448b141430406040026a78a8b14143040604002445438b141430406040023c544871628286080c0800444a890e2c5050c101810008f15122c5050c1018100091112a1c58a 0x4984871628286080c0800404095122c5050c101810008a891628286080c0800404095122c5050c101810008a891628286080c0800478a891628286080c08004984871628286080c0800404095122c5050c101810008a891628286080c0800404095122c5050c101810008a891628286) (pickBlockF p 116 0x8f15121c58a0a1820302001151228286080c080042438b141430406040023c5448b141430406040022a2458a0a182030200126121c58a0a18203020013f2a2458a0a182030200115122c5050c101810009f95122c5050c101810008a891628286080c0800478a891628286080c080 (pickBlockF p 117 0x2a2438b14143040604002121c58a0a18203020011e2a2438b14181823c54487141430406040022a2438b141430406040023c2438b141430406040022a2438b141430406040023c2438b141430406040022a2438b141430406040023c54487141430406040027a78a890e2c5050c10181 0x678a870a18203020011e0278f003c5438506040023c78f150e14304060401e0e143040608f150e14304060400206084871628286080c080042438b14143040604002122c5050c10181000848b14143040604002122c5050c101810008a091628286080c080042438b14143040604002))) (pickBlockF p 121 (pickBlockF p 119 0x604000805430406040020e10186080c3040605f950a1820302001150a182030201f812a1820302001150c10181000823f08fca850c10181001430406083040604106080c0022a1430406040020e2c286080c0800454a870a101810008a950e143040604015005438506040022a1c182 (pickBlockF p 120 0xc101820e2c286080c0800408f150a18203020013f0a101150e10181000800404542027e54286080c0800414a87080c0800478a850c100800408f150e101810008f070a182030478a870a18203020010b0a1820302001150a18203020010b0a1820302001150c10181000a0032a14304 0x2a2c286080c08004543850c101810008a8b0a182010009f822a14303020010b0a08a05042c2800500a8b0a1820302001007e5428606040028000a8b0a1818100085850c1008004160400a545850c10080042c28606040022a142030454585080c0022a142030208a850c10181000838b)) (pickBlockF p 122 0x60400208002830a181c02a14304060400216143040604003161430406040022a2c2840608a8b0a1820302001071614304060400204545850c1018100085860608586080c08004185850c10181000830600545850c10080042c58b0a182010008580162c08b0c101810008a8b0a10182 (pickBlockF p 123 0xc10181000838b0a18203020011c245438b0a1820302001401608e150e2c286080c080047038b0a182010008e1e2a1c3030478a870a1820302001150e1430406040022a1430406040023c5438b0a18203041c5850c1018100085850c101810009f85080c195161430406040021614304 0x3c545810078a890e2c28406040023c544871628286080c0800478a890e28286080c080045458606001150c0c0822a1430406040020e2c286080c080041c5850c101810008f150e2c286080c0800460a8b0a18203020013f0e0cc1516143040604002161430406040182a2c3030454585)))) (pickBlockF p 130 (pickBlockF p 127 (pickBlockF p 125 0x141430406040022a2438b141430406040023c5458a0a1820302001151654a85080cf15121c585080c080042c2950078a8b141430406040022a2c2950a0ca8b0654585080c0023c544871614203020011e2a040420a0c0800478a8b0278a8b14143040604002841411e2a141810008180 (pickBlockF p 126 0x2001150604042020048606040010048581005448b0a182030200112442c080845458402001222a24286080c08005081810048080020048b0c0c080242458a0604115122c5050c101810008a891628286080c0800450a8914182030208a89162830406001151228286080c080042438b 0x6040024c2458a0a182030200112161420300089150a101810449115122c286080c0800448595121820324544840608915122c5050c101810008a890601a95122c286080c080044848b0611a951210195160c9222a2458a0a182030200115160404208040022488580445448a0a18203)) (pickBlockF p 128 0x488a89161430406040022a2c0808488a8b0201115121430406040022a040420604001002458606040151604a891628286080c0800488a8b01080802a2c080445448a0a1820302001422a0c080020048606040010054581005448b0a182030200115122c5050c101810008a891414304 (pickBlockF p 129 0x604002840401e2a0c0803c5448b140c0823c54487162828406040023c544871628286080c0800478a890e28286080c080049848b14143040604002445458a0a1820302001151654315065448b0a182030200115005458a0a182030200115165428606545832a2c28406001150a10181 0x16283040604002121c58a0a1820302001151628284060011e2a2c5050c101810008a8b2a10a8a0a101823c54487162828406040022a01a8b080c10216101826a78a8b141430406040022a2c2b5080da95080ca8b0678a890e2c505080c0800478a8101081803c545810078a8b1414304))) (pickBlockF p 133 (pickBlockF p 131 0x78483020089e0e18080222458a0a1820302001070c040340a14004021430406040023c5448b1414304060400268040070a18080040400906040110e18091122c5050c101810008a890e28286080c08004f4a891628286080c0023c5448b14143040604115122c5050c101810008487 (pickBlockF p 132 0x6040023c5438b141430406040020e183090e143030444a890e28286080c080042c5050c0c1141414304060410b141430406001112a1c58a0a1820302001070c15a850c0c3030c01a9e2a2438a0a1820302001060201a05080c080041c3003c5448b141430406040020e180806814101 0xc0cf090e2c5050c1018100084871628286080c080041c30b0c10186061801e2a1c58a0a18203020010b0c04034080808716180803c2c5050c10181000838b0c01a04020010b0c10080047848b141430406040022a2438b141430406040022a2458a0a1820302001262a2438b1414304)) (pickBlockF p 134 0x7848716143040604002161808068100800e2c3003c245850c10181000838b0c04034022c3040200f0b141430406040022a2438b141430406040022a2458a0a18203020011e2a2438b14182030200115121c58a0a18203020010a0a182030208a871628286080c080041c30b1418182 (pickBlockF p 135 0x68040070c04001002c080221c30122245850c101810008a890e28286080c080045448b141430406040023c544871628286080c08004544871628286080c0800478a871628286080c080041c30b0c0c386062438b0a1820302001050c10181045438b141430406040020e185860618186 0x3c5438b141430406040022814304060410b0a1820300088950e2c5050c1018100083860c103030c00f15121c286080c080041808068100800e1801e2a245850c1018100083860201a0100785810044f070c040111628286080c080041c30100d020400043040200f0b14143040604002)))))) (pickBlockF p 159 (pickBlockF p 147 (pickBlockF p 141 (pickBlockF p 138 (pickBlockF p 137 0xa182030200126121c58a0a18203020011c2478a890e2c5050c10181000838b14101823840f15121c58a0a18203020011e0a1008038404871628286080c0800470f15121c5050c101810008f15121c58a0a1820302001262a2438b1414304060400222544870a1820302001070c18303 0xc1018100093090e2c5050c1018100084871628286080c08004984871628286080c0800498f15121c58a0a1820302001263c544871628286080c0800470a891628286080c0800471015122c5050c101810008585080401c402458a0a18203020011c2a2438b141430406040022a2458a) (pickBlockF p 139 0x200105080c08004e00801218181004048b141430406040028e544871618181701828608040202a2458a0a1820302001380608284020238100243030200809161430406040022a2438a0a182030200115122c5050c10180045448b14143040604115122c5050c1018100093090e2c505 (pickBlockF p 140 0xa18203020011e2a1c5050c1008004f4f15121c58a0a18203020011e2a1c58a0a18203020011514143040604002205448a0a18203020010a0a1010a0a1820304490151628286080c0800440a8b141430406040020a105050c10112405448a0a1820302001050804038405448b0a18203 0x8040022a2458a0a18203020010916282860804002285448b14143040604002121c58a0a1820100084871628286080c080042438b141430406040023c5438a0a182010008a890e2c5050c101810008f07162828608040022a2438b141430406040023c1c58a0a182010009a95121c58a))) (pickBlockF p 144 (pickBlockF p 142 0x14142030008f15121c58a0a18203020011e2a1418101082830200f151604f150e2c505080c08005082833c540800078a8b0200f15121c58a0a18203020011e2a1c58a0a18203020011e2a2438a0a1820302001150e2c506060848716282860804002121c58a0a1820302001091628286 (pickBlockF p 143 0x200a891628286080c080045458a0a1820302001142a283040604115162830406001151228286080c080042438b14143040604002121c58a0a18203020011e2a1c58a0a101810008a8b2a1c505045411e2a2438b141430406040022a00f150e2c505080c08004545950e281151608a8b 0x1628286080c00224545050c101810449aa22a2458a0a1820302001151604042080c92216040222a245050c101810008a8101082840604002020058a02001121604a8b141430406040022488580840401516101810088a8a0a18203020014208482840604002020050100082010a0090b)) (pickBlockF p 145 0x80c08005082950a0400100180800a040151604015122c286080c080045458a0a1820302001151228286080c0800498a891628286080c08004491151628286080c080044859524545040608915122c5050c101810008a802a2c5050c10181000890b0854506080890714182022a2c112 (pickBlockF p 146 0xc101810008a8b2a54115122c286080c08004540151628286080c08004545950a545822a2c286080c0022a1430406041222a245850c101810008a8b02021222a2c08044544850c101810008a810108281000400b0c040151604a8b141430406040024454580840401516040222a28286 0x78a87162828406040022a2ca8704545822a2c284060011e2a2438b0a18203020011e2a040420a0401e2a2c09e2a1c58a0a10181000a11e2a140800078a8b0200f15121c5850c101810008f150e2c5050c101810009a9e2a2438a0a1820302001262a2458a0a1820302001222a2c505)))) (pickBlockF p 153 (pickBlockF p 150 (pickBlockF p 148 0x2001340a0c0800e18080020058a02001110e18091122c5050c101810008a87141430406040027a5458a0a182030008f151628286080c0826a5448b14143040604002121c58a0c1018100084871628286080c0800478a87162828406040022a2ca87045411e2a2438b0a182030200115 (pickBlockF p 149 0x6040020a182030208286080c002225438a0a1820302001070c28286042828606085060008f090e2c5050c10181000830100d0080042438a0c0c0023c2458a0a1820302001070a1818100d00803c2c501000889e0e18080222c5050c1018100083860201a0002180800478a8a0a18203 0x121c5850c1018100085860201a0406040020e2c3003c245850c10181000838b0c04034080c0821618203020011e1628286080c080045438b141430406040026a5448b141430406040024c544871628286080c0800478a87141430406040020e283020a28286041c302222438b1414304)) (pickBlockF p 151 0x141818004d00801618080047858a0a1820302001150e2c5050c101810008a891628286080c0800478a87162830406040022a2438b141430406040023c1c58a0a1820302001070c183850c10115121c5850c101810008286080c0820e2c5050c10181000838608182020c083000e10f15 (pickBlockF p 152 0x2a2438b141430406040023c1c58a0a1820302001070c182090e1430406085050c1018104544871628286080c080041c58a0a1820302001070c10505042828608083020c0038a0a081820e141826a78a890e2c5050c1018100085860201a02021c5860200f091628286080c080042438b 0x8386007848b141430406040020e18080680401e16280800444f070c040111628286080c080041c30100d00010c040023c545050c101810009a01001c301000400b1404002221c301222458a0a1820302001150e28286080c080045448b141430406040023c5438b14143040604002))) (pickBlockF p 156 (pickBlockF p 154 0x121c58a0a1820302001183c5438a0a1820302001353c544871628286080c0800498a890e2c5050c101810008f150e28286080c080041c30b0c1c302222438b0a1820302001050c10181041430406001112a1c5050c10181000838616182020c083003c2438b0a1820302001060201a01 (pickBlockF p 155 0x121c58a0a1820302001182a2458a0a18203020010714143023080a891628286080c080042c2840200c20122c5050c101810008c150e2c5050c101810008a891628286080c0800498a890e2c5050c101810008c103c2438b1414304060400230784871628286080c08004782840200c10 0x920400b1404002922c5060008815122c5050c101810008a87141430406040022a2c5050c10180045458a0a182030208a891628286080c080041c58a0a1820302001262a2438b141430406040024c1c58a0a1820302001262a2438b141430406040024c78a871628286080c0800498f15)) (pickBlockF p 157 0x89202a28286080c08004ac28406245850809a902a245850c101810008815141430406040020a1048b0a10112405448b0a182030200105080c08004e1015122c5050c1018100082840201c01002c501000880b14143040604002700c10508040202a28286080c08004e09120a10080 (pickBlockF p 158 0xc10181000a0091628286080c0800500a15122c5050c10181000a0090e2c5050c1018100084871628286080c08004fca890e2c5050c101810009f95121c58a0a18203020013f2a2438b141430406040027afcf15121c58a0a18203020011e2a2438b141430406040022a245050c10181 0x45401e2a2c5050c101810008a8b2a1411516141151614304060011e2a2438b0a18203020011e2a040420a0c0803c545850804f150e2c5050c10181000a1050678a8506040003c545810078a890e2c286080c0800478a890e2c5050c101810008f15121c5050c10181000a0090e2c505))))) (pickBlockF p 170 (pickBlockF p 164 (pickBlockF p 161 (pickBlockF p 160 0x9f95122c5050c101810008a89141430406040024c5448b141430406040027e5448b14143040604002285448a0c10181045448b14182030008a8914143040604002121c58a0a1820302001090e2c5050c101810008f151628286080c08004545822a141150478a890e2c286080c080 0xc101810008a801608f151628286080c08004545822a08a8b0808f15121c58a0a18203020011e2a040420078a8b0a100803c5438b14143040604002840401e2a0401e2a2c1810478a890e2c5050c101810008f15121c58a0a18203020011e2a2438a0a182030200126122c5050c10181) (pickBlockF p 162 0x8a891628286080c0800498a890e2c5050c10181000a015121c5050c101810009e95122c5050c101800478a891628286080c0822a2458a0a1820302001090e2c506080c080042438b141430406040022a2c5050c101800478a8b141430406040022a2c1150808a830478a890e2c505 (pickBlockF p 163 0x2001070c08304041811e2a2438b141430406040022828286080c0822a2438b141430406040020e185060808304041801e2a1c58a0a18203020010b0c04034080c0800e2c2860800f0b141430406040020e2c30100d0203022c304060401e122c5050c101810008a890e2c5050c10181 0x2001070c082860428303041801e2a2438b0a18203020010b0c04034020048716283003c245850c10181000838b0a1820100d008b0c0401e1628286080c08004544871628286080c080045448b141430406040023c54487162830406040022a2438b141430406040022a1c58a0a18203))) (pickBlockF p 167 (pickBlockF p 165 0x6040023c544871628286080c0800498a890e2c5050c10181000a015121c5050c101810008a891628286080c0800478a890e2c5050c101810008a890e2c5050c1018100083836a78a871628286080c080041c3356a183850c08a890e2c286080c0800450286080c0822a1c58a0a18203 (pickBlockF p 166 0x14143040604002121c58a0a182030200126121c58a0a1820302001090e2c5050c1018100093090e2c5050c10181000931e2a2438b141430406040024c78a890e2c5050c100800461f95121c58a0a182030200115122c5050c1018100093090e2c5050c101810008c403c544871414304 0xc101810009c070478385080c0800440f15121c58a0a18203020011e2a2438a0a1820302001352a2438b141430406001353c544871628286080c080042438b141430406040026a78a890e28286080c08004fca890e28286080c080045448b14143040600115122c5050c10181045448b)) (pickBlockF p 168 0x6040020a1038b0a101123c5438b141430406040023c544871628286080c08004d4f15121c58a0a18203020011e2a1c58a0a182030200105080c2840640f15121c5050c10181000881e2a1c58a0a1820302001050854286080cf15121c5050c101810008f0508040380640f090e2c505 (pickBlockF p 169 0x1628286080c08004242840624585080cf15121c5850c101810008f15121c58a0a1820302001050824585080c91e121c5850c101810008f15121c58a0a1820302001353c544871628286080c0800478a871628286080c080041420716142022478487161430406040023c544871614304 0x2a243850c1018100082842a142023c5438b141430406040022078a871628286080c08004142050878a890e1430406040023c1420100e081e0e2c5050c101810009c070678385080c0802078a890e2c286080c0800478a890e28286080c08004d4f15121c58a0a1820302001123c54487)))) (pickBlockF p 176 (pickBlockF p 173 (pickBlockF p 171 0x2a2c5050c10180044ca8a0c0c0822a2c5050c1018104d4a891628286080c0800450a8914143040604114122c5050c10181045048b14143040604114225450606041142a245050c101810428301122c5050c10180044c58a0c0c002122c5050c10180042c50600545050c10181000881e (pickBlockF p 172 0x2001151628286080c080041421514143040480a891628286080c080042c2840201c06068048b1414304060400270085850c10181000900b141430406040022a1c58a0a182030200115122c5050c10181000858a0a181824c5438a0a18203020011e2a2438a0c10182225458a0c0c002 0x141430406040022a2c5050c1018100082840608b830a101826a80a891628286080c080042c2840201c0606090091628286080c08004e05850c10181000900b141430406040022a1c58a0a182030200115122c5050c101810008a891628286080c08004282841414202405458a0a18203)) (pickBlockF p 174 0xc101810009315121c5050c101810009a95122c5050c101800478a891628286080c0826a5448b14143040604002121c58a0a1820302001352a245050c1018100084871628286080c0800498a87141430406040022a2458a0a182030200115122c5050c1018100082842a142030480a8b (pickBlockF p 175 0x121c58a0a1820302001352a2458a0a182030200115122c5050c1018100082840a1820240245850c10181000848b0a18203020010508142202a2458a0a18203020010b0a10080708048b141430406040027008585080400240245850c101810008a890e2c5050c101810009a95122c505 0xa1820302001262a2438a0a1820302001352a2458a0a1820302001202a2458a0a18203020010914142091414203122c5050c101810008a891628286080c08004142351228284068048b1414304060400216142030201c20122c286080c08004e018b0a10080402458a0a182030200115))) (pickBlockF p 179 (pickBlockF p 177 0xe2c5050c101810009a903c2438b141430406040025828284582848a0a1019e2a1c5050c101810008f050804038060881e121c58a0a1820302001383c1420302001103c1c58a0a18203020011e2a1c5050c101810009a950e2c5050c1018004d4f15121c58a0a1820302001353c5438a (pickBlockF p 178 0x9a9e2a2438b141430406040023c544871628286080c0800428284041c5050808f071628286080c080047838b141430406040020a1038a0a1011e2a2438b141430406040023c5438b141430406040026a78a890e2c5050c10181000881e2a1c5050c1018100082841228286080cf09 0xe2c5050c101810009c1e0a101810040f071628286080c0800478a87141430406040026a78a890e2c5050c101810008f150e2c5050c1018100082842a143040678a890e2c5050c101810008f15121c58a0a1820302001050848286080cf150e2c5050c101810008f150e2c5050c10181)) (pickBlockF p 180 0x9a951628286080c0800478a890e28286080c080045448b1400f1512280b52a245050c1018100084871628286080c0800440f150e28286080c08004142050808f090e2c5050c10181000881e121c58a0a182030200105080c1020a1011e2a1c5050c101810008f0508040380640f09 (pickBlockF p 181 0x93090e2c5050c1018100093090e2c5050c101810009a9e2a1c58a0a1820302001352a2c5050c1018100084871628286080c08004d4f150e28286080c0800478a87141430406040022a28286080c0800478a890e2c5050c101810009a95122c5050c101810008f150e2c5050c10181 0x5458600543016a545050c10181))))))))))
  4

def node_2347 (i : Nat) : Bool := dagCheckNodeWithF m_2347 g_2347 (pickedBounds bds_2347 (picks_2347 i)) (dagTraceF m_2347 s_2347 12 f_2347) (dagRefPermF m_2347 g_2347 63 3457 (dagTraceF m_2347 s_2347 12 f_2347) l_2347) i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_0 : treeBlockF 0 128 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_1 : treeBlockF 128 256 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_2 : treeBlockF 256 384 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_3 : treeBlockF 384 512 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_4 : treeBlockF 512 640 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_5 : treeBlockF 640 768 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_6 : treeBlockF 768 896 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_7 : treeBlockF 896 1024 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_8 : treeBlockF 1024 1152 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_9 : treeBlockF 1152 1280 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_10 : treeBlockF 1280 1408 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_11 : treeBlockF 1408 1536 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_12 : treeBlockF 1536 1664 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_13 : treeBlockF 1664 1792 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_14 : treeBlockF 1792 1920 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_15 : treeBlockF 1920 2048 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_16 : treeBlockF 2048 2176 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_17 : treeBlockF 2176 2304 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_18 : treeBlockF 2304 2432 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_19 : treeBlockF 2432 2560 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_20 : treeBlockF 2560 2688 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_21 : treeBlockF 2688 2816 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_22 : treeBlockF 2816 2944 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_23 : treeBlockF 2944 3072 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_24 : treeBlockF 3072 3200 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_25 : treeBlockF 3200 3328 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_26 : treeBlockF 3328 3456 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_27 : treeBlockF 3456 3457 node_2347 = true := by decide +kernel
theorem nc_2347 : ∀ j, 0 ≤ j → j < 3457 → node_2347 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_2347_0) (joinChecks (certBlock nb_2347_1) (certBlock nb_2347_2))) (joinChecks (joinChecks (certBlock nb_2347_3) (certBlock nb_2347_4)) (joinChecks (certBlock nb_2347_5) (certBlock nb_2347_6)))) (joinChecks (joinChecks (certBlock nb_2347_7) (joinChecks (certBlock nb_2347_8) (certBlock nb_2347_9))) (joinChecks (joinChecks (certBlock nb_2347_10) (certBlock nb_2347_11)) (joinChecks (certBlock nb_2347_12) (certBlock nb_2347_13))))) (joinChecks (joinChecks (joinChecks (certBlock nb_2347_14) (joinChecks (certBlock nb_2347_15) (certBlock nb_2347_16))) (joinChecks (joinChecks (certBlock nb_2347_17) (certBlock nb_2347_18)) (joinChecks (certBlock nb_2347_19) (certBlock nb_2347_20)))) (joinChecks (joinChecks (certBlock nb_2347_21) (joinChecks (certBlock nb_2347_22) (certBlock nb_2347_23))) (joinChecks (joinChecks (certBlock nb_2347_24) (certBlock nb_2347_25)) (joinChecks (certBlock nb_2347_26) (certBlock nb_2347_27))))))
theorem lb_2347 : LowerBin m_2347 s_2347 g_2347 13 :=
  lowerDagPickedF (top := 63) (picks := picks_2347) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2347 sub_2347 gl_2347 rc_2347 nc_2347

theorem signedLower : LowerBin fullMask rootStock (canon fullMask (4276808360 * 2 ^ 32 + 3972581504)) 13 := lb_2347

def witnessGates : List Gate :=
  [⟨GateOp.and, [0, 2]⟩,
   ⟨GateOp.or, [6, 1]⟩,
   ⟨GateOp.or, [6, 3]⟩,
   ⟨GateOp.or, [0, 2]⟩,
   ⟨GateOp.and, [0, 5]⟩,
   ⟨GateOp.and, [3, 4]⟩,
   ⟨GateOp.or, [10, 11]⟩,
   ⟨GateOp.and, [7, 12]⟩,
   ⟨GateOp.or, [8, 4]⟩,
   ⟨GateOp.and, [9, 14]⟩,
   ⟨GateOp.and, [12, 5]⟩,
   ⟨GateOp.or, [1, 16]⟩,
   ⟨GateOp.and, [15, 17]⟩,
   ⟨GateOp.or, [13, 18]⟩]

theorem witnessSize : witnessGates.length = 14 := rfl

theorem witnessMonotone : Monotone2 ⟨witnessGates, 19⟩ := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witnessEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witnessGates, 19⟩ (List.ofFn x) =
    Nat.testBit (4276808360 * 2 ^ 32 + 3972581504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_48514

theorem PEqualNP.Outside.L_meta_48514 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3972581504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3972581504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_48514.table2_from_lowerBin
    (4276808360 * 2 ^ 32 + 3972581504) 14
    PEqualNP.Outside.L_meta_48514.signedLower
    PEqualNP.Outside.L_meta_48514.witnessGates 19
    PEqualNP.Outside.L_meta_48514.witnessSize
    PEqualNP.Outside.L_meta_48514.witnessMonotone
    PEqualNP.Outside.L_meta_48514.witnessEval
