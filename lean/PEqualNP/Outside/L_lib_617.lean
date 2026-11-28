import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_617

open Finset Classical

abbrev Cl (n : ℕ) := (Fin n × Bool) × (Fin n × Bool)

def sat {n : ℕ} (A : Finset (Cl n)) (x : Fin n → Bool) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2

noncomputable def den {n : ℕ} (A : Finset (Cl n)) : ℝ :=
  ((univ.filter (sat A)).card : ℝ) / 2 ^ n

theorem den_nonneg {n : ℕ} (A : Finset (Cl n)) : 0 ≤ den A := by
  unfold den; positivity

theorem den_mono {n : ℕ} (A B : Finset (Cl n)) (h : ∀ z, sat B z → sat A z) :
    den B ≤ den A := by
  unfold den
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (fun z hz => by simp at hz ⊢; exact h z hz)

theorem den_lt {n : ℕ} (A B : Finset (Cl n)) (h : den B < den A) :
    ∃ z, sat A z ∧ ¬ sat B z := by
  by_contra hc
  push Not at hc
  have := den_mono B A hc
  linarith

theorem den_pos {n : ℕ} (A : Finset (Cl n)) (h : 0 < den A) : ∃ z, sat A z := by
  by_contra hc
  push Not at hc
  have : univ.filter (sat A) = ∅ := by
    ext z; simp [hc z]
  unfold den at h
  rw [this] at h
  simp at h

/-! ## Packing and a bounded cover -/

def taut {n : ℕ} (c : Cl n) : Prop := c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2

def cover {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) : Prop :=
  ∀ c ∈ A, taut c ∨ c.1.1 ∈ C ∨ c.2.1 ∈ C

def dj {n : ℕ} (a b : Cl n) : Prop :=
  b.1.1 ≠ a.1.1 ∧ b.1.1 ≠ a.2.1 ∧ b.2.1 ≠ a.1.1 ∧ b.2.1 ≠ a.2.1

noncomputable def upd {n : ℕ} (c : Cl n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update (Function.update x c.1.1 c.1.2) c.2.1 c.2.2

theorem step {n : ℕ} (P : Finset (Cl n)) (c : Cl n) (hc : ¬ taut c)
    (hd : ∀ a ∈ P, dj a c) :
    4 * (univ.filter (sat (insert c P))).card ≤ 3 * (univ.filter (sat P)).card := by
  classical
  set s := univ.filter (sat P) with hs
  have hsplit := card_filter_add_card_filter_not
    (s := s) (fun x => x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2)
  have hins : univ.filter (sat (insert c P)) =
      s.filter (fun x => ¬ (x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2)) := by
    ext x
    simp only [hs, mem_filter, mem_univ, true_and, sat, mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun ⟨e1, e2⟩ => by rcases h1 with h | h <;> contradiction⟩
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      by_contra hh
      push Not at hh
      exact h1 hh
  have hinj : (s.filter (fun x => ¬ (x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2))).card ≤
      ((s.filter (fun x => x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2)) ×ˢ
        ((univ : Finset (Bool × Bool)).erase (c.1.2, c.2.2))).card := by
    apply card_le_card_of_injOn (fun x => (upd c x, (x c.1.1, x c.2.1)))
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, hs, mem_filter, mem_univ, true_and] at hx
      simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, hs, mem_univ, true_and,
        mem_erase, ne_eq, and_true]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro a ha
        have h := hd a ha
        obtain ⟨d1, d2, d3, d4⟩ := h
        have e1 : upd c x a.1.1 = x a.1.1 := by
          unfold upd
          rw [Function.update_of_ne (Ne.symm d3), Function.update_of_ne (Ne.symm d1)]
        have e2 : upd c x a.2.1 = x a.2.1 := by
          unfold upd
          rw [Function.update_of_ne (Ne.symm d4), Function.update_of_ne (Ne.symm d2)]
        rw [e1, e2]
        exact hx.1 a ha
      · unfold upd
        by_cases h : c.1.1 = c.2.1
        · have : c.1.2 = c.2.2 := by
            by_contra hh; exact hc ⟨h, hh⟩
          rw [h, Function.update_self, this]
        · rw [Function.update_of_ne h, Function.update_self]
      · unfold upd
        rw [Function.update_self]
      · intro h
        apply hx.2
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      funext i
      by_cases hi1 : i = c.1.1
      · rw [hi1, h2]
      by_cases hi2 : i = c.2.1
      · rw [hi2, h3]
      have := congrFun h1 i
      unfold upd at this
      rwa [Function.update_of_ne hi2, Function.update_of_ne hi1,
        Function.update_of_ne hi2, Function.update_of_ne hi1] at this
  rw [card_product, card_erase_of_mem (mem_univ _), card_univ] at hinj
  simp only [Fintype.card_prod, Fintype.card_bool] at hinj
  rw [hins]
  omega

theorem pack_bound {n : ℕ} (P : Finset (Cl n)) (h1 : ∀ a ∈ P, ¬ taut a)
    (h2 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → dj a b) :
    4 ^ P.card * (univ.filter (sat P)).card ≤ 3 ^ P.card * 2 ^ n := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [card_empty, pow_zero, one_mul]
    calc _ ≤ Fintype.card (Fin n → Bool) := card_le_univ _
      _ = 2 ^ n := by simp
  | insert c P hcP ih =>
    have ih' := ih (fun a ha => h1 a (mem_insert_of_mem ha))
      (fun a ha b hb hab => h2 a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
    have hs := step P c (h1 c (mem_insert_self c P))
      (fun a ha => h2 a (mem_insert_of_mem ha) c (mem_insert_self c P)
        (fun h => hcP (h ▸ ha)))
    rw [card_insert_of_notMem hcP, pow_succ, pow_succ]
    calc 4 ^ P.card * 4 * (univ.filter (sat (insert c P))).card
        = 4 ^ P.card * (4 * (univ.filter (sat (insert c P))).card) := by ring
      _ ≤ 4 ^ P.card * (3 * (univ.filter (sat P)).card) := Nat.mul_le_mul_left _ hs
      _ = 3 * (4 ^ P.card * (univ.filter (sat P)).card) := by ring
      _ ≤ 3 * (3 ^ P.card * 2 ^ n) := Nat.mul_le_mul_left _ ih'
      _ = 3 ^ P.card * 3 * 2 ^ n := by ring

theorem cover_exists (s : ℝ) (hs : 0 < s) : ∃ c : ℕ, ∀ (n : ℕ) (A : Finset (Cl n)),
    s ≤ den A → ∃ C : Finset (Fin n), C.card ≤ c ∧ cover A C := by
  classical
  obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one hs (by norm_num : (3 / 4 : ℝ) < 1)
  refine ⟨2 * k0, fun n A hA => ?_⟩
  set Fam := A.powerset.filter (fun P => (∀ a ∈ P, ¬ taut a) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → dj a b) with hFam
  have hne : Fam.Nonempty := ⟨∅, by simp [hFam]⟩
  obtain ⟨P, hP, hmax⟩ := exists_max_image Fam card hne
  simp only [hFam, mem_filter, mem_powerset] at hP
  obtain ⟨hPA, hP1, hP2⟩ := hP
  set C := P.biUnion (fun a => ({a.1.1, a.2.1} : Finset (Fin n))) with hC
  have hPk : P.card < k0 := by
    by_contra hh
    push Not at hh
    have hb := pack_bound P hP1 hP2
    have hdP : den P ≤ (3 / 4 : ℝ) ^ P.card := by
      unfold den
      rw [div_le_iff₀ (by positivity)]
      have : ((4 ^ P.card * (univ.filter (sat P)).card : ℕ) : ℝ) ≤
          ((3 ^ P.card * 2 ^ n : ℕ) : ℝ) := by exact_mod_cast hb
      push_cast at this
      have h4 : (0 : ℝ) < 4 ^ P.card := by positivity
      rw [div_pow]
      rw [div_mul_eq_mul_div, le_div_iff₀ h4]
      linarith
    have hAP : den A ≤ den P := den_mono P A (fun z hz c hc => hz c (hPA hc))
    have : (3 / 4 : ℝ) ^ P.card ≤ (3 / 4) ^ k0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hh
    linarith
  refine ⟨C, ?_, ?_⟩
  · calc C.card ≤ ∑ a ∈ P, ({a.1.1, a.2.1} : Finset (Fin n)).card := card_biUnion_le
      _ ≤ ∑ a ∈ P, 2 := sum_le_sum (fun a _ => card_le_two)
      _ = 2 * P.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * k0 := by omega
  · intro cl hcl
    by_cases ht : taut cl
    · exact Or.inl ht
    right
    by_contra hh
    push Not at hh
    obtain ⟨h1, h2⟩ := hh
    have hclP : cl ∉ P := by
      intro hm
      apply h1
      rw [hC, mem_biUnion]
      exact ⟨cl, hm, by simp⟩
    have hmem : ∀ a ∈ P, a.1.1 ∈ C ∧ a.2.1 ∈ C := by
      intro a ha
      rw [hC]
      exact ⟨mem_biUnion.2 ⟨a, ha, by simp⟩, mem_biUnion.2 ⟨a, ha, by simp⟩⟩
    have hin : insert cl P ∈ Fam := by
      simp only [hFam, mem_filter, mem_powerset]
      refine ⟨insert_subset hcl hPA, ?_, ?_⟩
      · intro a ha
        rcases mem_insert.1 ha with h | h
        · exact h ▸ ht
        · exact hP1 a h
      · intro a ha b hb hab
        rcases mem_insert.1 ha with h | h <;> rcases mem_insert.1 hb with h' | h'
        · exact absurd (h.trans h'.symm) hab
        · subst h
          obtain ⟨m1, m2⟩ := hmem b h'
          exact ⟨fun e => h1 (e ▸ m1), fun e => h2 (e ▸ m1), fun e => h1 (e ▸ m2),
            fun e => h2 (e ▸ m2)⟩
        · subst h'
          obtain ⟨m1, m2⟩ := hmem a h
          exact ⟨fun e => h1 (e.symm ▸ m1), fun e => h1 (e.symm ▸ m2),
            fun e => h2 (e.symm ▸ m1), fun e => h2 (e.symm ▸ m2)⟩
        · exact hP2 a h b h' hab
    have := hmax _ hin
    rw [card_insert_of_notMem hclP] at this
    omega

/-! ## Decomposition over a cover -/

def proj {n : ℕ} (C : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ C then x i else false

def R {n : ℕ} (C : Finset (Fin n)) : Finset (Fin n → Bool) :=
  Fintype.piFinset (fun i => if i ∈ C then (univ : Finset Bool) else {false})

theorem card_R {n : ℕ} (C : Finset (Fin n)) : (R C).card = 2 ^ C.card := by
  unfold R
  rw [Fintype.card_piFinset]
  have : ∀ i, (if i ∈ C then (univ : Finset Bool) else {false}).card =
      if i ∈ C then 2 else 1 := by
    intro i; split_ifs <;> simp
  simp only [this]
  rw [prod_ite_mem univ C (fun _ => 2), univ_inter, prod_const]

theorem proj_mem {n : ℕ} (C : Finset (Fin n)) (x : Fin n → Bool) : proj C x ∈ R C := by
  unfold proj R
  rw [Fintype.mem_piFinset]
  intro i
  by_cases h : i ∈ C <;> simp [h]

noncomputable def E {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (y : Fin n → Bool) :
    Finset (Fin n → Bool) :=
  (univ.filter (sat A)).filter (fun x => proj C x = y)

theorem den_eq_sum {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) :
    den A = ∑ y ∈ R C, ((E A C y).card : ℝ) / 2 ^ n := by
  unfold den E
  rw [card_eq_sum_card_fiberwise (f := proj C) (t := R C) (fun x _ => proj_mem C x)]
  push_cast
  rw [sum_div]

def allowed {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (y : Fin n → Bool)
    (i : Fin n) (b : Bool) : Prop :=
  ∀ cl ∈ A, ¬ (cl.1 = (i, b) ∧ cl.2.1 ∈ C ∧ y cl.2.1 = cl.2.2) ∧
    ¬ (cl.2 = (i, b) ∧ cl.1.1 ∈ C ∧ y cl.1.1 = cl.1.2)

open Classical in
noncomputable def Sset {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (y : Fin n → Bool)
    (i : Fin n) : Finset Bool :=
  if i ∈ C then {y i} else univ.filter (fun b => allowed A C y i b)

def okC {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (y : Fin n → Bool) : Prop :=
  ∀ cl ∈ A, cl.1.1 ∈ C → cl.2.1 ∈ C → y cl.1.1 ≠ cl.1.2 ∨ y cl.2.1 ≠ cl.2.2

theorem sat_iff {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (hC : cover A C)
    (y x : Fin n → Bool) (hag : ∀ i ∈ C, x i = y i) :
    sat A x ↔ okC A C y ∧ ∀ i, i ∉ C → allowed A C y i (x i) := by
  constructor
  · intro hx
    refine ⟨fun cl hcl h1 h2 => ?_, fun i hi cl hcl => ⟨?_, ?_⟩⟩
    · rw [← hag _ h1, ← hag _ h2]; exact hx cl hcl
    · rintro ⟨e, h2, h3⟩
      have e1 : cl.1.1 = i := by rw [e]
      have e2 : cl.1.2 = x i := by rw [e]
      rcases hx cl hcl with h | h
      · exact h (by rw [e1, e2])
      · exact h ((hag _ h2).trans h3)
    · rintro ⟨e, h2, h3⟩
      have e1 : cl.2.1 = i := by rw [e]
      have e2 : cl.2.2 = x i := by rw [e]
      rcases hx cl hcl with h | h
      · exact h ((hag _ h2).trans h3)
      · exact h (by rw [e1, e2])
  · rintro ⟨hok, hal⟩ cl hcl
    by_cases h1 : cl.1.1 ∈ C <;> by_cases h2 : cl.2.1 ∈ C
    · rw [hag _ h1, hag _ h2]; exact hok cl hcl h1 h2
    · by_contra hh
      push Not at hh
      exact (hal _ h2 cl hcl).2 ⟨Prod.ext rfl hh.2.symm, h1, (hag _ h1).symm.trans hh.1⟩
    · by_contra hh
      push Not at hh
      exact (hal _ h1 cl hcl).1 ⟨Prod.ext rfl hh.1.symm, h2, (hag _ h2).symm.trans hh.2⟩
    · rcases hC cl hcl with ht | h | h
      · obtain ⟨e1, e2⟩ := ht
        by_cases hx : x cl.1.1 = cl.1.2
        · right; rw [← e1, hx]; exact e2
        · left; exact hx
      · exact absurd h h1
      · exact absurd h h2

theorem proj_iff {n : ℕ} (C : Finset (Fin n)) (y : Fin n → Bool) (hy : y ∈ R C)
    (x : Fin n → Bool) : proj C x = y ↔ ∀ i ∈ C, x i = y i := by
  constructor
  · intro h i hi; rw [← h]; simp [proj, hi]
  · intro h
    funext i
    unfold proj
    split_ifs with hi
    · exact h i hi
    · unfold R at hy
      rw [Fintype.mem_piFinset] at hy
      have := hy i
      simp [hi] at this
      exact this.symm

theorem mem_E {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (hC : cover A C)
    (y : Fin n → Bool) (hy : y ∈ R C) (x : Fin n → Bool) :
    x ∈ E A C y ↔ okC A C y ∧ x ∈ Fintype.piFinset (Sset A C y) := by
  simp only [E, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rw [proj_iff C y hy]
  constructor
  · rintro ⟨hs, hag⟩
    have := (sat_iff A C hC y x hag).1 hs
    refine ⟨this.1, fun i => ?_⟩
    unfold Sset
    split_ifs with hi
    · simp [hag i hi]
    · simp [this.2 i hi]
  · rintro ⟨hok, hm⟩
    have hag : ∀ i ∈ C, x i = y i := by
      intro i hi
      have := hm i
      unfold Sset at this
      rw [if_pos hi] at this
      simpa using this
    refine ⟨(sat_iff A C hC y x hag).2 ⟨hok, fun i hi => ?_⟩, hag⟩
    have := hm i
    unfold Sset at this
    rw [if_neg hi] at this
    simpa using this

open Classical in
theorem term_eq {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (hC : cover A C)
    (y : Fin n → Bool) (hy : y ∈ R C) :
    ((E A C y).card : ℝ) / 2 ^ n =
      if okC A C y then ∏ i, (((Sset A C y i).card : ℝ) / 2) else 0 := by
  split_ifs with hok
  · have : E A C y = Fintype.piFinset (Sset A C y) := by
      ext x; rw [mem_E A C hC y hy]; simp [hok]
    rw [this, Fintype.card_piFinset]
    push_cast
    rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
  · have : E A C y = ∅ := by
      ext x; rw [mem_E A C hC y hy]; simp [hok]
    rw [this]
    simp

def Dy (x : ℝ) : Prop := x = 0 ∨ ∃ k : ℕ, x = (1 / 2) ^ k

theorem Dy_mul {a b : ℝ} (ha : Dy a) (hb : Dy b) : Dy (a * b) := by
  rcases ha with ha | ⟨k, hk⟩
  · left; rw [ha, zero_mul]
  rcases hb with hb | ⟨l, hl⟩
  · left; rw [hb, mul_zero]
  right; exact ⟨k + l, by rw [hk, hl, pow_add]⟩

theorem Dy_half (k : ℕ) (hk : k ≤ 2) : Dy ((k : ℝ) / 2) := by
  interval_cases k
  · left; simp
  · right; exact ⟨1, by norm_num⟩
  · right; exact ⟨0, by norm_num⟩

theorem card_le2 (s : Finset Bool) : s.card ≤ 2 := (card_le_univ s).trans (by simp)

open Classical in
theorem term_Dy {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (hC : cover A C)
    (y : Fin n → Bool) (hy : y ∈ R C) : Dy (((E A C y).card : ℝ) / 2 ^ n) := by
  rw [term_eq A C hC y hy]
  split_ifs
  · exact prod_induction _ Dy (fun a b => Dy_mul) (Or.inr ⟨0, by simp⟩)
      (fun i _ => Dy_half _ (card_le2 _))
  · exact Or.inl rfl

/-! ## Sums of few powers of one half -/

def SN (N : ℕ) (x : ℝ) : Prop :=
  ∃ l : List ℕ, l.length ≤ N ∧ x = (l.map (fun k => ((1 : ℝ) / 2) ^ k)).sum

theorem sum_SN {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, Dy (f i)) :
    SN s.card (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨l, hl, he⟩ := ih (fun i hi => h i (mem_insert_of_mem hi))
    rw [sum_insert ha, card_insert_of_notMem ha]
    rcases h a (mem_insert_self a s) with h0 | ⟨k, hk⟩
    · exact ⟨l, by omega, by rw [h0, he, zero_add]⟩
    · refine ⟨k :: l, by simp only [List.length_cons]; omega, ?_⟩
      rw [hk, he]
      simp

theorem SN_mono {N N' : ℕ} (h : N ≤ N') {x : ℝ} (hx : SN N x) : SN N' x := by
  obtain ⟨l, hl, he⟩ := hx
  exact ⟨l, hl.trans h, he⟩

theorem SN_nonneg {N : ℕ} {x : ℝ} (hx : SN N x) : 0 ≤ x := by
  obtain ⟨l, _, he⟩ := hx
  rw [he]
  apply List.sum_nonneg
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨k, _, rfl⟩ := hy
  positivity

theorem den_SN (s : ℝ) (hs : 0 < s) : ∃ N : ℕ, ∀ (n : ℕ) (A : Finset (Cl n)),
    s ≤ den A → SN N (den A) := by
  obtain ⟨c, hc⟩ := cover_exists s hs
  refine ⟨2 ^ c, fun n A h => ?_⟩
  obtain ⟨C, hCc, hC⟩ := hc n A h
  rw [den_eq_sum A C]
  apply SN_mono _ (sum_SN _ _ (fun y hy => term_Dy A C hC y hy))
  rw [card_R]
  exact Nat.pow_le_pow_right two_pos hCc

theorem fmin (J : ℕ) (P : ℕ → ℝ → Prop)
    (hm : ∀ j g g', P j g → 0 < g' → g' ≤ g → P j g')
    (h : ∀ j < J, ∃ g > 0, P j g) : ∃ g > 0, ∀ j < J, P j g := by
  induction J with
  | zero => exact ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ J ih =>
    obtain ⟨g, hg, hP⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨g', hg', hP'⟩ := h J (by omega)
    refine ⟨min g g', lt_min hg hg', fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact hm j g _ (hP j hj) (lt_min hg hg') (min_le_left _ _)
    · subst hj; exact hm _ g' _ hP' (lt_min hg hg') (min_le_right _ _)

theorem gap_SN (N : ℕ) : ∀ t : ℝ, 0 < t → ∃ g > 0, ∀ x, SN N x → x < t → x ≤ t - g := by
  induction N with
  | zero =>
    intro t ht
    refine ⟨t, ht, fun x hx _ => ?_⟩
    obtain ⟨l, hl, he⟩ := hx
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp at he
    rw [he]; linarith
  | succ N ih =>
    intro t ht
    obtain ⟨g0, hg0, h0⟩ := ih t ht
    obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (half_pos hg0) (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨g1, hg1, h1⟩ := fmin J (fun j g => (1 / 2 : ℝ) ^ j < t → ∀ x, SN N x →
        x < t - (1 / 2) ^ j → x ≤ t - (1 / 2) ^ j - g)
      (fun j g g' hP _ hle hj x hx hlt => by have := hP hj x hx hlt; linarith)
      (fun j _ => by
        by_cases hj : (1 / 2 : ℝ) ^ j < t
        · obtain ⟨g, hg, hP⟩ := ih (t - (1 / 2) ^ j) (by linarith)
          exact ⟨g, hg, fun _ x hx hlt => hP x hx hlt⟩
        · exact ⟨1, one_pos, fun h => absurd h hj⟩)
    refine ⟨min (g0 / 2) g1, lt_min (half_pos hg0) hg1, ?_⟩
    rintro x ⟨l, hl, hx⟩ hxt
    cases l with
    | nil =>
      simp at hx
      have := h0 0 ⟨[], by simp, by simp⟩ (by linarith)
      have := min_le_left (g0 / 2) g1
      linarith
    | cons k l =>
      simp only [List.map_cons, List.sum_cons] at hx
      have hyS : SN N (l.map (fun k => ((1 : ℝ) / 2) ^ k)).sum :=
        ⟨l, by simp only [List.length_cons] at hl; omega, rfl⟩
      have hy0 := SN_nonneg hyS
      have hk0 : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
      by_cases hk : (1 / 2 : ℝ) ^ k < g0 / 2
      · have := h0 _ hyS (by linarith)
        have := min_le_left (g0 / 2) g1
        linarith
      · push Not at hk
        have hkJ : k < J := by
          by_contra hh
          push Not at hh
          have : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ J :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hh
          linarith
        have := h1 k hkJ (by linarith) _ hyS (by linarith)
        have := min_le_right (g0 / 2) g1
        linarith

theorem part_a (t : ℝ) (ht : 0 < t) : ∃ gap : ℝ, 0 < gap ∧
    ∀ (n : ℕ) (A : Finset (Cl n)), den A < t → den A ≤ t - gap := by
  obtain ⟨N, hN⟩ := den_SN (t / 2) (half_pos ht)
  obtain ⟨g, hg, hG⟩ := gap_SN N t ht
  refine ⟨min g (t / 2), lt_min hg (half_pos ht), fun n A hA => ?_⟩
  by_cases h : t / 2 ≤ den A
  · have := hG _ (hN n A h) hA
    have := min_le_left g (t / 2)
    linarith
  · have := min_le_right g (t / 2)
    linarith

/-! ## Pinning: a bounded stronger formula -/

open Classical in
noncomputable def Act {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (y : Fin n → Bool) :
    Finset (Fin n) :=
  univ.filter (fun i => i ∉ C ∧ ∃ b, ¬ allowed A C y i b)

open Classical in
theorem term_small {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (hC : cover A C)
    (y : Fin n → Bool) (hy : y ∈ R C) :
    ((E A C y).card : ℝ) / 2 ^ n ≤ (1 / 2) ^ (Act A C y).card := by
  rw [term_eq A C hC y hy]
  split_ifs
  · calc ∏ i, (((Sset A C y i).card : ℝ) / 2)
        ≤ ∏ i, (if i ∈ Act A C y then (1 / 2 : ℝ) else 1) := by
          apply prod_le_prod₀
          · intro i _; positivity
          · intro i _
            split_ifs with hi
            · have hi' := hi
              simp only [Act, mem_filter, mem_univ, true_and] at hi'
              obtain ⟨hiC, b, hb⟩ := hi'
              have h1 : (Sset A C y i).card ≤ 1 := by
                unfold Sset
                rw [if_neg hiC]
                calc _ ≤ ((univ : Finset Bool).erase b).card := card_le_card (fun b' hb' => by
                        simp only [mem_filter, mem_univ, true_and] at hb'
                        simp only [mem_erase, mem_univ, and_true]
                        rintro rfl
                        exact hb hb')
                  _ = 1 := by simp
              have : ((Sset A C y i).card : ℝ) ≤ 1 := by exact_mod_cast h1
              linarith
            · have : ((Sset A C y i).card : ℝ) ≤ 2 := by exact_mod_cast card_le2 _
              linarith
      _ = (1 / 2) ^ (Act A C y).card := by
          rw [prod_ite_mem univ (Act A C y) (fun _ => (1 / 2 : ℝ)), univ_inter, prod_const]
  · positivity

theorem pin {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) (hC : cover A C) (M : ℕ) :
    ∃ (S : Finset (Fin n)) (B : Finset (Cl n)), S.card ≤ C.card + 2 ^ C.card * M ∧
      (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ (∀ cl ∈ B, cl ∈ A ∨ cl.1 = cl.2) ∧
      (∀ z, sat B z → sat A z) ∧ den A - 2 ^ C.card * (1 / 2) ^ (M + 1) ≤ den B := by
  classical
  set U := ((R C).filter (fun y => (Act A C y).card ≤ M)).biUnion (Act A C) with hU
  set S := C ∪ U with hS
  set B := A.filter (fun cl => cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∪
    ((A.filter (fun cl => cl.1.1 ∉ S ∧ cl.2.1 ∈ C)).image (fun cl => (cl.2, cl.2)) ∪
     (A.filter (fun cl => cl.2.1 ∉ S ∧ cl.1.1 ∈ C)).image (fun cl => (cl.1, cl.1))) with hB
  have hCS : ∀ i ∈ C, i ∈ S := fun i hi => mem_union_left _ hi
  refine ⟨S, B, ?_, ?_, ?_, ?_, ?_⟩
  · calc S.card ≤ C.card + U.card := card_union_le _ _
      _ ≤ C.card + 2 ^ C.card * M := by
        apply Nat.add_le_add_left
        calc U.card ≤ ∑ y ∈ (R C).filter (fun y => (Act A C y).card ≤ M), (Act A C y).card :=
              card_biUnion_le
          _ ≤ ∑ y ∈ (R C).filter (fun y => (Act A C y).card ≤ M), M :=
              sum_le_sum (fun y hy => (mem_filter.1 hy).2)
          _ = ((R C).filter (fun y => (Act A C y).card ≤ M)).card * M := by
              rw [sum_const, smul_eq_mul]
          _ ≤ (R C).card * M := Nat.mul_le_mul_right _ (card_filter_le _ _)
          _ = 2 ^ C.card * M := by rw [card_R]
  · intro cl hcl
    simp only [hB, mem_union, mem_filter, mem_image] at hcl
    rcases hcl with ⟨_, h1, h2⟩ | ⟨a, ⟨_, _, ha⟩, rfl⟩ | ⟨a, ⟨_, _, ha⟩, rfl⟩
    · exact ⟨h1, h2⟩
    · exact ⟨hCS _ ha, hCS _ ha⟩
    · exact ⟨hCS _ ha, hCS _ ha⟩
  · intro cl hcl
    simp only [hB, mem_union, mem_filter, mem_image] at hcl
    rcases hcl with ⟨h, _, _⟩ | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩
    · exact Or.inl h
    · exact Or.inr rfl
    · exact Or.inr rfl
  · intro z hz cl hcl
    by_cases hin : cl.1.1 ∈ S ∧ cl.2.1 ∈ S
    · exact hz cl (by simp only [hB, mem_union, mem_filter]; exact Or.inl ⟨hcl, hin⟩)
    · rcases hC cl hcl with ht | h1 | h2
      · obtain ⟨e1, e2⟩ := ht
        by_cases hx : z cl.1.1 = cl.1.2
        · right; rw [← e1, hx]; exact e2
        · left; exact hx
      · have h2 : cl.2.1 ∉ S := fun h => hin ⟨hCS _ h1, h⟩
        have := hz (cl.1, cl.1) (by
          simp only [hB, mem_union, mem_filter, mem_image]
          exact Or.inr (Or.inr ⟨cl, ⟨hcl, h2, h1⟩, rfl⟩))
        left
        rcases this with h | h <;> exact h
      · have h1 : cl.1.1 ∉ S := fun h => hin ⟨h, hCS _ h2⟩
        have := hz (cl.2, cl.2) (by
          simp only [hB, mem_union, mem_filter, mem_image]
          exact Or.inr (Or.inl ⟨cl, ⟨hcl, h1, h2⟩, rfl⟩))
        right
        rcases this with h | h <;> exact h
  · rw [den_eq_sum A C, den_eq_sum B C]
    have key : ∀ y ∈ R C, ((E A C y).card : ℝ) / 2 ^ n - ((E B C y).card : ℝ) / 2 ^ n ≤
        (1 / 2) ^ (M + 1) := by
      intro y hy
      by_cases hg : (Act A C y).card ≤ M
      · have hsub : E A C y ⊆ E B C y := by
          intro x hx
          simp only [E, mem_filter, mem_univ, true_and] at hx ⊢
          refine ⟨?_, hx.2⟩
          obtain ⟨hxA, hpx⟩ := hx
          have hag := (proj_iff C y hy x).1 hpx
          intro cl hcl
          simp only [hB, mem_union, mem_filter, mem_image] at hcl
          rcases hcl with ⟨h, _, _⟩ | ⟨a, ⟨haA, ha1, ha2⟩, rfl⟩ | ⟨a, ⟨haA, ha1, ha2⟩, rfl⟩
          · exact hxA cl h
          · dsimp only
            by_contra hh
            push Not at hh
            apply ha1
            have hact : a.1.1 ∈ Act A C y := by
              simp only [Act, mem_filter, mem_univ, true_and]
              refine ⟨fun h => ha1 (hCS _ h), a.1.2, fun hal => ?_⟩
              exact (hal a haA).1 ⟨rfl, ha2, (hag _ ha2).symm.trans hh.1⟩
            exact mem_union_right _ (mem_biUnion.2 ⟨y, mem_filter.2 ⟨hy, hg⟩, hact⟩)
          · dsimp only
            by_contra hh
            push Not at hh
            apply ha1
            have hact : a.2.1 ∈ Act A C y := by
              simp only [Act, mem_filter, mem_univ, true_and]
              refine ⟨fun h => ha1 (hCS _ h), a.2.2, fun hal => ?_⟩
              exact (hal a haA).2 ⟨rfl, ha2, (hag _ ha2).symm.trans hh.1⟩
            exact mem_union_right _ (mem_biUnion.2 ⟨y, mem_filter.2 ⟨hy, hg⟩, hact⟩)
        have h1 := card_le_card hsub
        have h2 : ((E A C y).card : ℝ) ≤ (E B C y).card := by exact_mod_cast h1
        have h3 : ((E A C y).card : ℝ) / 2 ^ n ≤ ((E B C y).card : ℝ) / 2 ^ n :=
          div_le_div_of_nonneg_right h2 (by positivity)
        have : (0 : ℝ) ≤ (1 / 2) ^ (M + 1) := by positivity
        linarith
      · push Not at hg
        have h1 := term_small A C hC y hy
        have h2 : (1 / 2 : ℝ) ^ (Act A C y).card ≤ (1 / 2) ^ (M + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hg
        have h3 : (0 : ℝ) ≤ ((E B C y).card : ℝ) / 2 ^ n := by positivity
        linarith
    have := sum_le_sum key
    rw [sum_sub_distrib, sum_const, card_R, nsmul_eq_mul] at this
    push_cast at this
    linarith

theorem bounded (t : ℝ) (ht : 0 < t) : ∃ K : ℕ, ∀ (n : ℕ) (A : Finset (Cl n)), t ≤ den A →
    ∃ (S : Finset (Fin n)) (B : Finset (Cl n)), S.card ≤ K ∧
      (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ t ≤ den B ∧
      (∀ cl ∈ B, cl ∈ A ∨ cl.1 = cl.2) ∧ (∀ z, sat B z → sat A z) := by
  obtain ⟨g, hg, hgap⟩ := part_a t ht
  obtain ⟨c, hc⟩ := cover_exists t ht
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hg (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨c + 2 ^ c * (c + m), fun n A hA => ?_⟩
  obtain ⟨C, hCc, hC⟩ := hc n A hA
  obtain ⟨S, B, h1, h2, h3, h4, h5⟩ := pin A C hC (c + m)
  refine ⟨S, B, ?_, h2, ?_, h3, h4⟩
  · calc S.card ≤ C.card + 2 ^ C.card * (c + m) := h1
      _ ≤ c + 2 ^ c * (c + m) :=
        Nat.add_le_add hCc (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos hCc))
  · have e1 : (2 : ℝ) ^ C.card ≤ 2 ^ c := pow_le_pow_right₀ (by norm_num) hCc
    have e2 : (2 : ℝ) ^ c * (1 / 2) ^ (c + m + 1) = (1 / 2) ^ (m + 1) := by
      rw [show c + m + 1 = c + (m + 1) by omega, pow_add, ← mul_assoc, ← mul_pow]
      norm_num
    have e3 : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have e4 : (2 : ℝ) ^ C.card * (1 / 2) ^ (c + m + 1) ≤ 2 ^ c * (1 / 2) ^ (c + m + 1) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    by_contra hlt
    push Not at hlt
    have := hgap n B hlt
    linarith

/-! ## Granularity and doubling -/

theorem gran {n : ℕ} (B : Finset (Cl n)) (S : Finset (Fin n))
    (hS : ∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) : ∃ m : ℕ, den B = m / 2 ^ S.card := by
  classical
  have hC : cover B S := fun cl hcl => Or.inr (Or.inl (hS cl hcl).1)
  refine ⟨((R S).filter (okC B S)).card, ?_⟩
  rw [den_eq_sum B S]
  have : ∀ y ∈ R S, ((E B S y).card : ℝ) / 2 ^ n =
      if okC B S y then (1 / 2 : ℝ) ^ S.card else 0 := by
    intro y hy
    rw [term_eq B S hC y hy]
    split_ifs with h
    · calc ∏ i, (((Sset B S y i).card : ℝ) / 2) = ∏ i, (if i ∈ S then (1 / 2 : ℝ) else 1) := by
            apply prod_congr rfl
            intro i _
            unfold Sset
            split_ifs with hi
            · simp
            · have : univ.filter (fun b => allowed B S y i b) = univ := by
                ext b
                simp only [mem_filter, mem_univ, true_and, iff_true]
                intro cl hcl
                refine ⟨fun ⟨e, _⟩ => hi ?_, fun ⟨e, _⟩ => hi ?_⟩
                · have : cl.1.1 = i := by rw [e]
                  exact this ▸ (hS cl hcl).1
                · have : cl.2.1 = i := by rw [e]
                  exact this ▸ (hS cl hcl).2
              rw [this]
              simp
        _ = (1 / 2) ^ S.card := by rw [prod_ite_mem, univ_inter, prod_const]
    · rfl
  rw [sum_congr rfl this, sum_ite, sum_const, sum_const_zero, add_zero, nsmul_eq_mul,
    one_div_pow, mul_one_div]

theorem double {n : ℕ} (B : Finset (Cl n)) (u : Fin n) (c : Bool)
    (hB : ∀ z, sat B z → z u ≠ c) (hne : ∃ w, sat B w) :
    ∃ B' : Finset (Cl n), den B' = 2 * den B := by
  classical
  have hB' : ∀ w, sat B w → w u = !c := by
    intro w hw
    have := hB w hw
    revert this
    cases w u <;> cases c <;> simp
  obtain ⟨w0, hw0⟩ := hne
  let T : Cl n := ((u, c), (u, !c))
  let g : Cl n → Cl n := fun cl =>
    if cl.1.1 = u then
      (if cl.1.2 = c then T else if cl.2.1 = u then (if cl.2.2 = c then T else cl)
        else (cl.2, cl.2))
    else if cl.2.1 = u then (if cl.2.2 = c then T else (cl.1, cl.1)) else cl
  refine ⟨B.image g, ?_⟩
  have key : ∀ z, sat (B.image g) z ↔ sat B (Function.update z u (!c)) := by
    intro z
    unfold sat
    rw [forall_mem_image]
    constructor
    · intro h cl hcl
      have hz := h hcl
      have hw := hw0 cl hcl
      have hwu := hB' w0 hw0
      rcases cl with ⟨⟨i, b⟩, j, b'⟩
      simp only [g, T] at hz hw ⊢
      by_cases hi : i = u <;> by_cases hj : j = u
      · subst hi; subst hj
        cases b <;> cases b' <;> cases c <;> simp_all
      · subst hi
        simp only [Function.update_self, Function.update_of_ne hj, if_true, hj, if_false] at hz ⊢
        cases b <;> cases c <;> simp_all
      · subst hj
        simp only [Function.update_self, Function.update_of_ne hi, if_true, hi, if_false] at hz ⊢
        cases b' <;> cases c <;> simp_all
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj, hi, hj, if_false] at hz ⊢
        exact hz
    · intro h cl hcl
      have hz := h cl hcl
      rcases cl with ⟨⟨i, b⟩, j, b'⟩
      simp only [g, T] at hz ⊢
      by_cases hi : i = u <;> by_cases hj : j = u
      · subst hi; subst hj
        cases b <;> cases b' <;> cases c <;> simp_all
      · subst hi
        simp only [Function.update_self, Function.update_of_ne hj, if_true, hj, if_false] at hz ⊢
        cases b <;> cases c <;> simp_all
      · subst hj
        simp only [Function.update_self, Function.update_of_ne hi, if_true, hi, if_false] at hz ⊢
        cases b' <;> cases c <;> simp_all
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj, hi, hj, if_false] at hz ⊢
        exact hz
  have hcard : (univ.filter (sat (B.image g))).card =
      ((univ.filter (sat B)) ×ˢ (univ : Finset Bool)).card := by
    apply card_nbij' (fun z => (Function.update z u (!c), z u))
      (fun p => Function.update p.1 u p.2)
    · intro z hz
      rw [mem_coe, mem_filter] at hz
      rw [mem_coe, mem_product, mem_filter]
      exact ⟨⟨mem_univ _, (key z).1 hz.2⟩, mem_univ _⟩
    · intro p hp
      rw [mem_coe, mem_product, mem_filter] at hp
      rw [mem_coe, mem_filter]
      refine ⟨mem_univ _, (key _).2 ?_⟩
      rw [Function.update_idem, Function.update_eq_self_iff.2 (hB' _ hp.1.2).symm]
      exact hp.1.2
    · intro z _
      simp only
      rw [Function.update_idem, Function.update_eq_self]
    · intro p hp
      rw [mem_coe, mem_product, mem_filter] at hp
      simp only
      rw [Function.update_idem, Function.update_eq_self_iff.2 (hB' _ hp.1.2).symm,
        Function.update_self]
  unfold den
  rw [hcard, card_product, card_univ, Fintype.card_bool]
  push_cast
  ring

/-! ## Products and stars -/

def mapC {m n : ℕ} (f : Fin m → Fin n) (cl : Cl m) : Cl n :=
  ((f cl.1.1, cl.1.2), (f cl.2.1, cl.2.2))

def join {d m : ℕ} (B : Finset (Cl d)) (Q : Finset (Cl m)) : Finset (Cl (d + m)) :=
  B.image (mapC (Fin.castAdd m)) ∪ Q.image (mapC (Fin.natAdd d))

theorem sat_join {d m : ℕ} (B : Finset (Cl d)) (Q : Finset (Cl m)) (x : Fin (d + m) → Bool) :
    sat (join B Q) x ↔
      sat B (fun i => x (Fin.castAdd m i)) ∧ sat Q (fun j => x (Fin.natAdd d j)) := by
  unfold sat join
  rw [forall_mem_union, forall_mem_image, forall_mem_image]
  rfl

theorem den_join {d m : ℕ} (B : Finset (Cl d)) (Q : Finset (Cl m)) :
    den (join B Q) = den B * den Q := by
  classical
  have hcard : (univ.filter (sat (join B Q))).card =
      ((univ.filter (sat B)) ×ˢ (univ.filter (sat Q))).card := by
    apply card_nbij' (fun x => (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd d j)))
      (fun p => Fin.append p.1 p.2)
    · intro z hz
      rw [mem_coe, mem_filter] at hz
      rw [mem_coe, mem_product, mem_filter, mem_filter]
      have := (sat_join B Q z).1 hz.2
      exact ⟨⟨mem_univ _, this.1⟩, mem_univ _, this.2⟩
    · intro p hp
      rw [mem_coe, mem_product, mem_filter, mem_filter] at hp
      rw [mem_coe, mem_filter]
      refine ⟨mem_univ _, (sat_join B Q _).2 ?_⟩
      simp only [Fin.append_left, Fin.append_right]
      exact ⟨hp.1.2, hp.2.2⟩
    · intro z _
      exact Fin.append_castAdd_natAdd
    · intro p _
      simp only [Fin.append_left, Fin.append_right]
  unfold den
  rw [hcard, card_product]
  push_cast
  rw [pow_add]
  field_simp

def star (m : ℕ) : Finset (Cl (m + 1)) :=
  univ.image (fun j : Fin m => ((0, true), (j.succ, true)))

theorem den_star (m : ℕ) : den (star m) = (2 ^ m + 1) / 2 ^ (m + 1) := by
  classical
  have hsat : ∀ z, sat (star m) z ↔ (z 0 = true → ∀ j : Fin m, z j.succ = false) := by
    intro z
    unfold sat star
    rw [forall_mem_image]
    constructor
    · intro h h0 j
      rcases h (mem_univ j) with h1 | h1
      · exact absurd h0 h1
      · simpa using h1
    · intro h j _
      by_cases h0 : z 0 = true
      · right; simp [h h0 j]
      · left; exact h0
  have hcard : (univ.filter (sat (star m))).card =
      (((({false} : Finset Bool) ×ˢ (univ : Finset (Fin m → Bool))) ∪
        {(true, fun _ => false)})).card := by
    apply card_nbij' (fun z => (z 0, Fin.tail z)) (fun p => Fin.cons p.1 p.2)
    · intro z hz
      rw [mem_coe, mem_filter, hsat] at hz
      rw [mem_coe, mem_union, mem_product, mem_singleton, mem_singleton]
      by_cases h0 : z 0 = true
      · right
        refine Prod.ext h0 ?_
        funext j
        exact hz.2 h0 j
      · left
        exact ⟨by simpa using h0, mem_univ _⟩
    · intro p hp
      rw [mem_coe, mem_union, mem_product, mem_singleton, mem_singleton] at hp
      rw [mem_coe, mem_filter, hsat]
      refine ⟨mem_univ _, ?_⟩
      rcases hp with ⟨h1, _⟩ | h
      · intro h0
        simp [h1] at h0
      · intro _ j
        rw [h]
        simp
    · intro z _
      exact Fin.cons_self_tail z
    · intro p _
      simp
  unfold den
  rw [hcard, card_union_of_disjoint]
  · simp
  · rw [disjoint_singleton_right, mem_product]
    simp

theorem part_b (t : ℝ) (ht : 0 < t) :
    (∀ e : ℝ, 0 < e → ∃ (n : ℕ) (A : Finset (Cl n)), t < den A ∧ den A < t + e) ↔
      ∃ (d : ℕ) (B : Finset (Cl d)), den B = 2 * t := by
  constructor
  · intro H
    obtain ⟨K, hK⟩ := bounded t ht
    set q : ℕ := ⌊t * 2 ^ K⌋₊ with hq
    have hq1 : t * 2 ^ K < q + 1 := Nat.lt_floor_add_one _
    have hε : 0 < (q + 1) / 2 ^ K - t := by
      rw [sub_pos, lt_div_iff₀ (by positivity)]
      exact hq1
    obtain ⟨n, A, hA1, hA2⟩ := H _ hε
    obtain ⟨S, B, h1, h2, h3, h4, h5⟩ := hK n A hA1.le
    obtain ⟨m, hm⟩ := gran B S h2
    have hBA := den_mono A B h5
    have hBt : den B = t := by
      apply le_antisymm _ h3
      have hlt : den B < (q + 1) / 2 ^ K := by linarith
      have hB2 : den B = ((m * 2 ^ (K - S.card) : ℕ) : ℝ) / 2 ^ K := by
        rw [hm]
        push_cast
        rw [show K = S.card + (K - S.card) by omega, pow_add]
        rw [Nat.add_sub_cancel_left]
        field_simp
      rw [hB2, div_lt_div_iff_of_pos_right (by positivity)] at hlt
      have hlt' : m * 2 ^ (K - S.card) < q + 1 := by exact_mod_cast hlt
      have hle : m * 2 ^ (K - S.card) ≤ q := by omega
      have : ((m * 2 ^ (K - S.card) : ℕ) : ℝ) ≤ t * 2 ^ K := by
        calc ((m * 2 ^ (K - S.card) : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
          _ ≤ t * 2 ^ K := Nat.floor_le (by positivity)
      rw [hB2, div_le_iff₀ (by positivity)]
      exact this
    obtain ⟨z, hzA, hzB⟩ := den_lt A B (by rw [hBt]; exact hA1)
    have hz' : ¬ sat B z := hzB
    unfold sat at hz'
    push Not at hz'
    obtain ⟨cl, hcl, hv⟩ := hz'
    have hunit : cl.1 = cl.2 := by
      rcases h4 cl hcl with h | h
      · exfalso
        rcases hzA cl h with h' | h'
        · exact h' hv.1
        · exact h' hv.2
      · exact h
    obtain ⟨B', hB'⟩ := double B cl.1.1 cl.1.2
      (fun w hw => by
        rcases hw cl hcl with h | h
        · exact h
        · rw [← hunit] at h; exact h)
      (den_pos B (by rw [hBt]; exact ht))
    exact ⟨n, B', by rw [hB', hBt]⟩
  · rintro ⟨d, B, hB⟩ e he
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos he ht) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨d + (m + 1), join B (star m), ?_⟩
    have hd : den (join B (star m)) = t + t * (1 / 2) ^ m := by
      have h : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
      rw [den_join, hB, den_star]
      field_simp
      linear_combination (-2 : ℝ) * h
    rw [hd]
    have h1 : 0 < t * (1 / 2) ^ m := by positivity
    have h2 : t * (1 / 2) ^ m < e := by
      rw [lt_div_iff₀ ht] at hm
      linarith
    constructor <;> linarith

end PEqualNP.Outside.L_lib_617

open PEqualNP.Outside.L_lib_617 in
theorem PEqualNP.Outside.L_lib_617 : let W := fun width : ℕ => Fin width → Bool
let F := fun arity : ℕ => Finset ((Fin arity × Bool) × (Fin arity × Bool))
let sat := fun (len : ℕ) (A : F len) (x : W len) => decide (∀ c ∈ A,
  x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2)
let den := fun (size : ℕ) (G : F size) =>
  ((Finset.univ.filter (fun w : W size => sat size G w = true)).card : ℝ) / 2 ^ size
∀ t : ℝ, 0 < t → t ≤ 1 →
  (∃ gap : ℝ, 0 < gap ∧ ∀ (n : ℕ) (A : F n), den n A < t → den n A ≤ t - gap) ∧
  ((∀ e : ℝ, 0 < e → ∃ (n : ℕ) (A : F n), t < den n A ∧ den n A < t + e) ↔
    ∃ (d : ℕ) (B : F d), den d B = 2 * t) ∧
  (∃ K : ℕ, ∀ (n : ℕ) (A : F n), t ≤ den n A →
    ∃ (S : Finset (Fin n)) (B : F n),
      S.card ≤ K ∧ (∀ c ∈ B, c.1.1 ∈ S ∧ c.2.1 ∈ S) ∧
      t ≤ den n B ∧ ∀ z : W n, sat n B z = true → sat n A z = true) := by
  have hsat : ∀ (n : ℕ) (A : Finset (Cl n)) (z : Fin n → Bool),
      decide (∀ c ∈ A, z c.1.1 ≠ c.1.2 ∨ z c.2.1 ≠ c.2.2) = true ↔ sat A z := by
    intro n A z
    simp [sat]
  have hden : ∀ (n : ℕ) (A : Finset (Cl n)),
      ((Finset.univ.filter (fun w : Fin n → Bool => decide (∀ c ∈ A,
        w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) = true)).card : ℝ) / 2 ^ n = den A := by
    intro n A
    unfold den
    congr 2
    congr 1
    ext w
    simp [sat]
  dsimp only
  intro t ht _
  simp only [hden]
  simp only [hsat]
  refine ⟨part_a t ht, part_b t ht, ?_⟩
  obtain ⟨K, hK⟩ := bounded t ht
  refine ⟨K, fun n A hA => ?_⟩
  obtain ⟨S, B, h1, h2, h3, _, h5⟩ := hK n A hA
  exact ⟨S, B, h1, h2, h3, h5⟩
