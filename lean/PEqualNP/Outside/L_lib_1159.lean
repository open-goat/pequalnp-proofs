import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1159_aux

open scoped BigOperators

/-! ### Part A: Basic cycle definitions and satisfaction characterization -/

abbrev Site (n : ℕ) := Fin (n + 2)
abbrev Bits (n : ℕ) := Finset (Site n)
abbrev Signing (n : ℕ) := Site n → Bool × Bool

def vertex (n : ℕ) : Bits n := Finset.univ

def comp {n : ℕ} (x : Bits n) : Bits n := vertex n \ x

def sat {n : ℕ} (x : Bits n) (q : Signing n) : Prop :=
  ∀ i : Site n, (decide (i ∈ x), decide ((i + 1 : Site n) ∈ x)) ≠ q i

noncomputable def replyOf {n : ℕ} (A : Finset (Bits n)) (q : Signing n) : Bool :=
  A.toList.any (fun x =>
    (Finset.univ : Finset (Site n)).toList.all (fun i =>
      (decide (i ∈ x), decide ((i + 1 : Site n) ∈ x)) != q i))

lemma replyOf_eq_true_iff {n : ℕ} (A : Finset (Bits n)) (q : Signing n) :
    replyOf A q = true ↔ ∃ x ∈ A, sat x q := by
  simp [replyOf, sat, List.any_eq_true, List.all_eq_true, bne_iff_ne]

lemma mem_comp_iff {n : ℕ} (x : Bits n) (i : Site n) :
    i ∈ comp x ↔ i ∉ x := by
  simp [comp, vertex]

lemma comp_comp {n : ℕ} (x : Bits n) : comp (comp x) = x := by
  ext i
  simp [mem_comp_iff]

lemma comp_ne_self {n : ℕ} (x : Bits n) : comp x ≠ x := by
  intro h
  have h0 : (0 : Site n) ∈ comp x ↔ (0 : Site n) ∈ x := by rw [h]
  rw [mem_comp_iff] at h0
  tauto

def flipSet {n : ℕ} (x S : Bits n) : Bits n :=
  (Finset.univ : Finset (Site n)).filter (fun i => decide (i ∈ x) != decide (i ∈ S))

lemma decide_mem_flipSet {n : ℕ} (x S : Bits n) (i : Site n) :
    decide (i ∈ flipSet x S) = (decide (i ∈ x) != decide (i ∈ S)) := by
  simp only [flipSet, Finset.mem_filter, Finset.mem_univ, true_and]
  cases decide (i ∈ x) <;> cases decide (i ∈ S) <;> rfl

lemma flipSet_parity_of_inter_singleton {n : ℕ} (x S T : Bits n) (t : Site n)
    (hST : S ∩ T = {t}) :
    (flipSet x S ∩ T).card % 2 ≠ (x ∩ T).card % 2 := by
  have htS : t ∈ S := (Finset.mem_inter.mp (by rw [hST]; exact Finset.mem_singleton_self t)).1
  have htT : t ∈ T := (Finset.mem_inter.mp (by rw [hST]; exact Finset.mem_singleton_self t)).2
  have hother : ∀ i : Site n, i ∈ T → i ≠ t → i ∉ S := by
    intro i hiT hit hiS
    have hmem : i ∈ S ∩ T := Finset.mem_inter.mpr ⟨hiS, hiT⟩
    rw [hST, Finset.mem_singleton] at hmem
    exact hit hmem
  by_cases htx : t ∈ x
  · have heq : flipSet x S ∩ T = (x ∩ T).erase t := by
      ext i
      by_cases hit : i = t
      · subst hit
        simp [flipSet, htx, htS]
      · by_cases hiT : i ∈ T
        · have hiS : i ∉ S := hother i hiT hit
          simp [flipSet, hiT, hiS, hit]
        · simp [hiT]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨htx, htT⟩)]
    have hpos : 0 < (x ∩ T).card := Finset.card_pos.mpr ⟨t, Finset.mem_inter.mpr ⟨htx, htT⟩⟩
    omega
  · have heq : flipSet x S ∩ T = insert t (x ∩ T) := by
      ext i
      by_cases hit : i = t
      · subst hit
        simp [flipSet, htx, htS, htT]
      · by_cases hiT : i ∈ T
        · have hiS : i ∉ S := hother i hiT hit
          simp [flipSet, hiT, hiS, hit]
        · simp [hiT, hit]
    rw [heq, Finset.card_insert_of_notMem (by simp [htx])]
    omega

/-! ### Part B: Edge labels and solution structure on the cycle -/

def isO {n : ℕ} (x : Bits n) (q : Signing n) (i : Site n) : Prop :=
  q i = (!(decide (i ∈ x)), !(decide ((i + 1 : Site n) ∈ x)))

def isL {n : ℕ} (x : Bits n) (q : Signing n) (i : Site n) : Prop :=
  q i = (!(decide (i ∈ x)), decide ((i + 1 : Site n) ∈ x))

def isR {n : ℕ} (x : Bits n) (q : Signing n) (i : Site n) : Prop :=
  q i = (decide (i ∈ x), !(decide ((i + 1 : Site n) ∈ x)))

lemma isO_not_isL {n : ℕ} {x : Bits n} {q : Signing n} {i : Site n}
    (h : isO x q i) : ¬ isL x q i := by
  intro hL
  have heq := h.symm.trans hL
  have h2 := congrArg Prod.snd heq
  cases h1 : decide ((i + 1 : Site n) ∈ x) <;> simp [h1] at h2

lemma isO_not_isR {n : ℕ} {x : Bits n} {q : Signing n} {i : Site n}
    (h : isO x q i) : ¬ isR x q i := by
  intro hR
  have heq := h.symm.trans hR
  have h1 := congrArg Prod.fst heq
  cases hb : decide (i ∈ x) <;> simp [hb] at h1

lemma isL_not_isO {n : ℕ} {x : Bits n} {q : Signing n} {i : Site n}
    (h : isL x q i) : ¬ isO x q i := fun hO => isO_not_isL hO h

lemma isL_not_isR {n : ℕ} {x : Bits n} {q : Signing n} {i : Site n}
    (h : isL x q i) : ¬ isR x q i := by
  intro hR
  have heq := h.symm.trans hR
  have h1 := congrArg Prod.fst heq
  cases hb : decide (i ∈ x) <;> simp [hb] at h1

lemma isR_not_isO {n : ℕ} {x : Bits n} {q : Signing n} {i : Site n}
    (h : isR x q i) : ¬ isO x q i := fun hO => isO_not_isR hO h

lemma isR_not_isL {n : ℕ} {x : Bits n} {q : Signing n} {i : Site n}
    (h : isR x q i) : ¬ isL x q i := fun hL => isL_not_isR hL h

lemma isO_or_isL_or_isR {n : ℕ} {x : Bits n} {q : Signing n} (hsat : sat x q) (i : Site n) :
    isO x q i ∨ isL x q i ∨ isR x q i := by
  have hne := hsat i
  rcases hq : q i with ⟨a, b⟩
  rw [hq] at hne
  dsimp only [isO, isL, isR]
  rw [hq]
  cases ha : a <;> cases hb : b <;>
    cases hx1 : decide (i ∈ x) <;> cases hx2 : decide ((i + 1 : Site n) ∈ x) <;>
    simp_all

lemma sat_flipSet_of_conds {n : ℕ} {x S : Bits n} {q : Signing n} (hsat : sat x q)
    (hO : ∀ i : Site n, i ∈ S → (i + 1 : Site n) ∈ S → ¬ isO x q i)
    (hL : ∀ i : Site n, i ∈ S → (i + 1 : Site n) ∉ S → ¬ isL x q i)
    (hR : ∀ i : Site n, i ∉ S → (i + 1 : Site n) ∈ S → ¬ isR x q i) :
    sat (flipSet x S) q := by
  intro i
  rw [decide_mem_flipSet, decide_mem_flipSet]
  by_cases hi : i ∈ S <;> by_cases hi1 : (i + 1 : Site n) ∈ S
  · have h := hO i hi hi1
    dsimp only [isO] at h
    simpa [hi, hi1] using Ne.symm h
  · have h := hL i hi hi1
    dsimp only [isL] at h
    simpa [hi, hi1] using Ne.symm h
  · have h := hR i hi hi1
    dsimp only [isR] at h
    simpa [hi, hi1] using Ne.symm h
  · simpa [hi, hi1] using hsat i

def addNat {n : ℕ} (i : Site n) : ℕ → Site n
  | 0 => i
  | d + 1 => addNat i d + 1

def subNat {n : ℕ} (i : Site n) : ℕ → Site n
  | 0 => i
  | d + 1 => subNat i d - 1

lemma addNat_val {n : ℕ} (i : Site n) (d : ℕ) :
    (addNat i d).val = (i.val + d) % (n + 2) := by
  induction d with
  | zero => simp [addNat, Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
    change ((addNat i d).val + (1 : Site n).val) % (n + 2) = _
    have h1 : (1 : Site n).val = 1 := Fin.val_one' (n + 2)
    rw [ih, h1, Nat.mod_add_mod, Nat.add_assoc]

lemma addNat_eq_add {n : ℕ} (i b : Site n) : addNat i b.val = i + b := by
  apply Fin.ext
  rw [addNat_val, Fin.val_add]

lemma subNat_add_addNat {n : ℕ} (i : Site n) (d : ℕ) :
    subNat i d + addNat (0 : Site n) d = i := by
  induction d with
  | zero => simp [subNat, addNat]
  | succ d ih =>
    change (subNat i d - 1) + (addNat 0 d + 1) = i
    calc (subNat i d - 1) + (addNat 0 d + 1) = subNat i d + addNat 0 d := by abel
      _ = i := ih

lemma subNat_eq_sub {n : ℕ} (i b : Site n) : subNat i b.val = i - b := by
  have h := subNat_add_addNat i b.val
  have h0 : addNat (0 : Site n) b.val = b := by rw [addNat_eq_add, zero_add]
  rw [h0] at h
  exact eq_sub_of_add_eq h

def allLSigning {n : ℕ} (x : Bits n) : Signing n :=
  fun i => (!(decide (i ∈ x)), decide ((i + 1 : Site n) ∈ x))

lemma sat_of_allL {n : ℕ} {x y : Bits n} {q : Signing n} (hall : ∀ i, isL x q i) :
    sat y q ↔ y = x ∨ y = comp x := by
  constructor
  · intro hsat
    have hstep : ∀ i : Site n, decide (i ∈ y) ≠ decide (i ∈ x) →
        decide ((i + 1 : Site n) ∈ y) ≠ decide ((i + 1 : Site n) ∈ x) := by
      intro i hne hEq
      have hqi := hall i
      dsimp only [isL] at hqi
      have hne' := hsat i
      rw [hqi, hEq] at hne'
      cases hy : decide (i ∈ y) <;> cases hx : decide (i ∈ x) <;> simp_all
    have hwalk : ∀ (i : Site n) (d : ℕ), decide (i ∈ y) ≠ decide (i ∈ x) →
        decide (addNat i d ∈ y) ≠ decide (addNat i d ∈ x) := by
      intro i d h0
      induction d with
      | zero => exact h0
      | succ d ih => exact hstep _ ih
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      have hex : ∃ i : Site n, decide (i ∈ y) ≠ decide (i ∈ x) := by
        by_contra hall_eq
        push Not at hall_eq
        apply hxy
        ext i
        have hi := hall_eq i
        simpa [decide_eq_decide] using hi
      rcases hex with ⟨i, hi⟩
      ext j
      rw [mem_comp_iff]
      have hcast : addNat i (j - i).val = j := by rw [addNat_eq_add]; abel
      have hj := hwalk i (j - i).val hi
      rw [hcast] at hj
      cases hjy : decide (j ∈ y) <;> cases hjx : decide (j ∈ x) <;> simp_all
  · rintro (rfl | rfl)
    · intro i
      rw [hall i]
      intro h
      have h1 := congrArg Prod.fst h
      cases hb : decide (i ∈ y) <;> simp [hb] at h1
    · intro i
      rw [hall i]
      intro h
      have h2 := congrArg Prod.snd h
      have hmem : decide ((i + 1 : Site n) ∈ comp x) = !(decide ((i + 1 : Site n) ∈ x)) := by
        by_cases h' : (i + 1 : Site n) ∈ x <;> simp [mem_comp_iff, h']
      rw [hmem] at h2
      cases hb : decide ((i + 1 : Site n) ∈ x) <;> simp [hb] at h2

lemma sat_of_allR {n : ℕ} {x y : Bits n} {q : Signing n} (hall : ∀ i, isR x q i) :
    sat y q ↔ y = x ∨ y = comp x := by
  constructor
  · intro hsat
    have hstep : ∀ i : Site n, decide ((i + 1 : Site n) ∈ y) ≠ decide ((i + 1 : Site n) ∈ x) →
        decide (i ∈ y) ≠ decide (i ∈ x) := by
      intro i hne hEq
      have hqi := hall i
      dsimp only [isR] at hqi
      have hne' := hsat i
      rw [hqi, hEq] at hne'
      cases hy : decide ((i + 1 : Site n) ∈ y) <;> cases hx : decide ((i + 1 : Site n) ∈ x) <;>
        simp_all
    have hwalk : ∀ (i : Site n) (d : ℕ), decide (i ∈ y) ≠ decide (i ∈ x) →
        decide (subNat i d ∈ y) ≠ decide (subNat i d ∈ x) := by
      intro i d h0
      induction d with
      | zero => exact h0
      | succ d ih =>
        have hcast : subNat i (d + 1) + 1 = subNat i d := by
          change (subNat i d - 1) + 1 = subNat i d; abel
        exact hstep (subNat i (d + 1)) (by rwa [hcast])
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      have hex : ∃ i : Site n, decide (i ∈ y) ≠ decide (i ∈ x) := by
        by_contra hall_eq
        push Not at hall_eq
        apply hxy
        ext i
        have hi := hall_eq i
        simpa [decide_eq_decide] using hi
      rcases hex with ⟨i, hi⟩
      ext j
      rw [mem_comp_iff]
      have hcast : subNat i (i - j).val = j := by rw [subNat_eq_sub]; abel
      have hj := hwalk i (i - j).val hi
      rw [hcast] at hj
      cases hjy : decide (j ∈ y) <;> cases hjx : decide (j ∈ x) <;> simp_all
  · rintro (rfl | rfl)
    · intro i
      rw [hall i]
      intro h
      have h2 := congrArg Prod.snd h
      cases hb : decide ((i + 1 : Site n) ∈ y) <;> simp [hb] at h2
    · intro i
      rw [hall i]
      intro h
      have h1 := congrArg Prod.fst h
      have hmem : decide (i ∈ comp x) = !(decide (i ∈ x)) := by
        by_cases h' : i ∈ x <;> simp [mem_comp_iff, h']
      rw [hmem] at h1
      cases hb : decide (i ∈ x) <;> simp [hb] at h1

lemma sat_allLSigning {n : ℕ} (x y : Bits n) :
    sat y (allLSigning x) ↔ y = x ∨ y = comp x :=
  sat_of_allL (fun _ => rfl)

lemma fin_add_one_eq_mk {n : ℕ} (m : Site n) (hm : m.val + 1 < n + 2) :
    m + 1 = ⟨m.val + 1, hm⟩ := by
  apply Fin.ext
  change (m.val + (1 : Site n).val) % (n + 2) = m.val + 1
  have h1 : (1 : Site n).val = 1 := Fin.val_one' (n + 2)
  rw [h1, Nat.mod_eq_of_lt hm]

lemma fin_last_add_one {n : ℕ} (m : Site n) (hm : m.val = n + 1) :
    m + 1 = 0 := by
  apply Fin.ext
  change (m.val + (1 : Site n).val) % (n + 2) = 0
  have h1 : (1 : Site n).val = 1 := Fin.val_one' (n + 2)
  rw [h1, hm]
  simp

lemma one_ne_zero_site (n : ℕ) : (1 : Site n) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  have h1 : (1 : Site n).val = 1 := Fin.val_one' (n + 2)
  rw [h1] at hv
  exact Nat.one_ne_zero hv

lemma exists_odd_flip_of_not_allL_not_allR {n : ℕ} (x : Bits n) (q : Signing n)
    (hsat : sat x q) (T : Bits n) (hTne : T.Nonempty) (hTeven : Even T.card)
    (hnotL : ¬ ∀ i, isL x q i) (hnotR : ¬ ∀ i, isR x q i) :
    ∃ y : Bits n, sat y q ∧ (y ∩ T).card % 2 ≠ (x ∩ T).card % 2 := by
  classical
  have hT2 : 2 ≤ T.card := by
    rcases hTeven with ⟨c, hc⟩
    have hpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega
  by_cases hO_ex : ∃ i₀ : Site n, isO x q i₀
  · -- Case 1: there is an O edge i0; re-index linearly starting at base = i0 + 1
    rcases hO_ex with ⟨i₀, hi₀O⟩
    let base : Site n := i₀ + 1
    let v : Site n → Site n := fun m => base + m
    have hv_bij : Function.Bijective v := by
      refine ⟨fun a b h => add_left_cancel h, fun j => ⟨j - base, by simp [v]⟩⟩
    have hv_last : v ⟨n + 1, by omega⟩ = i₀ := by
      dsimp only [v, base]
      have hlast : (⟨n + 1, by omega⟩ : Site n) + 1 = 0 := fin_last_add_one _ rfl
      calc i₀ + 1 + ⟨n + 1, by omega⟩ = i₀ + (⟨n + 1, by omega⟩ + 1) := by abel
        _ = i₀ + 0 := by rw [hlast]
        _ = i₀ := add_zero i₀
    let T_idx : Finset (Site n) := Finset.univ.filter (fun m => v m ∈ T)
    have hT_card : T_idx.card = T.card := by
      refine Finset.card_bij (fun m _ => v m) ?_ ?_ ?_
      · intro m hm; exact (Finset.mem_filter.mp hm).2
      · intro a _ b _ h; exact hv_bij.1 h
      · intro t ht
        rcases hv_bij.2 t with ⟨m, rfl⟩
        exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
    have hT_idx_ne : T_idx.Nonempty := Finset.card_pos.mp (by omega)
    let p := T_idx.min' hT_idx_ne
    let q_max := T_idx.max' hT_idx_ne
    have hp_mem : p ∈ T_idx := Finset.min'_mem T_idx hT_idx_ne
    have hq_mem : q_max ∈ T_idx := Finset.max'_mem T_idx hT_idx_ne
    have hp_lt_q : p < q_max := by
      have hle : p ≤ q_max := Finset.min'_le T_idx q_max hq_mem
      have hne : p ≠ q_max := by
        intro heq
        have hsub : T_idx ⊆ {p} := by
          intro t ht
          rw [Finset.mem_singleton]
          have h1 : p ≤ t := Finset.min'_le T_idx t ht
          have h2 : t ≤ q_max := Finset.le_max' T_idx t ht
          rw [← heq] at h2
          exact le_antisymm h2 h1
        have hle1 : T_idx.card ≤ 1 := by
          calc T_idx.card ≤ ({p} : Finset (Site n)).card := Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton p
        omega
      exact lt_of_le_of_ne hle hne
    let B : Finset (Site n) :=
      Finset.univ.filter (fun b => p ≤ b ∧ ∀ m : Site n, p ≤ m → m < b → isL x q (v m))
    have hB_ne : B.Nonempty :=
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, fun _ h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)⟩⟩
    let b := B.max' hB_ne
    have hb_mem : b ∈ B := Finset.max'_mem B hB_ne
    have hb_ge : p ≤ b := (Finset.mem_filter.mp hb_mem).2.1
    have hb_L : ∀ m : Site n, p ≤ m → m < b → isL x q (v m) := (Finset.mem_filter.mp hb_mem).2.2
    have hb_stop : b.val + 1 < n + 2 → ¬ isL x q (v b) := by
      intro hlt hLb
      let b' : Site n := ⟨b.val + 1, hlt⟩
      have hb'_mem : b' ∈ B := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · exact le_trans hb_ge (Fin.le_iff_val_le_val.mpr (by dsimp only [b']; omega))
        · intro m hpm hmb'
          have hmv : m.val ≤ b.val := by
            have := Fin.lt_iff_val_lt_val.mp hmb'
            dsimp only [b'] at this
            omega
          rcases Nat.lt_or_eq_of_le hmv with hltm | heqm
          · exact hb_L m hpm (Fin.lt_iff_val_lt_val.mpr hltm)
          · have : m = b := Fin.ext heqm
            rwa [this]
      have hle := Finset.le_max' B b' hb'_mem
      have := Fin.le_iff_val_le_val.mp hle
      dsimp only [b'] at this
      omega
    let Mid := T_idx.filter (fun t => p < t ∧ t ≤ b)
    by_cases hMid : Mid.Nonempty
    · -- Subcase 1a: r = max Mid, S = {v m | r <= m <= b}
      let r := Mid.max' hMid
      have hr_mem : r ∈ Mid := Finset.max'_mem Mid hMid
      have hr_T : r ∈ T_idx := (Finset.mem_filter.mp hr_mem).1
      have hp_lt_r : p < r := (Finset.mem_filter.mp hr_mem).2.1
      have hr_le_b : r ≤ b := (Finset.mem_filter.mp hr_mem).2.2
      let S : Bits n := Finset.univ.filter (fun j => r ≤ j - base ∧ j - base ≤ b)
      have hST : S ∩ T = {v r} := by
        ext j
        constructor
        · intro hj
          rcases Finset.mem_inter.mp hj with ⟨hjS, hjT⟩
          rcases Finset.mem_filter.mp hjS with ⟨_, hlo, hhi⟩
          let m := j - base
          have hvm : v m = j := by simp [v, m]
          have hmT : m ∈ T_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm.symm ▸ hjT⟩
          have hmMid : m ∈ Mid := Finset.mem_filter.mpr ⟨hmT, lt_of_lt_of_le hp_lt_r hlo, hhi⟩
          have hmr : m ≤ r := Finset.le_max' Mid m hmMid
          have heq : m = r := le_antisymm hmr hlo
          rw [Finset.mem_singleton, ← hvm, heq]
        · intro hj
          rw [Finset.mem_singleton] at hj
          subst hj
          refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, (Finset.mem_filter.mp hr_T).2⟩
          simp [v, hr_le_b]
      have hsat_y : sat (flipSet x S) q := by
        refine sat_flipSet_of_conds hsat ?_ ?_ ?_
        · intro i hi hi1
          let m := i - base
          have hvm : v m = i := by simp [v, m]
          rcases Finset.mem_filter.mp hi with ⟨_, hm_lo, hm_hi⟩
          rcases Finset.mem_filter.mp hi1 with ⟨_, hm1_lo, _⟩
          by_cases hlast : m.val = n + 1
          · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
            have hi1_sub : (i + 1 : Site n) - base = 0 := by
              rw [← hvm, hm_eq]
              have h1 : v ⟨n + 1, by omega⟩ + 1 = base := by
                rw [hv_last]
              rw [h1, sub_self]
            rw [hi1_sub] at hm1_lo
            have h0lt : (0 : Site n) < r := lt_of_le_of_lt (Fin.zero_le p) hp_lt_r
            exact absurd (lt_of_lt_of_le h0lt hm1_lo) (lt_irrefl _)
          · have hlt : m.val + 1 < n + 2 := by omega
            have hm_lt_b : m < b := by
              have hi1_sub : (i + 1 : Site n) - base = ⟨m.val + 1, hlt⟩ := by
                have h1 : (i + 1 : Site n) - base = m + 1 := by simp [m]; abel
                rw [h1, fin_add_one_eq_mk m hlt]
              have hm1_hi : (i + 1 : Site n) - base ≤ b := (Finset.mem_filter.mp hi1).2.2
              rw [hi1_sub] at hm1_hi
              exact Fin.lt_iff_val_lt_val.mpr (by have := Fin.le_iff_val_le_val.mp hm1_hi; dsimp at this; omega)
            rw [← hvm]
            exact isL_not_isO (hb_L m (le_of_lt (lt_of_lt_of_le hp_lt_r hm_lo)) hm_lt_b)
        · intro i hi hi1
          let m := i - base
          have hvm : v m = i := by simp [v, m]
          rcases Finset.mem_filter.mp hi with ⟨_, hm_lo, hm_hi⟩
          by_cases hlast : m.val = n + 1
          · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
            rw [← hvm, hm_eq, hv_last]
            exact isO_not_isL hi₀O
          · have hlt : m.val + 1 < n + 2 := by omega
            have hi1_sub : (i + 1 : Site n) - base = ⟨m.val + 1, hlt⟩ := by
              have h1 : (i + 1 : Site n) - base = m + 1 := by simp [m]; abel
              rw [h1, fin_add_one_eq_mk m hlt]
            have hnot : ¬ (r ≤ (⟨m.val + 1, hlt⟩ : Site n) ∧ (⟨m.val + 1, hlt⟩ : Site n) ≤ b) := by
              intro h; apply hi1; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hi1_sub]⟩
            have hlo1 : r ≤ (⟨m.val + 1, hlt⟩ : Site n) :=
              Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm_lo; dsimp; omega)
            have hgt : b.val < m.val + 1 := by
              by_contra hle; push Not at hle
              exact hnot ⟨hlo1, Fin.le_iff_val_le_val.mpr hle⟩
            have hmb : m = b := Fin.ext (by have := Fin.le_iff_val_le_val.mp hm_hi; omega)
            rw [← hvm, hmb]
            exact hb_stop (by rwa [← hmb])
        · intro i hi hi1
          let m := i - base
          have hvm : v m = i := by simp [v, m]
          rcases Finset.mem_filter.mp hi1 with ⟨_, hm1_lo, hm1_hi⟩
          by_cases hlast : m.val = n + 1
          · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
            rw [← hvm, hm_eq, hv_last]
            exact isO_not_isR hi₀O
          · have hlt : m.val + 1 < n + 2 := by omega
            have hi1_sub : (i + 1 : Site n) - base = ⟨m.val + 1, hlt⟩ := by
              have h1 : (i + 1 : Site n) - base = m + 1 := by simp [m]; abel
              rw [h1, fin_add_one_eq_mk m hlt]
            rw [hi1_sub] at hm1_lo hm1_hi
            have hnot : ¬ (r ≤ m ∧ m ≤ b) := by
              intro h; apply hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
            have hhi_m : m ≤ b :=
              Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm1_hi; dsimp at this; omega)
            have hmltr : m.val < r.val := by
              by_contra hge; push Not at hge
              exact hnot ⟨Fin.le_iff_val_le_val.mpr hge, hhi_m⟩
            have hm1eq : m.val + 1 = r.val := by
              have := Fin.le_iff_val_le_val.mp hm1_lo; dsimp at this; omega
            have hpm : p ≤ m :=
              Fin.le_iff_val_le_val.mpr (by have := Fin.lt_iff_val_lt_val.mp hp_lt_r; omega)
            have hmb : m < b :=
              Fin.lt_iff_val_lt_val.mpr (by have := Fin.le_iff_val_le_val.mp hr_le_b; omega)
            rw [← hvm]
            exact isL_not_isR (hb_L m hpm hmb)
      exact ⟨flipSet x S, hsat_y, flipSet_parity_of_inter_singleton x S T (v r) hST⟩
    · -- Subcase 1b: Mid = empty, so b < q_max <= n+1, S = {v m | a <= m <= b}
      have hb_lt_q : b < q_max := by
        by_contra hge; push Not at hge
        exact hMid ⟨q_max, Finset.mem_filter.mpr ⟨hq_mem, hp_lt_q, hge⟩⟩
      have hb_lt_N : b.val + 1 < n + 2 := by
        have := Fin.lt_iff_val_lt_val.mp hb_lt_q
        omega
      let A_set : Finset (Site n) :=
        Finset.univ.filter (fun a => a ≤ p ∧ ∀ m : Site n, a ≤ m → m < p → isR x q (v m))
      have hA_ne : A_set.Nonempty :=
        ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, fun _ h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)⟩⟩
      let a := A_set.min' hA_ne
      have ha_mem : a ∈ A_set := Finset.min'_mem A_set hA_ne
      have ha_le : a ≤ p := (Finset.mem_filter.mp ha_mem).2.1
      have ha_R : ∀ m : Site n, a ≤ m → m < p → isR x q (v m) := (Finset.mem_filter.mp ha_mem).2.2
      have ha_stop : ∀ (m : Site n), m.val + 1 = a.val → ¬ isR x q (v m) := by
        intro m hma hRm
        have hm_mem : m ∈ A_set := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) ha_le
          · intro k hmk hkp
            have hkv : a.val ≤ k.val ∨ k.val = m.val := by
              have := Fin.le_iff_val_le_val.mp hmk; omega
            rcases hkv with hge | heq
            · exact ha_R k (Fin.le_iff_val_le_val.mpr hge) hkp
            · have : k = m := Fin.ext heq
              rwa [this]
        have hle := Finset.min'_le A_set m hm_mem
        have := Fin.le_iff_val_le_val.mp hle
        omega
      let S : Bits n := Finset.univ.filter (fun j => a ≤ j - base ∧ j - base ≤ b)
      have hST : S ∩ T = {v p} := by
        ext j
        constructor
        · intro hj
          rcases Finset.mem_inter.mp hj with ⟨hjS, hjT⟩
          rcases Finset.mem_filter.mp hjS with ⟨_, _, hhi⟩
          let m := j - base
          have hvm : v m = j := by simp [v, m]
          have hmT : m ∈ T_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm.symm ▸ hjT⟩
          have hpm : p ≤ m := Finset.min'_le T_idx m hmT
          have heq : m = p := by
            by_contra hne
            have hlt : p < m := lt_of_le_of_ne hpm (Ne.symm hne)
            exact hMid ⟨m, Finset.mem_filter.mpr ⟨hmT, hlt, hhi⟩⟩
          rw [Finset.mem_singleton, ← hvm, heq]
        · intro hj
          rw [Finset.mem_singleton] at hj
          subst hj
          refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, (Finset.mem_filter.mp hp_mem).2⟩
          simp [v, ha_le, hb_ge]
      have hsat_y : sat (flipSet x S) q := by
        refine sat_flipSet_of_conds hsat ?_ ?_ ?_
        · intro i hi hi1
          let m := i - base
          have hvm : v m = i := by simp [v, m]
          rcases Finset.mem_filter.mp hi with ⟨_, hm_lo, hm_hi⟩
          have hnotlast : m.val ≠ n + 1 := by
            have := Fin.le_iff_val_le_val.mp hm_hi; omega
          have hlt : m.val + 1 < n + 2 := by omega
          have hm_lt_b : m < b := by
            have hi1_sub : (i + 1 : Site n) - base = ⟨m.val + 1, hlt⟩ := by
              have h1 : (i + 1 : Site n) - base = m + 1 := by simp [m]; abel
              rw [h1, fin_add_one_eq_mk m hlt]
            have hm1_hi : (i + 1 : Site n) - base ≤ b := (Finset.mem_filter.mp hi1).2.2
            rw [hi1_sub] at hm1_hi
            exact Fin.lt_iff_val_lt_val.mpr (by have := Fin.le_iff_val_le_val.mp hm1_hi; dsimp at this; omega)
          rw [← hvm]
          by_cases hmp : m < p
          · exact isR_not_isO (ha_R m hm_lo hmp)
          · push Not at hmp
            exact isL_not_isO (hb_L m hmp hm_lt_b)
        · intro i hi hi1
          let m := i - base
          have hvm : v m = i := by simp [v, m]
          rcases Finset.mem_filter.mp hi with ⟨_, hm_lo, hm_hi⟩
          have hnotlast : m.val ≠ n + 1 := by
            have := Fin.le_iff_val_le_val.mp hm_hi; omega
          have hlt : m.val + 1 < n + 2 := by omega
          have hi1_sub : (i + 1 : Site n) - base = ⟨m.val + 1, hlt⟩ := by
            have h1 : (i + 1 : Site n) - base = m + 1 := by simp [m]; abel
            rw [h1, fin_add_one_eq_mk m hlt]
          have hnot : ¬ (a ≤ (⟨m.val + 1, hlt⟩ : Site n) ∧ (⟨m.val + 1, hlt⟩ : Site n) ≤ b) := by
            intro h; apply hi1; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hi1_sub]⟩
          have hlo1 : a ≤ (⟨m.val + 1, hlt⟩ : Site n) :=
            Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm_lo; dsimp; omega)
          have hgt : b.val < m.val + 1 := by
            by_contra hle; push Not at hle
            exact hnot ⟨hlo1, Fin.le_iff_val_le_val.mpr hle⟩
          have hmb : m = b := Fin.ext (by have := Fin.le_iff_val_le_val.mp hm_hi; omega)
          rw [← hvm, hmb]
          exact hb_stop hb_lt_N
        · intro i hi hi1
          let m := i - base
          have hvm : v m = i := by simp [v, m]
          rcases Finset.mem_filter.mp hi1 with ⟨_, hm1_lo, hm1_hi⟩
          by_cases hlast : m.val = n + 1
          · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
            rw [← hvm, hm_eq, hv_last]
            exact isO_not_isR hi₀O
          · have hlt : m.val + 1 < n + 2 := by omega
            have hi1_sub : (i + 1 : Site n) - base = ⟨m.val + 1, hlt⟩ := by
              have h1 : (i + 1 : Site n) - base = m + 1 := by simp [m]; abel
              rw [h1, fin_add_one_eq_mk m hlt]
            rw [hi1_sub] at hm1_lo hm1_hi
            have hnot : ¬ (a ≤ m ∧ m ≤ b) := by
              intro h; apply hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
            have hhi_m : m ≤ b :=
              Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm1_hi; dsimp at this; omega)
            have hmlta : m.val < a.val := by
              by_contra hge; push Not at hge
              exact hnot ⟨Fin.le_iff_val_le_val.mpr hge, hhi_m⟩
            have hm1eq : m.val + 1 = a.val := by
              have := Fin.le_iff_val_le_val.mp hm1_lo; dsimp at this; omega
            rw [← hvm]
            exact ha_stop m hm1eq
      exact ⟨flipSet x S, hsat_y, flipSet_parity_of_inter_singleton x S T (v p) hST⟩
  · -- Case 2: no O edge; every edge is L or R, and both L and R occur
    push Not at hO_ex
    have hLR : ∀ i : Site n, isL x q i ∨ isR x q i := fun i =>
      (isO_or_isL_or_isR hsat i).resolve_left (hO_ex i)
    have hexL : ∃ i₁ : Site n, isL x q i₁ := by
      by_contra hno; push Not at hno
      exact hnotR fun i => (hLR i).resolve_left (hno i)
    have hexR : ∃ i₂ : Site n, isR x q i₂ := by
      by_contra hno; push Not at hno
      exact hnotL fun i => (hLR i).resolve_right (hno i)
    rcases hexL with ⟨i₁, hi₁L⟩
    rcases hexR with ⟨i₂, hi₂R⟩
    -- Find a sink v0 where isL (v0 - 1) and isR v0
    have hex_d : ∃ d : ℕ, isR x q (addNat i₁ d) := by
      refine ⟨(i₂ - i₁).val, ?_⟩
      have hcast : addNat i₁ (i₂ - i₁).val = i₂ := by rw [addNat_eq_add]; abel
      rwa [hcast]
    let d₀ := Nat.find hex_d
    have hd₀R : isR x q (addNat i₁ d₀) := Nat.find_spec hex_d
    have hd₀_pos : 0 < d₀ := by
      by_contra h0
      have hd0 : d₀ = 0 := by omega
      rw [hd0] at hd₀R
      exact isL_not_isR hi₁L hd₀R
    let v₀ : Site n := addNat i₁ d₀
    have hv₀_prev_L : isL x q (v₀ - 1) := by
      have hlt : d₀ - 1 < d₀ := by omega
      have hnotR' : ¬ isR x q (addNat i₁ (d₀ - 1)) := Nat.find_min hex_d hlt
      have heq : addNat i₁ (d₀ - 1) = v₀ - 1 := by
        dsimp only [v₀]
        have h1 : d₀ = (d₀ - 1) + 1 := by omega
        have h2 : addNat i₁ d₀ = addNat i₁ (d₀ - 1) + 1 := by
          conv_lhs => rw [h1]
          rfl
        rw [h2]; abel
      rw [heq] at hnotR'
      exact (hLR (v₀ - 1)).resolve_right hnotR'
    by_cases hv₀T : v₀ ∈ T
    · -- Subcase 2.0: sink v0 in T, S = {v0}
      let S : Bits n := {v₀}
      have hST : S ∩ T = {v₀} := by
        ext j; simp [S, hv₀T]
      have hsat_y : sat (flipSet x S) q := by
        refine sat_flipSet_of_conds hsat ?_ ?_ ?_
        · intro i _ _; exact hO_ex i
        · intro i hi hi1
          have hiv : i = v₀ := Finset.mem_singleton.mp hi
          subst hiv
          exact isR_not_isL hd₀R
        · intro i hi hi1
          have hiv : i + 1 = v₀ := Finset.mem_singleton.mp hi1
          have hi_eq : i = v₀ - 1 := eq_sub_of_add_eq hiv
          subst hi_eq
          exact isL_not_isR hv₀_prev_L
      exact ⟨flipSet x S, hsat_y, flipSet_parity_of_inter_singleton x S T v₀ hST⟩
    · -- Subcase 2.1: sink v0 not in T
      let v : Site n → Site n := fun m => v₀ + m
      have hv_bij : Function.Bijective v :=
        ⟨fun a b h => add_left_cancel h, fun j => ⟨j - v₀, by simp [v]⟩⟩
      have hv_last : v ⟨n + 1, by omega⟩ = v₀ - 1 := by
        dsimp only [v]
        have hlast : (⟨n + 1, by omega⟩ : Site n) + 1 = 0 := fin_last_add_one _ rfl
        calc v₀ + ⟨n + 1, by omega⟩ = v₀ + (⟨n + 1, by omega⟩ + 1) - 1 := by abel
          _ = v₀ + 0 - 1 := by rw [hlast]
          _ = v₀ - 1 := by simp
      let T_idx : Finset (Site n) := Finset.univ.filter (fun m => v m ∈ T)
      have hT_card : T_idx.card = T.card := by
        refine Finset.card_bij (fun m _ => v m) ?_ ?_ ?_
        · intro m hm; exact (Finset.mem_filter.mp hm).2
        · intro a _ b _ h; exact hv_bij.1 h
        · intro t ht
          rcases hv_bij.2 t with ⟨m, rfl⟩
          exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
      have hT_idx_ne : T_idx.Nonempty := Finset.card_pos.mp (by omega)
      have h0_not_T : (0 : Site n) ∉ T_idx := by
        intro h0
        have := (Finset.mem_filter.mp h0).2
        simp [v] at this
        exact hv₀T this
      let p := T_idx.min' hT_idx_ne
      let q_max := T_idx.max' hT_idx_ne
      have hp_mem : p ∈ T_idx := Finset.min'_mem T_idx hT_idx_ne
      have hq_mem : q_max ∈ T_idx := Finset.max'_mem T_idx hT_idx_ne
      have hp_pos : 0 < p.val := by
        have hne : p ≠ 0 := fun h => h0_not_T (h ▸ hp_mem)
        exact Nat.pos_of_ne_zero (fun hv => hne (Fin.ext hv))
      have hp_lt_q : p < q_max := by
        have hle : p ≤ q_max := Finset.min'_le T_idx q_max hq_mem
        have hne : p ≠ q_max := by
          intro heq
          have hsub : T_idx ⊆ {p} := by
            intro t ht
            rw [Finset.mem_singleton]
            have h1 : p ≤ t := Finset.min'_le T_idx t ht
            have h2 : t ≤ q_max := Finset.le_max' T_idx t ht
            rw [← heq] at h2
            exact le_antisymm h2 h1
          have hle1 : T_idx.card ≤ 1 := by
            calc T_idx.card ≤ ({p} : Finset (Site n)).card := Finset.card_le_card hsub
              _ = 1 := Finset.card_singleton p
          omega
        exact lt_of_le_of_ne hle hne
      let B : Finset (Site n) :=
        Finset.univ.filter (fun b => p ≤ b ∧ ∀ m : Site n, p ≤ m → m < b → isL x q (v m))
      have hB_ne : B.Nonempty :=
        ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, fun _ h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)⟩⟩
      let b := B.max' hB_ne
      have hb_mem : b ∈ B := Finset.max'_mem B hB_ne
      have hb_ge : p ≤ b := (Finset.mem_filter.mp hb_mem).2.1
      have hb_L : ∀ m : Site n, p ≤ m → m < b → isL x q (v m) := (Finset.mem_filter.mp hb_mem).2.2
      have hb_stop : b.val + 1 < n + 2 → ¬ isL x q (v b) := by
        intro hlt hLb
        let b' : Site n := ⟨b.val + 1, hlt⟩
        have hb'_mem : b' ∈ B := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · exact le_trans hb_ge (Fin.le_iff_val_le_val.mpr (by dsimp only [b']; omega))
          · intro m hpm hmb'
            have hmv : m.val ≤ b.val := by
              have := Fin.lt_iff_val_lt_val.mp hmb'
              dsimp only [b'] at this; omega
            rcases Nat.lt_or_eq_of_le hmv with hltm | heqm
            · exact hb_L m hpm (Fin.lt_iff_val_lt_val.mpr hltm)
            · have : m = b := Fin.ext heqm
              rwa [this]
        have hle := Finset.le_max' B b' hb'_mem
        have := Fin.le_iff_val_le_val.mp hle
        dsimp only [b'] at this; omega
      let Mid := T_idx.filter (fun t => p < t ∧ t ≤ b)
      by_cases hMid : Mid.Nonempty
      · let r := Mid.max' hMid
        have hr_mem : r ∈ Mid := Finset.max'_mem Mid hMid
        have hr_T : r ∈ T_idx := (Finset.mem_filter.mp hr_mem).1
        have hp_lt_r : p < r := (Finset.mem_filter.mp hr_mem).2.1
        have hr_le_b : r ≤ b := (Finset.mem_filter.mp hr_mem).2.2
        have hr_ge2 : 2 ≤ r.val := by
          have := Fin.lt_iff_val_lt_val.mp hp_lt_r; omega
        by_cases hb_last : b.val = n + 1
        · -- Subcase 2.1a-wrap: b = n + 1, S = insert v0 {v m | r <= m}
          let S : Bits n := Finset.univ.filter (fun j => j - v₀ = 0 ∨ r ≤ j - v₀)
          have hST : S ∩ T = {v r} := by
            ext j
            constructor
            · intro hj
              rcases Finset.mem_inter.mp hj with ⟨hjS, hjT⟩
              rcases (Finset.mem_filter.mp hjS).2 with h0 | hlo
              · have hjv : j = v₀ := sub_eq_zero.mp h0
                exact absurd (hjv ▸ hjT) hv₀T
              · let m := j - v₀
                have hvm : v m = j := by simp [v, m]
                have hmT : m ∈ T_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm.symm ▸ hjT⟩
                have hm_le_b : m ≤ b := Fin.le_iff_val_le_val.mpr (by omega)
                have hmMid : m ∈ Mid := Finset.mem_filter.mpr ⟨hmT, lt_of_lt_of_le hp_lt_r hlo, hm_le_b⟩
                have hmr : m ≤ r := Finset.le_max' Mid m hmMid
                have heq : m = r := le_antisymm hmr hlo
                rw [Finset.mem_singleton, ← hvm, heq]
            · intro hj
              rw [Finset.mem_singleton] at hj
              subst hj
              refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, (Finset.mem_filter.mp hr_T).2⟩
              right; simp [v]
          have hsat_y : sat (flipSet x S) q := by
            refine sat_flipSet_of_conds hsat ?_ ?_ ?_
            · intro i _ _; exact hO_ex i
            · intro i hi hi1
              let m := i - v₀
              have hvm : v m = i := by simp [v, m]
              rcases (Finset.mem_filter.mp hi).2 with hm0 | hmlo
              · have hiv : i = v₀ := sub_eq_zero.mp hm0
                subst hiv; exact isR_not_isL hd₀R
              · by_cases hlast : m.val = n + 1
                · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
                  have hi1_sub : (i + 1 : Site n) - v₀ = 0 := by
                    rw [← hvm, hm_eq, hv_last]; abel
                  exfalso; apply hi1
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hi1_sub⟩
                · have hlt : m.val + 1 < n + 2 := by omega
                  have hi1_sub : (i + 1 : Site n) - v₀ = ⟨m.val + 1, hlt⟩ := by
                    have h1 : (i + 1 : Site n) - v₀ = m + 1 := by simp [m]; abel
                    rw [h1, fin_add_one_eq_mk m hlt]
                  exfalso; apply hi1
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
                  rw [hi1_sub]
                  exact Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hmlo; dsimp; omega)
            · intro i hi hi1
              let m := i - v₀
              have hvm : v m = i := by simp [v, m]
              by_cases hlast : m.val = n + 1
              · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
                rw [← hvm, hm_eq, hv_last]; exact isL_not_isR hv₀_prev_L
              · have hlt : m.val + 1 < n + 2 := by omega
                have hi1_sub : (i + 1 : Site n) - v₀ = ⟨m.val + 1, hlt⟩ := by
                  have h1 : (i + 1 : Site n) - v₀ = m + 1 := by simp [m]; abel
                  rw [h1, fin_add_one_eq_mk m hlt]
                have hnot : ¬ (m = 0 ∨ r ≤ m) := by
                  intro h; apply hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
                rcases (Finset.mem_filter.mp hi1).2 with hm1_0 | hm1_lo
                · rw [hi1_sub] at hm1_0
                  have hv0 := congrArg Fin.val hm1_0
                  dsimp at hv0; omega
                · rw [hi1_sub] at hm1_lo
                  have hmltr : m.val < r.val := by
                    by_contra hge; push Not at hge
                    exact hnot (Or.inr (Fin.le_iff_val_le_val.mpr hge))
                  have hm1eq : m.val + 1 = r.val := by
                    have := Fin.le_iff_val_le_val.mp hm1_lo; dsimp at this; omega
                  have hpm : p ≤ m :=
                    Fin.le_iff_val_le_val.mpr (by have := Fin.lt_iff_val_lt_val.mp hp_lt_r; omega)
                  have hmb : m < b :=
                    Fin.lt_iff_val_lt_val.mpr (by omega)
                  rw [← hvm]
                  exact isL_not_isR (hb_L m hpm hmb)
          exact ⟨flipSet x S, hsat_y, flipSet_parity_of_inter_singleton x S T (v r) hST⟩
        · -- Subcase 2.1a-nowrap: b.val + 1 < n + 2, S = {v m | r <= m <= b}
          have hb_lt_N : b.val + 1 < n + 2 := by omega
          let S : Bits n := Finset.univ.filter (fun j => r ≤ j - v₀ ∧ j - v₀ ≤ b)
          have hST : S ∩ T = {v r} := by
            ext j
            constructor
            · intro hj
              rcases Finset.mem_inter.mp hj with ⟨hjS, hjT⟩
              rcases Finset.mem_filter.mp hjS with ⟨_, hlo, hhi⟩
              let m := j - v₀
              have hvm : v m = j := by simp [v, m]
              have hmT : m ∈ T_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm.symm ▸ hjT⟩
              have hmMid : m ∈ Mid := Finset.mem_filter.mpr ⟨hmT, lt_of_lt_of_le hp_lt_r hlo, hhi⟩
              have hmr : m ≤ r := Finset.le_max' Mid m hmMid
              have heq : m = r := le_antisymm hmr hlo
              rw [Finset.mem_singleton, ← hvm, heq]
            · intro hj
              rw [Finset.mem_singleton] at hj
              subst hj
              refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, (Finset.mem_filter.mp hr_T).2⟩
              simp [v, hr_le_b]
          have hsat_y : sat (flipSet x S) q := by
            refine sat_flipSet_of_conds hsat ?_ ?_ ?_
            · intro i _ _; exact hO_ex i
            · intro i hi hi1
              let m := i - v₀
              have hvm : v m = i := by simp [v, m]
              rcases Finset.mem_filter.mp hi with ⟨_, hm_lo, hm_hi⟩
              have hnotlast : m.val ≠ n + 1 := by
                have := Fin.le_iff_val_le_val.mp hm_hi; omega
              have hlt : m.val + 1 < n + 2 := by omega
              have hi1_sub : (i + 1 : Site n) - v₀ = ⟨m.val + 1, hlt⟩ := by
                have h1 : (i + 1 : Site n) - v₀ = m + 1 := by simp [m]; abel
                rw [h1, fin_add_one_eq_mk m hlt]
              have hnot : ¬ (r ≤ (⟨m.val + 1, hlt⟩ : Site n) ∧ (⟨m.val + 1, hlt⟩ : Site n) ≤ b) := by
                intro h; apply hi1; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hi1_sub]⟩
              have hlo1 : r ≤ (⟨m.val + 1, hlt⟩ : Site n) :=
                Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm_lo; dsimp; omega)
              have hgt : b.val < m.val + 1 := by
                by_contra hle; push Not at hle
                exact hnot ⟨hlo1, Fin.le_iff_val_le_val.mpr hle⟩
              have hmb : m = b := Fin.ext (by have := Fin.le_iff_val_le_val.mp hm_hi; omega)
              rw [← hvm, hmb]
              exact hb_stop hb_lt_N
            · intro i hi hi1
              let m := i - v₀
              have hvm : v m = i := by simp [v, m]
              rcases Finset.mem_filter.mp hi1 with ⟨_, hm1_lo, hm1_hi⟩
              by_cases hlast : m.val = n + 1
              · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
                rw [← hvm, hm_eq, hv_last]; exact isL_not_isR hv₀_prev_L
              · have hlt : m.val + 1 < n + 2 := by omega
                have hi1_sub : (i + 1 : Site n) - v₀ = ⟨m.val + 1, hlt⟩ := by
                  have h1 : (i + 1 : Site n) - v₀ = m + 1 := by simp [m]; abel
                  rw [h1, fin_add_one_eq_mk m hlt]
                rw [hi1_sub] at hm1_lo hm1_hi
                have hnot : ¬ (r ≤ m ∧ m ≤ b) := by
                  intro h; apply hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
                have hhi_m : m ≤ b :=
                  Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm1_hi; dsimp at this; omega)
                have hmltr : m.val < r.val := by
                  by_contra hge; push Not at hge
                  exact hnot ⟨Fin.le_iff_val_le_val.mpr hge, hhi_m⟩
                have hm1eq : m.val + 1 = r.val := by
                  have := Fin.le_iff_val_le_val.mp hm1_lo; dsimp at this; omega
                have hpm : p ≤ m :=
                  Fin.le_iff_val_le_val.mpr (by have := Fin.lt_iff_val_lt_val.mp hp_lt_r; omega)
                have hmb : m < b :=
                  Fin.lt_iff_val_lt_val.mpr (by have := Fin.le_iff_val_le_val.mp hr_le_b; omega)
                rw [← hvm]
                exact isL_not_isR (hb_L m hpm hmb)
          exact ⟨flipSet x S, hsat_y, flipSet_parity_of_inter_singleton x S T (v r) hST⟩
      · -- Subcase 2.1b: Mid = empty, b < q_max <= n+1, S = {v m | a <= m <= b}
        have hb_lt_q : b < q_max := by
          by_contra hge; push Not at hge
          exact hMid ⟨q_max, Finset.mem_filter.mpr ⟨hq_mem, hp_lt_q, hge⟩⟩
        have hb_lt_N : b.val + 1 < n + 2 := by
          have := Fin.lt_iff_val_lt_val.mp hb_lt_q; omega
        let A_set : Finset (Site n) :=
          Finset.univ.filter (fun a => a ≤ p ∧ ∀ m : Site n, a ≤ m → m < p → isR x q (v m))
        have hA_ne : A_set.Nonempty :=
          ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, fun _ h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)⟩⟩
        let a := A_set.min' hA_ne
        have ha_mem : a ∈ A_set := Finset.min'_mem A_set hA_ne
        have ha_le : a ≤ p := (Finset.mem_filter.mp ha_mem).2.1
        have ha_R : ∀ m : Site n, a ≤ m → m < p → isR x q (v m) := (Finset.mem_filter.mp ha_mem).2.2
        have ha_stop : ∀ (m : Site n), m.val + 1 = a.val → ¬ isR x q (v m) := by
          intro m hma hRm
          have hm_mem : m ∈ A_set := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) ha_le
            · intro k hmk hkp
              have hkv : a.val ≤ k.val ∨ k.val = m.val := by
                have := Fin.le_iff_val_le_val.mp hmk; omega
              rcases hkv with hge | heq
              · exact ha_R k (Fin.le_iff_val_le_val.mpr hge) hkp
              · have : k = m := Fin.ext heq
                rwa [this]
          have hle := Finset.min'_le A_set m hm_mem
          have := Fin.le_iff_val_le_val.mp hle; omega
        let S : Bits n := Finset.univ.filter (fun j => a ≤ j - v₀ ∧ j - v₀ ≤ b)
        have hST : S ∩ T = {v p} := by
          ext j
          constructor
          · intro hj
            rcases Finset.mem_inter.mp hj with ⟨hjS, hjT⟩
            rcases Finset.mem_filter.mp hjS with ⟨_, _, hhi⟩
            let m := j - v₀
            have hvm : v m = j := by simp [v, m]
            have hmT : m ∈ T_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm.symm ▸ hjT⟩
            have hpm : p ≤ m := Finset.min'_le T_idx m hmT
            have heq : m = p := by
              by_contra hne
              have hlt : p < m := lt_of_le_of_ne hpm (Ne.symm hne)
              exact hMid ⟨m, Finset.mem_filter.mpr ⟨hmT, hlt, hhi⟩⟩
            rw [Finset.mem_singleton, ← hvm, heq]
          · intro hj
            rw [Finset.mem_singleton] at hj
            subst hj
            refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, (Finset.mem_filter.mp hp_mem).2⟩
            simp [v, ha_le, hb_ge]
        have hsat_y : sat (flipSet x S) q := by
          refine sat_flipSet_of_conds hsat ?_ ?_ ?_
          · intro i _ _; exact hO_ex i
          · intro i hi hi1
            let m := i - v₀
            have hvm : v m = i := by simp [v, m]
            rcases Finset.mem_filter.mp hi with ⟨_, hm_lo, hm_hi⟩
            have hnotlast : m.val ≠ n + 1 := by
              have := Fin.le_iff_val_le_val.mp hm_hi; omega
            have hlt : m.val + 1 < n + 2 := by omega
            have hi1_sub : (i + 1 : Site n) - v₀ = ⟨m.val + 1, hlt⟩ := by
              have h1 : (i + 1 : Site n) - v₀ = m + 1 := by simp [m]; abel
              rw [h1, fin_add_one_eq_mk m hlt]
            have hnot : ¬ (a ≤ (⟨m.val + 1, hlt⟩ : Site n) ∧ (⟨m.val + 1, hlt⟩ : Site n) ≤ b) := by
              intro h; apply hi1; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hi1_sub]⟩
            have hlo1 : a ≤ (⟨m.val + 1, hlt⟩ : Site n) :=
              Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm_lo; dsimp; omega)
            have hgt : b.val < m.val + 1 := by
              by_contra hle; push Not at hle
              exact hnot ⟨hlo1, Fin.le_iff_val_le_val.mpr hle⟩
            have hmb : m = b := Fin.ext (by have := Fin.le_iff_val_le_val.mp hm_hi; omega)
            rw [← hvm, hmb]
            exact hb_stop hb_lt_N
          · intro i hi hi1
            let m := i - v₀
            have hvm : v m = i := by simp [v, m]
            rcases Finset.mem_filter.mp hi1 with ⟨_, hm1_lo, hm1_hi⟩
            by_cases hlast : m.val = n + 1
            · have hm_eq : m = ⟨n + 1, by omega⟩ := Fin.ext hlast
              rw [← hvm, hm_eq, hv_last]; exact isL_not_isR hv₀_prev_L
            · have hlt : m.val + 1 < n + 2 := by omega
              have hi1_sub : (i + 1 : Site n) - v₀ = ⟨m.val + 1, hlt⟩ := by
                have h1 : (i + 1 : Site n) - v₀ = m + 1 := by simp [m]; abel
                rw [h1, fin_add_one_eq_mk m hlt]
              rw [hi1_sub] at hm1_lo hm1_hi
              have hnot : ¬ (a ≤ m ∧ m ≤ b) := by
                intro h; apply hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
              have hhi_m : m ≤ b :=
                Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hm1_hi; dsimp at this; omega)
              have hmlta : m.val < a.val := by
                by_contra hge; push Not at hge
                exact hnot ⟨Fin.le_iff_val_le_val.mpr hge, hhi_m⟩
              have hm1eq : m.val + 1 = a.val := by
                have := Fin.le_iff_val_le_val.mp hm1_lo; dsimp at this; omega
              rw [← hvm]
              exact ha_stop m hm1eq
        exact ⟨flipSet x S, hsat_y, flipSet_parity_of_inter_singleton x S T (v p) hST⟩

lemma sol_structure {n : ℕ} (T : Bits n) (D : Finset (Bits n)) (b : ℕ)
    (hTne : T.Nonempty) (hTeven : Even T.card)
    (hpar : ∀ x ∈ D, (x ∩ T).card % 2 = b % 2)
    (q : Signing n) (x : Bits n) (hxD : x ∈ D) (hsat : sat x q)
    (hsub : ∀ y : Bits n, sat y q → y ∈ D) :
    ∀ y : Bits n, sat y q ↔ y = x ∨ y = comp x := by
  by_cases hL : ∀ i, isL x q i
  · exact fun y => sat_of_allL hL
  · by_cases hR : ∀ i, isR x q i
    · exact fun y => sat_of_allR hR
    · rcases exists_odd_flip_of_not_allL_not_allR x q hsat T hTne hTeven hL hR with ⟨y, hsy, hne⟩
      have hyD : y ∈ D := hsub y hsy
      have h1 := hpar y hyD
      have h2 := hpar x hxD
      omega

/-! ### Part C: Complementary pair partition of D -/

noncomputable def pairSet {n : ℕ} (D : Finset (Bits n)) : Finset (Finset (Bits n)) :=
  D.image (fun x => ({x, comp x} : Finset (Bits n)))

lemma pairSet_card_eq_two {n : ℕ} {D : Finset (Bits n)} {P : Finset (Bits n)}
    (hP : P ∈ pairSet D) : P.card = 2 := by
  rcases Finset.mem_image.mp hP with ⟨x, _, rfl⟩
  exact Finset.card_pair (comp_ne_self x).symm

lemma pairSet_disjoint {n : ℕ} {D : Finset (Bits n)} {P₁ P₂ : Finset (Bits n)}
    (h1 : P₁ ∈ pairSet D) (h2 : P₂ ∈ pairSet D) (hne : P₁ ≠ P₂) : Disjoint P₁ P₂ := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  apply hne
  rcases Finset.mem_image.mp h1 with ⟨x, _, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨y, _, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
  rcases hz1 with rfl | rfl <;> rcases hz2 with hxy | hxy
  · subst hxy; rfl
  · subst hxy; ext w; simp [comp_comp, or_comm]
  · rw [← hxy]; ext w; simp [comp_comp, or_comm]
  · have : x = y := by
      have := congrArg comp hxy
      simpa [comp_comp] using this
    subst this; rfl

lemma pairSet_biUnion {n : ℕ} {D : Finset (Bits n)} (hcomp : ∀ x ∈ D, comp x ∈ D) :
    (pairSet D).biUnion id = D := by
  ext z
  simp only [Finset.mem_biUnion, id_eq, pairSet, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hxD, rfl⟩, hz⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxD
    · exact hcomp x hxD
  · intro hzD
    exact ⟨{z, comp z}, ⟨z, hzD, rfl⟩, Finset.mem_insert_self z _⟩

lemma card_eq_two_mul_pairSet {n : ℕ} {D : Finset (Bits n)} (hcomp : ∀ x ∈ D, comp x ∈ D) :
    D.card = 2 * (pairSet D).card := by
  have h1 : D.card = ((pairSet D).biUnion id).card := by rw [pairSet_biUnion hcomp]
  rw [h1, Finset.card_biUnion (t := id) (fun P₁ h1 P₂ h2 hne => pairSet_disjoint h1 h2 hne)]
  simp only [id_eq]
  have hsum : (pairSet D).sum (fun P => P.card) = (pairSet D).sum (fun _ => 2) :=
    Finset.sum_congr rfl fun P hP => pairSet_card_eq_two hP
  rw [hsum, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Part D: Adaptive algorithm (upper bound) -/

def stepState (m e : ℕ) (st : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  if bit = false ∧ st.1 < m then
    if st.2 + 1 = e + 1 then (st.1 + 1, 0) else (st.1, st.2 + 1)
  else st

def stateOf (m e : ℕ) (h : List Bool) : ℕ × ℕ :=
  h.foldl (stepState m e) (0, 0)

lemma stateOf_props (m e : ℕ) (h : List Bool) :
    (stateOf m e h).1 ≤ m ∧
    ((stateOf m e h).1 < m → (stateOf m e h).2 < e + 1) ∧
    ((stateOf m e h).1 = m → (stateOf m e h).2 = 0) ∧
    (stateOf m e h).1 * (e + 1) + (stateOf m e h).2 = min (m * (e + 1)) (h.count false) := by
  induction h using List.reverseRecOn with
  | nil =>
    simp [stateOf]
  | append_singleton l bit ih =>
    rcases ih with ⟨h1, h2, h3, h4⟩
    have hstep : stateOf m e (l ++ [bit]) = stepState m e (stateOf m e l) bit := by
      simp [stateOf, List.foldl_concat]
    rw [hstep, List.count_append, List.count_singleton]
    dsimp only [stepState]
    cases bit
    · simp only [beq_self_eq_true, ite_true, true_and]
      by_cases hlt : (stateOf m e l).1 < m
      · simp only [hlt, ite_true]
        have hf := h2 hlt
        by_cases hfull : (stateOf m e l).2 + 1 = e + 1
        · simp only [hfull, ite_true]
          refine ⟨by omega, fun _ => by omega, fun _ => trivial, ?_⟩
          have hmul : ((stateOf m e l).1 + 1) * (e + 1) = (stateOf m e l).1 * (e + 1) + (e + 1) := by ring
          have hle_m : (stateOf m e l).1 + 1 ≤ m := by omega
          have hle_prod : ((stateOf m e l).1 + 1) * (e + 1) ≤ m * (e + 1) := Nat.mul_le_mul_right _ hle_m
          omega
        · simp only [hfull, ite_false]
          refine ⟨by omega, fun _ => by omega, fun heq => by omega, ?_⟩
          have hle_m : (stateOf m e l).1 + 1 ≤ m := by omega
          have hle_prod : ((stateOf m e l).1 + 1) * (e + 1) ≤ m * (e + 1) := Nat.mul_le_mul_right _ hle_m
          have hmul : ((stateOf m e l).1 + 1) * (e + 1) = (stateOf m e l).1 * (e + 1) + (e + 1) := by ring
          omega
      · simp only [hlt, ite_false]
        have heqm : (stateOf m e l).1 = m := by omega
        have hz := h3 heqm
        refine ⟨h1, fun hf => False.elim hf, h3, ?_⟩
        rw [heqm, hz, add_zero] at h4 ⊢
        omega
    · simp only [Bool.false_eq_true, false_and, ite_false, beq_iff_eq, Nat.add_zero]
      exact ⟨h1, h2, h3, h4⟩

lemma count_false_add_true (h : List Bool) : h.count false + h.count true = h.length := by
  induction h with
  | nil => simp
  | cons b l ih => cases b <;> simp <;> omega

lemma run_upper_bound {n k e : ℕ} (D : Finset (Bits n))
    (hcomp : ∀ x ∈ D, comp x ∈ D)
    (hcase : D = ∅ ∨ (D.card / 2) * (e + 1) + e ≤ k) :
    ∃ ask : Fin k → List Bool → Signing n, ∃ answer : List Bool → Bool,
      ∀ (A : Finset (Bits n)) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl
          (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)])
          ([] : List Bool)) = decide (A ∩ D).Nonempty := by
  classical
  rcases hcase with rfl | hk
  · refine ⟨fun _ _ _ => (false, false), fun _ => false, fun A flips _ => ?_⟩
    simp
  · by_cases hD0 : D = ∅
    · subst hD0
      refine ⟨fun _ _ _ => (false, false), fun _ => false, fun A flips _ => ?_⟩
      simp
    · let m := D.card / 2
      have hcardD : D.card = 2 * (pairSet D).card := card_eq_two_mul_pairSet hcomp
      have hm_eq : (pairSet D).card = m := by dsimp only [m]; omega
      have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD0
      have hm_pos : 0 < m := by
        have hpos : 0 < D.card := Finset.card_pos.mpr hDne
        dsimp only [m]; omega
      let eP : Fin m ≃ {P // P ∈ pairSet D} := (Fintype.equivFinOfCardEq (by simp [hm_eq])).symm
      let rep : Fin m → Bits n := fun i =>
        Classical.choose (Finset.mem_image.mp (eP i).2)
      have hrep_spec : ∀ i : Fin m, rep i ∈ D ∧ ({rep i, comp (rep i)} : Finset (Bits n)) = (eP i).1 :=
        fun i => Classical.choose_spec (Finset.mem_image.mp (eP i).2)
      let pairSigning : Fin m → Signing n := fun i => allLSigning (rep i)
      have hreply_pair : ∀ (A : Finset (Bits n)) (i : Fin m),
          replyOf A (pairSigning i) = true ↔ (A ∩ (eP i).1).Nonempty := by
        intro A i
        rw [replyOf_eq_true_iff]
        have hP := (hrep_spec i).2
        constructor
        · rintro ⟨y, hyA, hsat⟩
          have hy : y = rep i ∨ y = comp (rep i) := (sat_allLSigning (rep i) y).mp hsat
          refine ⟨y, Finset.mem_inter.mpr ⟨hyA, ?_⟩⟩
          rw [← hP]; simpa using hy
        · rintro ⟨y, hy⟩
          rcases Finset.mem_inter.mp hy with ⟨hyA, hyP⟩
          rw [← hP] at hyP
          have hy : y = rep i ∨ y = comp (rep i) := by simpa using hyP
          exact ⟨y, hyA, (sat_allLSigning (rep i) y).mpr hy⟩
      let ask : Fin k → List Bool → Signing n := fun _ h =>
        let idx := (stateOf m e h).1
        if hi : idx < m then pairSigning ⟨idx, hi⟩ else pairSigning ⟨0, hm_pos⟩
      let answer : List Bool → Bool := fun h => decide ((stateOf m e h).1 < m)
      refine ⟨ask, answer, fun A flips hflips => ?_⟩
      by_cases hAD : (A ∩ D).Nonempty
      · -- Positive case: pick i* with (A ∩ eP i*).Nonempty
        rcases hAD with ⟨x, hx⟩
        rcases Finset.mem_inter.mp hx with ⟨hxA, hxD⟩
        have hPx : ({x, comp x} : Finset (Bits n)) ∈ pairSet D :=
          Finset.mem_image.mpr ⟨x, hxD, rfl⟩
        let iStar : Fin m := eP.symm ⟨{x, comp x}, hPx⟩
        have hiStar_true : replyOf A (pairSigning iStar) = true := by
          rw [hreply_pair]
          refine ⟨x, Finset.mem_inter.mpr ⟨hxA, ?_⟩⟩
          have heq : (eP iStar).1 = {x, comp x} := by
            dsimp only [iStar]; simp
          rw [heq]; exact Finset.mem_insert_self x _
        have hinv : ∀ l : List (Fin k), l.Nodup →
            let h := l.foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
            (stateOf m e h).1 < iStar.val ∨
              ((stateOf m e h).1 = iStar.val ∧
                (stateOf m e h).2 ≤ (l.filter (fun j => decide (j ∈ flips))).length) := by
          intro l
          induction l using List.reverseRecOn with
          | nil =>
            intro _
            by_cases h0 : 0 < iStar.val
            · exact Or.inl h0
            · right; simp [stateOf]; omega
          | append_singleton l j ih =>
            intro hnodup
            have hnodup_l : l.Nodup :=
              (List.nodup_append.mp hnodup).1
            have hih := ih hnodup_l
            set h := l.foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
            have hfold : (l ++ [j]).foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) [] =
                h ++ [replyOf A (ask j h) != decide (j ∈ flips)] := by
              rw [List.foldl_concat]
            change (stateOf m e ((l ++ [j]).foldl _ [])).1 < iStar.val ∨ _
            rw [hfold]
            have hst_step : stateOf m e (h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) =
                stepState m e (stateOf m e h) (replyOf A (ask j h) != decide (j ∈ flips)) := by
              simp [stateOf, List.foldl_concat]
            rw [hst_step]
            have hfilt : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).length =
                (l.filter (fun t => decide (t ∈ flips))).length + if j ∈ flips then 1 else 0 := by
              rw [List.filter_append, List.length_append]
              by_cases hj : j ∈ flips <;> simp [hj]
            rw [hfilt]
            rcases hih with hlt | ⟨heq, hle⟩
            · dsimp only [stepState]
              by_cases hc1 : (replyOf A (ask j h) != decide (j ∈ flips)) = false ∧ (stateOf m e h).1 < m
              · rw [if_pos hc1]
                by_cases hc2 : (stateOf m e h).2 + 1 = e + 1
                · rw [if_pos hc2]
                  by_cases hlt' : (stateOf m e h).1 + 1 < iStar.val
                  · exact Or.inl hlt'
                  · exact Or.inr ⟨by omega, by omega⟩
                · rw [if_neg hc2]
                  exact Or.inl hlt
              · rw [if_neg hc1]
                exact Or.inl hlt
            · have hi_lt_m : (stateOf m e h).1 < m := by omega
              have hask : ask j h = pairSigning iStar := by
                dsimp only [ask]
                rw [dif_pos hi_lt_m]
                congr 1; exact Fin.ext heq
              rw [hask, hiStar_true]
              by_cases hj : j ∈ flips
              · simp only [hj, decide_true, bne_self_eq_false]
                have hflips_le : (l.filter (fun t => decide (t ∈ flips))).length + 1 ≤ e := by
                  have hsub : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).toFinset ⊆ flips := by
                    intro t ht
                    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ht
                    exact ht.2
                  have hnd_f : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).Nodup :=
                    List.Nodup.filter _ hnodup
                  have hcard_eq : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).length =
                      ((l ++ [j]).filter (fun t => decide (t ∈ flips))).toFinset.card :=
                    (List.toFinset_card_of_nodup hnd_f).symm
                  have hle_e : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).length ≤ e := by
                    rw [hcard_eq]
                    exact le_trans (Finset.card_le_card hsub) hflips
                  rw [hfilt, if_pos hj] at hle_e
                  exact hle_e
                dsimp only [stepState]
                have hnotfull : (stateOf m e h).2 + 1 ≠ e + 1 := by omega
                simp only [hi_lt_m, and_self, ite_true, hnotfull, ite_false]
                exact Or.inr ⟨heq, by omega⟩
              · simp only [hj, decide_false, Bool.bne_false, ite_false]
                dsimp only [stepState]
                simp only [Bool.true_eq_false, false_and, ite_false]
                exact Or.inr ⟨heq, by omega⟩
        have hfin := hinv (List.finRange k) (List.nodup_finRange k)
        have hlt_m : (stateOf m e ((List.finRange k).foldl
            (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) [])).1 < m := by
          rcases hfin with h1 | ⟨h1, _⟩ <;> omega
        have hAD_ne : (A ∩ D).Nonempty := ⟨x, hx⟩
        simp [answer, hAD_ne, hlt_m]
      · -- Negative case: A ∩ D = empty, so every ask returns false
        have hall_false : ∀ (j : Fin k) (h : List Bool), replyOf A (ask j h) = false := by
          intro j h
          rw [Bool.eq_false_iff]
          intro htrue
          dsimp only [ask] at htrue
          split_ifs at htrue with hi
          · rw [hreply_pair] at htrue
            rcases htrue with ⟨y, hy⟩
            rcases Finset.mem_inter.mp hy with ⟨hyA, hyP⟩
            have hyD : y ∈ D := by
              rw [← pairSet_biUnion hcomp, Finset.mem_biUnion]
              exact ⟨(eP ⟨(stateOf m e h).1, hi⟩).1, (eP _).2, hyP⟩
            exact hAD ⟨y, Finset.mem_inter.mpr ⟨hyA, hyD⟩⟩
          · rw [hreply_pair] at htrue
            rcases htrue with ⟨y, hy⟩
            rcases Finset.mem_inter.mp hy with ⟨hyA, hyP⟩
            have hyD : y ∈ D := by
              rw [← pairSet_biUnion hcomp, Finset.mem_biUnion]
              exact ⟨(eP ⟨0, hm_pos⟩).1, (eP _).2, hyP⟩
            exact hAD ⟨y, Finset.mem_inter.mpr ⟨hyA, hyD⟩⟩
        have hcnt : ∀ l : List (Fin k),
            let h := l.foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
            h.length = l.length ∧ h.count true = (l.filter (fun j => decide (j ∈ flips))).length := by
          intro l
          induction l using List.reverseRecOn with
          | nil => simp
          | append_singleton l j ih =>
            set h := l.foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
            have hfold : (l ++ [j]).foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) [] =
                h ++ [replyOf A (ask j h) != decide (j ∈ flips)] := List.foldl_concat ..
            dsimp only
            rw [hfold, hall_false j h, Bool.false_bne, List.length_append, List.length_singleton,
                List.length_append, List.length_singleton, List.count_append, List.count_singleton,
                List.filter_append, List.length_append]
            by_cases hj : j ∈ flips <;> simp [hj, ih.1, ih.2]
        have hfin := hcnt (List.finRange k)
        set h := (List.finRange k).foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
        have hlen : h.length = k := by rw [hfin.1, List.length_finRange]
        have htrue_le : h.count true ≤ e := by
          rw [hfin.2]
          have hsub : ((List.finRange k).filter (fun j => decide (j ∈ flips))).toFinset ⊆ flips := by
            intro t ht
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ht
            exact ht.2
          have hnd : ((List.finRange k).filter (fun j => decide (j ∈ flips))).Nodup :=
            List.Nodup.filter _ (List.nodup_finRange k)
          rw [← List.toFinset_card_of_nodup hnd]
          exact le_trans (Finset.card_le_card hsub) hflips
        have hfalse_ge : m * (e + 1) ≤ h.count false := by
          have hsum := count_false_add_true h
          change m * (e + 1) + e ≤ k at hk
          omega
        rcases stateOf_props m e h with ⟨hst1, hst2, _, hst4⟩
        have hmin : min (m * (e + 1)) (h.count false) = m * (e + 1) := min_eq_left hfalse_ge
        rw [hmin] at hst4
        have heqm : (stateOf m e h).1 = m := by
          by_contra hne
          have hlt : (stateOf m e h).1 < m := lt_of_le_of_ne hst1 hne
          have hlt2 := hst2 hlt
          have hle_m : (stateOf m e h).1 + 1 ≤ m := by omega
          have hmul : ((stateOf m e h).1 + 1) * (e + 1) ≤ m * (e + 1) := Nat.mul_le_mul_right _ hle_m
          have hexp : ((stateOf m e h).1 + 1) * (e + 1) = (stateOf m e h).1 * (e + 1) + (e + 1) := by ring
          omega
        simp [answer, hAD, heqm]

/-! ### Part E: Adversary lower bound -/

lemma comp_closed_of_algo {n k e : ℕ} (T : Bits n) (D : Finset (Bits n)) (b : ℕ)
    (hTne : T.Nonempty) (hTeven : Even T.card)
    (hpar : ∀ x ∈ D, (x ∩ T).card % 2 = b % 2)
    (ask : Fin k → List Bool → Signing n) (answer : List Bool → Bool)
    (halgo : ∀ (A : Finset (Bits n)) (flips : Finset (Fin k)), flips.card ≤ e →
      answer ((List.finRange k).foldl
        (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)])
        ([] : List Bool)) = decide (A ∩ D).Nonempty) :
    ∀ x ∈ D, comp x ∈ D := by
  classical
  intro x hxD
  by_contra hcx
  let U : Finset (Bits n) := Finset.univ \ D
  let A1 : Finset (Bits n) := insert x U
  have hreply_eq : ∀ q : Signing n, replyOf U q = replyOf A1 q := by
    intro q
    apply Bool.eq_iff_iff.mpr
    rw [replyOf_eq_true_iff, replyOf_eq_true_iff]
    constructor
    · rintro ⟨y, hyU, hsat⟩
      exact ⟨y, Finset.mem_insert_of_mem hyU, hsat⟩
    · rintro ⟨y, hyA1, hsat⟩
      rcases Finset.mem_insert.mp hyA1 with rfl | hyU
      · by_cases hsub : ∀ z : Bits n, sat z q → z ∈ D
        · have hstruc := sol_structure T D b hTne hTeven hpar q y hxD hsat hsub
          have hsc : sat (comp y) q := (hstruc (comp y)).mpr (Or.inr rfl)
          exact absurd (hsub (comp y) hsc) hcx
        · push Not at hsub
          rcases hsub with ⟨z, hsz, hzD⟩
          exact ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzD⟩, hsz⟩
      · exact ⟨y, hyU, hsat⟩
  have hfold_eq : (List.finRange k).foldl
        (fun h j => h ++ [replyOf U (ask j h) != decide (j ∈ (∅ : Finset (Fin k)))]) [] =
      (List.finRange k).foldl
        (fun h j => h ++ [replyOf A1 (ask j h) != decide (j ∈ (∅ : Finset (Fin k)))]) [] := by
    congr 1; funext h j; rw [hreply_eq]
  have h0 := halgo U ∅ (by simp)
  have h1 := halgo A1 ∅ (by simp)
  rw [hfold_eq] at h0
  have hUD : ¬ (U ∩ D).Nonempty := by
    rintro ⟨y, hy⟩
    rcases Finset.mem_inter.mp hy with ⟨hyU, hyD⟩
    exact (Finset.mem_sdiff.mp hyU).2 hyD
  have hA1D : (A1 ∩ D).Nonempty :=
    ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_insert_self x U, hxD⟩⟩
  simp [hUD, hA1D] at h0 h1
  rw [h0] at h1
  exact Bool.false_ne_true h1

structure AdvState (m k : ℕ) where
  hist : List Bool
  fSet : Fin m → Finset (Fin k)
  tSet : Fin m → Finset (Fin k)

lemma lower_bound_of_algo {n k e : ℕ} (T : Bits n) (D : Finset (Bits n)) (b : ℕ)
    (hTne : T.Nonempty) (hTeven : Even T.card)
    (hpar : ∀ x ∈ D, (x ∩ T).card % 2 = b % 2)
    (hcomp : ∀ x ∈ D, comp x ∈ D)
    (hDne : D.Nonempty)
    (ask : Fin k → List Bool → Signing n) (answer : List Bool → Bool)
    (halgo : ∀ (A : Finset (Bits n)) (flips : Finset (Fin k)), flips.card ≤ e →
      answer ((List.finRange k).foldl
        (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)])
        ([] : List Bool)) = decide (A ∩ D).Nonempty) :
    (D.card / 2) * (e + 1) + e ≤ k := by
  classical
  by_contra hlt_k
  push Not at hlt_k
  let m := D.card / 2
  have hcardD : D.card = 2 * (pairSet D).card := card_eq_two_mul_pairSet hcomp
  have hm_eq : (pairSet D).card = m := by dsimp only [m]; omega
  have hm_pos : 0 < m := by
    have hpos : 0 < D.card := Finset.card_pos.mpr hDne
    dsimp only [m]; omega
  let eP : Fin m ≃ {P // P ∈ pairSet D} := (Fintype.equivFinOfCardEq (by simp [hm_eq])).symm
  let U : Finset (Bits n) := Finset.univ \ D
  -- Classify each query q: either Sol(q) = eP i for a unique i, or reply(U ∪ B, q) = reply(U, q) for all B <= D
  let qMatch (q : Signing n) (i : Fin m) : Prop :=
    ∀ y : Bits n, sat y q ↔ y ∈ (eP i).1
  let qIdx (q : Signing n) : Option (Fin m) :=
    if h : ∃ i : Fin m, qMatch q i then some (Classical.choose h) else none
  have hqIdx_some : ∀ (q : Signing n) (i : Fin m), qIdx q = some i →
      (replyOf U q = false) ∧
      (replyOf (U ∪ (eP i).1) q = true) ∧
      (∀ i' : Fin m, i' ≠ i → replyOf (U ∪ (eP i').1) q = false) := by
    intro q i hqi
    dsimp only [qIdx] at hqi
    split_ifs at hqi with hex
    · have hi_eq : Classical.choose hex = i := Option.some.inj hqi
      have hm : qMatch q i := hi_eq ▸ Classical.choose_spec hex
      have hsubD : (eP i).1 ⊆ D := by
        intro y hy
        rw [← pairSet_biUnion hcomp, Finset.mem_biUnion]
        exact ⟨(eP i).1, (eP i).2, hy⟩
      have hU : replyOf U q = false := by
        rw [Bool.eq_false_iff, ne_eq, replyOf_eq_true_iff]
        rintro ⟨y, hyU, hsat⟩
        have hyP : y ∈ (eP i).1 := (hm y).mp hsat
        exact (Finset.mem_sdiff.mp hyU).2 (hsubD hyP)
      have hUi : replyOf (U ∪ (eP i).1) q = true := by
        rw [replyOf_eq_true_iff]
        have hPne : (eP i).1.Nonempty :=
          Finset.card_pos.mp (by rw [pairSet_card_eq_two (eP i).2]; omega)
        rcases hPne with ⟨y, hyP⟩
        exact ⟨y, Finset.mem_union_right U hyP, (hm y).mpr hyP⟩
      have hUi' : ∀ i' : Fin m, i' ≠ i → replyOf (U ∪ (eP i').1) q = false := by
        intro i' hne
        rw [Bool.eq_false_iff, ne_eq, replyOf_eq_true_iff]
        rintro ⟨y, hy, hsat⟩
        have hyP : y ∈ (eP i).1 := (hm y).mp hsat
        rcases Finset.mem_union.mp hy with hyU | hyP'
        · exact (Finset.mem_sdiff.mp hyU).2 (hsubD hyP)
        · have hPne : (eP i').1 ≠ (eP i).1 := fun h => hne (eP.injective (Subtype.ext h))
          exact Finset.disjoint_left.mp (pairSet_disjoint (eP i').2 (eP i).2 hPne) hyP' hyP
      exact ⟨hU, hUi, hUi'⟩
  have hqIdx_none : ∀ (q : Signing n), qIdx q = none →
      ∀ i : Fin m, replyOf (U ∪ (eP i).1) q = replyOf U q := by
    intro q hqn i
    have hno : ¬ ∃ j : Fin m, qMatch q j := by
      dsimp only [qIdx] at hqn
      split_ifs at hqn with hex
      exact hex
    apply Bool.eq_iff_iff.mpr
    rw [replyOf_eq_true_iff, replyOf_eq_true_iff]
    constructor
    · rintro ⟨y, hy, hsat⟩
      rcases Finset.mem_union.mp hy with hyU | hyP
      · exact ⟨y, hyU, hsat⟩
      · by_cases hsub : ∀ z : Bits n, sat z q → z ∈ D
        · have hyD : y ∈ D := by
            rw [← pairSet_biUnion hcomp, Finset.mem_biUnion]
            exact ⟨(eP i).1, (eP i).2, hyP⟩
          have hstruc := sol_structure T D b hTne hTeven hpar q y hyD hsat hsub
          have hPmem : ({y, comp y} : Finset (Bits n)) ∈ pairSet D :=
            Finset.mem_image.mpr ⟨y, hyD, rfl⟩
          let j : Fin m := eP.symm ⟨{y, comp y}, hPmem⟩
          exfalso; apply hno; refine ⟨j, fun z => ?_⟩
          have hj_eq : (eP j).1 = {y, comp y} := by dsimp only [j]; simp
          rw [hj_eq, hstruc z]
          simp
        · push Not at hsub
          rcases hsub with ⟨z, hsz, hzD⟩
          exact ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzD⟩, hsz⟩
    · rintro ⟨y, hyU, hsat⟩
      exact ⟨y, Finset.mem_union_left _ hyU, hsat⟩
  -- Last-survivor adversary step
  let advStep : AdvState m k → Fin k → AdvState m k := fun st j =>
    let q := ask j st.hist
    match qIdx q with
    | none => { st with hist := st.hist ++ [replyOf U q] }
    | some i =>
      if (∀ i' : Fin m, i' ≠ i → e + 1 ≤ (st.fSet i').card) ∧ e ≤ (st.fSet i).card then
        { hist := st.hist ++ [true]
          fSet := st.fSet
          tSet := Function.update st.tSet i (insert j (st.tSet i)) }
      else
        { hist := st.hist ++ [false]
          fSet := Function.update st.fSet i (insert j (st.fSet i))
          tSet := st.tSet }
  let advInit : AdvState m k := { hist := [], fSet := fun _ => ∅, tSet := fun _ => ∅ }
  -- Prove invariants by reverse induction on any Nodup list l
  have hinv : ∀ l : List (Fin k), l.Nodup →
      let st := l.foldl advStep advInit
      (∀ i : Fin m, ∀ j ∈ st.fSet i, j ∈ l) ∧
      (∀ i : Fin m, ∀ j ∈ st.tSet i, j ∈ l) ∧
      ((Finset.univ : Finset (Fin m)).sum (fun i => (st.fSet i).card + (st.tSet i).card) ≤ l.length) ∧
      (∃ i₀ : Fin m, (st.fSet i₀).card ≤ e) ∧
      (∀ i : Fin m, (st.tSet i).Nonempty →
        (st.fSet i).card = e ∧
        (∀ i' : Fin m, i' ≠ i → e + 1 ≤ (st.fSet i').card) ∧
        (∀ i' : Fin m, i' ≠ i → st.tSet i' = ∅)) ∧
      (∀ flips : Finset (Fin k),
        (∀ j ∈ l, j ∈ flips ↔ ∃ i : Fin m, j ∈ st.tSet i) →
        l.foldl (fun h j => h ++ [replyOf U (ask j h) != decide (j ∈ flips)]) [] = st.hist) ∧
      (∀ (iStar : Fin m) (flips : Finset (Fin k)),
        (∀ j ∈ l, j ∈ flips ↔ j ∈ st.fSet iStar ∨ ∃ i : Fin m, i ≠ iStar ∧ j ∈ st.tSet i) →
        l.foldl (fun h j => h ++ [replyOf (U ∪ (eP iStar).1) (ask j h) != decide (j ∈ flips)]) [] = st.hist) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨fun _ _ h => absurd h (Finset.notMem_empty _),
              fun _ _ h => absurd h (Finset.notMem_empty _),
              by simp [advInit],
              ⟨⟨0, hm_pos⟩, by simp [advInit]⟩,
              fun _ h => absurd h (by simp [advInit]),
              fun _ _ => rfl,
              fun _ _ _ => rfl⟩
    | append_singleton l j ih =>
      intro hnodup
      have hnd_split := List.nodup_append.mp hnodup
      have hnd_l : l.Nodup := hnd_split.1
      have hj_not_l : j ∉ l := fun hjl => hnd_split.2.2 j hjl j (List.mem_singleton_self j) rfl
      rcases ih hnd_l with ⟨hsubF, hsubT, hsum, hex_le, ht_inv, htrU, htrP⟩
      set st := l.foldl advStep advInit
      have hfold : (l ++ [j]).foldl advStep advInit = advStep st j := List.foldl_concat ..
      dsimp only
      rw [hfold]
      have hj_not_f : ∀ i, j ∉ st.fSet i := fun i h => hj_not_l (hsubF i j h)
      have hj_not_t : ∀ i, j ∉ st.tSet i := fun i h => hj_not_l (hsubT i j h)
      dsimp only [advStep]
      rcases hq : qIdx (ask j st.hist) with _ | i
      · -- qIdx = none
        refine ⟨fun i' t ht => List.mem_append_left _ (hsubF i' t ht),
                fun i' t ht => List.mem_append_left _ (hsubT i' t ht),
                by simp only [List.length_append, List.length_singleton]; omega,
                hex_le, ht_inv, ?_, ?_⟩
        · intro flips hfl
          rw [List.foldl_concat]
          have hfl_l : ∀ t ∈ l, t ∈ flips ↔ ∃ i' : Fin m, t ∈ st.tSet i' :=
            fun t ht => hfl t (List.mem_append_left _ ht)
          rw [htrU flips hfl_l]
          have hj_fl : j ∉ flips := by
            rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
            rintro ⟨i', hi'⟩; exact hj_not_t i' hi'
          simp [hj_fl]
        · intro iStar flips hfl
          rw [List.foldl_concat]
          have hfl_l : ∀ t ∈ l, t ∈ flips ↔ t ∈ st.fSet iStar ∨ ∃ i' : Fin m, i' ≠ iStar ∧ t ∈ st.tSet i' :=
            fun t ht => hfl t (List.mem_append_left _ ht)
          rw [htrP iStar flips hfl_l]
          have hj_fl : j ∉ flips := by
            rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
            rintro (h1 | ⟨i', _, h2⟩)
            · exact hj_not_f iStar h1
            · exact hj_not_t i' h2
          simp [hj_fl, hqIdx_none (ask j st.hist) hq iStar]
      · -- qIdx = some i
        rcases hqIdx_some (ask j st.hist) i hq with ⟨hrepU, hrepUi, hrepUi'⟩
        dsimp only
        split_ifs with hcond
        · -- Answer true: update tSet i
          dsimp only
          have hfi_eq : (st.fSet i).card = e := by
            rcases hex_le with ⟨i₀, hi₀⟩
            by_cases hio : i₀ = i
            · subst hio; omega
            · have := hcond.1 i₀ hio; omega
          have hother_t : ∀ i' : Fin m, i' ≠ i → st.tSet i' = ∅ := by
            intro i' hne
            by_contra hne_e
            have hne' : (st.tSet i').Nonempty := Finset.nonempty_iff_ne_empty.mpr hne_e
            have hfi' := (ht_inv i' hne').1
            have hge := hcond.1 i' hne
            omega
          refine ⟨fun i' t ht => List.mem_append_left _ (hsubF i' t ht), ?_, ?_, hex_le, ?_, ?_, ?_⟩
          · intro i' t ht
            by_cases hi' : i' = i
            · subst hi'; simp only [Function.update_self, Finset.mem_insert] at ht
              rcases ht with htj | ht'
              · subst htj; exact List.mem_append_right _ (List.mem_singleton_self _)
              · exact List.mem_append_left _ (hsubT i' t ht')
            · rw [Function.update_of_ne hi'] at ht
              exact List.mem_append_left _ (hsubT i' t ht)
          · have hsum_eq : (Finset.univ : Finset (Fin m)).sum
                (fun i' => (st.fSet i').card + (Function.update st.tSet i (insert j (st.tSet i)) i').card) =
                (Finset.univ : Finset (Fin m)).sum (fun i' => (st.fSet i').card + (st.tSet i').card) + 1 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
                  ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
              have hrest : (Finset.univ.erase i).sum
                  (fun i' => (st.fSet i').card + (Function.update st.tSet i (insert j (st.tSet i)) i').card) =
                  (Finset.univ.erase i).sum (fun i' => (st.fSet i').card + (st.tSet i').card) :=
                Finset.sum_congr rfl fun i' hi' => by
                  rw [Function.update_of_ne (Finset.mem_erase.mp hi').1]
              rw [hrest, Function.update_self, Finset.card_insert_of_notMem (hj_not_t i)]
              omega
            rw [hsum_eq, List.length_append, List.length_singleton]
            omega
          · intro i' hne'
            by_cases hi' : i' = i
            · subst hi'
              refine ⟨hfi_eq, hcond.1, fun i'' hne'' => ?_⟩
              rw [Function.update_of_ne hne'']
              exact hother_t i'' hne''
            · rw [Function.update_of_ne hi'] at hne'
              rw [hother_t i' hi'] at hne'
              exact absurd hne' (by simp)
          · intro flips hfl
            rw [List.foldl_concat]
            have hfl_l : ∀ t ∈ l, t ∈ flips ↔ ∃ i' : Fin m, t ∈ st.tSet i' := by
              intro t ht
              rw [hfl t (List.mem_append_left _ ht)]
              constructor
              · rintro ⟨i', hi'⟩
                by_cases heq : i' = i
                · subst heq; rw [Function.update_self] at hi'
                  rcases Finset.mem_insert.mp hi' with rfl | ht'
                  · exact absurd ht hj_not_l
                  · exact ⟨i', ht'⟩
                · rw [Function.update_of_ne heq] at hi'; exact ⟨i', hi'⟩
              · rintro ⟨i', hi'⟩
                refine ⟨i', ?_⟩
                by_cases heq : i' = i
                · subst heq; rw [Function.update_self]; exact Finset.mem_insert_of_mem hi'
                · rw [Function.update_of_ne heq]; exact hi'
            rw [htrU flips hfl_l]
            have hj_fl : j ∈ flips := by
              rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
              exact ⟨i, by rw [Function.update_self]; exact Finset.mem_insert_self j _⟩
            simp [hj_fl, hrepU]
          · intro iStar flips hfl
            rw [List.foldl_concat]
            have hfl_l : ∀ t ∈ l, t ∈ flips ↔ t ∈ st.fSet iStar ∨ ∃ i' : Fin m, i' ≠ iStar ∧ t ∈ st.tSet i' := by
              intro t ht
              rw [hfl t (List.mem_append_left _ ht)]
              constructor
              · rintro (h1 | ⟨i', hne', hi'⟩)
                · exact Or.inl h1
                · by_cases heq : i' = i
                  · subst heq; rw [Function.update_self] at hi'
                    rcases Finset.mem_insert.mp hi' with rfl | ht'
                    · exact absurd ht hj_not_l
                    · exact Or.inr ⟨i', hne', ht'⟩
                  · rw [Function.update_of_ne heq] at hi'; exact Or.inr ⟨i', hne', hi'⟩
              · rintro (h1 | ⟨i', hne', hi'⟩)
                · exact Or.inl h1
                · refine Or.inr ⟨i', hne', ?_⟩
                  by_cases heq : i' = i
                  · subst heq; rw [Function.update_self]; exact Finset.mem_insert_of_mem hi'
                  · rw [Function.update_of_ne heq]; exact hi'
            rw [htrP iStar flips hfl_l]
            by_cases hst_i : iStar = i
            · subst hst_i
              have hj_fl : j ∉ flips := by
                rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
                rintro (h1 | ⟨i', hne', hi'⟩)
                · exact hj_not_f iStar h1
                · rw [Function.update_of_ne hne'] at hi'; exact hj_not_t i' hi'
              simp [hj_fl, hrepUi]
            · have hj_fl : j ∈ flips := by
                rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
                exact Or.inr ⟨i, Ne.symm hst_i, by rw [Function.update_self]; exact Finset.mem_insert_self j _⟩
              simp [hj_fl, hrepUi' iStar hst_i]
        · -- Answer false: update fSet i
          dsimp only
          refine ⟨?_, fun i' t ht => List.mem_append_left _ (hsubT i' t ht), ?_, ?_, ?_, ?_, ?_⟩
          · intro i' t ht
            by_cases hi' : i' = i
            · subst hi'; simp only [Function.update_self, Finset.mem_insert] at ht
              rcases ht with htj | ht'
              · subst htj; exact List.mem_append_right _ (List.mem_singleton_self _)
              · exact List.mem_append_left _ (hsubF i' t ht')
            · rw [Function.update_of_ne hi'] at ht
              exact List.mem_append_left _ (hsubF i' t ht)
          · have hsum_eq : (Finset.univ : Finset (Fin m)).sum
                (fun i' => (Function.update st.fSet i (insert j (st.fSet i)) i').card + (st.tSet i').card) =
                (Finset.univ : Finset (Fin m)).sum (fun i' => (st.fSet i').card + (st.tSet i').card) + 1 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
                  ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
              have hrest : (Finset.univ.erase i).sum
                  (fun i' => (Function.update st.fSet i (insert j (st.fSet i)) i').card + (st.tSet i').card) =
                  (Finset.univ.erase i).sum (fun i' => (st.fSet i').card + (st.tSet i').card) :=
                Finset.sum_congr rfl fun i' hi' => by
                  rw [Function.update_of_ne (Finset.mem_erase.mp hi').1]
              rw [hrest, Function.update_self, Finset.card_insert_of_notMem (hj_not_f i)]
              omega
            rw [hsum_eq, List.length_append, List.length_singleton]
            omega
          · by_cases hfi_lt : (st.fSet i).card < e
            · refine ⟨i, ?_⟩
              rw [Function.update_self, Finset.card_insert_of_notMem (hj_not_f i)]
              omega
            · push Not at hfi_lt
              have hex_other : ∃ i' : Fin m, i' ≠ i ∧ (st.fSet i').card ≤ e := by
                by_contra hno; push Not at hno
                exact hcond ⟨fun i' hne => by have := hno i' hne; omega, hfi_lt⟩
              rcases hex_other with ⟨i', hne', hle'⟩
              refine ⟨i', ?_⟩
              rw [Function.update_of_ne hne']
              exact hle'
          · intro i' hne'
            rcases ht_inv i' hne' with ⟨hfi', hge', hte'⟩
            have hne_i : i' ≠ i := by
              rintro rfl
              exact hcond ⟨hge', by omega⟩
            refine ⟨by rw [Function.update_of_ne hne_i]; exact hfi', fun i'' hne'' => ?_, hte'⟩
            by_cases heq : i'' = i
            · subst heq
              rw [Function.update_self, Finset.card_insert_of_notMem (hj_not_f _)]
              have := hge' _ hne''
              omega
            · rw [Function.update_of_ne heq]
              exact hge' i'' hne''
          · intro flips hfl
            rw [List.foldl_concat]
            have hfl_l : ∀ t ∈ l, t ∈ flips ↔ ∃ i' : Fin m, t ∈ st.tSet i' :=
              fun t ht => hfl t (List.mem_append_left _ ht)
            rw [htrU flips hfl_l]
            have hj_fl : j ∉ flips := by
              rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
              rintro ⟨i', hi'⟩; exact hj_not_t i' hi'
            simp [hj_fl, hrepU]
          · intro iStar flips hfl
            rw [List.foldl_concat]
            have hfl_l : ∀ t ∈ l, t ∈ flips ↔ t ∈ st.fSet iStar ∨ ∃ i' : Fin m, i' ≠ iStar ∧ t ∈ st.tSet i' := by
              intro t ht
              rw [hfl t (List.mem_append_left _ ht)]
              constructor
              · rintro (h1 | h2)
                · by_cases heq : iStar = i
                  · subst heq; rw [Function.update_self] at h1
                    rcases Finset.mem_insert.mp h1 with rfl | ht'
                    · exact absurd ht hj_not_l
                    · exact Or.inl ht'
                  · rw [Function.update_of_ne heq] at h1; exact Or.inl h1
                · exact Or.inr h2
              · rintro (h1 | h2)
                · refine Or.inl ?_
                  by_cases heq : iStar = i
                  · subst heq; rw [Function.update_self]; exact Finset.mem_insert_of_mem h1
                  · rw [Function.update_of_ne heq]; exact h1
                · exact Or.inr h2
            rw [htrP iStar flips hfl_l]
            by_cases hst_i : iStar = i
            · subst hst_i
              have hj_fl : j ∈ flips := by
                rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
                exact Or.inl (by rw [Function.update_self]; exact Finset.mem_insert_self j _)
              simp [hj_fl, hrepUi]
            · have hj_fl : j ∉ flips := by
                rw [hfl j (List.mem_append_right _ (List.mem_singleton_self j))]
                rintro (h1 | ⟨i', _, hi'⟩)
                · rw [Function.update_of_ne hst_i] at h1; exact hj_not_f iStar h1
                · exact hj_not_t i' hi'
              simp [hj_fl, hrepUi' iStar hst_i]
  -- Apply invariants to List.finRange k
  rcases hinv (List.finRange k) (List.nodup_finRange k) with ⟨_, _, hsum, hex_le, ht_inv, htrU, htrP⟩
  set st := (List.finRange k).foldl advStep advInit
  rw [List.length_finRange] at hsum
  have hUD : ¬ (U ∩ D).Nonempty := by
    rintro ⟨y, hy⟩
    rcases Finset.mem_inter.mp hy with ⟨hyU, hyD⟩
    exact (Finset.mem_sdiff.mp hyU).2 hyD
  have hPD : ∀ i : Fin m, ((U ∪ (eP i).1) ∩ D).Nonempty := by
    intro i
    have hPne : (eP i).1.Nonempty :=
      Finset.card_pos.mp (by rw [pairSet_card_eq_two (eP i).2]; omega)
    rcases hPne with ⟨y, hyP⟩
    have hyD : y ∈ D := by
      rw [← pairSet_biUnion hcomp, Finset.mem_biUnion]
      exact ⟨(eP i).1, (eP i).2, hyP⟩
    exact ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_union_right U hyP, hyD⟩⟩
  by_cases hexT : ∃ iStar : Fin m, (st.tSet iStar).Nonempty
  · rcases hexT with ⟨iStar, hneT⟩
    rcases ht_inv iStar hneT with ⟨hf_eq, hge_other, ht_other⟩
    have ht_le : (st.tSet iStar).card ≤ e := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ iStar)] at hsum
      have hother_sum : (m - 1) * (e + 1) ≤ (Finset.univ.erase iStar).sum (fun i => (st.fSet i).card + (st.tSet i).card) := by
        calc (m - 1) * (e + 1) = (Finset.univ.erase iStar).card * (e + 1) := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ iStar), Finset.card_fin]
          _ = (Finset.univ.erase iStar).sum (fun _ => e + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (Finset.univ.erase iStar).sum (fun i => (st.fSet i).card + (st.tSet i).card) :=
              Finset.sum_le_sum fun i hi => by
                have := hge_other i (Finset.mem_erase.mp hi).1
                omega
      have hm_split : m * (e + 1) = (m - 1) * (e + 1) + (e + 1) := by
        have h1 : m = (m - 1) + 1 := by omega
        conv_lhs => rw [h1]
        ring
      change k < m * (e + 1) + e at hlt_k
      omega
    have hrunU : (List.finRange k).foldl
        (fun h j => h ++ [replyOf U (ask j h) != decide (j ∈ st.tSet iStar)]) [] = st.hist := by
      apply htrU (st.tSet iStar)
      intro j _
      constructor
      · intro hj; exact ⟨iStar, hj⟩
      · rintro ⟨i', hi'⟩
        by_cases heq : i' = iStar
        · rwa [← heq]
        · rw [ht_other i' heq] at hi'; exact absurd hi' (Finset.notMem_empty _)
    have hrunP : (List.finRange k).foldl
        (fun h j => h ++ [replyOf (U ∪ (eP iStar).1) (ask j h) != decide (j ∈ st.fSet iStar)]) [] = st.hist := by
      apply htrP iStar (st.fSet iStar)
      intro j _
      constructor
      · intro hj; exact Or.inl hj
      · rintro (hj | ⟨i', hne', hi'⟩)
        · exact hj
        · rw [ht_other i' hne'] at hi'; exact absurd hi' (Finset.notMem_empty _)
    have h0 := halgo U (st.tSet iStar) ht_le
    have h1 := halgo (U ∪ (eP iStar).1) (st.fSet iStar) (by omega)
    rw [hrunU] at h0
    rw [hrunP] at h1
    simp [hUD, hPD iStar] at h0 h1
    rw [h0] at h1
    exact Bool.false_ne_true h1
  · push Not at hexT
    rcases hex_le with ⟨iStar, hfi_le⟩
    have hrunU : (List.finRange k).foldl
        (fun h j => h ++ [replyOf U (ask j h) != decide (j ∈ (∅ : Finset (Fin k)))]) [] = st.hist := by
      apply htrU ∅
      intro j _
      simp [hexT]
    have hrunP : (List.finRange k).foldl
        (fun h j => h ++ [replyOf (U ∪ (eP iStar).1) (ask j h) != decide (j ∈ st.fSet iStar)]) [] = st.hist := by
      apply htrP iStar (st.fSet iStar)
      intro j _
      simp [hexT]
    have h0 := halgo U ∅ (by simp)
    have h1 := halgo (U ∪ (eP iStar).1) (st.fSet iStar) hfi_le
    rw [hrunU] at h0
    rw [hrunP] at h1
    simp [hUD, hPD iStar] at h0 h1
    rw [h0] at h1
    exact Bool.false_ne_true h1

theorem main :
    ∀ (n k e : Nat),
      let Site := Fin (n + 2)
      let Bits := Finset Site
      let Signing := Site → Bool × Bool
      let vertex := (Finset.univ : Finset Site)
      let reply := fun (A : Finset Bits) (q : Signing) => A.toList.any (fun x =>
        vertex.toList.all (fun i =>
          (decide (i ∈ x), decide ((i + 1 : Site) ∈ x)) != q i))
      ∀ (T : Bits) (D : Finset Bits) (b : Nat), T.Nonempty → Even T.card →
        (∀ x ∈ D, (x ∩ T).card % 2 = b % 2) →
        ( (∃ ask : Fin k → List Bool → Signing, ∃ answer : List Bool → Bool,
            ∀ (A : Finset Bits) (flips : Finset (Fin k)), flips.card ≤ e →
              answer ((List.finRange k).foldl (fun h j => h ++ [reply A (ask j h) != decide (j ∈ flips)])
                ([] : List Bool)) = decide (A ∩ D).Nonempty) ↔
          (∀ x ∈ D, vertex \ x ∈ D) ∧ (D = ∅ ∨ (D.card / 2) * (e + 1) + e ≤ k) ) := by
  intro n k e
  dsimp only
  intro T D b hTne hTeven hpar
  constructor
  · rintro ⟨ask, answer, halgo⟩
    have hcomp : ∀ x ∈ D, comp x ∈ D :=
      comp_closed_of_algo T D b hTne hTeven hpar ask answer halgo
    refine ⟨hcomp, ?_⟩
    by_cases hD0 : D = ∅
    · exact Or.inl hD0
    · right
      exact lower_bound_of_algo T D b hTne hTeven hpar hcomp
        (Finset.nonempty_iff_ne_empty.mpr hD0) ask answer halgo
  · rintro ⟨hcomp, hcase⟩
    exact run_upper_bound D hcomp hcase

end PEqualNP.Outside.L_lib_1159_aux

theorem PEqualNP.Outside.L_lib_1159 :
∀ (n k e : Nat),
  let Site := Fin (n + 2)
  let Bits := Finset Site
  let Signing := Site → Bool × Bool
  let vertex := (Finset.univ : Finset Site)
  let reply := fun (A : Finset Bits) (q : Signing) => A.toList.any (fun x =>
    vertex.toList.all (fun i =>
      (decide (i ∈ x), decide ((i + 1 : Site) ∈ x)) != q i))
  ∀ (T : Bits) (D : Finset Bits) (b : Nat), T.Nonempty → Even T.card →
    (∀ x ∈ D, (x ∩ T).card % 2 = b % 2) →
    ( (∃ ask : Fin k → List Bool → Signing, ∃ answer : List Bool → Bool,
        ∀ (A : Finset Bits) (flips : Finset (Fin k)), flips.card ≤ e →
          answer ((List.finRange k).foldl (fun h j => h ++ [reply A (ask j h) != decide (j ∈ flips)])
            ([] : List Bool)) = decide (A ∩ D).Nonempty) ↔
      (∀ x ∈ D, vertex \ x ∈ D) ∧ (D = ∅ ∨ (D.card / 2) * (e + 1) + e ≤ k) ) :=
  PEqualNP.Outside.L_lib_1159_aux.main
