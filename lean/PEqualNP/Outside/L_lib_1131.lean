import PEqualNP.Defs
import Mathlib

open scoped symmDiff

namespace PEqualNP.Outside.L_lib_1131_aux

variable {n m : ℕ}

def bd (u v : Fin m → Fin n) (x : Finset (Fin m)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card + (x.filter (fun i => v i = j)).card) % 2 = 1)

def cr (u v : Fin m → Fin n) (U : Finset (Fin n)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => decide (u i ∈ U) != decide (v i ∈ U))

def total (u v : Fin m → Fin n) (d : Finset (Fin n)) (F : Finset (Finset (Fin m × Bool))) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter
    (fun x => bd u v x = d ∧ ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).card

def shores (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun U => cr u v U ⊆ T ∧ (cr u v U).card ≤ k)

def sg (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) (i : Fin n) : Finset (Finset (Fin n)) :=
  (shores u v T k).filter (fun U => i ∈ U)

def sigs (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).image (sg u v T k)).card

def valid (T : Finset (Fin m)) (t w : ℕ) (F : Finset (Finset (Fin m × Bool))) : Prop :=
  F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T


def pc {α : Type*} (A : Finset α) : ZMod 2 := (A.card : ZMod 2)

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem pc_eq_sum {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    pc (s.filter p) = ∑ i ∈ s, (if p i then (1 : ZMod 2) else 0) := by
  unfold pc
  rw [Finset.sum_boole]

theorem pc_empty {α : Type*} : pc (∅ : Finset α) = 0 := by simp [pc]

theorem pc_singleton {α : Type*} (a : α) : pc ({a} : Finset α) = 1 := by simp [pc]

theorem pc_union_disj {α : Type*} [DecidableEq α] {A B : Finset α} (h : Disjoint A B) :
    pc (A ∪ B) = pc A + pc B := by
  unfold pc
  rw [Finset.card_union_of_disjoint h, Nat.cast_add]

theorem pc_symmDiff {α : Type*} [DecidableEq α] (A B : Finset α) :
    pc (A ∆ B) = pc A + pc B := by
  have h1 : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
    have e1 : A ∆ B = (A \ B) ∪ (B \ A) := symmDiff_def A B
    have hd : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
    rw [e1, Finset.card_union_of_disjoint hd]
    have := Finset.card_sdiff_add_card_inter A B
    have := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at this
    omega
  unfold pc
  have h2 : ((A ∆ B).card : ZMod 2) + 2 * ((A ∩ B).card : ZMod 2) =
      (A.card : ZMod 2) + B.card := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) h1
  have h3 : (2 : ZMod 2) = 0 := rfl
  rw [h3, zero_mul, add_zero] at h2
  exact h2

theorem inter_symmDiff_left {α : Type*} [DecidableEq α] (e U W : Finset α) :
    e ∩ (U ∆ W) = (e ∩ U) ∆ (e ∩ W) := by
  ext a; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto

theorem symmDiff_inter_right {α : Type*} [DecidableEq α] (A B U : Finset α) :
    (A ∆ B) ∩ U = (A ∩ U) ∆ (B ∩ U) := by
  ext a; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto

theorem filter_symmDiff' {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p]
    (x y : Finset α) : (x ∆ y).filter p = x.filter p ∆ y.filter p := by
  ext a; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto

theorem mem_cr (u v : Fin m → Fin n) (U : Finset (Fin n)) (i : Fin m) :
    i ∈ cr u v U ↔ ¬ (u i ∈ U ↔ v i ∈ U) := by
  unfold cr
  by_cases h1 : u i ∈ U <;> by_cases h2 : v i ∈ U <;> simp [h1, h2]

theorem cr_compl (u v : Fin m → Fin n) (U : Finset (Fin n)) : cr u v Uᶜ = cr u v U := by
  ext i; simp only [mem_cr, Finset.mem_compl]; tauto

theorem cr_univ (u v : Fin m → Fin n) : cr u v Finset.univ = ∅ := by
  ext i; simp [mem_cr]

theorem cr_symmDiff (u v : Fin m → Fin n) (U W : Finset (Fin n)) :
    cr u v (U ∆ W) = cr u v U ∆ cr u v W := by
  ext i; simp only [mem_cr, Finset.mem_symmDiff]; tauto

theorem mem_bd (u v : Fin m → Fin n) (x : Finset (Fin m)) (j : Fin n) :
    j ∈ bd u v x ↔ (pc (x.filter (fun i => u i = j)) + pc (x.filter (fun i => v i = j)) = 1) := by
  unfold bd pc
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [← Nat.cast_add, ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]

theorem bd_empty (u v : Fin m → Fin n) : bd u v ∅ = ∅ := by
  ext j; simp [mem_bd, pc]

theorem bd_symmDiff (u v : Fin m → Fin n) (x y : Finset (Fin m)) :
    bd u v (x ∆ y) = bd u v x ∆ bd u v y := by
  ext j
  rw [Finset.mem_symmDiff, mem_bd, mem_bd, mem_bd, filter_symmDiff', filter_symmDiff',
    pc_symmDiff, pc_symmDiff]
  generalize pc (Finset.filter (fun i => u i = j) x) = a
  generalize pc (Finset.filter (fun i => u i = j) y) = b
  generalize pc (Finset.filter (fun i => v i = j) x) = c
  generalize pc (Finset.filter (fun i => v i = j) y) = d
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;> decide

theorem parity_id (u v : Fin m → Fin n) (x : Finset (Fin m)) (U : Finset (Fin n)) :
    pc (bd u v x ∩ U) = pc (x ∩ cr u v U) := by
  have e1 : bd u v x ∩ U = U.filter (fun j => j ∈ bd u v x) := by
    ext j; simp only [Finset.mem_inter, Finset.mem_filter]; tauto
  have e2 : x ∩ cr u v U = x.filter (fun i => i ∈ cr u v U) := by
    ext i; simp only [Finset.mem_inter, Finset.mem_filter]
  rw [e1, e2, pc_eq_sum, pc_eq_sum]
  have step1 : ∀ j ∈ U, (if j ∈ bd u v x then (1 : ZMod 2) else 0) =
      ∑ i ∈ x, ((if u i = j then (1 : ZMod 2) else 0) + (if v i = j then 1 else 0)) := by
    intro j _
    have hm := mem_bd u v x j
    rw [pc_eq_sum, pc_eq_sum, ← Finset.sum_add_distrib] at hm
    rcases zmod2_cases (∑ i ∈ x, ((if u i = j then (1 : ZMod 2) else 0) +
        (if v i = j then 1 else 0))) with h | h
    · rw [if_neg (by rw [hm, h]; decide), h]
    · rw [if_pos (by rw [hm]; exact h), h]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  by_cases h1 : u i ∈ U <;> by_cases h2 : v i ∈ U <;> simp [h1, h2, mem_cr] <;> decide

theorem insert_eq_symmDiff {α : Type*} [DecidableEq α] {a : α} {y : Finset α} (h : a ∉ y) :
    insert a y = {a} ∆ y := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
  by_cases hb : b = a
  · subst hb; simp [h]
  · simp [hb]

theorem realize (u v : Fin m → Fin n) (E : Finset (Fin m)) :
    ∀ e : Finset (Fin n), (∀ U : Finset (Fin n), Disjoint (cr u v U) E → pc (e ∩ U) = 0) →
      ∃ y ⊆ E, bd u v y = e := by
  induction E using Finset.induction_on with
  | empty =>
    intro e he
    refine ⟨∅, Finset.Subset.refl _, ?_⟩
    rw [bd_empty]
    symm
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    have := he {j} (Finset.disjoint_empty_right _)
    rw [Finset.inter_singleton_of_mem hj, pc_singleton] at this
    exact absurd this (by decide)
  | @insert a E ha ih =>
    intro e he
    by_cases h1 : ∀ U : Finset (Fin n), Disjoint (cr u v U) E → pc (e ∩ U) = 0
    · obtain ⟨y, hyE, hy⟩ := ih e h1
      exact ⟨y, hyE.trans (Finset.subset_insert _ _), hy⟩
    by_cases h2 : ∀ U : Finset (Fin n), Disjoint (cr u v U) E →
        pc ((e ∆ bd u v {a}) ∩ U) = 0
    · obtain ⟨y, hyE, hy⟩ := ih _ h2
      have hay : a ∉ y := fun h => ha (hyE h)
      refine ⟨insert a y, Finset.insert_subset_insert _ hyE, ?_⟩
      rw [insert_eq_symmDiff hay, bd_symmDiff, hy, symmDiff_comm e, symmDiff_symmDiff_cancel_left]
    exfalso
    push_neg at h1 h2
    obtain ⟨U1, hU1d, hU1⟩ := h1
    obtain ⟨U2, hU2d, hU2⟩ := h2
    have ha1 : a ∈ cr u v U1 := by
      by_contra hn
      exact hU1 (he U1 (Finset.disjoint_insert_right.mpr ⟨hn, hU1d⟩))
    have pD2 := parity_id u v {a} U2
    rw [symmDiff_inter_right, pc_symmDiff] at hU2
    have ha2 : a ∈ cr u v U2 := by
      by_contra hn
      have h0 : ({a} : Finset (Fin m)) ∩ cr u v U2 = ∅ := by
        ext b; simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, hb⟩; exact absurd hb hn
        · intro hb; simp at hb
      rw [h0, pc_empty] at pD2
      rw [pD2, add_zero] at hU2
      exact hU2 (he U2 (Finset.disjoint_insert_right.mpr ⟨hn, hU2d⟩))
    rw [Finset.singleton_inter_of_mem ha2, pc_singleton] at pD2
    rw [pD2] at hU2
    have hU2' : pc (e ∩ U2) = 0 := by
      rcases zmod2_cases (pc (e ∩ U2)) with h | h
      · exact h
      · rw [h] at hU2; exact absurd hU2 (by decide)
    have hU1' : pc (e ∩ U1) = 1 := by
      rcases zmod2_cases (pc (e ∩ U1)) with h | h
      · exact absurd h hU1
      · exact h
    have hd3 : Disjoint (cr u v (U1 ∆ U2)) (insert a E) := by
      rw [Finset.disjoint_insert_right, cr_symmDiff]
      constructor
      · rw [Finset.mem_symmDiff]; tauto
      · rw [Finset.disjoint_left]
        intro i hi hiE
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨hi, _⟩ | ⟨hi, _⟩
        · exact Finset.disjoint_left.mp hU1d hi hiE
        · exact Finset.disjoint_left.mp hU2d hi hiE
    have := he _ hd3
    rw [inter_symmDiff_left, pc_symmDiff, hU1', hU2'] at this
    exact absurd this (by decide)

theorem mem_shores {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ} {U : Finset (Fin n)} :
    U ∈ shores u v T k ↔ cr u v U ⊆ T ∧ (cr u v U).card ≤ k := by
  unfold shores; simp

theorem mem_sg {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ} {i : Fin n}
    {U : Finset (Fin n)} : U ∈ sg u v T k i ↔ U ∈ shores u v T k ∧ i ∈ U := by
  unfold sg; rw [Finset.mem_filter]

theorem sg_mem_iff {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ} {i j : Fin n}
    {U : Finset (Fin n)} (h : sg u v T k i = sg u v T k j) (hU : U ∈ shores u v T k) :
    i ∈ U ↔ j ∈ U := by
  have h1 : U ∈ sg u v T k i ↔ U ∈ sg u v T k j := by rw [h]
  simp only [mem_sg, hU, true_and] at h1
  exact h1

theorem shores_compl {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ} {U : Finset (Fin n)}
    (h : U ∈ shores u v T k) : Uᶜ ∈ shores u v T k := by
  rw [mem_shores, cr_compl]; exact mem_shores.mp h

theorem univ_mem_shores (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) :
    (Finset.univ : Finset (Fin n)) ∈ shores u v T k := by
  rw [mem_shores, cr_univ]; simp

theorem submod {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ} {U W : Finset (Fin n)}
    (hU : U ∈ shores u v T k) (hW : W ∈ shores u v T k) :
    U ∩ W ∈ shores u v T k ∨ U ∪ W ∈ shores u v T k := by
  rw [mem_shores] at hU hW ⊢
  rw [mem_shores]
  obtain ⟨hU1, hU2⟩ := hU
  obtain ⟨hW1, hW2⟩ := hW
  have s1 : cr u v (U ∩ W) ∪ cr u v (U ∪ W) ⊆ cr u v U ∪ cr u v W := by
    intro i; simp only [Finset.mem_union, mem_cr, Finset.mem_inter]; tauto
  have s2 : cr u v (U ∩ W) ∩ cr u v (U ∪ W) ⊆ cr u v U ∩ cr u v W := by
    intro i; simp only [Finset.mem_union, mem_cr, Finset.mem_inter]; tauto
  have c1 := Finset.card_union_add_card_inter (cr u v (U ∩ W)) (cr u v (U ∪ W))
  have c2 := Finset.card_union_add_card_inter (cr u v U) (cr u v W)
  have c3 := Finset.card_le_card s1
  have c4 := Finset.card_le_card s2
  have t1 : cr u v (U ∩ W) ⊆ T := fun i hi =>
    (Finset.union_subset hU1 hW1) (s1 (Finset.mem_union_left _ hi))
  have t2 : cr u v (U ∪ W) ⊆ T := fun i hi =>
    (Finset.union_subset hU1 hW1) (s1 (Finset.mem_union_right _ hi))
  by_cases h : (cr u v (U ∩ W)).card ≤ k
  · exact Or.inl ⟨t1, h⟩
  · exact Or.inr ⟨t2, by omega⟩

theorem even_of_blocks {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ}
    (e U : Finset (Fin n)) (hU : U ∈ shores u v T k)
    (he : ∀ i, pc (e.filter (fun j => sg u v T k j = sg u v T k i)) = 0) : pc (e ∩ U) = 0 := by
  unfold pc
  rw [Finset.card_eq_sum_card_image (sg u v T k) (e ∩ U), Nat.cast_sum]
  apply Finset.sum_eq_zero
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hσ
  have : (e ∩ U).filter (fun j => sg u v T k j = sg u v T k i) =
      e.filter (fun j => sg u v T k j = sg u v T k i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      exact (sg_mem_iff h3 hU).mpr (Finset.mem_inter.mp hi).2
  rw [this]; exact he i

theorem blocks_of_even {u v : Fin m → Fin n} {T : Finset (Fin m)} {k : ℕ} :
    ∀ (N : ℕ) (e : Finset (Fin n)), e.card ≤ N →
    (∀ U ∈ shores u v T k, pc (e ∩ U) = 0) →
    ∀ i, pc (e.filter (fun j => sg u v T k j = sg u v T k i)) = 0 := by
  intro N
  induction N with
  | zero =>
    intro e he _ i
    have : e = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp he)
    subst this; simp [pc]
  | succ N ih =>
    intro e hcard he i
    by_contra hne
    have hodd : pc (e.filter (fun j => sg u v T k j = sg u v T k i)) = 1 := by
      rcases zmod2_cases (pc (e.filter (fun j => sg u v T k j = sg u v T k i))) with h | h
      · exact absurd h hne
      · exact h
    have hne' : (e.filter (fun j => sg u v T k j = sg u v T k i)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h, pc_empty] at hodd
      exact absurd hodd (by decide)
    obtain ⟨s, hs⟩ := hne'
    rw [Finset.mem_filter] at hs
    have hev : pc e = 0 := by
      have := he Finset.univ (univ_mem_shores u v T k)
      rwa [Finset.inter_univ] at this
    have hex : ∃ t ∈ e, sg u v T k t ≠ sg u v T k i := by
      by_contra hcon
      push_neg at hcon
      have : e.filter (fun j => sg u v T k j = sg u v T k i) = e := Finset.filter_true_of_mem hcon
      rw [this, hev] at hodd
      exact absurd hodd (by decide)
    obtain ⟨t, ht, hti⟩ := hex
    have hst : sg u v T k s ≠ sg u v T k t := by rw [hs.2]; exact fun h => hti h.symm
    have hW : ∃ W ∈ shores u v T k, s ∈ W ∧ t ∉ W := by
      by_contra hcon
      push_neg at hcon
      apply hst
      ext W
      simp only [mem_sg]
      constructor
      · rintro ⟨hW, hsW⟩; exact ⟨hW, hcon W hW hsW⟩
      · rintro ⟨hW, htW⟩
        refine ⟨hW, ?_⟩
        by_contra hsW
        have := hcon Wᶜ (shores_compl hW) (Finset.mem_compl.mpr hsW)
        exact (Finset.mem_compl.mp this) htW
    obtain ⟨W, hW, hsW, htW⟩ := hW
    have hcard' : (e ∩ W).card ≤ N := by
      have : e ∩ W ⊂ e := ⟨Finset.inter_subset_left,
        fun h => htW (Finset.mem_inter.mp (h ht)).2⟩
      have := Finset.card_lt_card this
      omega
    have he'ev : ∀ U ∈ shores u v T k, pc (e ∩ W ∩ U) = 0 := by
      intro U hU
      have eq1 : e ∩ W ∩ U = e ∩ (U ∩ W) := by
        ext; simp only [Finset.mem_inter]; tauto
      rw [eq1]
      rcases submod hU hW with h | h
      · exact he _ h
      · have c := Finset.card_union_add_card_inter (e ∩ U) (e ∩ W)
        have q1 : (e ∩ U) ∪ (e ∩ W) = e ∩ (U ∪ W) := (Finset.inter_union_distrib_left _ _ _).symm
        have q2 : (e ∩ U) ∩ (e ∩ W) = e ∩ (U ∩ W) := by
          ext; simp only [Finset.mem_inter]; tauto
        rw [q1, q2] at c
        have hc := congrArg (Nat.cast : ℕ → ZMod 2) c
        push_cast at hc
        have h1 := he _ h
        have h2 := he U hU
        have h3 := he W hW
        unfold pc at h1 h2 h3 ⊢
        rw [h1, h2, h3] at hc
        simpa using hc
    have key := ih (e ∩ W) hcard' he'ev i
    have eq2 : (e ∩ W).filter (fun j => sg u v T k j = sg u v T k i) =
        e.filter (fun j => sg u v T k j = sg u v T k i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        have : sg u v T k j = sg u v T k s := h3.trans hs.2.symm
        exact (sg_mem_iff this hW).mpr hsW
    rw [eq2] at key
    exact hne key

theorem exists_section {α β : Type*} [DecidableEq α] [DecidableEq β] (π : α → β)
    (S : Finset α) : ∃ R ⊆ S, R.image π = S.image π ∧ Set.InjOn π R := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, rfl, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨R, hRS, hRi, hinj⟩ := ih
    by_cases hπ : π a ∈ S.image π
    · refine ⟨R, hRS.trans (Finset.subset_insert _ _), ?_, hinj⟩
      rw [hRi, Finset.image_insert, Finset.insert_eq_of_mem hπ]
    · refine ⟨insert a R, Finset.insert_subset_insert _ hRS, ?_, ?_⟩
      · rw [Finset.image_insert, Finset.image_insert, hRi]
      · rw [Finset.coe_insert, Set.injOn_insert (fun h => ha (hRS h))]
        refine ⟨hinj, ?_⟩
        rw [← Finset.coe_image, hRi]
        exact hπ

theorem filter_sec {α β : Type*} [DecidableEq α] [DecidableEq β] {π : α → β} {R : Finset α}
    (hinj : Set.InjOn π R) (q : α → Prop) [DecidablePred q] {r : α} (hr : r ∈ R) :
    (R.filter q).filter (fun σ => π σ = π r) = if q r then {r} else ∅ := by
  ext a
  simp only [Finset.mem_filter]
  split_ifs with h
  · rw [Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ha, _⟩, he⟩; exact hinj ha hr he
    · rintro rfl; exact ⟨⟨hr, h⟩, rfl⟩
  · simp only [Finset.notMem_empty, iff_false, not_and]
    intro ha he
    have := hinj ha.1 hr he
    subst this
    exact h ha.2

theorem comb_count {α β : Type*} [DecidableEq α] [DecidableEq β] (π : α → β) (S : Finset α) :
    (S.powerset.filter (fun A => ∀ τ ∈ S.image π, pc (A.filter (fun σ => π σ = τ)) = 0)).card =
      2 ^ (S.card - (S.image π).card) := by
  obtain ⟨R, hRS, hRi, hinj⟩ := exists_section π S
  have hRcard : R.card = (S.image π).card := by
    rw [← hRi, Finset.card_image_of_injOn hinj]
  rw [← hRcard, ← Finset.card_sdiff_of_subset hRS, ← Finset.card_powerset]
  apply Finset.card_nbij' (fun A => A \ R)
    (fun A₀ => A₀ ∪ R.filter (fun a => pc (A₀.filter (fun σ => π σ = π a)) = 1))
  · intro A hA
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hA
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    exact Finset.sdiff_subset_sdiff hA.1 (le_refl _)
  · intro A₀ hA₀
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hA₀
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset]
    refine ⟨Finset.union_subset (hA₀.trans Finset.sdiff_subset)
      (Finset.filter_subset _ _ |>.trans hRS), ?_⟩
    intro τ hτ
    rw [← hRi] at hτ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hτ
    rw [Finset.filter_union, filter_sec hinj _ hr]
    have hdisj : Disjoint (A₀.filter (fun σ => π σ = π r))
        (if pc (A₀.filter (fun σ => π σ = π r)) = 1 then {r} else ∅) := by
      split_ifs
      · rw [Finset.disjoint_singleton_right, Finset.mem_filter]
        intro h
        have := hA₀ h.1
        rw [Finset.mem_sdiff] at this
        exact this.2 hr
      · exact Finset.disjoint_empty_right _
    rw [pc_union_disj hdisj]
    rcases zmod2_cases (pc (A₀.filter (fun σ => π σ = π r))) with h | h
    · rw [if_neg (by rw [h]; decide), pc_empty, h]; decide
    · rw [if_pos h, pc_singleton, h]; decide
  · intro A hA
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hA
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
    by_cases haR : a ∈ R
    · have hev := hA.2 (π a) (Finset.mem_image_of_mem π (hRS haR))
      have hsplit : A.filter (fun σ => π σ = π a) =
          (A \ R).filter (fun σ => π σ = π a) ∪
            (R.filter (fun σ => σ ∈ A)).filter (fun σ => π σ = π a) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        by_cases hb : b ∈ R <;> simp [hb]
      have hdisj : Disjoint ((A \ R).filter (fun σ => π σ = π a))
          ((R.filter (fun σ => σ ∈ A)).filter (fun σ => π σ = π a)) := by
        rw [Finset.disjoint_left]
        intro b hb1 hb2
        simp only [Finset.mem_filter, Finset.mem_sdiff] at hb1 hb2
        exact hb1.1.2 hb2.1.1
      rw [hsplit, pc_union_disj hdisj, filter_sec hinj _ haR] at hev
      by_cases haA : a ∈ A
      · rw [if_pos haA, pc_singleton] at hev
        have : pc ((A \ R).filter (fun σ => π σ = π a)) = 1 := by
          rcases zmod2_cases (pc ((A \ R).filter (fun σ => π σ = π a))) with h | h
          · rw [h] at hev; exact absurd hev (by decide)
          · exact h
        simp [haR, haA, this]
      · rw [if_neg haA, pc_empty, add_zero] at hev
        simp [haR, haA, hev]
    · simp [haR]
  · intro A₀ hA₀
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hA₀
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1.1 h2
    · intro h
      have := hA₀ h
      rw [Finset.mem_sdiff] at this
      exact ⟨Or.inl h, this.2⟩

theorem total_shift (u v : Fin m → Fin n) (d d' : Finset (Fin n))
    (F : Finset (Finset (Fin m × Bool))) (y S : Finset (Fin m)) (hyS : Disjoint y S)
    (hy : bd u v y = d ∆ d') (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 ∈ S) :
    total u v d F = total u v d' F := by
  have hcl : ∀ x, ∀ C ∈ F, (∃ l ∈ C, decide (l.1 ∈ x) = l.2) →
      (∃ l ∈ C, decide (l.1 ∈ x ∆ y) = l.2) := by
    intro x C hC hx
    obtain ⟨l, hl, hlx⟩ := hx
    refine ⟨l, hl, ?_⟩
    have hlS := hF C hC l hl
    have hly : l.1 ∉ y := fun h => Finset.disjoint_left.mp hyS h hlS
    rw [← hlx]
    exact decide_eq_decide.mpr (by rw [Finset.mem_symmDiff]; tauto)
  unfold total
  apply Finset.card_nbij' (fun x => x ∆ y) (fun x => x ∆ y)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, fun C hC => hcl x C hC (hx.2 C hC)⟩
    rw [bd_symmDiff, hx.1, hy, symmDiff_symmDiff_cancel_left]
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, fun C hC => hcl x C hC (hx.2 C hC)⟩
    rw [bd_symmDiff, hx.1, hy, symmDiff_comm d d', symmDiff_symmDiff_cancel_left]
  · intro x _
    simp only [symmDiff_symmDiff_cancel_right]
  · intro x _
    simp only [symmDiff_symmDiff_cancel_right]

theorem realize_off (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) (d d' : Finset (Fin n))
    (h : ∀ U ∈ shores u v T k, pc ((d ∆ d') ∩ U) = 0) (S : Finset (Fin m)) (hST : S ⊆ T)
    (hSk : S.card ≤ k) : ∃ y, Disjoint y S ∧ bd u v y = d ∆ d' := by
  obtain ⟨y, hyE, hy⟩ := realize u v (Finset.univ \ S) (d ∆ d') (by
    intro U hU
    apply h
    have hsub : cr u v U ⊆ S := by
      intro i hi
      by_contra hiS
      exact Finset.disjoint_left.mp hU hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiS⟩)
    rw [mem_shores]
    exact ⟨hsub.trans hST, (Finset.card_le_card hsub).trans hSk⟩)
  refine ⟨y, ?_, hy⟩
  rw [Finset.disjoint_left]
  intro i hiy hiS
  exact (Finset.mem_sdiff.mp (hyE hiy)).2 hiS

theorem F3count (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : ℕ) (d d' : Finset (Fin n))
    (h : ∀ U ∈ shores u v T (t * w), pc ((d ∆ d') ∩ U) = 0)
    (F : Finset (Finset (Fin m × Bool))) (hF : valid T t w F) :
    total u v d F = total u v d' F := by
  have hSF : ∀ C ∈ F, ∀ l ∈ C, l.1 ∈ F.biUnion (fun C => C.image Prod.fst) := by
    intro C hC l hl
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_image_of_mem _ hl⟩
  have hST : F.biUnion (fun C => C.image Prod.fst) ⊆ T := by
    intro i hi
    obtain ⟨C, hC, hiC⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hiC
    exact (hF.2 C hC).2 l hl
  have hScard : (F.biUnion (fun C => C.image Prod.fst)).card ≤ t * w := by
    calc (F.biUnion (fun C => C.image Prod.fst)).card
        ≤ ∑ C ∈ F, (C.image Prod.fst).card := Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ F, w :=
          Finset.sum_le_sum (fun C hC => (Finset.card_image_le).trans (hF.2 C hC).1)
      _ = F.card * w := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ t * w := Nat.mul_le_mul_right _ hF.1
  obtain ⟨y, hyS, hy⟩ := realize_off u v T (t * w) d d' h _ hST hScard
  exact total_shift u v d d' F y _ hyS hy hSF

theorem sat_witness_set (T : Finset (Fin m)) (x : Finset (Fin m)) :
    ∀ F : Finset (Finset (Fin m × Bool)), (∀ C ∈ F, ∀ l ∈ C, l.1 ∈ T) →
    (∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2) →
    ∃ S : Finset (Fin m), S ⊆ T ∧ S.card ≤ F.card ∧
      ∀ C ∈ F, ∃ l ∈ C, l.1 ∈ S ∧ decide (l.1 ∈ x) = l.2 := by
  intro F
  induction F using Finset.induction_on with
  | empty => intro _ _; exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | @insert C F hC ih =>
    intro hT hx
    obtain ⟨S, hST, hSc, hS⟩ := ih (fun C' hC' => hT C' (Finset.mem_insert_of_mem hC'))
      (fun C' hC' => hx C' (Finset.mem_insert_of_mem hC'))
    obtain ⟨l, hl, hlx⟩ := hx C (Finset.mem_insert_self _ _)
    refine ⟨insert l.1 S, Finset.insert_subset (hT C (Finset.mem_insert_self _ _) l hl) hST,
      ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hC]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hSc)
    · intro C' hC'
      rcases Finset.mem_insert.mp hC' with rfl | hC'
      · exact ⟨l, hl, Finset.mem_insert_self _ _, hlx⟩
      · obtain ⟨l', hl', hl'S, hl'x⟩ := hS C' hC'
        exact ⟨l', hl', Finset.mem_insert_of_mem hl'S, hl'x⟩

theorem F3sat_dir (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : ℕ) (d d' : Finset (Fin n))
    (h : ∀ U ∈ shores u v T t, pc ((d ∆ d') ∩ U) = 0)
    (F : Finset (Finset (Fin m × Bool))) (hF : valid T t w F)
    (hpos : 0 < total u v d F) : 0 < total u v d' F := by
  unfold total at hpos ⊢
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hx
  obtain ⟨S, hST, hSc, hS⟩ := sat_witness_set T x F (fun C hC => (hF.2 C hC).2) hx.2.2
  obtain ⟨y, hyS, hy⟩ := realize_off u v T t d d' h S hST (hSc.trans hF.1)
  apply Finset.card_pos.mpr
  refine ⟨x ∆ y, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · rw [bd_symmDiff, hx.2.1, hy, symmDiff_symmDiff_cancel_left]
  · intro C hC
    obtain ⟨l, hl, hlS, hlx⟩ := hS C hC
    refine ⟨l, hl, ?_⟩
    have hly : l.1 ∉ y := fun h' => Finset.disjoint_left.mp hyS h' hlS
    rw [← hlx]
    exact decide_eq_decide.mpr (by rw [Finset.mem_symmDiff]; tauto)

theorem F3sat (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : ℕ) (d d' : Finset (Fin n))
    (h : ∀ U ∈ shores u v T t, pc ((d ∆ d') ∩ U) = 0)
    (F : Finset (Finset (Fin m × Bool))) (hF : valid T t w F) :
    min 1 (total u v d F) = min 1 (total u v d' F) := by
  have h' : ∀ U ∈ shores u v T t, pc ((d' ∆ d) ∩ U) = 0 := by
    intro U hU; rw [symmDiff_comm]; exact h U hU
  have a1 := F3sat_dir u v T t w d d' h F hF
  have a2 := F3sat_dir u v T t w d' d h' F hF
  by_cases h0 : total u v d F = 0
  · have : total u v d' F = 0 := by
      by_contra hne
      have := a2 (Nat.pos_of_ne_zero hne)
      omega
    rw [h0, this]
  · have := a1 (Nat.pos_of_ne_zero h0)
    omega

theorem no_agree (u v : Fin m → Fin n) {d d' : Finset (Fin n)} {x0 x : Finset (Fin m)}
    {U : Finset (Fin n)} (hx0 : bd u v x0 = d) (hx : bd u v x = d')
    (hodd : pc ((d ∆ d') ∩ U) = 1) (hag : ∀ i ∈ cr u v U, (i ∈ x ↔ i ∈ x0)) : False := by
  have hagree : x ∩ cr u v U = x0 ∩ cr u v U := by
    ext i; simp only [Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hag i h2).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hag i h2).mpr h1, h2⟩
  have p1 := parity_id u v x0 U
  have p2 := parity_id u v x U
  rw [hx0] at p1
  rw [hx] at p2
  rw [symmDiff_inter_right, pc_symmDiff, p1, p2, hagree] at hodd
  generalize pc (x0 ∩ cr u v U) = a at hodd
  rcases zmod2_cases a with rfl | rfl <;> exact absurd hodd (by decide)

theorem F4sat (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : ℕ) (hw : 0 < w)
    (d d' : Finset (Fin n)) (x0 : Finset (Fin m)) (hx0 : bd u v x0 = d)
    (U : Finset (Fin n)) (hU : U ∈ shores u v T t) (hodd : pc ((d ∆ d') ∩ U) = 1) :
    ∃ F, valid T t w F ∧ min 1 (total u v d F) ≠ min 1 (total u v d' F) := by
  rw [mem_shores] at hU
  refine ⟨(cr u v U).image (fun i => ({(i, decide (i ∈ x0))} : Finset (Fin m × Bool))),
    ⟨?_, ?_⟩, ?_⟩
  · exact Finset.card_image_le.trans hU.2
  · intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨by rw [Finset.card_singleton]; omega, ?_⟩
    intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact hU.1 hi
  · have hpos : 0 < total u v d
        ((cr u v U).image (fun i => ({(i, decide (i ∈ x0))} : Finset (Fin m × Bool)))) := by
      unfold total
      apply Finset.card_pos.mpr
      refine ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0, ?_⟩⟩
      intro C hC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact ⟨(i, decide (i ∈ x0)), Finset.mem_singleton_self _, rfl⟩
    have hzero : total u v d'
        ((cr u v U).image (fun i => ({(i, decide (i ∈ x0))} : Finset (Fin m × Bool)))) = 0 := by
      unfold total
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨_, hxd, hxF⟩ := hx
      apply no_agree u v hx0 hxd hodd
      intro i hi
      obtain ⟨l, hl, hlx⟩ := hxF _ (Finset.mem_image_of_mem _ hi)
      rw [Finset.mem_singleton] at hl
      subst hl
      exact decide_eq_decide.mp hlx
    rw [hzero]
    omega

theorem ie_lemma {ι α : Type*} [DecidableEq ι] (P : ι → α → Prop) [∀ q, DecidablePred (P q)] :
    ∀ (I : Finset ι) (X Y : Finset α),
    (∀ J ⊆ I, (X.filter (fun x => ∀ q ∈ J, P q x)).card =
      (Y.filter (fun x => ∀ q ∈ J, P q x)).card) →
    (X.filter (fun x => ∀ q ∈ I, ¬ P q x)).card = (Y.filter (fun x => ∀ q ∈ I, ¬ P q x)).card := by
  intro I
  induction I using Finset.induction_on with
  | empty =>
    intro X Y h
    have := h ∅ (Finset.Subset.refl _)
    simpa using this
  | @insert a I ha ih =>
    intro X Y h
    have hX := Finset.card_filter_add_card_filter_not
      (s := X.filter (fun x => ∀ q ∈ I, ¬ P q x)) (P a)
    have hY := Finset.card_filter_add_card_filter_not
      (s := Y.filter (fun x => ∀ q ∈ I, ¬ P q x)) (P a)
    have eX : X.filter (fun x => ∀ q ∈ insert a I, ¬ P q x) =
        (X.filter (fun x => ∀ q ∈ I, ¬ P q x)).filter (fun x => ¬ P a x) := by
      ext x; simp only [Finset.mem_filter, Finset.forall_mem_insert]; tauto
    have eY : Y.filter (fun x => ∀ q ∈ insert a I, ¬ P q x) =
        (Y.filter (fun x => ∀ q ∈ I, ¬ P q x)).filter (fun x => ¬ P a x) := by
      ext x; simp only [Finset.mem_filter, Finset.forall_mem_insert]; tauto
    have fX : (X.filter (fun x => ∀ q ∈ I, ¬ P q x)).filter (P a) =
        (X.filter (P a)).filter (fun x => ∀ q ∈ I, ¬ P q x) := by
      ext x; simp only [Finset.mem_filter]; tauto
    have fY : (Y.filter (fun x => ∀ q ∈ I, ¬ P q x)).filter (P a) =
        (Y.filter (P a)).filter (fun x => ∀ q ∈ I, ¬ P q x) := by
      ext x; simp only [Finset.mem_filter]; tauto
    have i1 := ih X Y (fun J hJ => h J (hJ.trans (Finset.subset_insert _ _)))
    have i2 := ih (X.filter (P a)) (Y.filter (P a)) (by
      intro J hJ
      have := h (insert a J) (Finset.insert_subset_insert _ hJ)
      have e1 : (X.filter (P a)).filter (fun x => ∀ q ∈ J, P q x) =
          X.filter (fun x => ∀ q ∈ insert a J, P q x) := by
        ext x; simp only [Finset.mem_filter, Finset.forall_mem_insert]; tauto
      have e2 : (Y.filter (P a)).filter (fun x => ∀ q ∈ J, P q x) =
          Y.filter (fun x => ∀ q ∈ insert a J, P q x) := by
        ext x; simp only [Finset.mem_filter, Finset.forall_mem_insert]; tauto
      rw [e1, e2]; exact this)
    rw [eX, eY]
    rw [fX] at hX
    rw [fY] at hY
    omega

theorem rank_lt {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) :
    (S.filter (· < i)).card < S.card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => by
    have := h hi; simp at this⟩

theorem rank_inj_aux {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hlt : i < j) :
    (S.filter (· < i)).card < (S.filter (· < j)).card := by
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.trans hlt⟩
  · intro hsub
    have := hsub (Finset.mem_filter.mpr ⟨hi, hlt⟩)
    simp at this

theorem rank_inj {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S)
    (h : (S.filter (· < i)).card = (S.filter (· < j)).card) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := rank_inj_aux hi hlt; omega
  · have := rank_inj_aux hj hlt; omega

theorem group_card (S : Finset (Fin m)) (w q : ℕ) (hw : 0 < w) :
    (S.filter (fun i => (S.filter (· < i)).card / w = q)).card ≤ w := by
  have hsub : (S.filter (fun i => (S.filter (· < i)).card / w = q)).image
      (fun i => (S.filter (· < i)).card) ⊆ Finset.Ico (q * w) (q * w + w) := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_Ico]
    have h1 := Nat.div_mul_le_self (S.filter (· < i)).card w
    have h2 := Nat.lt_div_mul_add (a := (S.filter (· < i)).card) hw
    rw [hi.2] at h1 h2
    exact ⟨h1, h2⟩
  have hinj : Set.InjOn (fun i => (S.filter (· < i)).card)
      ↑(S.filter (fun i => (S.filter (· < i)).card / w = q)) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_filter] at hi hj
    exact rank_inj hi.1 hj.1 hij
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Ico, Nat.add_sub_cancel_left] at this
  exact this

theorem F4count (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : ℕ) (hw : 0 < w)
    (d d' : Finset (Fin n)) (x0 : Finset (Fin m)) (hx0 : bd u v x0 = d)
    (U : Finset (Fin n)) (hU : U ∈ shores u v T (t * w)) (hodd : pc ((d ∆ d') ∩ U) = 1) :
    ∃ F, valid T t w F ∧ total u v d F ≠ total u v d' F := by
  rw [mem_shores] at hU
  by_contra hcon
  push_neg at hcon
  have hval : ∀ J ⊆ Finset.range t, valid T t w (J.image (fun q =>
      ((cr u v U).filter (fun i => ((cr u v U).filter (· < i)).card / w = q)).image
        (fun i => (i, !decide (i ∈ x0))))) := by
    intro J hJ
    refine ⟨Finset.card_image_le.trans ((Finset.card_le_card hJ).trans_eq (Finset.card_range t)),
      ?_⟩
    intro C hC
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨Finset.card_image_le.trans (group_card _ w q hw), ?_⟩
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    exact hU.1 (Finset.mem_filter.mp hi).1
  have hIE := ie_lemma (fun q x => ∃ l ∈ ((cr u v U).filter
      (fun i => ((cr u v U).filter (· < i)).card / w = q)).image
        (fun i => (i, !decide (i ∈ x0))), decide (l.1 ∈ x) = l.2) (Finset.range t)
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bd u v x = d))
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bd u v x = d')) (by
      intro J hJ
      have := hcon _ (hval J hJ)
      unfold total at this
      have e1 : ∀ d0 : Finset (Fin n),
          ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bd u v x = d0)).filter
            (fun x => ∀ q ∈ J, ∃ l ∈ ((cr u v U).filter
              (fun i => ((cr u v U).filter (· < i)).card / w = q)).image
                (fun i => (i, !decide (i ∈ x0))), decide (l.1 ∈ x) = l.2) =
          (Finset.univ : Finset (Finset (Fin m))).filter (fun x => bd u v x = d0 ∧
            ∀ C ∈ J.image (fun q =>
              ((cr u v U).filter (fun i => ((cr u v U).filter (· < i)).card / w = q)).image
                (fun i => (i, !decide (i ∈ x0)))), ∃ l ∈ C, decide (l.1 ∈ x) = l.2) := by
        intro d0
        ext x
        simp only [Finset.mem_filter, Finset.forall_mem_image]
        tauto
      rw [e1 d, e1 d']
      exact this)
  have hL : x0 ∈ ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bd u v x = d)).filter
      (fun x => ∀ q ∈ Finset.range t, ¬ ∃ l ∈ ((cr u v U).filter
        (fun i => ((cr u v U).filter (· < i)).card / w = q)).image
          (fun i => (i, !decide (i ∈ x0))), decide (l.1 ∈ x) = l.2) := by
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, hx0⟩, ?_⟩
    intro q _ hex
    obtain ⟨l, hl, hlx⟩ := hex
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
    revert hlx
    dsimp only
    cases decide (i ∈ x0) <;> decide
  have hR : ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bd u v x = d')).filter
      (fun x => ∀ q ∈ Finset.range t, ¬ ∃ l ∈ ((cr u v U).filter
        (fun i => ((cr u v U).filter (· < i)).card / w = q)).image
          (fun i => (i, !decide (i ∈ x0))), decide (l.1 ∈ x) = l.2) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rw [Finset.mem_filter, Finset.mem_filter] at hx
    obtain ⟨⟨_, hxd⟩, hxq⟩ := hx
    apply no_agree u v hx0 hxd hodd
    intro i hi
    have hq : ((cr u v U).filter (· < i)).card / w < t := by
      apply Nat.div_lt_of_lt_mul
      have := rank_lt hi
      rw [Nat.mul_comm]
      exact lt_of_lt_of_le this hU.2
    have := hxq _ (Finset.mem_range.mpr hq)
    by_contra hne
    apply this
    refine ⟨(i, !decide (i ∈ x0)), Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨hi, rfl⟩), ?_⟩
    show decide (i ∈ x) = !decide (i ∈ x0)
    by_cases h1 : i ∈ x <;> by_cases h2 : i ∈ x0 <;> simp [h1, h2] at hne ⊢
  rw [hR, Finset.card_empty] at hIE
  exact absurd hIE (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨x0, hL⟩))


theorem code_iff {α κ : Type*} [Fintype α] [DecidableEq α] (valid : κ → Prop)
    [DecidablePred valid] [DecidableEq (κ → ℕ)] (resp : α → κ → ℕ) (b : ℕ) :
    (∃ (encode : α → Fin b) (decode : Fin b → κ → ℕ),
      ∀ d F, valid F → decode (encode d) F = resp d F) ↔
    ((Finset.univ : Finset α).image (fun d => fun F => if valid F then resp d F else 0)).card
      ≤ b := by
  constructor
  · rintro ⟨enc, dec, h⟩
    calc _ ≤ ((Finset.univ : Finset (Fin b)).image
            (fun j => fun F => if valid F then dec j F else 0)).card := by
          apply Finset.card_le_card
          intro r hr
          obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hr
          refine Finset.mem_image.mpr ⟨enc d, Finset.mem_univ _, ?_⟩
          funext F
          by_cases hF : valid F
          · simp only [hF, ↓reduceIte, h d F hF]
          · simp only [hF, ↓reduceIte]
      _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
      _ = b := Finset.card_fin b
  · intro hb
    let e := ((Finset.univ : Finset α).image
      (fun d => fun F => if valid F then resp d F else 0)).equivFin
    refine ⟨fun d => Fin.castLE hb (e ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ d)⟩),
      fun j F => if h : j.val < ((Finset.univ : Finset α).image
        (fun d => fun F => if valid F then resp d F else 0)).card then
          (e.symm ⟨j.val, h⟩).val F else 0, ?_⟩
    intro d F hF
    simp [hF]

theorem image_card_eq {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (f : α → β) (g : α → γ) (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) :
    (s.image f).card = (s.image g).card := by
  have h1 : (s.image (fun a => (f a, g a))).image Prod.fst = s.image f := by
    rw [Finset.image_image]; rfl
  have h2 : (s.image (fun a => (f a, g a))).image Prod.snd = s.image g := by
    rw [Finset.image_image]; rfl
  have i1 : Set.InjOn (Prod.fst : β × γ → β) (s.image (fun a => (f a, g a)) : Set (β × γ)) := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    simp only at hpq
    rw [Prod.mk.injEq]
    exact ⟨hpq, (h a ha b hb).mp hpq⟩
  have i2 : Set.InjOn (Prod.snd : β × γ → γ) (s.image (fun a => (f a, g a)) : Set (β × γ)) := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    simp only at hpq
    rw [Prod.mk.injEq]
    exact ⟨(h a ha b hb).mpr hpq, hpq⟩
  rw [← h1, ← h2, Finset.card_image_of_injOn i1, Finset.card_image_of_injOn i2]

def Pk (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) (d : Finset (Fin n)) :
    Finset (Finset (Finset (Fin n))) :=
  ((Finset.univ : Finset (Fin n)).image (sg u v T k)).filter
    (fun σ => pc (d.filter (fun i => sg u v T k i = σ)) = 1)

def proj (u v : Fin m → Fin n) (σ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  σ.filter (fun U => (cr u v U).card ≤ 0)

theorem sg_zero (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) (i : Fin n) :
    sg u v T 0 i = proj u v (sg u v T k i) := by
  ext U
  simp only [proj, Finset.mem_filter, mem_sg, mem_shores]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem S0_eq (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).image (sg u v T k)).image (proj u v) =
      (Finset.univ : Finset (Fin n)).image (sg u v T 0) := by
  rw [Finset.image_image]
  congr 1
  funext i
  exact (sg_zero u v T k i).symm

theorem fiber_rel (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) (d : Finset (Fin n))
    (τ : Finset (Finset (Fin n))) :
    pc (d.filter (fun i => sg u v T 0 i = τ)) =
      pc ((Pk u v T k d).filter (fun σ => proj u v σ = τ)) := by
  have H : ∀ i ∈ d.filter (fun i => sg u v T 0 i = τ), sg u v T k i ∈
      ((Finset.univ : Finset (Fin n)).image (sg u v T k)).filter (fun σ => proj u v σ = τ) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), by rw [← sg_zero]; exact hi.2⟩
  have e1 := Finset.card_eq_sum_card_fiberwise H
  have e2 : (Pk u v T k d).filter (fun σ => proj u v σ = τ) =
      (((Finset.univ : Finset (Fin n)).image (sg u v T k)).filter
        (fun σ => proj u v σ = τ)).filter (fun σ => σ ∈ Pk u v T k d) := by
    ext σ; simp only [Pk, Finset.mem_filter]; tauto
  rw [e2, pc_eq_sum _ (fun σ => σ ∈ Pk u v T k d)]
  unfold pc
  rw [e1, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mem_filter] at hσ
  have e3 : (d.filter (fun i => sg u v T 0 i = τ)).filter (fun i => sg u v T k i = σ) =
      d.filter (fun i => sg u v T k i = σ) := by
    ext i; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [sg_zero u v T k, h3, hσ.2]⟩, h3⟩
  rw [e3]
  show pc (d.filter (fun i => sg u v T k i = σ)) = _
  simp only [Pk, Finset.mem_filter, hσ.1, true_and]
  rcases zmod2_cases (pc (d.filter (fun i => sg u v T k i = σ))) with h | h
  · rw [h]; decide
  · rw [h]; decide

theorem Pk_eq_iff (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ) (d d' : Finset (Fin n)) :
    Pk u v T k d = Pk u v T k d' ↔
      ∀ i, pc ((d ∆ d').filter (fun j => sg u v T k j = sg u v T k i)) = 0 := by
  have key : ∀ σ, pc ((d ∆ d').filter (fun j => sg u v T k j = σ)) =
      pc (d.filter (fun j => sg u v T k j = σ)) + pc (d'.filter (fun j => sg u v T k j = σ)) := by
    intro σ; rw [filter_symmDiff', pc_symmDiff]
  have z : ∀ a b : ZMod 2, a + b = 0 ↔ (a = 1 ↔ b = 1) := by
    intro a b
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
  constructor
  · intro h i
    rw [key, z]
    have h2 : sg u v T k i ∈ Pk u v T k d ↔ sg u v T k i ∈ Pk u v T k d' := by rw [h]
    simp only [Pk, Finset.mem_filter, Finset.mem_image_of_mem _ (Finset.mem_univ i),
      true_and] at h2
    exact h2
  · intro h
    ext σ
    simp only [Pk, Finset.mem_filter]
    constructor
    · rintro ⟨hσ, h1⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hσ
      have := h i
      rw [key, z] at this
      exact ⟨hσ, this.mp h1⟩
    · rintro ⟨hσ, h1⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hσ
      have := h i
      rw [key, z] at this
      exact ⟨hσ, this.mpr h1⟩

theorem count_main (u v : Fin m → Fin n) (T : Finset (Fin m)) (k : ℕ)
    (valid : Finset (Finset (Fin m × Bool)) → Prop)
    (resp : Finset (Fin n) → Finset (Finset (Fin m × Bool)) → ℕ)
    (hvalid0 : valid ∅)
    (hpos : ∀ x, resp (bd u v x) ∅ ≠ 0)
    (hzero : ∀ d F, (∀ x, bd u v x ≠ d) → resp d F = 0)
    (hF3 : ∀ d d', (∀ U ∈ shores u v T k, pc ((d ∆ d') ∩ U) = 0) →
      ∀ F, valid F → resp d F = resp d' F)
    (hF4 : ∀ x d', ∀ U ∈ shores u v T k, pc ((bd u v x ∆ d') ∩ U) = 1 →
      ∃ F, valid F ∧ resp (bd u v x) F ≠ resp d' F)
    (b : ℕ) :
    (∃ (encode : Finset (Fin n) → Fin b)
        (decode : Fin b → Finset (Finset (Fin m × Bool)) → ℕ),
      ∀ d F, valid F → decode (encode d) F = resp d F) ↔
    2 ^ (sigs u v T k - sigs u v T 0) + (if n = 0 then 0 else 1) ≤ b := by
  classical
  rw [code_iff valid resp b]
  suffices hc : ((Finset.univ : Finset (Finset (Fin n))).image
      (fun d => fun F => if valid F then resp d F else 0)).card =
      2 ^ (sigs u v T k - sigs u v T 0) + (if n = 0 then 0 else 1) by rw [hc]
  have huniv : (Finset.univ : Finset (Finset (Fin n))) =
      ((Finset.univ : Finset (Finset (Fin m))).image (bd u v)) ∪
        (Finset.univ \ (Finset.univ : Finset (Finset (Fin m))).image (bd u v)) := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [huniv, Finset.image_union, Finset.card_union_of_disjoint]
  · congr 1
    · have hker : ∀ d ∈ (Finset.univ : Finset (Finset (Fin m))).image (bd u v),
          ∀ d' ∈ (Finset.univ : Finset (Finset (Fin m))).image (bd u v),
          (fun F => if valid F then resp d F else 0) =
            (fun F => if valid F then resp d' F else 0) ↔
            Pk u v T k d = Pk u v T k d' := by
        intro d hd d' _
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
        rw [Pk_eq_iff]
        constructor
        · intro hR
          apply blocks_of_even _ _ le_rfl
          intro U hU
          by_contra hne
          have h1 : pc ((bd u v x ∆ d') ∩ U) = 1 := (zmod2_cases _).resolve_left hne
          obtain ⟨F, hFv, hFne⟩ := hF4 x d' U hU h1
          have := congrFun hR F
          simp only [hFv, ↓reduceIte] at this
          exact hFne this
        · intro hB
          have hU : ∀ U ∈ shores u v T k, pc ((bd u v x ∆ d') ∩ U) = 0 :=
            fun U hU => even_of_blocks _ U hU hB
          funext F
          by_cases hFv : valid F
          · simp only [hFv, ↓reduceIte]; exact hF3 _ _ hU F hFv
          · simp only [hFv, ↓reduceIte]
      have hGood : ((Finset.univ : Finset (Finset (Fin m))).image (bd u v)).image (Pk u v T k) =
          ((Finset.univ : Finset (Fin n)).image (sg u v T k)).powerset.filter
            (fun A => ∀ τ ∈ ((Finset.univ : Finset (Fin n)).image (sg u v T k)).image (proj u v),
              pc (A.filter (fun σ => proj u v σ = τ)) = 0) := by
        ext A
        rw [Finset.mem_filter, Finset.mem_powerset, S0_eq]
        constructor
        · intro hA
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hA
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro τ hτ
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hτ
          rw [← fiber_rel]
          apply blocks_of_even (k := 0) _ _ le_rfl
          intro U hU
          rw [parity_id]
          have : cr u v U = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (mem_shores.mp hU).2)
          rw [this, Finset.inter_empty, pc_empty]
        · rintro ⟨hAS, hA⟩
          have hPk : Pk u v T k ((Finset.univ : Finset (Fin n)).filter (fun i =>
              sg u v T k i ∈ A ∧ ∀ j, sg u v T k j = sg u v T k i → i ≤ j)) = A := by
            ext σ
            unfold Pk
            rw [Finset.mem_filter]
            constructor
            · rintro ⟨_, h1⟩
              by_contra hσA
              have : ((Finset.univ : Finset (Fin n)).filter (fun i =>
                  sg u v T k i ∈ A ∧ ∀ j, sg u v T k j = sg u v T k i → i ≤ j)).filter
                    (fun i => sg u v T k i = σ) = ∅ := by
                apply Finset.eq_empty_of_forall_notMem
                intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                exact hσA (hi.2 ▸ hi.1.1)
              rw [this, pc_empty] at h1
              exact absurd h1 (by decide)
            · intro hσA
              have hσ := hAS hσA
              refine ⟨hσ, ?_⟩
              obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp hσ
              have hne : ((Finset.univ : Finset (Fin n)).filter
                  (fun j => sg u v T k j = σ)).Nonempty := ⟨i0, by simp [hi0]⟩
              obtain ⟨imin, hmem, hle⟩ : ∃ imin, sg u v T k imin = σ ∧
                  ∀ j, sg u v T k j = σ → imin ≤ j :=
                ⟨((Finset.univ : Finset (Fin n)).filter (fun j => sg u v T k j = σ)).min' hne,
                  (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2,
                  fun j hj => Finset.min'_le ((Finset.univ : Finset (Fin n)).filter
                    (fun j => sg u v T k j = σ)) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
              have : ((Finset.univ : Finset (Fin n)).filter (fun i =>
                  sg u v T k i ∈ A ∧ ∀ j, sg u v T k j = sg u v T k i → i ≤ j)).filter
                    (fun i => sg u v T k i = σ) = {imin} := by
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                constructor
                · rintro ⟨⟨_, hmin⟩, hi⟩
                  exact le_antisymm (hmin imin (hmem.trans hi.symm)) (hle i hi)
                · rintro rfl
                  exact ⟨⟨hmem ▸ hσA, fun j hj => hle j (hj.trans hmem)⟩, hmem⟩
              rw [this, pc_singleton]
          obtain ⟨y, _, hy⟩ := realize u v Finset.univ ((Finset.univ : Finset (Fin n)).filter
              (fun i => sg u v T k i ∈ A ∧ ∀ j, sg u v T k j = sg u v T k i → i ≤ j)) (by
            intro U hU
            have hcr : cr u v U = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro i hi
              exact Finset.disjoint_left.mp hU hi (Finset.mem_univ i)
            have hU0 : U ∈ shores u v T 0 := by rw [mem_shores, hcr]; simp
            apply even_of_blocks _ U hU0
            intro i
            rw [fiber_rel u v T k, hPk]
            exact hA _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
          exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy⟩, hPk⟩
      have hc := comb_count (proj u v) ((Finset.univ : Finset (Fin n)).image (sg u v T k))
      rw [image_card_eq _ _ (Pk u v T k) hker, hGood]
      refine Eq.trans ?_ (hc.trans ?_)
      · first
          | rfl
          | (congr 1; ext A; simp only [Finset.mem_filter])
      · rw [S0_eq]; rfl
    · have hz : ∀ d ∈ (Finset.univ \ (Finset.univ : Finset (Finset (Fin m))).image (bd u v)),
          (fun F => if valid F then resp d F else 0) = fun _ => 0 := by
        intro d hd
        rw [Finset.mem_sdiff] at hd
        have hd' : ∀ x, bd u v x ≠ d := fun x hx =>
          hd.2 (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)
        funext F
        rw [hzero d F hd']
        simp
      by_cases hn : n = 0
      · rw [if_pos hn]
        subst hn
        have : (Finset.univ \ (Finset.univ : Finset (Finset (Fin m))).image (bd u v)) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro d hd
          rw [Finset.mem_sdiff] at hd
          apply hd.2
          have hd0 : d = ∅ := Finset.eq_empty_of_isEmpty d
          exact Finset.mem_image.mpr ⟨∅, Finset.mem_univ _, by rw [hd0, bd_empty]⟩
        rw [this, Finset.image_empty, Finset.card_empty]
      · rw [if_neg hn]
        have hmem0 : ({⟨0, Nat.pos_of_ne_zero hn⟩} : Finset (Fin n)) ∈
            (Finset.univ \ (Finset.univ : Finset (Finset (Fin m))).image (bd u v)) := by
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hx
          obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hx
          have := parity_id u v x Finset.univ
          rw [hx, cr_univ, Finset.inter_empty, Finset.inter_univ, pc_empty, pc_singleton] at this
          exact absurd this (by decide)
        have hsub : (Finset.univ \ (Finset.univ : Finset (Finset (Fin m))).image (bd u v)).image
            (fun d => fun F => if valid F then resp d F else 0) = {fun _ => 0} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          constructor
          · exact Finset.mem_image.mpr ⟨_, hmem0, hz _ hmem0⟩
          · intro r hr
            obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hr
            exact hz d hd
        rw [hsub, Finset.card_singleton]
  · rw [Finset.disjoint_left]
    intro r hr1 hr2
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hr1
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨d', hd', hdd⟩ := Finset.mem_image.mp hr2
    rw [Finset.mem_sdiff] at hd'
    have hd'' : ∀ x, bd u v x ≠ d' := fun x hx =>
      hd'.2 (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)
    have := congrFun hdd ∅
    simp only [hvalid0, ↓reduceIte] at this
    rw [hzero d' ∅ hd''] at this
    exact hpos x this.symm

theorem main_iff (n m : ℕ) (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : ℕ) (hw : 0 < w)
    (wantCounts : Bool) (b : ℕ) :
    (∃ (encode : Finset (Fin n) → Fin b) (decode : Fin b → Finset (Finset (Fin m × Bool)) → Nat),
      ∀ d F, valid T t w F → decode (encode d) F =
        if wantCounts then total u v d F else min 1 (total u v d F)) ↔
      2 ^ (sigs u v T (if wantCounts then t * w else t) - sigs u v T 0) +
        (if n = 0 then 0 else 1) ≤ b := by
  have hvalid0 : valid T t w ∅ := ⟨by simp, by simp⟩
  have htpos : ∀ x, total u v (bd u v x) ∅ ≠ 0 := by
    intro x
    unfold total
    apply Nat.pos_iff_ne_zero.mp
    apply Finset.card_pos.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by simp⟩⟩
  have htzero : ∀ d F, (∀ x, bd u v x ≠ d) → total u v d F = 0 := by
    intro d F hd
    unfold total
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    exact hd x (Finset.mem_filter.mp hx).2.1
  cases wantCounts with
  | true =>
    exact count_main u v T (t * w) (valid T t w) (fun d F => total u v d F) hvalid0 htpos htzero
      (fun d d' h F hF => F3count u v T t w d d' h F hF)
      (fun x d' U hU hodd => F4count u v T t w hw (bd u v x) d' x rfl U hU hodd) b
  | false =>
    exact count_main u v T t (valid T t w) (fun d F => min 1 (total u v d F)) hvalid0
      (fun x => by show min 1 (total u v (bd u v x) ∅) ≠ 0; have := htpos x; omega)
      (fun d F hd => by show min 1 (total u v d F) = 0; rw [htzero d F hd]; rfl)
      (fun d d' h F hF => F3sat u v T t w d d' h F hF)
      (fun x d' U hU hodd => F4sat u v T t w hw (bd u v x) d' x rfl U hU hodd) b

end PEqualNP.Outside.L_lib_1131_aux

theorem PEqualNP.Outside.L_lib_1131 : ∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : Nat), 0 < w →
  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let crossing := fun (U : Finset (Fin n)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun i => decide (u i ∈ U) != decide (v i ∈ U))

  let Clause := Finset (Fin m × Bool)
  let holds := fun (x : Finset (Fin m)) (C : Clause) =>
    ∃ l ∈ C, decide (l.1 ∈ x) = l.2
  let valid := fun (F : Finset Clause) =>
    F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T

  let total := fun (d : Finset (Fin n)) (F : Finset Clause) =>
    (cube.filter (fun x => boundary x = d ∧ ∀ C ∈ F, holds x C)).card

  let signatures := fun (k : Nat) =>
    let shores := vertices.filter (fun U => crossing U ⊆ T ∧ (crossing U).card ≤ k)
    ((Finset.univ : Finset (Fin n)).image
      (fun i => shores.filter (fun U => i ∈ U))).card
  ∀ (wantCounts : Bool) (b : Nat),
    let k := if wantCounts then t * w else t
    (∃ (encode : Finset (Fin n) → Fin b) (decode : Fin b → Finset Clause → Nat),
      ∀ d F, valid F → decode (encode d) F =
        if wantCounts then total d F else min 1 (total d F)) ↔
      2 ^ (signatures k - signatures 0) + (if n = 0 then 0 else 1) ≤ b
  := by
  intro n m u v T t w hw cube vertices boundary crossing Clause holds valid total signatures
    wantCounts b k
  exact PEqualNP.Outside.L_lib_1131_aux.main_iff n m u v T t w hw wantCounts b
