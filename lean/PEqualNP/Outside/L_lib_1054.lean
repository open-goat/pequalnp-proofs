import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1054_aux

abbrev W (n : ℕ) := Fin n → Bool
abbrev Form (n : ℕ) := Finset ((Fin n × Bool) × (Fin n × Bool))

def sat (n : ℕ) (A : Form n) (x : W n) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2

def addable (n : ℕ) (A : Form n) (z : W n) : Prop :=
  ∃ B : Form n, ∀ x : W n, sat n B x ↔ (sat n A x ∨ x = z)

def maj {n : ℕ} (a b c : W n) : W n :=
  fun i => (a i && b i) || (b i && c i) || (c i && a i)

lemma maj_bool_two (a b c u : Bool)
    (h : ((a && b) || (b && c) || (c && a)) = u) :
    (a = u ∧ b = u) ∨ (b = u ∧ c = u) ∨ (c = u ∧ a = u) := by
  revert h
  cases a <;> cases b <;> cases c <;> cases u <;> decide

lemma sat_maj_closed {n : ℕ} (B : Form n) (a b c : W n)
    (ha : sat n B a) (hb : sat n B b) (hc : sat n B c) :
    sat n B (maj a b c) := by
  intro cl hcl
  by_contra h
  push Not at h
  rcases h with ⟨h1, h2⟩
  have hm1 := maj_bool_two (a cl.1.1) (b cl.1.1) (c cl.1.1) cl.1.2 h1
  have hm2 := maj_bool_two (a cl.2.1) (b cl.2.1) (c cl.2.1) cl.2.2 h2
  rcases hm1 with ⟨ha1, hb1⟩ | ⟨hb1, hc1⟩ | ⟨hc1, ha1⟩ <;>
    rcases hm2 with ⟨ha2, hb2⟩ | ⟨hb2, hc2⟩ | ⟨hc2, ha2⟩
  · rcases ha cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases hb cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases ha cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases hb cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases hb cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases hc cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases ha cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases hc cl hcl with hne | hne <;> exact hne (by assumption)
  · rcases hc cl hcl with hne | hne <;> exact hne (by assumption)

lemma maj_closed_pair_proj {n : ℕ} (hn : 0 < n) (R : Set (W n))
    (hmaj : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, maj a b c ∈ R)
    (x : W n) (hpair : ∀ i j : Fin n, ∃ y ∈ R, y i = x i ∧ y j = x j) :
    x ∈ R := by
  have hind : ∀ m : ℕ, ∀ S : Finset (Fin n), S.card = m → ∃ y ∈ R, ∀ i ∈ S, y i = x i := by
    intro m
    induction m with
    | zero =>
      intro S hS
      rcases hpair ⟨0, hn⟩ ⟨0, hn⟩ with ⟨y, hyR, _, _⟩
      refine ⟨y, hyR, fun i hi => ?_⟩
      rw [Finset.card_eq_zero.mp hS] at hi
      simp at hi
    | succ m ih =>
      cases m with
      | zero =>
        intro S hS
        rcases Finset.card_eq_one.mp hS with ⟨a, rfl⟩
        rcases hpair a a with ⟨y, hyR, hya, _⟩
        refine ⟨y, hyR, fun i hi => ?_⟩
        rw [Finset.mem_singleton.mp hi]
        exact hya
      | succ m =>
        cases m with
        | zero =>
          intro S hS
          rcases Finset.card_eq_two.mp hS with ⟨a, b, _, rfl⟩
          rcases hpair a b with ⟨y, hyR, hya, hyb⟩
          refine ⟨y, hyR, fun i hi => ?_⟩
          rcases Finset.mem_insert.mp hi with rfl | hib
          · exact hya
          · rw [Finset.mem_singleton.mp hib]
            exact hyb
        | succ k =>
          intro S hS
          have hpos0 : 0 < S.card := by omega
          rcases Finset.card_pos.mp hpos0 with ⟨i1, hi1⟩
          have hc1 : (S.erase i1).card = k + 2 := by rw [Finset.card_erase_of_mem hi1]; omega
          rcases Finset.card_pos.mp (by omega : 0 < (S.erase i1).card) with ⟨i2, hi2e⟩
          rcases Finset.mem_erase.mp hi2e with ⟨hi2ne1, hi2⟩
          have hc12 : ((S.erase i1).erase i2).card = k + 1 := by
            rw [Finset.card_erase_of_mem hi2e]; omega
          rcases Finset.card_pos.mp (by omega : 0 < ((S.erase i1).erase i2).card) with ⟨i3, hi3e⟩
          rcases Finset.mem_erase.mp hi3e with ⟨hi3ne2, hi3e1⟩
          rcases Finset.mem_erase.mp hi3e1 with ⟨hi3ne1, hi3⟩
          have hc2 : (S.erase i2).card = k + 2 := by rw [Finset.card_erase_of_mem hi2]; omega
          have hc3 : (S.erase i3).card = k + 2 := by rw [Finset.card_erase_of_mem hi3]; omega
          rcases ih (S.erase i1) hc1 with ⟨y1, hy1R, hy1⟩
          rcases ih (S.erase i2) hc2 with ⟨y2, hy2R, hy2⟩
          rcases ih (S.erase i3) hc3 with ⟨y3, hy3R, hy3⟩
          refine ⟨maj y1 y2 y3, hmaj y1 hy1R y2 hy2R y3 hy3R, fun i hi => ?_⟩
          dsimp only [maj]
          by_cases h1 : i = i1
          · subst h1
            have h2i : y2 i = x i := hy2 i (Finset.mem_erase.mpr ⟨Ne.symm hi2ne1, hi⟩)
            have h3i : y3 i = x i := hy3 i (Finset.mem_erase.mpr ⟨Ne.symm hi3ne1, hi⟩)
            rw [h2i, h3i]
            cases y1 i <;> cases x i <;> decide
          · by_cases h2 : i = i2
            · subst h2
              have h1i : y1 i = x i := hy1 i (Finset.mem_erase.mpr ⟨hi2ne1, hi⟩)
              have h3i : y3 i = x i := hy3 i (Finset.mem_erase.mpr ⟨Ne.symm hi3ne2, hi⟩)
              rw [h1i, h3i]
              cases y2 i <;> cases x i <;> decide
            · have h1i : y1 i = x i := hy1 i (Finset.mem_erase.mpr ⟨h1, hi⟩)
              have h2i : y2 i = x i := hy2 i (Finset.mem_erase.mpr ⟨h2, hi⟩)
              rw [h1i, h2i]
              cases y3 i <;> cases x i <;> decide
  rcases hind n Finset.univ (by simp) with ⟨y, hyR, hy⟩
  have hxy : x = y := funext (fun i => (hy i (Finset.mem_univ i)).symm)
  rwa [hxy]

lemma exists_form_of_maj_closed {n : ℕ} (R : Set (W n))
    (hmaj : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, maj a b c ∈ R)
    (hne : R.Nonempty) :
    ∃ B : Form n, ∀ x : W n, sat n B x ↔ x ∈ R := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨∅, fun x => ?_⟩
    rcases hne with ⟨y, hy⟩
    have hxy : x = y := funext (fun i => Fin.elim0 i)
    simp [sat, hxy, hy]
  · let B : Form n := Finset.univ.filter (fun cl : (Fin n × Bool) × (Fin n × Bool) =>
      ∀ y ∈ R, y cl.1.1 ≠ cl.1.2 ∨ y cl.2.1 ≠ cl.2.2)
    refine ⟨B, fun x => ?_⟩
    constructor
    · intro hsat
      refine maj_closed_pair_proj (by omega) R hmaj x (fun i j => ?_)
      by_contra hno
      push Not at hno
      have hcl : ((i, x i), (j, x j)) ∈ B := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => ?_⟩
        by_cases h1 : y i = x i
        · right; exact hno y hy h1
        · left; exact h1
      rcases hsat ((i, x i), (j, x j)) hcl with hne1 | hne2
      · exact hne1 rfl
      · exact hne2 rfl
    · intro hx cl hcl
      exact (Finset.mem_filter.mp hcl).2 x hx

lemma addable_iff_maj_closed {n : ℕ} (A : Form n) (z : W n) :
    addable n A z ↔
      ∀ a b c : W n, (sat n A a ∨ a = z) → (sat n A b ∨ b = z) → (sat n A c ∨ c = z) →
        (sat n A (maj a b c) ∨ maj a b c = z) := by
  constructor
  · rintro ⟨B, hB⟩ a b c ha hb hc
    exact (hB (maj a b c)).mp (sat_maj_closed B a b c ((hB a).mpr ha) ((hB b).mpr hb) ((hB c).mpr hc))
  · intro hmaj
    let R : Set (W n) := {x : W n | sat n A x ∨ x = z}
    exact exists_form_of_maj_closed R (fun a ha b hb c hc => hmaj a b c ha hb hc) ⟨z, Or.inr rfl⟩

lemma maj_eq_of_eq_pair {n : ℕ} (a b c : W n) (u : W n)
    (h : (a = u ∧ b = u) ∨ (b = u ∧ c = u) ∨ (c = u ∧ a = u)) :
    maj a b c = u := by
  funext i
  dsimp only [maj]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases b i <;> cases c i <;> decide
  · cases a i <;> cases c i <;> decide
  · cases a i <;> cases b i <;> decide

lemma maj_comm12 {n : ℕ} (a b c : W n) : maj a b c = maj b a c := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> cases c i <;> decide

lemma maj_comm23 {n : ℕ} (a b c : W n) : maj a b c = maj a c b := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> cases c i <;> decide

lemma addable_iff_test {n : ℕ} (A : Form n) (z : W n) :
    addable n A z ↔
      ∀ c ∈ A, ∀ k : Fin n,
        ¬ (z c.1.1 = c.1.2 ∧ z c.2.1 = c.2.2 ∧
           (∃ a : W n, sat n A a ∧ a c.1.1 = c.1.2 ∧ a k ≠ z k) ∧
           (∃ b : W n, sat n A b ∧ b c.2.1 = c.2.2 ∧ b k ≠ z k)) := by
  rw [addable_iff_maj_closed]
  constructor
  · intro hmaj c hc k ⟨hz1, hz2, ⟨a, ha, ha1, hak⟩, ⟨b, hb, hb2, hbk⟩⟩
    have hm := hmaj a b z (Or.inl ha) (Or.inl hb) (Or.inr rfl)
    rcases hm with hsat | heq
    · rcases hsat c hc with hne1 | hne2
      · apply hne1
        dsimp only [maj]
        rw [ha1, hz1]
        cases b c.1.1 <;> cases c.1.2 <;> decide
      · apply hne2
        dsimp only [maj]
        rw [hb2, hz2]
        cases a c.2.1 <;> cases c.2.2 <;> decide
    · have hk := congrFun heq k
      dsimp only [maj] at hk
      revert hak hbk hk
      cases a k <;> cases b k <;> cases z k <;> decide
  · intro htest
    have hpair_z : ∀ a b : W n, sat n A a → sat n A b → sat n A (maj a b z) ∨ maj a b z = z := by
      intro a b ha hb
      by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hnsat, hnez⟩
      have hex_cl : ∃ c ∈ A, maj a b z c.1.1 = c.1.2 ∧ maj a b z c.2.1 = c.2.2 := by
        dsimp only [sat] at hnsat
        push Not at hnsat
        exact hnsat
      have hex_k : ∃ k : Fin n, maj a b z k ≠ z k := by
        by_contra hall
        push Not at hall
        exact hnez (funext hall)
      rcases hex_cl with ⟨c, hcA, hm1, hm2⟩
      rcases hex_k with ⟨k, hmk⟩
      have hak : a k ≠ z k := by
        intro heq; apply hmk; dsimp only [maj]; rw [heq]; cases b k <;> cases z k <;> decide
      have hbk : b k ≠ z k := by
        intro heq; apply hmk; dsimp only [maj]; rw [heq]; cases a k <;> cases z k <;> decide
      have hz1 : z c.1.1 = c.1.2 := by
        by_contra hne
        have h1 := maj_bool_two (a c.1.1) (b c.1.1) (z c.1.1) c.1.2 hm1
        have hab1 : a c.1.1 = c.1.2 ∧ b c.1.1 = c.1.2 := by
          rcases h1 with h | ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h hne
          · exact absurd h hne
        have ha2 : a c.2.1 ≠ c.2.2 := (ha c hcA).resolve_left (not_not.mpr hab1.1)
        have hb2 : b c.2.1 ≠ c.2.2 := (hb c hcA).resolve_left (not_not.mpr hab1.2)
        have h2 := maj_bool_two (a c.2.1) (b c.2.1) (z c.2.1) c.2.2 hm2
        rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · exact ha2 h
        · exact hb2 h
        · exact ha2 h
      have hz2 : z c.2.1 = c.2.2 := by
        by_contra hne
        have h2 := maj_bool_two (a c.2.1) (b c.2.1) (z c.2.1) c.2.2 hm2
        have hab2 : a c.2.1 = c.2.2 ∧ b c.2.1 = c.2.2 := by
          rcases h2 with h | ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h hne
          · exact absurd h hne
        have ha1 : a c.1.1 ≠ c.1.2 := (ha c hcA).resolve_right (not_not.mpr hab2.1)
        have hb1 : b c.1.1 ≠ c.1.2 := (hb c hcA).resolve_right (not_not.mpr hab2.2)
        have h1 := maj_bool_two (a c.1.1) (b c.1.1) (z c.1.1) c.1.2 hm1
        rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · exact ha1 h
        · exact hb1 h
        · exact ha1 h
      have h1or : a c.1.1 = c.1.2 ∨ b c.1.1 = c.1.2 := by
        rcases maj_bool_two (a c.1.1) (b c.1.1) (z c.1.1) c.1.2 hm1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl h
      have h2or : a c.2.1 = c.2.2 ∨ b c.2.1 = c.2.2 := by
        rcases maj_bool_two (a c.2.1) (b c.2.1) (z c.2.1) c.2.2 hm2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl h
      rcases h1or with ha1 | hb1 <;> rcases h2or with ha2 | hb2
      · rcases ha c hcA with h | h
        · exact h ha1
        · exact h ha2
      · exact htest c hcA k ⟨hz1, hz2, ⟨a, ha, ha1, hak⟩, ⟨b, hb, hb2, hbk⟩⟩
      · exact htest c hcA k ⟨hz1, hz2, ⟨b, hb, hb1, hbk⟩, ⟨a, ha, ha2, hak⟩⟩
      · rcases hb c hcA with h | h
        · exact h hb1
        · exact h hb2
    intro a b c ha hb hc
    rcases ha with ha | rfl <;> rcases hb with hb | rfl <;> rcases hc with hc | rfl
    · exact Or.inl (sat_maj_closed A a b c ha hb hc)
    · exact hpair_z a b ha hb
    · rw [maj_comm23]; exact hpair_z a c ha hc
    · exact Or.inr (maj_eq_of_eq_pair _ _ _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · rw [maj_comm12, maj_comm23]; exact hpair_z b c hb hc
    · exact Or.inr (maj_eq_of_eq_pair _ _ _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact Or.inr (maj_eq_of_eq_pair _ _ _ _ (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (maj_eq_of_eq_pair _ _ _ _ (Or.inl ⟨rfl, rfl⟩))

lemma width_three_sharp (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Form n, ¬ ∃ D : Form n, ∀ z : W n, sat n D z ↔ addable n A z := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let tailCl : Finset ((Fin n × Bool) × (Fin n × Bool)) :=
    (Finset.univ.filter (fun j : Fin n => 2 ≤ j.val)).image (fun j => ((j, true), (j, true)))
  let A : Form n := insert ((i0, false), (i1, true)) (insert ((i0, true), (i1, false)) tailCl)
  refine ⟨A, ?_⟩
  rintro ⟨D, hD⟩
  let a0 : W n := fun _ => false
  let a1 : W n := fun j => decide (j.val < 2)
  have hsat_iff : ∀ x : W n, sat n A x ↔ x = a0 ∨ x = a1 := by
    intro x
    constructor
    · intro hx
      have h01a := hx ((i0, false), (i1, true)) (Finset.mem_insert_self _ _)
      have h01b := hx ((i0, true), (i1, false)) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have htail : ∀ j : Fin n, 2 ≤ j.val → x j = false := by
        intro j hj
        have hmem : ((j, true), (j, true)) ∈ A :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩))
        have hxj := hx ((j, true), (j, true)) hmem
        cases h : x j
        · rfl
        · rcases hxj with hne | hne <;> exact absurd h hne
      cases hx0 : x i0
      · left
        have hx1 : x i1 = false := by
          cases h : x i1
          · rfl
          · rcases h01a with hne | hne
            · exact absurd hx0 hne
            · exact absurd h hne
        funext j
        by_cases hj0 : j.val = 0
        · have : j = i0 := Fin.ext hj0; rw [this, hx0]
        · by_cases hj1 : j.val = 1
          · have : j = i1 := Fin.ext hj1; rw [this, hx1]
          · exact htail j (by omega)
      · right
        have hx1 : x i1 = true := by
          cases h : x i1
          · rcases h01b with hne | hne
            · exact absurd hx0 hne
            · exact absurd h hne
          · rfl
        funext j
        by_cases hj0 : j.val = 0
        · have : j = i0 := Fin.ext hj0; rw [this, hx0]; rfl
        · by_cases hj1 : j.val = 1
          · have : j = i1 := Fin.ext hj1; rw [this, hx1]; rfl
          · rw [htail j (by omega)]
            dsimp only [a1]
            simp [show ¬ j.val < 2 by omega]
    · rintro (rfl | rfl)
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · right; simp [a0]
        · rcases Finset.mem_insert.mp hc with rfl | hc
          · left; simp [a0]
          · rcases Finset.mem_image.mp hc with ⟨j, _, rfl⟩
            left; simp [a0]
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · left; simp [a1, i0]
        · rcases Finset.mem_insert.mp hc with rfl | hc
          · right; simp [a1, i1]
          · rcases Finset.mem_image.mp hc with ⟨j, hj, rfl⟩
            have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hj).2
            left
            dsimp only [a1]
            simp [show ¬ j.val < 2 by omega]
  let z1 : W n := fun j => decide (j.val = 1)
  let z2 : W n := fun j => decide (j.val < 3)
  let z3 : W n := fun j => decide (j.val = 2)
  have hadd_of_maj : ∀ z : W n, (maj a0 a1 z = a0 ∨ maj a0 a1 z = a1 ∨ maj a0 a1 z = z) → addable n A z := by
    intro z hmz
    rw [addable_iff_maj_closed]
    have hsat_z : sat n A (maj a0 a1 z) ∨ maj a0 a1 z = z := by
      rcases hmz with h | h | h
      · exact Or.inl ((hsat_iff _).mpr (Or.inl h))
      · exact Or.inl ((hsat_iff _).mpr (Or.inr h))
      · exact Or.inr h
    intro a b c ha hb hc
    have ha' : a = a0 ∨ a = a1 ∨ a = z := by
      rcases ha with h | h
      · rcases (hsat_iff a).mp h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    have hb' : b = a0 ∨ b = a1 ∨ b = z := by
      rcases hb with h | h
      · rcases (hsat_iff b).mp h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    have hc' : c = a0 ∨ c = a1 ∨ c = z := by
      rcases hc with h | h
      · rcases (hsat_iff c).mp h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    by_cases hab : a = b
    · rw [maj_eq_of_eq_pair _ _ _ a (Or.inl ⟨rfl, hab.symm⟩)]; exact ha
    · by_cases hbc : b = c
      · rw [maj_eq_of_eq_pair _ _ _ b (Or.inr (Or.inl ⟨rfl, hbc.symm⟩))]; exact hb
      · by_cases hca : c = a
        · rw [maj_eq_of_eq_pair _ _ _ c (Or.inr (Or.inr ⟨rfl, hca.symm⟩))]; exact hc
        · rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
            first
            | exact absurd rfl hab
            | exact absurd rfl hbc
            | exact absurd rfl hca
            | exact hsat_z
            | (rw [maj_comm23]; exact hsat_z)
            | (rw [maj_comm12]; exact hsat_z)
            | (rw [maj_comm12, maj_comm23]; exact hsat_z)
            | (rw [maj_comm23, maj_comm12]; exact hsat_z)
            | (rw [maj_comm12, maj_comm23, maj_comm12]; exact hsat_z)
  have hz1 : addable n A z1 := hadd_of_maj z1 (Or.inr (Or.inr (by
    funext j; dsimp only [maj, a0, a1, z1]
    by_cases h0 : j.val = 0
    · simp [h0]
    · by_cases h1 : j.val = 1
      · simp [h1]
      · simp [h1, show ¬ j.val < 2 by omega])))
  have hz2 : addable n A z2 := hadd_of_maj z2 (Or.inr (Or.inl (by
    funext j; dsimp only [maj, a0, a1, z2]
    by_cases h2 : j.val < 2
    · simp [h2, show j.val < 3 by omega]
    · simp [h2])))
  have hz3 : addable n A z3 := hadd_of_maj z3 (Or.inl (by
    funext j; dsimp only [maj, a0, a1, z3]
    by_cases h2 : j.val < 2
    · simp [h2, show j.val ≠ 2 by omega]
    · simp [h2]))
  have hmw : addable n A (maj z1 z2 z3) :=
    (hD (maj z1 z2 z3)).mp (sat_maj_closed D z1 z2 z3 ((hD z1).mpr hz1) ((hD z2).mpr hz2) ((hD z3).mpr hz3))
  have hnotw : ¬ addable n A (maj z1 z2 z3) := by
    rw [addable_iff_test]
    intro htest
    apply htest ((i0, false), (i1, true)) (Finset.mem_insert_self _ _) i2
    refine ⟨?_, ?_, ⟨a0, (hsat_iff a0).mpr (Or.inl rfl), rfl, ?_⟩,
      ⟨a1, (hsat_iff a1).mpr (Or.inr rfl), by simp [a1, i1], ?_⟩⟩
    · simp [maj, z1, z2, z3, i0]
    · simp [maj, z1, z2, z3, i1]
    · simp [maj, a0, z1, z2, z3, i2]
    · simp [maj, a1, z1, z2, z3, i2]
  exact hnotw hmw

lemma main_proof :
    let W := fun n : ℕ => Fin n → Bool
    let F := fun n : ℕ => Finset ((Fin n × Bool) × (Fin n × Bool))
    let sat := fun (n : ℕ) (A : F n) (x : W n) =>
      ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
    let addable := fun (n : ℕ) (A : F n) (z : W n) =>
      ∃ B : F n, ∀ x : W n, (sat n B x ↔ (sat n A x ∨ x = z))
    ((∀ (n : ℕ) (A : F n) (z : W n),
      addable n A z ↔ ∀ c ∈ A, ∀ k : Fin n,
        ¬ (z c.1.1 = c.1.2 ∧ z c.2.1 = c.2.2 ∧
           (∃ a : W n, sat n A a ∧ a c.1.1 = c.1.2 ∧ a k ≠ z k) ∧
           (∃ b : W n, sat n A b ∧ b c.2.1 = c.2.2 ∧ b k ≠ z k))) ∧
     (∀ n : ℕ, 3 ≤ n → ∃ A : F n,
        ¬ ∃ D : F n, ∀ z : W n, (sat n D z ↔ addable n A z))) :=
  ⟨fun _ A z => addable_iff_test A z, width_three_sharp⟩

end PEqualNP.Outside.L_lib_1054_aux

theorem PEqualNP.Outside.L_lib_1054 :
let W := fun n : ℕ => Fin n → Bool
let F := fun n : ℕ => Finset ((Fin n × Bool) × (Fin n × Bool))
let sat := fun (n : ℕ) (A : F n) (x : W n) =>
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
let addable := fun (n : ℕ) (A : F n) (z : W n) =>
  ∃ B : F n, ∀ x : W n, (sat n B x ↔ (sat n A x ∨ x = z))
((∀ (n : ℕ) (A : F n) (z : W n),
  addable n A z ↔ ∀ c ∈ A, ∀ k : Fin n,
    ¬ (z c.1.1 = c.1.2 ∧ z c.2.1 = c.2.2 ∧
       (∃ a : W n, sat n A a ∧ a c.1.1 = c.1.2 ∧ a k ≠ z k) ∧
       (∃ b : W n, sat n A b ∧ b c.2.1 = c.2.2 ∧ b k ≠ z k))) ∧
 (∀ n : ℕ, 3 ≤ n → ∃ A : F n,
    ¬ ∃ D : F n, ∀ z : W n, (sat n D z ↔ addable n A z))) := by
  exact PEqualNP.Outside.L_lib_1054_aux.main_proof
