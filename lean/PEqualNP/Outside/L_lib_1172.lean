import Mathlib
import PEqualNP.Defs

open scoped symmDiff

namespace PEqualNP.Outside.L_lib_1172

open Finset

theorem card_symmDiff_parity {α : Type} [DecidableEq α] (s t : Finset α) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 : s ∆ t = (s \ t) ∪ (t \ s) := rfl
  have h2 : Disjoint (s \ t) (t \ s) := disjoint_sdiff_sdiff
  have h3 := card_sdiff_add_card_inter s t
  have h4 := card_sdiff_add_card_inter t s
  rw [h1, card_union_of_disjoint h2, inter_comm t s] at *
  omega

theorem count {α : Type} [Fintype α] [DecidableEq α] (I K : Finset (Finset α)) :
    ∑ x : Finset α, (K.filter (fun c => c ∆ x ∈ I)).card = K.card * I.card := by
  calc ∑ x : Finset α, (K.filter (fun c => c ∆ x ∈ I)).card
      = ∑ x : Finset α, ∑ c ∈ K, (if c ∆ x ∈ I then 1 else 0) := by
        simp only [card_filter]
    _ = ∑ c ∈ K, ∑ x : Finset α, (if c ∆ x ∈ I then 1 else 0) := Finset.sum_comm
    _ = ∑ c ∈ K, I.card := by
        refine sum_congr rfl (fun c _ => ?_)
        rw [← card_filter]
        refine card_nbij' (fun x => c ∆ x) (fun y => c ∆ y) ?_ ?_ ?_ ?_
        · intro x hx
          simpa using hx
        · intro y hy
          simpa [symmDiff_symmDiff_cancel_left] using hy
        · intro x _
          exact symmDiff_symmDiff_cancel_left c x
        · intro y _
          exact symmDiff_symmDiff_cancel_left c y
    _ = K.card * I.card := by simp [sum_const, smul_eq_mul]

theorem core {α : Type} [Fintype α] [DecidableEq α] (I K : Finset (Finset α))
    (hdown : ∀ a b, a ⊆ b → b ∈ I → a ∈ I) (hK0 : (∅ : Finset α) ∈ K)
    (hKx : ∀ c d, c ∈ K → d ∈ K → c ∆ d ∈ K) :
    (∀ x : Finset α, (K.filter (fun c => c ∆ x ∈ I)).card = 1) ↔
      I.card * K.card = (univ : Finset (Finset α)).card ∧
      ∀ w ∈ K, w.Nonempty → ¬ ∃ a ∈ I, a ⊆ w ∧ w \ a ∈ I := by
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have hs := count I K
      simp only [H, sum_const, smul_eq_mul, mul_one] at hs
      rw [mul_comm, ← hs, card_univ]
    · rintro w hw hne ⟨a, ha, haw, hwa⟩
      obtain ⟨c, hc⟩ := card_eq_one.1 (H a)
      have m0 : (∅ : Finset α) ∈ K.filter (fun c => c ∆ a ∈ I) := by
        simp only [mem_filter]
        refine ⟨hK0, ?_⟩
        rw [show (∅ : Finset α) = ⊥ from rfl, bot_symmDiff]
        exact ha
      have m1 : w ∈ K.filter (fun c => c ∆ a ∈ I) := by
        simp only [mem_filter]
        refine ⟨hw, ?_⟩
        rw [symmDiff_of_ge haw]
        exact hwa
      rw [hc, mem_singleton] at m0 m1
      exact hne.ne_empty (m1.trans m0.symm)
  · rintro ⟨hc, hsupp⟩
    have hle : ∀ x : Finset α, (K.filter (fun c => c ∆ x ∈ I)).card ≤ 1 := by
      intro x
      refine card_le_one.2 (fun c1 h1 c2 h2 => ?_)
      rw [mem_filter] at h1 h2
      by_contra hne
      have hw : c1 ∆ c2 ∈ K := hKx c1 c2 h1.1 h2.1
      have hwne : (c1 ∆ c2).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h0
        exact hne (symmDiff_eq_bot.1 h0)
      apply hsupp _ hw hwne
      refine ⟨(c1 ∆ x) ∩ (c1 ∆ c2), hdown _ _ inter_subset_left h1.2, inter_subset_right, ?_⟩
      refine hdown _ _ ?_ h2.2
      intro y hy
      simp only [mem_sdiff, mem_inter, mem_symmDiff] at hy ⊢
      tauto
    have hsum := count I K
    rw [mul_comm, hc, card_univ] at hsum
    have key := (Finset.sum_eq_sum_iff_of_le (s := (univ : Finset (Finset α)))
      (f := fun x => (K.filter (fun c => c ∆ x ∈ I)).card) (g := fun _ => 1)
      (fun x _ => hle x)).1 (by simpa using hsum)
    intro x
    exact key x (mem_univ x)

end PEqualNP.Outside.L_lib_1172

open Finset PEqualNP.Outside.L_lib_1172 in
theorem PEqualNP.Outside.L_lib_1172 : ∀ (n t h : Nat) (scope : Fin t → Finset (Fin n)) (row : Fin h → Finset (Fin n)),
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let indep := cube.filter (fun x => ∀ j, ¬ scope j ⊆ x)
  let kernel := cube.filter (fun x => ∀ j, (row j ∩ x).card % 2 = 0)
  let xor := fun (x y : Bits) => (x \ y) ∪ (y \ x)
  (∀ x : Bits, (kernel.filter (fun c => xor c x ∈ indep)).card = 1) ↔
    indep.card * kernel.card = cube.card ∧
    ∀ w ∈ kernel, w.Nonempty → ¬ ∃ a ∈ indep, a ⊆ w ∧ w \ a ∈ indep := by
  intro n t h scope row Bits cube indep kernel xor
  have hdown : ∀ a b, a ⊆ b → b ∈ indep → a ∈ indep := by
    intro a b hab hb
    simp only [indep, cube, mem_filter, mem_univ, true_and] at hb ⊢
    intro j hj
    exact hb j (hj.trans hab)
  have hK0 : (∅ : Finset (Fin n)) ∈ kernel := by
    simp [kernel, cube]
  have hKx : ∀ c d, c ∈ kernel → d ∈ kernel → c ∆ d ∈ kernel := by
    intro c d hc hd
    simp only [kernel, cube, mem_filter, mem_univ, true_and] at hc hd ⊢
    intro j
    rw [inf_symmDiff_distrib_left]
    have e := card_symmDiff_parity (row j ∩ c) (row j ∩ d)
    have e1 := hc j
    have e2 := hd j
    change ((row j ∩ c) ∆ (row j ∩ d)).card % 2 = 0
    omega
  exact core indep kernel hdown hK0 hKx
