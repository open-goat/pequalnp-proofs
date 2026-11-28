import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1172_aux

open scoped symmDiff

theorem inj_of_uniq {α : Type*} [DecidableEq α] (I K : Finset (Finset α))
    (uniq : ∀ x c c', c ∈ K → c ∆ x ∈ I → c' ∈ K → c' ∆ x ∈ I → c = c') :
    Set.InjOn (fun p : Finset α × Finset α => p.1 ∆ p.2) (K ×ˢ I : Finset _) := by
  rintro ⟨c, a⟩ hp ⟨c', a'⟩ hp' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
  dsimp at heq
  have e1 : c ∆ (c ∆ a) = a := symmDiff_symmDiff_cancel_left c a
  have e2 : c' ∆ (c ∆ a) = a' := by rw [heq]; exact symmDiff_symmDiff_cancel_left c' a'
  have hcc : c = c' :=
    uniq (c ∆ a) c c' hp.1 (by rw [e1]; exact hp.2) hp'.1 (by rw [e2]; exact hp'.2)
  subst hcc
  exact Prod.ext rfl (e1.symm.trans e2)

theorem gen {α : Type*} [DecidableEq α] [Fintype α] (I K : Finset (Finset α))
    (hI : ∀ x ∈ I, ∀ y, y ⊆ x → y ∈ I) (h0 : ∅ ∈ K) (hK : ∀ x ∈ K, ∀ y ∈ K, x ∆ y ∈ K) :
    (∀ x : Finset α, (K.filter (fun c => c ∆ x ∈ I)).card = 1) ↔
      I.card * K.card = (Finset.univ : Finset (Finset α)).card ∧
      ∀ w ∈ K, w.Nonempty → ¬ ∃ a ∈ I, a ⊆ w ∧ w \ a ∈ I := by
  constructor
  · intro h
    have uniq : ∀ x c c', c ∈ K → c ∆ x ∈ I → c' ∈ K → c' ∆ x ∈ I → c = c' := by
      intro x c c' hc hcx hc' hcx'
      exact Finset.card_le_one.mp (h x).le c (by simp [hc, hcx]) c' (by simp [hc', hcx'])
    refine ⟨?_, ?_⟩
    · rw [mul_comm, ← Finset.card_product]
      refine Finset.card_bij (fun p _ => p.1 ∆ p.2) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro p hp q hq heq
        exact inj_of_uniq I K uniq (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) heq
      · intro x _
        obtain ⟨c, hc⟩ := Finset.card_pos.mp (by rw [h x]; exact one_pos)
        simp only [Finset.mem_filter] at hc
        exact ⟨(c, c ∆ x), by simp [hc.1, hc.2], symmDiff_symmDiff_cancel_left c x⟩
    · rintro w hw hne ⟨a, ha, haw, hwa⟩
      have e : w ∆ a = w \ a := by
        ext i
        have := @haw i
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        tauto
      have : (∅ : Finset α) = w := uniq a ∅ w h0
        (by rw [← Finset.bot_eq_empty, bot_symmDiff]; exact ha) hw (by rw [e]; exact hwa)
      exact hne.ne_empty this.symm
  · rintro ⟨hcard, hsup⟩
    have uniq : ∀ x c c', c ∈ K → c ∆ x ∈ I → c' ∈ K → c' ∆ x ∈ I → c = c' := by
      intro x c c' hc hcx hc' hcx'
      by_contra hne
      refine hsup (c ∆ c') (hK c hc c' hc') ?_
        ⟨(c ∆ x) \ (c' ∆ x), hI _ hcx _ Finset.sdiff_subset, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hne (symmDiff_eq_bot.mp h)
      · intro i
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        tauto
      · refine hI _ hcx' _ ?_
        intro i
        simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        tauto
    have himg : ((K ×ˢ I).image (fun p : Finset α × Finset α => p.1 ∆ p.2)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn (inj_of_uniq I K uniq), Finset.card_product, mul_comm, hcard,
        Finset.card_univ]
    intro x
    apply le_antisymm
    · refine Finset.card_le_one.mpr (fun c hc c' hc' => ?_)
      simp only [Finset.mem_filter] at hc hc'
      exact uniq x c c' hc.1 hc.2 hc'.1 hc'.2
    · have hx : x ∈ (K ×ˢ I).image (fun p : Finset α × Finset α => p.1 ∆ p.2) := by
        rw [himg]; exact Finset.mem_univ x
      obtain ⟨⟨c, a⟩, hp, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_product] at hp
      refine Finset.card_pos.mpr ⟨c, ?_⟩
      simp only [Finset.mem_filter]
      refine ⟨hp.1, ?_⟩
      rw [symmDiff_symmDiff_cancel_left]
      exact hp.2

theorem par {α : Type*} [DecidableEq α] (r x y : Finset α) :
    (r ∩ (x ∆ y)).card % 2 = ((r ∩ x).card + (r ∩ y).card) % 2 := by
  have e : r ∩ (x ∆ y) = ((r ∩ x) \ (r ∩ y)) ∪ ((r ∩ y) \ (r ∩ x)) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have d : Disjoint ((r ∩ x) \ (r ∩ y)) ((r ∩ y) \ (r ∩ x)) := by
    rw [Finset.disjoint_left]
    intro i
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have h1 := Finset.card_sdiff_add_card_inter (r ∩ x) (r ∩ y)
  have h2 := Finset.card_sdiff_add_card_inter (r ∩ y) (r ∩ x)
  rw [Finset.inter_comm (r ∩ y) (r ∩ x)] at h2
  rw [e, Finset.card_union_of_disjoint d]
  omega

end PEqualNP.Outside.L_lib_1172_aux


theorem PEqualNP.Outside.L_lib_1172 : ∀ (n t h : Nat) (scope : Fin t → Finset (Fin n)) (row : Fin h → Finset (Fin n)),
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let indep := cube.filter (fun x => ∀ j, ¬ scope j ⊆ x)
  let kernel := cube.filter (fun x => ∀ j, (row j ∩ x).card % 2 = 0)
  let xor := fun (x y : Bits) => (x \ y) ∪ (y \ x)
  (∀ x : Bits, (kernel.filter (fun c => xor c x ∈ indep)).card = 1) ↔
    indep.card * kernel.card = cube.card ∧
    ∀ w ∈ kernel, w.Nonempty → ¬ ∃ a ∈ indep, a ⊆ w ∧ w \ a ∈ indep := by
  intro n t h scope row
  refine PEqualNP.Outside.L_lib_1172_aux.gen
    (Finset.univ.filter (fun x : Finset (Fin n) => ∀ j, ¬ scope j ⊆ x))
    (Finset.univ.filter (fun x : Finset (Fin n) => ∀ j, (row j ∩ x).card % 2 = 0)) ?_ ?_ ?_
  · intro x hx y hyx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact fun j hj => hx j (hj.trans hyx)
  · simp
  · intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
    intro j
    have := PEqualNP.Outside.L_lib_1172_aux.par (row j) x y
    have := hx j
    have := hy j
    omega
