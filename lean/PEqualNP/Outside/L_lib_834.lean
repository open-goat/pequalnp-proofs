import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_834

open Finset Function

theorem zmod2_eq_one {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

theorem lin {K : Type} [Field K] [Algebra (ZMod 2) K] {g : ℕ}
    (u : Fin g → K) (f : Fin g → (K →ₗ[ZMod 2] ZMod 2)) (w : K) (i : Fin g)
    (c : Fin g → ZMod 2) (S : Finset (Fin g)) :
    f i (w * ∑ j ∈ S, c j • u j) = ∑ j ∈ S, c j * f i (w * u j) := by
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_comm, map_smul, smul_eq_mul]

theorem periodic_pt {g : ℕ} (nxt : Fin g → Fin g) (i0 : Fin g) :
    ∃ a n, 0 < n ∧ IsPeriodicPt nxt n (nxt^[a] i0) := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => nxt^[n] i0)
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, ?_⟩
    show nxt^[b - a] (nxt^[a] i0) = nxt^[a] i0
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
    exact he.symm
  · refine ⟨b, a - b, by omega, ?_⟩
    show nxt^[a - b] (nxt^[b] i0) = nxt^[b] i0
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
    exact he

theorem forward {K : Type} [Field K] [Algebra (ZMod 2) K] {g : ℕ}
    (u : Fin g → K) (f : Fin g → (K →ₗ[ZMod 2] ZMod 2)) (w : K)
    (S : Finset (Fin g)) (x : K) (hx0 : x ≠ 0)
    (hx : x = w * ∑ i ∈ S, (f i x) • u i) :
    ∃ (l : ℕ) (hl : 0 < l) (p : Fin l ↪ Fin g),
      ∀ j : Fin l, f (p j) (w * u (p ⟨(j.val+1) % l, Nat.mod_lt _ hl⟩)) ≠ 0 := by
  classical
  have key : ∀ i, f i x ≠ 0 → ∃ j, f j x ≠ 0 ∧ f i (w * u j) ≠ 0 := by
    intro i hi
    by_contra hne
    push_neg at hne
    apply hi
    have h1 : f i x = ∑ j ∈ S, f j x * f i (w * u j) := by
      conv_lhs => rw [hx]
      exact lin u f w i (fun j => f j x) S
    rw [h1]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hj : f j x = 0
    · rw [hj, zero_mul]
    · rw [hne j hj, mul_zero]
  have hex : ∃ i, f i x ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hx0
    rw [hx]
    simp [hne]
  obtain ⟨i0, hi0⟩ := hex
  let nxt : Fin g → Fin g := fun i => if h : f i x ≠ 0 then Classical.choose (key i h) else i
  have hnxt : ∀ i, f i x ≠ 0 → f (nxt i) x ≠ 0 ∧ f i (w * u (nxt i)) ≠ 0 := by
    intro i hi
    have e : nxt i = Classical.choose (key i hi) := dif_pos hi
    rw [e]
    exact Classical.choose_spec (key i hi)
  have hit : ∀ n, f (nxt^[n] i0) x ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hi0
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hnxt _ ih).1
  obtain ⟨a, n, hn, hper⟩ := periodic_pt nxt i0
  have hqit : ∀ m, f (nxt^[m] (nxt^[a] i0)) x ≠ 0 := by
    intro m
    rw [← Function.iterate_add_apply]
    exact hit _
  have hl := hper.minimalPeriod_pos hn
  refine ⟨minimalPeriod nxt (nxt^[a] i0), hl, ⟨fun j => nxt^[j.val] (nxt^[a] i0), ?_⟩, ?_⟩
  · intro j1 j2 h
    exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod j1.isLt j2.isLt h)
  · intro j
    show f (nxt^[j.val] (nxt^[a] i0))
      (w * u (nxt^[(j.val + 1) % minimalPeriod nxt (nxt^[a] i0)] (nxt^[a] i0))) ≠ 0
    rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']
    exact (hnxt _ (hqit _)).2

def Cyc {g : ℕ} (E : Fin g → Fin g → Prop) (l : ℕ) (c : ℕ → Fin g) : Prop :=
  0 < l ∧ (∀ i, c (i + l) = c i) ∧ (∀ i j, i < l → j < l → c i = c j → i = j) ∧
    ∀ i, E (c i) (c (i + 1))

theorem cyc_mod {g : ℕ} {E : Fin g → Fin g → Prop} {l : ℕ} {c : ℕ → Fin g}
    (h : Cyc E l c) (i : ℕ) : c i = c (i % l) := by
  have hp : ∀ k r, c (r + l * k) = c r := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih => intro r; rw [Nat.mul_succ, ← Nat.add_assoc, h.2.1, ih]
  conv_lhs => rw [← Nat.mod_add_div i l]
  exact hp _ _

theorem cyc_eq {g : ℕ} {E : Fin g → Fin g → Prop} {l : ℕ} {c : ℕ → Fin g}
    (h : Cyc E l c) {x y : ℕ} (hxy : c x = c y) : x % l = y % l := by
  rw [cyc_mod h x, cyc_mod h y] at hxy
  exact h.2.2.1 _ _ (Nat.mod_lt _ h.1) (Nat.mod_lt _ h.1) hxy

theorem shorten {g : ℕ} {E : Fin g → Fin g → Prop} {l : ℕ} {c : ℕ → Fin g}
    (h : Cyc E l c) {a b : ℕ}
    (hab : a + 1 < b) (hb : b ≤ a + l) (hE : E (c a) (c b)) :
    ∃ c', Cyc E (a + l - b + 1) c' := by
  have h0 := h
  obtain ⟨hl, hper, hinj, harc⟩ := h
  set L := a + l - b + 1 with hL
  have hL0 : 0 < L := by omega
  refine ⟨fun i => c (b + i % L), hL0, ?_, ?_, ?_⟩
  · intro i
    simp only [Nat.add_mod_right]
  · intro i j hi hj hij
    simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hij
    have h1 := cyc_eq h0 hij
    have h2 : i % l = j % l := Nat.ModEq.add_left_cancel' b h1
    rwa [Nat.mod_eq_of_lt (by omega : i < l), Nat.mod_eq_of_lt (by omega : j < l)] at h2
  · intro i
    have hi := Nat.mod_lt i hL0
    have e : (i % L + 1) % L = (i + 1) % L := (Nat.mod_modEq i L).add_right 1
    show E (c (b + i % L)) (c (b + (i + 1) % L))
    by_cases hc : i % L + 1 < L
    · have h3 : (i + 1) % L = i % L + 1 := by
        rw [← e]
        exact Nat.mod_eq_of_lt hc
      rw [h3, ← Nat.add_assoc]
      exact harc _
    · have h1 : i % L + 1 = L := by omega
      have h3 : (i + 1) % L = 0 := by
        rw [← e, h1, Nat.mod_self]
      rw [h3, Nat.add_zero]
      have h2 : b + i % L = a + l := by omega
      rw [h2, hper]
      exact hE

theorem nochord {g : ℕ} {E : Fin g → Fin g → Prop} {l : ℕ} {c : ℕ → Fin g}
    (h : Cyc E l c) (hmin : ∀ l' < l, ∀ c', ¬ Cyc E l' c') {a b : ℕ}
    (hab : a + 1 < b) (hb : b ≤ a + l) : ¬ E (c a) (c b) := by
  intro hE
  obtain ⟨c', hc'⟩ := shorten h hab hb hE
  exact hmin _ (by omega) c' hc'

theorem backward {K : Type} [Field K] [Algebra (ZMod 2) K] {g : ℕ}
    (u : Fin g → K) (f : Fin g → (K →ₗ[ZMod 2] ZMod 2)) (w : K)
    (l : ℕ) (hl : 0 < l) (p : Fin l ↪ Fin g)
    (hp : ∀ j : Fin l, f (p j) (w * u (p ⟨(j.val+1) % l, Nat.mod_lt _ hl⟩)) ≠ 0) :
    ∃ (S : Finset (Fin g)) (x : K), x ≠ 0 ∧ x = w * ∑ i ∈ S, (f i x) • u i := by
  classical
  have hex : ∃ l, ∃ c, Cyc (fun i j => f i (w * u j) ≠ 0) l c := by
    refine ⟨l, fun i => p ⟨i % l, Nat.mod_lt _ hl⟩, hl, ?_, ?_, ?_⟩
    · intro i
      exact congrArg p (Fin.ext (Nat.add_mod_right i l))
    · intro i j hi hj hij
      have h2 : i % l = j % l := congrArg Fin.val (p.injective hij)
      rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
    · intro i
      have h3 := hp ⟨i % l, Nat.mod_lt _ hl⟩
      have e : p ⟨(i + 1) % l, Nat.mod_lt _ hl⟩ =
          p ⟨((⟨i % l, Nat.mod_lt _ hl⟩ : Fin l).val + 1) % l, Nat.mod_lt _ hl⟩ :=
        congrArg p (Fin.ext ((Nat.mod_modEq i l).add_right 1).symm)
      show f (p ⟨i % l, Nat.mod_lt _ hl⟩) (w * u (p ⟨(i + 1) % l, Nat.mod_lt _ hl⟩)) ≠ 0
      rw [e]
      exact h3
  obtain ⟨c, hc⟩ := Nat.find_spec hex
  have hmin : ∀ l' < Nat.find hex, ∀ c', ¬ Cyc (fun i j => f i (w * u j) ≠ 0) l' c' :=
    fun l' h c' hc' => Nat.find_min hex h ⟨c', hc'⟩
  set L0 := Nat.find hex with hL0
  have hpos : 0 < L0 := hc.1
  have hzero : ∀ a < L0, ∀ b0 < L0, c b0 ≠ c (a + 1) → f (c a) (w * u (c b0)) = 0 := by
    intro a ha b0 hb0 hne
    by_contra hE
    by_cases hba : a < b0
    · have h1 : a + 1 < b0 := by
        rcases Nat.lt_or_ge (a + 1) b0 with h | h
        · exact h
        · exfalso
          apply hne
          congr 1
          omega
      exact nochord hc hmin h1 (by omega) hE
    · have hcb : c (b0 + L0) = c b0 := hc.2.1 b0
      have h1 : a + 1 < b0 + L0 := by
        rcases Nat.lt_or_ge (a + 1) (b0 + L0) with h | h
        · exact h
        · exfalso
          apply hne
          rw [← hcb]
          congr 1
          omega
      exact nochord hc hmin h1 (by omega) (by rw [hcb]; exact hE)
  set S := (range L0).image c with hS
  have memS : ∀ i, c i ∈ S := by
    intro i
    rw [cyc_mod hc i]
    exact mem_image_of_mem c (mem_range.2 (Nat.mod_lt _ hpos))
  set x := w * ∑ i ∈ S, u i with hx
  have hval : ∀ s ∈ S, f s x = 1 := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hs
    rw [mem_range] at ha
    have e1 : f (c a) x = ∑ j ∈ S, (1 : ZMod 2) * f (c a) (w * u j) := by
      rw [← lin u f w (c a) (fun _ => 1) S]
      simp only [one_smul, hx]
    rw [e1, Finset.sum_eq_single_of_mem (c (a + 1)) (memS _)]
    · rw [one_mul]
      exact zmod2_eq_one (hc.2.2.2 a)
    · intro j hj hne
      obtain ⟨b0, hb0, rfl⟩ := mem_image.1 hj
      rw [mem_range] at hb0
      rw [hzero a ha b0 hb0 hne, mul_zero]
  refine ⟨S, x, ?_, ?_⟩
  · intro h0
    have := hval (c 0) (memS 0)
    rw [h0, map_zero] at this
    exact absurd this (by decide)
  · conv_lhs => rw [hx]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hval i hi, one_smul]

end PEqualNP.Outside.L_lib_834

open PEqualNP.Outside.L_lib_834 in
theorem PEqualNP.Outside.L_lib_834 :
let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] (g : ℕ)
    (u : Fin g → K) (f : Fin g → (K →ₗ[F] F)) (w : K), w ≠ 0 →
  ((∃ (S : Finset (Fin g)) (x : K), x ≠ 0 ∧
    x = w * ∑ i ∈ S, (f i x) • u i) ↔
  ∃ (l : ℕ) (hl : 0 < l) (p : Fin l ↪ Fin g),
    ∀ j : Fin l, f (p j) (w * u (p ⟨(j.val+1) % l, Nat.mod_lt _ hl⟩)) ≠ 0) := by
  intro F K _ _ g u f w _
  constructor
  · rintro ⟨S, x, hx0, hx⟩
    exact forward u f w S x hx0 hx
  · rintro ⟨l, hl, p, hp⟩
    exact backward u f w l hl p hp
