import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1034

open Finset

abbrev Cl (n : ℕ) := (Fin n × Bool) × (Fin n × Bool)

def sb {k : ℕ} (A : Finset (Cl k)) (w : Fin k → Bool) : Bool :=
  decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

def ms {k : ℕ} (A : Finset (Cl k)) : ℕ :=
  (Finset.univ.filter (fun x : Fin k → Bool => sb A x = true)).card

theorem sb_iff {k : ℕ} (A : Finset (Cl k)) (w : Fin k → Bool) :
    sb A w = true ↔ ∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
  unfold sb; exact decide_eq_true_iff

def mapC {m n : ℕ} (f : Fin m → Fin n) (cl : Cl m) : Cl n :=
  ((f cl.1.1, cl.1.2), (f cl.2.1, cl.2.2))

def ctr (d m : ℕ) : Fin (d + 1 + m) := Fin.castAdd m (Fin.last d)

def old (d m : ℕ) (i : Fin d) : Fin (d + 1 + m) := Fin.castAdd m (Fin.castSucc i)

def base (d m : ℕ) (B : Finset (Cl d)) : Finset (Cl (d + 1 + m)) :=
  B.image (mapC (old d m)) ∪ {((ctr d m, false), (ctr d m, false))}

def ext (d m : ℕ) (B : Finset (Cl d)) (z : Fin (d + 1 + m) → Bool) : Finset (Cl (d + 1 + m)) :=
  B.image (mapC (old d m)) ∪
    (univ.filter (fun k => k ≠ ctr d m)).image (fun k => ((ctr d m, false), (k, !z k)))

theorem sb_base (d m : ℕ) (B : Finset (Cl d)) (x : Fin (d + 1 + m) → Bool) :
    sb (base d m B) x = true ↔ x (ctr d m) = true ∧ sb B (fun i => x (old d m i)) = true := by
  rw [sb_iff, sb_iff, base, forall_mem_union, forall_mem_image]
  simp only [mem_singleton, forall_eq, mapC, or_self, ne_eq, Bool.not_eq_false]
  exact And.comm

theorem sb_ext (d m : ℕ) (B : Finset (Cl d)) (z x : Fin (d + 1 + m) → Bool) :
    sb (ext d m B z) x = true ↔ sb B (fun i => x (old d m i)) = true ∧
      ∀ k, k ≠ ctr d m → x (ctr d m) = true ∨ x k = z k := by
  rw [sb_iff, sb_iff, ext, forall_mem_union, forall_mem_image, forall_mem_image]
  simp only [mapC, mem_filter, mem_univ, true_and, ne_eq, Bool.not_eq_false]
  apply and_congr Iff.rfl
  apply forall_congr'; intro k; apply imp_congr Iff.rfl
  apply or_congr Iff.rfl
  cases x k <;> cases z k <;> simp

theorem card_P (d m : ℕ) (B : Finset (Cl d)) (b : Bool) :
    (univ.filter (fun x : Fin (d + 1 + m) → Bool =>
      x (ctr d m) = b ∧ sb B (fun i => x (old d m i)) = true)).card = ms B * 2 ^ m := by
  have h : (univ.filter (fun x : Fin (d + 1 + m) → Bool =>
      x (ctr d m) = b ∧ sb B (fun i => x (old d m i)) = true)).card =
      ((univ.filter (fun y : Fin d → Bool => sb B y = true)) ×ˢ
        (univ : Finset (Fin m → Bool))).card := by
    apply card_nbij' (fun x => ((fun i => x (old d m i)), fun j => x (Fin.natAdd (d + 1) j)))
      (fun p => Fin.append (Fin.snoc p.1 b) p.2)
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      rw [mem_coe, mem_product, mem_filter]
      exact ⟨⟨mem_univ _, hx.2.2⟩, mem_univ _⟩
    · intro p hp
      rw [mem_coe, mem_product, mem_filter] at hp
      rw [mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_, ?_⟩
      · simp [ctr, Fin.append_left, Fin.snoc_last]
      · simpa [old, Fin.append_left, Fin.snoc_castSucc] using hp.1.2
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simp only [Fin.append_left, Fin.snoc_last]
          exact hx.2.1.symm
        · simp [old, Fin.append_left, Fin.snoc_castSucc]
      · simp [Fin.append_right]
    · intro p _
      simp [old, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
  rw [h, card_product, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rfl

theorem ms_base (d m : ℕ) (B : Finset (Cl d)) : ms (base d m B) = ms B * 2 ^ m := by
  rw [← card_P d m B true, ms]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact sb_base d m B x

theorem main (d : ℕ) (B : Finset (Cl d)) (m : ℕ) :
    ∃ (bs : Finset (Cl (d + 1 + m))) (S : Finset (Fin (d + 1 + m) → Bool))
      (extend : (Fin (d + 1 + m) → Bool) → Finset (Cl (d + 1 + m))),
      ms bs = ms B * 2 ^ m ∧ S.card = ms B * 2 ^ m ∧
      ∀ z ∈ S, sb bs z = false ∧ ms (extend z) = ms B * 2 ^ m + 1 ∧
        ∀ x, (sb (extend z) x = true ↔ (sb bs x = true ∨ x = z)) := by
  refine ⟨base d m B, univ.filter (fun x : Fin (d + 1 + m) → Bool =>
      x (ctr d m) = false ∧ sb B (fun i => x (old d m i)) = true), ext d m B,
    ms_base d m B, card_P d m B false, ?_⟩
  intro z hz
  rw [mem_filter] at hz
  obtain ⟨_, hz0, hzB⟩ := hz
  have hzb : sb (base d m B) z = false := by
    cases h : sb (base d m B) z
    · rfl
    · have := ((sb_base d m B z).1 h).1
      rw [hz0] at this
      exact absurd this (by decide)
  have key : ∀ x, (sb (ext d m B z) x = true ↔ (sb (base d m B) x = true ∨ x = z)) := by
    intro x
    rw [sb_ext, sb_base]
    constructor
    · rintro ⟨hB, hk⟩
      cases hc : x (ctr d m)
      · right
        funext k
        by_cases hkc : k = ctr d m
        · rw [hkc, hc, hz0]
        · rcases hk k hkc with h | h
          · rw [hc] at h; exact absurd h (by decide)
          · exact h
      · left; exact ⟨rfl, hB⟩
    · rintro (⟨hc, hB⟩ | rfl)
      · exact ⟨hB, fun k _ => Or.inl hc⟩
      · exact ⟨hzB, fun k _ => Or.inr rfl⟩
  refine ⟨hzb, ?_, key⟩
  have hset : univ.filter (fun x => sb (ext d m B z) x = true) =
      insert z (univ.filter (fun x => sb (base d m B) x = true)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    rw [key x, or_comm]
  rw [ms, hset, card_insert_of_notMem, ← ms, ms_base]
  simp [hzb]

end PEqualNP.Outside.L_lib_1034

open PEqualNP.Outside.L_lib_1034 in
theorem PEqualNP.Outside.L_lib_1034 : let W := fun k : ℕ => Fin k → Bool
let F := fun k : ℕ => Finset ((Fin k × Bool) × (Fin k × Bool))
let sat := fun (k : ℕ) (A : F k) (w : W k) => decide (∀ c ∈ A,
  w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
let mass := fun (k : ℕ) (A : F k) =>
  (Finset.univ.filter (fun x : W k => sat k A x = true)).card
∀ (d : ℕ) (B : F d) (m : ℕ),
  let n := d + 1 + m
  let N := mass d B * 2 ^ m
  ∃ (base : F n) (S : Finset (W n)) (extend : W n → F n),
    mass n base = N ∧ S.card = N ∧
    ∀ z ∈ S, sat n base z = false ∧ mass n (extend z) = N + 1 ∧
      ∀ x : W n, (sat n (extend z) x = true ↔ (sat n base x = true ∨ x = z)) := by
  intro W F sat mass d B m n N
  exact main d B m
