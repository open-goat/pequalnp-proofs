import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18500_4 (h1 :
  let I := Fin 13
  let X := Finset I × Finset I
  let G := Bool × ℕ × ℕ
  let D : Finset I := {0,1,3,9}
  let col (j : I) : Set X := {v | j ∈ v.2}
  let initial : List (Set X) := List.ofFn (fun i : Fin 25 => {v : X | if i.val < 12 then Fin.ofNat 13 (i.val + 1) ∈ v.1 else Fin.ofNat 13 (i.val - 12) ∈ v.2})
  let step (w : List (Set X)) (g : G) := w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)
  let frontRow (r : ℕ) := fun d : ℕ => col (Fin.ofNat 13 (13 + d - r))
  let prep (r : ℕ) := let f := frontRow r; [f 0 ∪ f 1, f 3 ∪ f 9, (f 0 ∪ f 1) ∪ (f 3 ∪ f 9)]
  let bank := initial ++ (List.range 6).flatMap (fun j => prep (7+j))
  let inner : Set X := {v | ∃ p ∈ v.1, 0 < p.val ∧ p.val < 7 ∧ ∃ l ∈ v.2, p+l ∈ D}
  let aux : Set X := {v | ∃ l ∈ v.2, l ∈ D}
  ∃ (gs : List G) (o q : ℕ), gs.length ≤ 31 ∧ o < 54 + gs.length ∧ q < 54 + gs.length ∧
    ∀ t : List (Set X), t.length = 11 → let w := gs.foldl step (bank ++ t)
      w.getD o ∅ = inner ∧ aux \ inner ⊆ w.getD q ∅ ∧ w.getD q ∅ ⊆ aux ∪ inner) (h2 :
  let I := Fin 13
  let X := Finset I × Finset I
  let G := Bool × ℕ × ℕ
  let D : Finset I := {0,1,3,9}
  let col (j : I) : Set X := {v | j ∈ v.2}
  let initial : List (Set X) := List.ofFn (fun i : Fin 25 => {v : X | if i.val < 12 then Fin.ofNat 13 (i.val + 1) ∈ v.1 else Fin.ofNat 13 (i.val - 12) ∈ v.2})
  let step (w : List (Set X)) (g : G) := w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)
  let frontRow (r : ℕ) := fun d : ℕ => col (Fin.ofNat 13 (13 + d - r))
  let prep (r : ℕ) := let f := frontRow r; [f 0 ∪ f 1, f 3 ∪ f 9, (f 0 ∪ f 1) ∪ (f 3 ∪ f 9)]
  let bank := initial ++ (List.range 6).flatMap (fun j => prep (7+j))
  let outer : Set X := {v | ∃ p ∈ v.1, 7 ≤ p.val ∧ ∃ l ∈ v.2, p+l ∈ D}
  ∃ (gs : List G) (t : List (Set X)), gs.length = 29 ∧ t.length = 11 ∧
    gs.foldl step initial = bank ++ t ∧ (bank ++ t).getD 53 ∅ = outer) : let x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : Fin (25 : ℕ) → Set x1 := fun (x3 : Fin (25 : ℕ)) => {x4 : x1 | if ↑x3 < (12 : ℕ) then Fin.ofNat (13 : ℕ) (↑x3 + (1 : ℕ)) ∈ x4.1 else Fin.ofNat (13 : ℕ) (↑x3 - (12 : ℕ)) ∈ x4.2}; have x4 : Set x1 := {x4 : x1 | ∃ x5 ∈ x4.1, x5 ≠ (0 : Fin (13 : ℕ)) ∧ ∃ x6 ∈ x4.2, x5 + x6 ∈ x2}; have x5 : Set x1 := {x5 : x1 | ∃ x6 ∈ x5.2, x6 ∈ x2}; ∃ (x6 : List (Bool × ℕ × ℕ)) (x7 : ℕ) (x8 : ℕ),   have x9 : List (Set x1) := List.foldl (fun (x9 : List (Set x1)) (x10 : Bool × ℕ × ℕ) => x9.concat (if x10.1 = Bool.true then x9.getD x10.2.1 ∅ ∩ x9.getD x10.2.2 ∅ else x9.getD x10.2.1 ∅ ∪ x9.getD x10.2.2 ∅)) (List.ofFn x3) x6;   x6.length ≤ (61 : ℕ) ∧ x7 < (25 : ℕ) + x6.length ∧ x8 < (25 : ℕ) + x6.length ∧ x9.getD x7 ∅ = x4 ∧ x5 \ x4 ⊆ x9.getD x8 ∅ ∧ x9.getD x8 ∅ ⊆ x5 ∪ x4 := by
  let I := Fin 13
  let X := Finset I × Finset I
  let G := Bool × ℕ × ℕ
  let D : Finset I := {0,1,3,9}
  let col (j : I) : Set X := {v | j ∈ v.2}
  let initial : List (Set X) := List.ofFn (fun i : Fin 25 => {v : X | if i.val < 12 then Fin.ofNat 13 (i.val + 1) ∈ v.1 else Fin.ofNat 13 (i.val - 12) ∈ v.2})
  let step (w : List (Set X)) (g : G) := w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)
  let frontRow (r : ℕ) := fun d : ℕ => col (Fin.ofNat 13 (13 + d - r))
  let prep (r : ℕ) := let f := frontRow r; [f 0 ∪ f 1, f 3 ∪ f 9, (f 0 ∪ f 1) ∪ (f 3 ∪ f 9)]
  let bank := initial ++ (List.range 6).flatMap (fun j => prep (7+j))
  let inner : Set X := {v | ∃ p ∈ v.1, 0 < p.val ∧ p.val < 7 ∧ ∃ l ∈ v.2, p+l ∈ D}
  let aux : Set X := {v | ∃ l ∈ v.2, l ∈ D}
  let outer : Set X := {v | ∃ p ∈ v.1, 7 ≤ p.val ∧ ∃ l ∈ v.2, p+l ∈ D}
  let target : Set X := {v | ∃ p ∈ v.1, p ≠ 0 ∧ ∃ l ∈ v.2, p+l ∈ D}
  have length_fold (gs : List G) (w : List (Set X)) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [step,Nat.add_assoc,Nat.add_comm]
  have keep (gs : List G) (w : List (Set X)) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i ∅ = w.getD i ∅ := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step, List.concat_eq_append, List.getD_append _ _ _ _ hi]
  change ∃ (gs : List G) (o q : ℕ),
    let w := gs.foldl step initial
    gs.length ≤ 61 ∧ o < 25 + gs.length ∧ q < 25 + gs.length ∧
    w.getD o ∅ = target ∧ aux \ target ⊆ w.getD q ∅ ∧ w.getD q ∅ ⊆ aux ∪ target
  change ∃ (gs : List G) (o q : ℕ), gs.length ≤ 31 ∧ o < 54 + gs.length ∧ q < 54 + gs.length ∧
      ∀ t : List (Set X), t.length = 11 → let w := gs.foldl step (bank ++ t)
        w.getD o ∅ = inner ∧ aux \ inner ⊆ w.getD q ∅ ∧ w.getD q ∅ ⊆ aux ∪ inner at h1
  change ∃ (gs : List G) (t : List (Set X)), gs.length = 29 ∧ t.length = 11 ∧
      gs.foldl step initial = bank ++ t ∧ (bank ++ t).getD 53 ∅ = outer at h2
  obtain ⟨g,o,q,hg,ho,hq,hs⟩ := h1
  obtain ⟨b,t,hb,ht,hbase,houter⟩ := h2
  obtain ⟨hm,hl,hu⟩ := hs t ht
  let w := g.foldl step (bank ++ t)
  change w.getD o ∅ = inner at hm
  have hw : w.length = 54 + g.length := by
    rw [show w.length = _ from length_fold g (bank ++ t), List.length_append, ht, show bank.length = 43 from rfl]
  have hold : w.getD 53 ∅ = outer := by
    exact (keep g _ 53 (by rw [List.length_append,ht,show bank.length = 43 from rfl]; decide)).trans houter
  have hsplit : outer ∪ inner = target := by
    ext v
    constructor
    · rintro (⟨p,hp,hv,h⟩ | ⟨p,hp,hv,_,h⟩)
      · exact ⟨p,hp,Fin.pos_iff_ne_zero.mp (show 0 < p.val by omega),h⟩
      · exact ⟨p,hp,Fin.pos_iff_ne_zero.mp hv,h⟩
    · rintro ⟨p,hp,hn,h⟩
      by_cases h7 : 7 ≤ p.val
      · exact Or.inl ⟨p,hp,h7,h⟩
      · exact Or.inr ⟨p,hp,Fin.pos_iff_ne_zero.mpr hn,by omega,h⟩
  let allG : List G := (b ++ g) ++ [(false,53,o)]
  have hlen : allG.length = 30 + g.length := by simp [allG,hb,Nat.add_comm]
  have hall : allG.foldl step initial = w ++ [target] := by
    simp only [allG,List.foldl_append,List.foldl_cons,List.foldl_nil,hbase]
    change step w (false,53,o) = _
    simp only [step, Bool.false_eq_true, ite_false, List.concat_eq_append, hold, hm, hsplit]
  refine ⟨allG,w.length,q,by omega,by omega,by omega,?_,?_,?_⟩
  · rw [hall,List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
    rfl
  · rw [hall,List.getD_append _ _ _ _ (show q < w.length by omega)]
    intro z hz
    exact hl ⟨hz.1,fun hi => hz.2 (hsplit ▸ Or.inr hi)⟩
  · rw [hall,List.getD_append _ _ _ _ (show q < w.length by omega)]
    intro z hz
    rcases hu hz with ha|hi
    · exact Or.inl ha
    · exact Or.inr (hsplit ▸ Or.inr hi)
