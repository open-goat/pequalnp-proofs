import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1084

open Finset

variable {n : ℕ}

/-- Laminar family closed under the union rule, without the empty set. -/
def Good (G : Finset (Finset (Fin n))) : Prop :=
  (∀ a ∈ G, ∀ b ∈ G, Disjoint a b ∨ a ⊆ b ∨ b ⊆ a) ∧
  (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, Disjoint a b → a ⊆ c → b ⊆ c → c = a ∪ b) ∧
  ∅ ∉ G

theorem ne_of_mem {G : Finset (Finset (Fin n))} (hG : Good G) {a : Finset (Fin n)}
    (ha : a ∈ G) : a.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact hG.2.2 ha


abbrev Cl (n : ℕ) := (Fin n × Bool) × (Fin n × Bool)

def Sat {n : ℕ} (A : Finset (Cl n)) (x : Fin n → Bool) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2

/-- A set is 2-clause definable when each outside word is cut off by a pair of positions. -/
theorem define {n : ℕ} (T : (Fin n → Bool) → Prop)
    (h : ∀ x, ¬ T x → ∃ p q : Fin n, ∀ t, T t → t p ≠ x p ∨ t q ≠ x q) :
    ∃ B : Finset (Cl n), ∀ x, (Sat B x ↔ T x) := by
  classical
  refine ⟨univ.filter (fun c : Cl n => ∀ t, T t → t c.1.1 ≠ c.1.2 ∨ t c.2.1 ≠ c.2.2), ?_⟩
  intro x
  constructor
  · intro hx
    by_contra hT
    obtain ⟨p, q, hpq⟩ := h x hT
    have := hx ((p, x p), (q, x q)) (by simp only [mem_filter, mem_univ, true_and]; exact hpq)
    simp at this
  · intro hT c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    exact hc x hT

theorem bmaj : ∀ a1 b1 c1 a2 b2 c2 l1 l2 : Bool,
    (a1 ≠ l1 ∨ a2 ≠ l2) → (b1 ≠ l1 ∨ b2 ≠ l2) → (c1 ≠ l1 ∨ c2 ≠ l2) →
    ((if b1 = c1 then b1 else a1) ≠ l1 ∨ (if b2 = c2 then b2 else a2) ≠ l2) := by
  decide

theorem sat_maj {n : ℕ} (B : Finset (Cl n)) (x y u : Fin n → Bool)
    (hx : Sat B x) (hy : Sat B y) (hu : Sat B u) :
    Sat B (fun i => if y i = u i then y i else x i) := by
  intro c hc
  exact bmaj _ _ _ _ _ _ _ _ (hx c hc) (hy c hc) (hu c hc)

def dl (r z : Fin n → Bool) : Finset (Fin n) := univ.filter (fun i => z i ≠ r i)

theorem mem_dl {r z : Fin n → Bool} {i : Fin n} : i ∈ dl r z ↔ z i ≠ r i := by
  simp [dl]

theorem beq3 : ∀ a b c : Bool, (a ≠ c ↔ b ≠ c) → a = b := by decide

theorem dl_inj (r : Fin n → Bool) : Function.Injective (dl r) := by
  intro z z' h
  funext i
  apply beq3 _ _ (r i)
  rw [← mem_dl, ← mem_dl, h]

theorem dl_self (r : Fin n → Bool) : dl r r = ∅ := by
  ext i
  simp [dl]

theorem dl_ne {r z : Fin n → Bool} (h : z ≠ r) : (dl r z).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro e
  rw [← dl_self r] at e
  exact h (dl_inj r e)

def fl (r : Fin n → Bool) (D : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ D then !r i else r i

theorem dl_fl (r : Fin n → Bool) (D : Finset (Fin n)) : dl r (fl r D) = D := by
  ext i
  rw [mem_dl]
  unfold fl
  by_cases h : i ∈ D
  · rw [if_pos h]
    cases r i <;> simp [h]
  · rw [if_neg h]
    simp [h]

def Free (r : Fin n → Bool) (S : Finset (Fin n → Bool)) : Prop :=
  ∀ D : Finset (Fin n → Bool), D ⊆ S → ∃ A : Finset (Cl n), ∀ x : Fin n → Bool,
    (Sat A x ↔ (x = r ∨ x ∈ D))

theorem maj_mem {r : Fin n → Bool} {S : Finset (Fin n → Bool)} (hf : Free r S)
    (x y u : Fin n → Bool) (hx : x = r ∨ x ∈ S) (hy : y = r ∨ y ∈ S) (hu : u = r ∨ u ∈ S) :
    (fun i => if y i = u i then y i else x i) = r ∨
    (fun i => if y i = u i then y i else x i) = x ∨
    (fun i => if y i = u i then y i else x i) = y ∨
    (fun i => if y i = u i then y i else x i) = u := by
  classical
  obtain ⟨A, hA⟩ := hf (S.filter (fun w => w = x ∨ w = y ∨ w = u)) (filter_subset _ _)
  have hs : ∀ w, (w = r ∨ w ∈ S) → (w = x ∨ w = y ∨ w = u) → Sat A w := by
    intro w hw hw'
    apply (hA w).2
    rcases hw with h | h
    · exact Or.inl h
    · exact Or.inr (mem_filter.2 ⟨h, hw'⟩)
  have hm := sat_maj A x y u (hs x hx (Or.inl rfl)) (hs y hy (Or.inr (Or.inl rfl)))
    (hs u hu (Or.inr (Or.inr rfl)))
  rcases (hA _).1 hm with h | h
  · exact Or.inl h
  · exact Or.inr (mem_filter.1 h).2

theorem bA : ∀ a b c : Bool, (if a = b then a else c) = c → a ≠ c → b ≠ c → False := by
  decide
theorem bB : ∀ a b c : Bool, (if a = b then a else c) = a → a ≠ c → b ≠ c := by decide
theorem bC : ∀ a b c : Bool, (if a = b then a else c) = b → b ≠ c → a ≠ c := by decide
theorem bU : ∀ a b c d : Bool, ¬ (a ≠ d ∧ b ≠ d) → (a ≠ d → c ≠ d) → (b ≠ d → c ≠ d) →
    (((if a = b then a else c) ≠ d) ↔ (a ≠ d ∨ b ≠ d)) := by decide

theorem good_of {r : Fin n → Bool} {S : Finset (Fin n → Bool)} (hr : r ∉ S) (hf : Free r S) :
    Good (S.image (dl r)) := by
  have hne : ∀ x ∈ S, (dl r x).Nonempty := fun x hx => dl_ne (fun e => hr (e ▸ hx))
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
    rcases maj_mem hf r x y (Or.inl rfl) (Or.inr hx) (Or.inr hy) with h | h | h | h
    · left
      rw [Finset.disjoint_left]
      intro i hi hi'
      exact bA _ _ _ (congrFun h i) (mem_dl.1 hi) (mem_dl.1 hi')
    · left
      rw [Finset.disjoint_left]
      intro i hi hi'
      exact bA _ _ _ (congrFun h i) (mem_dl.1 hi) (mem_dl.1 hi')
    · right; left
      intro i hi
      exact mem_dl.2 (bB _ _ _ (congrFun h i) (mem_dl.1 hi))
    · right; right
      intro i hi
      exact mem_dl.2 (bC _ _ _ (congrFun h i) (mem_dl.1 hi))
  · intro a ha b hb c hc hab hac hbc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hc
    have key : ∀ i, ((if x i = y i then x i else u i) ≠ r i) ↔ (x i ≠ r i ∨ y i ≠ r i) := by
      intro i
      apply bU
      · rintro ⟨h1, h2⟩
        exact Finset.disjoint_left.1 hab (mem_dl.2 h1) (mem_dl.2 h2)
      · intro h1
        exact mem_dl.1 (hac (mem_dl.2 h1))
      · intro h1
        exact mem_dl.1 (hbc (mem_dl.2 h1))
    rcases maj_mem hf u x y (Or.inr hu) (Or.inr hx) (Or.inr hy) with h | h | h | h
    · exfalso
      obtain ⟨i, hi⟩ := hne x hx
      have := (key i).2 (Or.inl (mem_dl.1 hi))
      exact this (congrFun h i)
    · ext i
      rw [mem_union, mem_dl, mem_dl, mem_dl, ← key i, congrFun h i]
    · exfalso
      obtain ⟨i, hi⟩ := hne y hy
      have h2 := (key i).2 (Or.inr (mem_dl.1 hi))
      rw [congrFun h i] at h2
      exact Finset.disjoint_left.1 hab (mem_dl.2 h2) hi
    · exfalso
      obtain ⟨i, hi⟩ := hne x hx
      have h2 := (key i).2 (Or.inl (mem_dl.1 hi))
      rw [congrFun h i] at h2
      exact Finset.disjoint_left.1 hab hi (mem_dl.2 h2)
  · intro h
    obtain ⟨x, hx, e⟩ := mem_image.1 h
    rw [← dl_self r] at e
    exact hr (dl_inj r e ▸ hx)

theorem bE : ∀ a b c : Bool, a = b ↔ (a ≠ c ↔ b ≠ c) := by decide

theorem cut_of {r : Fin n → Bool} {D : Finset (Fin n → Bool)} {x : Fin n → Bool} {p q : Fin n}
    (hpq : p ∈ dl r x ∨ q ∈ dl r x)
    (h : ∀ t ∈ D, (p ∈ dl r t ↔ p ∈ dl r x) → (q ∈ dl r t ↔ q ∈ dl r x) → False) :
    ∀ t, (t = r ∨ t ∈ D) → t p ≠ x p ∨ t q ≠ x q := by
  intro t ht
  by_contra hc
  push Not at hc
  have h1 := (bE _ _ (r p)).1 hc.1
  have h2 := (bE _ _ (r q)).1 hc.2
  rw [← mem_dl, ← mem_dl] at h1 h2
  rcases ht with rfl | ht
  · rw [dl_self] at h1 h2
    rcases hpq with h3 | h3
    · exact absurd (h1.2 h3) (Finset.notMem_empty p)
    · exact absurd (h2.2 h3) (Finset.notMem_empty q)
  · exact h t ht h1 h2

theorem suff {r : Fin n → Bool} {S : Finset (Fin n → Bool)} (hG : Good (S.image (dl r))) :
    Free r S := by
  intro D hD
  apply define (fun x => x = r ∨ x ∈ D)
  intro x hx
  have hxr : x ≠ r := fun e => hx (Or.inl e)
  have hxD : x ∉ D := fun e => hx (Or.inr e)
  have hH : ∀ t ∈ D, dl r t ∈ S.image (dl r) := fun t ht => mem_image_of_mem _ (hD ht)
  have hXG : ∀ t ∈ D, dl r t ≠ dl r x := fun t ht e => hxD (dl_inj r e ▸ ht)
  have hX := dl_ne hxr
  set X := dl r x with hXdef
  by_cases h1 : ∃ p ∈ X, ∃ q, q ∉ X ∧ ∀ t ∈ D, p ∈ dl r t → q ∈ dl r t
  · obtain ⟨p, hp, q, hq, h⟩ := h1
    refine ⟨p, q, cut_of (Or.inl hp) ?_⟩
    intro t ht h1' h2'
    exact hq (h2'.1 (h t ht (h1'.2 hp)))
  push Not at h1
  by_cases h2 : ∃ p ∈ X, ∀ t ∈ D, p ∉ dl r t
  · obtain ⟨p, hp, h⟩ := h2
    refine ⟨p, p, cut_of (Or.inl hp) ?_⟩
    intro t ht h3 _
    exact h t ht (h3.2 hp)
  push Not at h2
  have h3 : ∀ p ∈ X, ∃ t ∈ D, p ∈ dl r t ∧ dl r t ⊆ X := by
    intro p hp
    obtain ⟨t1, ht1, hpt1⟩ := h2 p hp
    obtain ⟨t, htC, hmin⟩ := (D.filter (fun t => p ∈ dl r t)).exists_min_image
      (fun t => (dl r t).card) ⟨t1, mem_filter.2 ⟨ht1, hpt1⟩⟩
    have ht := (mem_filter.1 htC).1
    have hpt := (mem_filter.1 htC).2
    refine ⟨t, ht, hpt, ?_⟩
    intro q hq
    by_contra hqX
    obtain ⟨t', ht', hp', hq'⟩ := h1 p hp q hqX
    have hc := hmin t' (mem_filter.2 ⟨ht', hp'⟩)
    rcases hG.1 _ (hH t ht) _ (hH t' ht') with h | h | h
    · exact Finset.disjoint_left.1 h hpt hp'
    · exact hq' (h hq)
    · have hss : dl r t' ⊂ dl r t := ssubset_of_subset_of_ne h (fun e => hq' (e ▸ hq))
      have := card_lt_card hss
      omega
  obtain ⟨p0, hp0⟩ := hX
  obtain ⟨t0, ht0, _, ht0X⟩ := h3 p0 hp0
  obtain ⟨a, haE, hmax⟩ := (D.filter (fun t => dl r t ⊆ X)).exists_max_image
    (fun t => (dl r t).card) ⟨t0, mem_filter.2 ⟨ht0, ht0X⟩⟩
  have ha := (mem_filter.1 haE).1
  have haX := (mem_filter.1 haE).2
  obtain ⟨q, hqX, hqa⟩ : ∃ q ∈ X, q ∉ dl r a := by
    by_contra hc
    push Not at hc
    exact hXG a ha (Subset.antisymm haX hc)
  obtain ⟨b, hb, hqb, hbX⟩ := h3 q hqX
  have hcb := hmax b (mem_filter.2 ⟨hb, hbX⟩)
  have hab : Disjoint (dl r a) (dl r b) := by
    rcases hG.1 _ (hH a ha) _ (hH b hb) with h | h | h
    · exact h
    · have hss : dl r a ⊂ dl r b := ssubset_of_subset_of_ne h (fun e => hqa (e ▸ hqb))
      have := card_lt_card hss
      omega
    · exact absurd (h hqb) hqa
  obtain ⟨p, hp⟩ := ne_of_mem hG (hH a ha)
  refine ⟨p, q, cut_of (Or.inr hqX) ?_⟩
  intro t ht h4 h5
  have hpt := h4.2 (haX hp)
  have hqt := h5.2 hqX
  have hat : dl r a ⊆ dl r t := by
    rcases hG.1 _ (hH a ha) _ (hH t ht) with h | h | h
    · exact absurd hpt (Finset.disjoint_left.1 h hp)
    · exact h
    · exact absurd (h hqt) hqa
  have hbt : dl r b ⊆ dl r t := by
    rcases hG.1 _ (hH b hb) _ (hH t ht) with h | h | h
    · exact absurd hqt (Finset.disjoint_left.1 h hqb)
    · exact h
    · exact absurd (h hpt) (Finset.disjoint_left.1 hab hp)
  have he := hG.2.1 _ (hH a ha) _ (hH b hb) _ (hH t ht) hab hat hbt
  have htX : dl r t ⊆ X := he ▸ union_subset haX hbX
  have hct := hmax t (mem_filter.2 ⟨ht, htX⟩)
  rw [he, card_union_of_disjoint hab] at hct
  have : 0 < (dl r b).card := card_pos.2 ⟨q, hqb⟩
  omega

def Struct (T : Finset (Finset (Fin n))) : Prop :=
  let tops := T.filter (fun U => ∀ V ∈ T, U ⊆ V → U = V)
  (∀ U ∈ tops, ∀ V ∈ tops, U ≠ V → Disjoint U V) ∧
     ∀ U ∈ tops,
       ((∀ X ∈ T, X ⊆ U → ∀ Y ∈ T, Y ⊆ U → X ⊆ Y ∨ Y ⊆ X) ∨
        (∃ X ∈ T, ∃ Y ∈ T, X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
          X ∪ Y = U ∧ ∀ Z ∈ T, Z ⊆ U → (Z = X ∨ Z = Y ∨ Z = U)))

theorem above_top (T : Finset (Finset (Fin n))) {a : Finset (Fin n)} (ha : a ∈ T) :
    ∃ U ∈ T.filter (fun U => ∀ V ∈ T, U ⊆ V → U = V), a ⊆ U := by
  obtain ⟨U, hUC, hmax⟩ := (T.filter (fun U => a ⊆ U)).exists_max_image
    (fun U => U.card) ⟨a, mem_filter.2 ⟨ha, subset_rfl⟩⟩
  have hU := (mem_filter.1 hUC).1
  have haU := (mem_filter.1 hUC).2
  refine ⟨U, mem_filter.2 ⟨hU, ?_⟩, haU⟩
  intro V hV hUV
  exact eq_of_subset_of_card_le hUV (hmax V (mem_filter.2 ⟨hV, haU.trans hUV⟩))

theorem nd {a b : Finset (Fin n)} (hab : Disjoint a b) (h : a ⊆ b) (ha : a.Nonempty) : False := by
  obtain ⟨i, hi⟩ := ha
  exact Finset.disjoint_left.1 hab hi (h hi)

theorem sub_left {X Y Z : Finset (Fin n)} (h : Z ⊆ X ∪ Y) (hd : Disjoint Z Y) : Z ⊆ X := by
  intro i hi
  rcases mem_union.1 (h hi) with h1 | h1
  · exact h1
  · exact absurd h1 (Finset.disjoint_left.1 hd hi)

theorem sub_eq {T : Finset (Finset (Fin n))} (hG : Good T) {X Y U Z : Finset (Fin n)}
    (hY : Y ∈ T) (hU : U ∈ T) (hZ : Z ∈ T) (hXY : Disjoint X Y) (hUe : X ∪ Y = U)
    (hZX : Z ⊆ X) : Z = X := by
  have hU' := hG.2.1 Z hZ Y hY U hU (disjoint_of_subset_left hZX hXY)
    (hUe ▸ hZX.trans subset_union_left) (hUe ▸ subset_union_right)
  apply Subset.antisymm hZX
  apply sub_left _ hXY
  rw [← hU', ← hUe]
  exact subset_union_left

theorem struct_of_good {T : Finset (Finset (Fin n))} (hG : Good T) : Struct T := by
  refine ⟨?_, ?_⟩
  · intro U hU V hV hne
    have hU1 := (mem_filter.1 hU).1
    have hU2 := (mem_filter.1 hU).2
    have hV1 := (mem_filter.1 hV).1
    have hV2 := (mem_filter.1 hV).2
    rcases hG.1 U hU1 V hV1 with h | h | h
    · exact h
    · exact absurd (hU2 V hV1 h) hne
    · exact absurd (hV2 U hU1 h).symm hne
  · intro U hUt
    have hU := (mem_filter.1 hUt).1
    by_cases hc : ∀ X ∈ T, X ⊆ U → ∀ Y ∈ T, Y ⊆ U → X ⊆ Y ∨ Y ⊆ X
    · exact Or.inl hc
    right
    push Not at hc
    obtain ⟨X, hX, hXU, Y, hY, hYU, h1, h2⟩ := hc
    have hXY : Disjoint X Y := by
      rcases hG.1 X hX Y hY with h | h | h
      · exact h
      · exact absurd h h1
      · exact absurd h h2
    have hUe := (hG.2.1 X hX Y hY U hU hXY hXU hYU).symm
    have neX := ne_of_mem hG hX
    have neY := ne_of_mem hG hY
    refine ⟨X, hX, Y, hY, neX, neY, hXY, hUe, ?_⟩
    intro Z hZ hZU
    rw [← hUe] at hZU
    rcases hG.1 Z hZ X hX with h | h | h
    · right; left
      exact sub_eq hG hX hU hZ hXY.symm (by rw [union_comm]; exact hUe)
        (sub_left (by rw [union_comm]; exact hZU) h)
    · left
      exact sub_eq hG hY hU hZ hXY hUe h
    · rcases hG.1 Z hZ Y hY with h' | h' | h'
      · left
        exact Subset.antisymm (sub_left hZU h') h
      · exact (nd hXY (h.trans h') neX).elim
      · right; right
        apply Subset.antisymm (by rw [← hUe]; exact hZU)
        rw [← hUe]
        exact union_subset h h'

theorem good_of_struct {T : Finset (Finset (Fin n))} (hs : Struct T) (h0 : ∅ ∉ T) : Good T := by
  have hne : ∀ a ∈ T, a.Nonempty := fun a ha => by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    exact h0 ha
  refine ⟨?_, ?_, h0⟩
  · intro a ha b hb
    obtain ⟨U, hU, haU⟩ := above_top T ha
    obtain ⟨V, hV, hbV⟩ := above_top T hb
    by_cases hUV : U = V
    · subst hUV
      rcases hs.2 U hU with hch | ⟨X, hX, Y, hY, _, _, hXY, _, hZ⟩
      · exact Or.inr (hch a ha haU b hb hbV)
      · rcases hZ a ha haU with rfl | rfl | rfl <;> rcases hZ b hb hbV with rfl | rfl | rfl
        all_goals first
          | exact Or.inl hXY
          | exact Or.inl hXY.symm
          | exact Or.inr (Or.inl subset_rfl)
          | exact Or.inr (Or.inl ‹_›)
          | exact Or.inr (Or.inr ‹_›)
    · exact Or.inl (Disjoint.mono haU hbV (hs.1 U hU V hV hUV))
  · intro a ha b hb c hc hab hac hbc
    obtain ⟨U, hU, hcU⟩ := above_top T hc
    have haU := hac.trans hcU
    have hbU := hbc.trans hcU
    have hna := hne a ha
    have hnb := hne b hb
    rcases hs.2 U hU with hch | ⟨X, hX, Y, hY, _, _, hXY, hUe, hZ⟩
    · rcases hch a ha haU b hb hbU with h | h
      · exact (nd hab h hna).elim
      · exact (nd hab.symm h hnb).elim
    · rcases hZ a ha haU with rfl | rfl | rfl <;> rcases hZ b hb hbU with rfl | rfl | rfl
      all_goals first
        | exact (nd hab subset_rfl hna).elim
        | exact (nd hab ‹_› hna).elim
        | exact (nd hab.symm ‹_› hnb).elim
        | (apply Subset.antisymm _ (union_subset hac hbc)
           first
            | (rw [hUe]; exact hcU)
            | (rw [union_comm, hUe]; exact hcU))

end PEqualNP.Outside.L_lib_1084

open Finset PEqualNP.Outside.L_lib_1084 in
theorem PEqualNP.Outside.L_lib_1084 :
let W := fun n : ℕ => Fin n → Bool
let F := fun n : ℕ => Finset ((Fin n × Bool) × (Fin n × Bool))
let sat := fun (n : ℕ) (A : F n) (x : W n) =>
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
let delta := fun (n : ℕ) (r z : W n) =>
  Finset.univ.filter (fun i : Fin n => z i ≠ r i)
let free := fun (n : ℕ) (r : W n) (S : Finset (W n)) =>
  ∀ D : Finset (W n), D ⊆ S → ∃ A : F n, ∀ x : W n,
    (sat n A x ↔ (x = r ∨ x ∈ D))
∀ (n : ℕ) (r : W n) (S : Finset (W n)), r ∉ S →
  let T := S.image (delta n r)
  let tops := T.filter (fun U => ∀ V ∈ T, U ⊆ V → U = V)
  (free n r S ↔
    ((∀ U ∈ tops, ∀ V ∈ tops, U ≠ V → Disjoint U V) ∧
     ∀ U ∈ tops,
       ((∀ X ∈ T, X ⊆ U → ∀ Y ∈ T, Y ⊆ U → X ⊆ Y ∨ Y ⊆ X) ∨
        (∃ X ∈ T, ∃ Y ∈ T, X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
          X ∪ Y = U ∧ ∀ Z ∈ T, Z ⊆ U → (Z = X ∨ Z = Y ∨ Z = U))))) := by
  intro W F sat delta free n r S hr
  show Free r S ↔ Struct (S.image (dl r))
  have h0 : ∅ ∉ S.image (dl r) := by
    intro h
    obtain ⟨x, hx, e⟩ := mem_image.1 h
    rw [← dl_self r] at e
    exact hr (dl_inj r e ▸ hx)
  constructor
  · intro hf
    exact struct_of_good (good_of hr hf)
  · intro hs
    exact suff (good_of_struct hs h0)
