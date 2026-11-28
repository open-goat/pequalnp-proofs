import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1085

open Finset

variable {n : ℕ}

/-- Laminar family closed under the union rule, without the empty set. -/
def Good (G : Finset (Finset (Fin n))) : Prop :=
  (∀ a ∈ G, ∀ b ∈ G, Disjoint a b ∨ a ⊆ b ∨ b ⊆ a) ∧
  (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, Disjoint a b → a ⊆ c → b ⊆ c → c = a ∪ b) ∧
  ∅ ∉ G

def wit (G : Finset (Finset (Fin n))) (c : Finset (Fin n)) : Finset (Fin n) :=
  c.filter (fun i => ∀ d ∈ G, i ∈ d → d ⊆ c → d = c)

def Priv (G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  G.filter (fun c => (wit G c).Nonempty)

def Bin (G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  G.filter (fun c => ¬ (wit G c).Nonempty)

def Atom (G : Finset (Finset (Fin n))) (a : Finset (Fin n)) : Prop :=
  ∀ d ∈ G, d ⊆ a → d = a

theorem ne_of_mem {G : Finset (Finset (Fin n))} (hG : Good G) {a : Finset (Fin n)}
    (ha : a ∈ G) : a.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact hG.2.2 ha

theorem wit_disj {G : Finset (Finset (Fin n))} (hG : Good G) {c c' : Finset (Fin n)}
    (hc : c ∈ G) (hc' : c' ∈ G) (hne : c ≠ c') : Disjoint (wit G c) (wit G c') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [wit, mem_filter] at hi hi'
  rcases hG.1 c hc c' hc' with h | h | h
  · exact Finset.disjoint_left.1 h hi.1 hi'.1
  · exact hne (hi'.2 c hc hi.1 h)
  · exact hne (hi.2 c' hc' hi'.1 h).symm

theorem sum_wit {G : Finset (Finset (Fin n))} (hG : Good G) :
    ∑ c ∈ Priv G, (wit G c).card = ((Priv G).biUnion (wit G)).card := by
  rw [card_biUnion]
  intro c hc c' hc' hne
  exact wit_disj hG (mem_filter.1 hc).1 (mem_filter.1 hc').1 hne

theorem priv_le {G : Finset (Finset (Fin n))} (hG : Good G) :
    (Priv G).card ≤ ∑ c ∈ Priv G, (wit G c).card ∧ ∑ c ∈ Priv G, (wit G c).card ≤ n := by
  constructor
  · rw [card_eq_sum_ones]
    apply sum_le_sum
    intro c hc
    exact (mem_filter.1 hc).2.card_pos
  · rw [sum_wit hG]
    calc _ ≤ (univ : Finset (Fin n)).card := card_le_univ _
      _ = n := by simp

theorem atom_wit {G : Finset (Finset (Fin n))} {a : Finset (Fin n)} (ha : Atom G a) :
    wit G a = a := by
  apply filter_true_of_mem
  intro i _ d hd _ hda
  exact ha d hd hda

theorem atom_priv {G : Finset (Finset (Fin n))} (hG : Good G) {a : Finset (Fin n)}
    (haG : a ∈ G) (ha : Atom G a) : a ∈ Priv G := by
  refine mem_filter.2 ⟨haG, ?_⟩
  rw [atom_wit ha]
  exact ne_of_mem hG haG

theorem atom_of_union {G : Finset (Finset (Fin n))} (hG : Good G) {a b : Finset (Fin n)}
    (ha : a ∈ G) (hb : b ∈ G) (hab : Disjoint a b) (hc : a ∪ b ∈ G) : Atom G a := by
  intro d hd hda
  have e := hG.2.1 d hd b hb (a ∪ b) hc (Finset.disjoint_of_subset_left hda hab)
    (hda.trans subset_union_left) subset_union_right
  apply le_antisymm hda
  intro i hi
  have hi' : i ∈ d ∪ b := by rw [← e]; exact mem_union_left _ hi
  rcases mem_union.1 hi' with h | h
  · exact h
  · exact absurd h (Finset.disjoint_left.1 hab hi)

theorem bin_split {G : Finset (Finset (Fin n))} (hG : Good G) {c : Finset (Fin n)}
    (hc : c ∈ Bin G) : ∃ a b, a ∈ G ∧ b ∈ G ∧ Disjoint a b ∧ c = a ∪ b ∧
      Atom G a ∧ Atom G b := by
  obtain ⟨hcG, hw⟩ := mem_filter.1 hc
  have hsub : ∀ i ∈ c, ∃ d ∈ G, i ∈ d ∧ d ⊆ c ∧ d ≠ c := by
    intro i hi
    by_contra h
    push Not at h
    exact hw ⟨i, mem_filter.2 ⟨hi, fun d hd hid hdc => h d hd hid hdc⟩⟩
  obtain ⟨i, hi⟩ := ne_of_mem hG hcG
  set T := G.filter (fun d => d ⊆ c ∧ d ≠ c) with hT
  have hTn : T.Nonempty := by
    obtain ⟨d, hd, _, h1, h2⟩ := hsub i hi
    exact ⟨d, mem_filter.2 ⟨hd, h1, h2⟩⟩
  obtain ⟨a, haT, hmax⟩ := exists_max_image T Finset.card hTn
  obtain ⟨haG, hac, hne⟩ := mem_filter.1 haT
  obtain ⟨j, hjc, hja⟩ : ∃ j ∈ c, j ∉ a := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hac h)
  obtain ⟨b, hbG, hjb, hbc, hbne⟩ := hsub j hjc
  have hab : Disjoint a b := by
    rcases hG.1 a haG b hbG with h | h | h
    · exact h
    · exfalso
      have hlt : a ⊂ b := ⟨h, fun h' => hja (h' hjb)⟩
      have := hmax b (mem_filter.2 ⟨hbG, hbc, hbne⟩)
      have := card_lt_card hlt
      omega
    · exact absurd (h hjb) hja
  have hceq := hG.2.1 a haG b hbG c hcG hab hac hbc
  have hU : a ∪ b ∈ G := hceq ▸ hcG
  refine ⟨a, b, haG, hbG, hab, hceq, atom_of_union hG haG hbG hab hU, ?_⟩
  rw [union_comm] at hU
  exact atom_of_union hG hbG haG hab.symm hU

theorem bin_sub {G : Finset (Finset (Fin n))} (hG : Good G) {c c' : Finset (Fin n)}
    (hc' : c' ∈ Bin G) (hc : c ∈ G) (hsub : c ⊆ c') : c = c' ∨ Atom G c := by
  obtain ⟨a, b, ha, hb, hab, rfl, hA, hB⟩ := bin_split hG hc'
  have key : ∀ x, x ∈ G → Atom G x → c ⊆ x → Atom G c := by
    intro x _ hx hcx
    have e := hx c hc hcx
    subst e
    exact hx
  rcases hG.1 c hc a ha with h1 | h1 | h1
  · right
    apply key b hb hB
    intro i hi
    rcases mem_union.1 (hsub hi) with h | h
    · exact absurd h (Finset.disjoint_left.1 h1 hi)
    · exact h
  · exact Or.inr (key a ha hA h1)
  rcases hG.1 c hc b hb with h2 | h2 | h2
  · right
    apply key a ha hA
    intro i hi
    rcases mem_union.1 (hsub hi) with h | h
    · exact h
    · exact absurd h (Finset.disjoint_left.1 h2 hi)
  · exact Or.inr (key b hb hB h2)
  · exact Or.inl (le_antisymm hsub (union_subset h1 h2))

theorem priv_bin {G : Finset (Finset (Fin n))} {c : Finset (Fin n)} (h1 : c ∈ Priv G)
    (h2 : c ∈ Bin G) : False :=
  (mem_filter.1 h2).2 (mem_filter.1 h1).2

theorem bin_disj {G : Finset (Finset (Fin n))} (hG : Good G) {c c' : Finset (Fin n)}
    (hc : c ∈ Bin G) (hc' : c' ∈ Bin G) (hne : c ≠ c') : Disjoint c c' := by
  have hcG := (mem_filter.1 hc).1
  have hcG' := (mem_filter.1 hc').1
  rcases hG.1 c hcG c' hcG' with h | h | h
  · exact h
  · rcases bin_sub hG hc' hcG h with e | e
    · exact absurd e hne
    · exact (priv_bin (atom_priv hG hcG e) hc).elim
  · rcases bin_sub hG hc hcG' h with e | e
    · exact absurd e.symm hne
    · exact (priv_bin (atom_priv hG hcG' e) hc').elim

theorem bin_card {G : Finset (Finset (Fin n))} (hG : Good G) {c : Finset (Fin n)}
    (hc : c ∈ Bin G) : 2 ≤ c.card := by
  obtain ⟨a, b, ha, hb, hab, rfl, _, _⟩ := bin_split hG hc
  rw [card_union_of_disjoint hab]
  have := (ne_of_mem hG ha).card_pos
  have := (ne_of_mem hG hb).card_pos
  omega

theorem sum_bin {G : Finset (Finset (Fin n))} (hG : Good G) :
    ∑ c ∈ Bin G, c.card = ((Bin G).biUnion id).card := by
  rw [card_biUnion]
  · rfl
  intro c hc c' hc' hne
  exact bin_disj hG hc hc' hne

theorem bin_le {G : Finset (Finset (Fin n))} (hG : Good G) : 2 * (Bin G).card ≤ n := by
  have h1 : 2 * (Bin G).card ≤ ∑ c ∈ Bin G, c.card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum (fun c hc => bin_card hG hc)
  have h2 : ((Bin G).biUnion id).card ≤ n := by
    calc _ ≤ (univ : Finset (Fin n)).card := card_le_univ _
      _ = n := by simp
  rw [← sum_bin hG] at h2
  omega

theorem card_split (G : Finset (Finset (Fin n))) :
    G.card = (Priv G).card + (Bin G).card :=
  (card_filter_add_card_filter_not _).symm

theorem bound {G : Finset (Finset (Fin n))} (hG : Good G) : G.card ≤ n + n / 2 := by
  have := card_split G
  have := (priv_le hG).1
  have := (priv_le hG).2
  have := bin_le hG
  omega

theorem eq_case {G : Finset (Finset (Fin n))} (hG : Good G) (he : G.card = n + n / 2) :
    (∀ i : Fin n, {i} ∈ G) ∧ ∀ D ∈ G, D.card = 1 ∨ D.card = 2 := by
  have hs := card_split G
  have hp1 := (priv_le hG).1
  have hp2 := (priv_le hG).2
  have hb := bin_le hG
  have hP : (Priv G).card = n := by omega
  have hB : (Bin G).card = n / 2 := by omega
  -- every witness set is a singleton
  have hw1 : ∀ c ∈ Priv G, (wit G c).card = 1 := by
    intro c hc
    have h1 := (mem_filter.1 hc).2.card_pos
    by_contra h
    have hlt : ∑ d ∈ Priv G, 1 < ∑ d ∈ Priv G, (wit G d).card :=
      sum_lt_sum (fun d hd => (mem_filter.1 hd).2.card_pos) ⟨c, hc, by omega⟩
    rw [← card_eq_sum_ones] at hlt
    omega
  have hcov : ∀ i : Fin n, ∃ c ∈ Priv G, i ∈ wit G c := by
    have hu : (Priv G).biUnion (wit G) = univ := by
      apply eq_univ_of_card
      rw [← sum_wit hG]
      simp only [Fintype.card_fin]
      omega
    intro i
    have : i ∈ (Priv G).biUnion (wit G) := by rw [hu]; exact mem_univ i
    simpa using this
  have hatom1 : ∀ a ∈ G, Atom G a → a.card = 1 := by
    intro a ha hA
    have := hw1 a (atom_priv hG ha hA)
    rwa [atom_wit hA] at this
  have hbin2 : ∀ c ∈ Bin G, c.card = 2 := by
    intro c hc
    obtain ⟨a, b, ha, hb', hab, rfl, hA, hB'⟩ := bin_split hG hc
    rw [card_union_of_disjoint hab, hatom1 a ha hA, hatom1 b hb' hB']
  -- at most one coordinate is outside the pairs
  have hcovB : ∀ i j : Fin n, i ≠ j → (∃ p ∈ Bin G, i ∈ p) ∨ ∃ p ∈ Bin G, j ∈ p := by
    intro i j hij
    by_contra h
    push Not at h
    obtain ⟨hi, hj⟩ := h
    have hsum : ∑ c ∈ Bin G, c.card = 2 * (n / 2) := by
      rw [sum_congr rfl hbin2, sum_const, hB, smul_eq_mul, mul_comm]
    have hU : ((Bin G).biUnion id).card = 2 * (n / 2) := by rw [← sum_bin hG, hsum]
    have hsub : insert i ({j} : Finset (Fin n)) ⊆ univ \ (Bin G).biUnion id := by
      intro k hk
      simp only [mem_insert, mem_singleton] at hk
      simp only [mem_sdiff, mem_univ, true_and, mem_biUnion, id, not_exists, not_and]
      rcases hk with rfl | rfl
      · exact fun p hp hk => hi p hp hk
      · exact fun p hp hk => hj p hp hk
    have h1 := card_le_card hsub
    rw [card_pair hij, card_sdiff_of_subset (subset_univ _), hU, card_univ,
      Fintype.card_fin] at h1
    omega
  have hpriv1 : ∀ c ∈ Priv G, c.card = 1 := by
    intro c hc
    have hcG := (mem_filter.1 hc).1
    obtain ⟨i, hi⟩ := (mem_filter.1 hc).2
    have hic : i ∈ c := (mem_filter.1 hi).1
    by_contra hne
    obtain ⟨j, hjc, hji⟩ : ∃ j ∈ c, j ≠ i := by
      by_contra h
      push Not at h
      apply hne
      rw [card_eq_one]
      exact ⟨i, eq_singleton_iff_unique_mem.2 ⟨hic, h⟩⟩
    have hk : ∃ k ∈ c, ∃ p ∈ Bin G, k ∈ p := by
      rcases hcovB i j hji.symm with ⟨p, hp, h⟩ | ⟨p, hp, h⟩
      · exact ⟨i, hic, p, hp, h⟩
      · exact ⟨j, hjc, p, hp, h⟩
    obtain ⟨k, hkc, p, hp, hkp⟩ := hk
    have hpG := (mem_filter.1 hp).1
    rcases hG.1 c hcG p hpG with h | h | h
    · exact Finset.disjoint_left.1 h hkc hkp
    · rcases bin_sub hG hp hcG h with e | e
      · exact priv_bin hc (e ▸ hp)
      · exact hne (hatom1 c hcG e)
    · obtain ⟨a, b, ha, hb', hab, hpe, _, _⟩ := bin_split hG hp
      have e := hG.2.1 a ha b hb' c hcG hab (hpe ▸ h |> fun h' => subset_union_left.trans h')
        (hpe ▸ h |> fun h' => subset_union_right.trans h')
      rw [← hpe] at e
      exact priv_bin hc (e ▸ hp)
  constructor
  · intro i
    obtain ⟨c, hc, hi⟩ := hcov i
    have hic : i ∈ c := (mem_filter.1 hi).1
    obtain ⟨x, hx⟩ := card_eq_one.1 (hpriv1 c hc)
    rw [hx] at hic
    rw [mem_singleton] at hic
    rw [hic, ← hx]
    exact (mem_filter.1 hc).1
  · intro D hD
    by_cases h : (wit G D).Nonempty
    · exact Or.inl (hpriv1 D (mem_filter.2 ⟨hD, h⟩))
    · exact Or.inr (hbin2 D (mem_filter.2 ⟨hD, h⟩))

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

theorem count (P : Finset (Finset (Fin n))) (hP : ∀ e ∈ P, e.card = 2) :
    (univ.filter (fun D : Finset (Fin n) => D.card = 1 ∨ D ∈ P)).card = n + P.card := by
  have e : univ.filter (fun D : Finset (Fin n) => D.card = 1 ∨ D ∈ P) =
      powersetCard 1 univ ∪ P := by
    ext D
    simp [mem_powersetCard_univ]
  rw [e, card_union_of_disjoint, card_powersetCard, card_univ, Fintype.card_fin,
    Nat.choose_one_right]
  rw [Finset.disjoint_left]
  intro D h1 h2
  rw [mem_powersetCard_univ] at h1
  have := hP D h2
  omega

theorem card_S (r : Fin n → Bool) (P : Finset (Finset (Fin n))) (hP : ∀ e ∈ P, e.card = 2)
    (S : Finset (Fin n → Bool)) (h : ∀ z, z ∈ S ↔ ((dl r z).card = 1 ∨ dl r z ∈ P)) :
    S.card = n + P.card := by
  rw [← count P hP, ← card_image_of_injective S (dl_inj r)]
  congr 1
  ext D
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h z).1 hz
  · intro hD
    refine ⟨fl r D, (h _).2 ?_, dl_fl r D⟩
    rw [dl_fl]
    exact hD

theorem bE : ∀ a b c : Bool, a = b ↔ (a ≠ c ↔ b ≠ c) := by decide

theorem suff (r : Fin n → Bool) (P : Finset (Finset (Fin n))) (hP2 : ∀ e ∈ P, e.card = 2)
    (hPd : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f)
    (S : Finset (Fin n → Bool)) (hS : ∀ z, z ∈ S ↔ ((dl r z).card = 1 ∨ dl r z ∈ P)) :
    Free r S := by
  intro D hD
  apply define (fun x => x = r ∨ x ∈ D)
  intro x hx
  have hxr : x ≠ r := fun e => hx (Or.inl e)
  have hxD : x ∉ D := fun e => hx (Or.inr e)
  have hcut : ∀ p q : Fin n, (∀ t, t ∈ D → (p ∈ dl r t ↔ p ∈ dl r x) →
      (q ∈ dl r t ↔ q ∈ dl r x) → False) → (p ∈ dl r x ∨ q ∈ dl r x) →
      ∀ t, (t = r ∨ t ∈ D) → t p ≠ x p ∨ t q ≠ x q := by
    intro p q h hpq t ht
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
  have hX := dl_ne hxr
  set X := dl r x with hXdef
  have hDS : ∀ t ∈ D, (dl r t).card = 1 ∨ dl r t ∈ P := fun t ht => (hS t).1 (hD ht)
  have hdx : ∀ t, dl r t = X → t = x := fun t e => dl_inj r e
  have hpair : ∀ e ∈ P, ∀ i j : Fin n, i ≠ j → i ∈ e → j ∈ e → e = insert i {j} := by
    intro e he i j hij hi hj
    symm
    apply eq_of_subset_of_card_le
    · intro k hk
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    · rw [hP2 e he, card_pair hij]
  have hmeet : ∀ e ∈ P, ∀ f ∈ P, ∀ i, i ∈ e → i ∈ f → e = f := by
    intro e he f hf i hie hif
    by_contra hne
    exact Finset.disjoint_left.1 (hPd e he f hf hne) hie hif
  by_cases hA : ∃ i ∈ X, ∃ j ∈ X, i ≠ j ∧ insert i {j} ∉ P
  · obtain ⟨i, hi, j, hj, hij, hnP⟩ := hA
    refine ⟨i, j, hcut i j ?_ (Or.inl hi)⟩
    intro t ht h1 h2
    have hit := h1.2 hi
    have hjt := h2.2 hj
    rcases hDS t ht with h | h
    · obtain ⟨k, hk⟩ := card_eq_one.1 h
      rw [hk, mem_singleton] at hit hjt
      exact hij (hit.trans hjt.symm)
    · exact hnP (hpair _ h i j hij hit hjt ▸ h)
  push Not at hA
  obtain ⟨i, hi⟩ := hX
  by_cases h1 : ∃ j ∈ X, j ≠ i
  · obtain ⟨j, hj, hji⟩ := h1
    have he := hA i hi j hj hji.symm
    have hXe : X = insert i {j} := by
      apply le_antisymm
      · intro k hk
        by_contra hk'
        simp only [mem_insert, mem_singleton, not_or] at hk'
        have hf := hA i hi k hk (Ne.symm hk'.1)
        have := hmeet _ he _ hf i (mem_insert_self _ _) (mem_insert_self _ _)
        have hjk : j ∈ insert i ({k} : Finset (Fin n)) := this ▸ (by simp)
        simp only [mem_insert, mem_singleton] at hjk
        rcases hjk with h | h
        · exact hji h
        · exact hk'.2 h.symm
      · intro k hk
        simp only [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hi
        · exact hj
    refine ⟨i, j, hcut i j ?_ (Or.inl hi)⟩
    intro t ht h2 h3
    have hit := h2.2 hi
    have hjt := h3.2 hj
    rcases hDS t ht with h | h
    · obtain ⟨k, hk⟩ := card_eq_one.1 h
      rw [hk, mem_singleton] at hit hjt
      exact hji (hjt.trans hit.symm)
    · have e1 := hpair _ h i j hji.symm hit hjt
      rw [← hXe] at e1
      exact hxD (hdx t e1 ▸ ht)
  · push Not at h1
    have hXi : X = {i} := eq_singleton_iff_unique_mem.2 ⟨hi, h1⟩
    have hsing : ∀ t ∈ D, i ∈ dl r t → (dl r t).card = 1 → False := by
      intro t ht hit hc
      obtain ⟨k, hk⟩ := card_eq_one.1 hc
      rw [hk, mem_singleton] at hit
      rw [← hit] at hk
      rw [← hXi] at hk
      exact hxD (hdx t hk ▸ ht)
    by_cases h2 : ∃ p ∈ P, i ∈ p
    · obtain ⟨p, hp, hip⟩ := h2
      obtain ⟨j, hjp, hji⟩ : ∃ j ∈ p, j ≠ i := by
        by_contra h
        push Not at h
        have : p.card ≤ 1 := card_le_one.2 (fun a ha b hb => (h a ha).trans (h b hb).symm)
        rw [hP2 p hp] at this
        omega
      refine ⟨i, j, hcut i j ?_ (Or.inl hi)⟩
      intro t ht h3 h4
      have hit := h3.2 hi
      have hjt : j ∉ dl r t := fun h => by
        have := h4.1 h
        rw [hXi, mem_singleton] at this
        exact hji this
      rcases hDS t ht with h | h
      · exact hsing t ht hit h
      · exact hjt (hmeet _ h _ hp i hit hip ▸ hjp)
    · push Not at h2
      refine ⟨i, i, hcut i i ?_ (Or.inl hi)⟩
      intro t ht h3 _
      have hit := h3.2 hi
      rcases hDS t ht with h | h
      · exact hsing t ht hit h
      · exact h2 _ h hit

end PEqualNP.Outside.L_lib_1085

open Finset PEqualNP.Outside.L_lib_1085 in
theorem PEqualNP.Outside.L_lib_1085 :
let W := fun n : ℕ => Fin n → Bool
let F := fun n : ℕ => Finset ((Fin n × Bool) × (Fin n × Bool))
let sat := fun (n : ℕ) (A : F n) (x : W n) =>
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
let delta := fun (n : ℕ) (r z : W n) =>
  Finset.univ.filter (fun i : Fin n => z i ≠ r i)
let free := fun (n : ℕ) (r : W n) (S : Finset (W n)) =>
  ∀ D : Finset (W n), D ⊆ S → ∃ A : F n, ∀ x : W n,
    (sat n A x ↔ (x = r ∨ x ∈ D))
∀ (n : ℕ) (r : W n),
  (∃ S : Finset (W n), r ∉ S ∧ free n r S ∧ S.card = n + n / 2) ∧
  ∀ S : Finset (W n), r ∉ S → free n r S →
    S.card ≤ n + n / 2 ∧
    (S.card = n + n / 2 ↔
      ∃ P : Finset (Finset (Fin n)), P.card = n / 2 ∧
        (∀ e ∈ P, e.card = 2) ∧
        (∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f) ∧
        ∀ z : W n, (z ∈ S ↔ ((delta n r z).card = 1 ∨ delta n r z ∈ P))) := by
  intro W F sat delta free n r
  show (∃ S : Finset (Fin n → Bool), r ∉ S ∧ Free r S ∧ S.card = n + n / 2) ∧
    ∀ S : Finset (Fin n → Bool), r ∉ S → Free r S →
      S.card ≤ n + n / 2 ∧
      (S.card = n + n / 2 ↔
        ∃ P : Finset (Finset (Fin n)), P.card = n / 2 ∧
          (∀ e ∈ P, e.card = 2) ∧
          (∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f) ∧
          ∀ z : Fin n → Bool, (z ∈ S ↔ ((dl r z).card = 1 ∨ dl r z ∈ P)))
  constructor
  · let g : Fin (n / 2) → Finset (Fin n) := fun k =>
      insert ⟨2 * k.val, by omega⟩ {⟨2 * k.val + 1, by omega⟩}
    have hg : ∀ k i, i ∈ g k ↔ (i.val = 2 * k.val ∨ i.val = 2 * k.val + 1) := by
      intro k i
      simp only [g, mem_insert, mem_singleton, Fin.ext_iff]
    let P0 := (univ : Finset (Fin (n / 2))).image g
    have hinj : Function.Injective g := by
      intro k k' h
      have := (hg k' ⟨2 * k.val, by omega⟩).1 (h ▸ (hg k _).2 (Or.inl rfl))
      apply Fin.ext
      simp only at this
      omega
    have hP2 : ∀ e ∈ P0, e.card = 2 := by
      intro e he
      obtain ⟨k, _, rfl⟩ := mem_image.1 he
      apply card_pair
      simp [Fin.ext_iff]
    have hPd : ∀ e ∈ P0, ∀ f ∈ P0, e ≠ f → Disjoint e f := by
      intro e he f hf hne
      obtain ⟨k, _, rfl⟩ := mem_image.1 he
      obtain ⟨k', _, rfl⟩ := mem_image.1 hf
      have hkk : k.val ≠ k'.val := fun h => hne (congrArg g (Fin.ext h))
      rw [Finset.disjoint_left]
      intro i h1 h2
      rw [hg] at h1 h2
      omega
    have hPc : P0.card = n / 2 := by
      rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    let S0 := (univ : Finset (Fin n → Bool)).filter
      (fun z => (dl r z).card = 1 ∨ dl r z ∈ P0)
    have hS0 : ∀ z, z ∈ S0 ↔ ((dl r z).card = 1 ∨ dl r z ∈ P0) := by
      intro z
      simp [S0]
    refine ⟨S0, ?_, suff r P0 hP2 hPd S0 hS0, ?_⟩
    · rw [hS0, dl_self]
      rintro (h | h)
      · simp at h
      · have := hP2 _ h
        simp at this
    · rw [card_S r P0 hP2 S0 hS0, hPc]
  · intro S hr hf
    have hG := good_of hr hf
    have hcard : S.card = (S.image (dl r)).card := (card_image_of_injective S (dl_inj r)).symm
    have hmem : ∀ z, z ∈ S ↔ dl r z ∈ S.image (dl r) := fun z =>
      ((dl_inj r).mem_finset_image).symm
    refine ⟨hcard ▸ bound hG, ⟨fun he => ?_, ?_⟩⟩
    · obtain ⟨hsing, h12⟩ := eq_case hG (hcard ▸ he)
      let P := (S.image (dl r)).filter (fun D => D.card = 2)
      have hP2 : ∀ e ∈ P, e.card = 2 := fun e he => (mem_filter.1 he).2
      have hiff : ∀ D, D ∈ S.image (dl r) ↔ (D.card = 1 ∨ D ∈ P) := by
        intro D
        constructor
        · intro hD
          rcases h12 D hD with h | h
          · exact Or.inl h
          · exact Or.inr (mem_filter.2 ⟨hD, h⟩)
        · rintro (h | h)
          · obtain ⟨i, rfl⟩ := card_eq_one.1 h
            exact hsing i
          · exact (mem_filter.1 h).1
      have hGe : S.image (dl r) = univ.filter (fun D : Finset (Fin n) => D.card = 1 ∨ D ∈ P) := by
        ext D
        rw [hiff]
        simp
      have hPc := count P hP2
      rw [← hGe, ← hcard, he] at hPc
      refine ⟨P, by omega, hP2, ?_, fun z => (hmem z).trans (hiff _)⟩
      intro e he f hf hne
      rcases hG.1 e (mem_filter.1 he).1 f (mem_filter.1 hf).1 with h | h | h
      · exact h
      · exact absurd (eq_of_subset_of_card_le h (by rw [hP2 e he, hP2 f hf])) hne
      · exact absurd (eq_of_subset_of_card_le h (by rw [hP2 e he, hP2 f hf])).symm hne
    · rintro ⟨P, hPc, hP2, _, hS⟩
      rw [card_S r P hP2 S hS, hPc]
