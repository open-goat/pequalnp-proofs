import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1404

def qb_x {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P]
    (T : Finset α) (i : ℕ) : ℕ :=
  (T.powerset.filter (fun w => w.card = i ∧ ¬ P w)).card

theorem qb_x_le {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P]
    (T : Finset α) (i : ℕ) : qb_x P T i ≤ T.card.choose i := by
  unfold qb_x
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_filter, Finset.mem_powerset] at hw
  rw [Finset.mem_powersetCard]
  exact ⟨hw.1, hw.2.1⟩

theorem qb_x_top {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P]
    (T : Finset α) : qb_x P T T.card = if P T then 0 else 1 := by
  unfold qb_x
  have h : T.powerset.filter (fun w => w.card = T.card ∧ ¬ P w)
      = (T.powersetCard T.card).filter (fun w => ¬ P w) := by
    rw [Finset.powersetCard_eq_filter, Finset.filter_filter]
  rw [h, Finset.powersetCard_self, Finset.filter_singleton]
  split_ifs <;> simp_all

theorem qb_dc {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P]
    (T : Finset α) (i : ℕ) :
    ∑ t ∈ T, qb_x P (T.erase t) i = (T.card - i) * qb_x P T i := by
  unfold qb_x
  have h1 : ∀ t ∈ T, ((T.erase t).powerset.filter (fun w => w.card = i ∧ ¬ P w)).card
      = ∑ w ∈ T.powerset.filter (fun w => w.card = i ∧ ¬ P w), if t ∉ w then 1 else 0 := by
    intro t _
    rw [← Finset.card_filter]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  rw [Finset.sum_congr rfl h1, Finset.sum_comm,
    Finset.card_eq_sum_ones (T.powerset.filter (fun w => w.card = i ∧ ¬ P w)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.mem_filter, Finset.mem_powerset] at hw
  rw [← Finset.card_filter, mul_one, ← Finset.sdiff_eq_filter,
    Finset.card_sdiff_of_subset hw.1, hw.2.1]

theorem qb_lower {α : Type*} [DecidableEq α] (P : Finset α → Prop) [DecidablePred P] :
    ∀ n : ℕ, ∀ T : Finset α, T.card = n →
    ∃ L : Finset (Finset α), (∀ x ∈ L, x ⊆ T ∧ x.card < n ∧ P x) ∧
      (∀ x ∈ L, ∀ y ∈ L, x ⊆ y ∨ y ⊆ x) ∧
      (n : ℚ) - L.card ≤ ∑ i ∈ Finset.range n, (qb_x P T i : ℚ) / (n.choose i) := by
  intro n
  induction n with
  | zero =>
    intro T _
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    intro T hT
    have key : ∀ t ∈ T, ∃ L : Finset (Finset α), (∀ x ∈ L, x ⊆ T ∧ x.card < n + 1 ∧ P x) ∧
        (∀ x ∈ L, ∀ y ∈ L, x ⊆ y ∨ y ⊆ x) ∧
        ((n + 1 : ℕ) : ℚ) - L.card ≤ ∑ i ∈ Finset.range n, (qb_x P (T.erase t) i : ℚ) / (n.choose i)
          + (if P (T.erase t) then 0 else 1) := by
      intro t ht
      have hTe : (T.erase t).card = n := by rw [Finset.card_erase_of_mem ht, hT]; rfl
      obtain ⟨L, hL1, hL2, hL3⟩ := ih (T.erase t) hTe
      by_cases hP : P (T.erase t)
      · have hnot : T.erase t ∉ L := fun h => by have := (hL1 _ h).2.1; omega
        refine ⟨insert (T.erase t) L, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact ⟨Finset.erase_subset _ _, by omega, hP⟩
          · obtain ⟨h1, h2, h3⟩ := hL1 x hx
            exact ⟨h1.trans (Finset.erase_subset _ _), by omega, h3⟩
        · intro x hx y hy
          rcases Finset.mem_insert.1 hx with hxa | hxL <;> rcases Finset.mem_insert.1 hy with hya | hyL
          · rw [hxa, hya]
            exact Or.inl (Finset.Subset.refl _)
          · rw [hxa]
            exact Or.inr (hL1 y hyL).1
          · rw [hya]
            exact Or.inl (hL1 x hxL).1
          · exact hL2 x hxL y hyL
        · rw [Finset.card_insert_of_notMem hnot]
          simp only [hP]
          push_cast
          linarith
      · refine ⟨L, fun x hx => ?_, hL2, ?_⟩
        · obtain ⟨h1, h2, h3⟩ := hL1 x hx
          exact ⟨h1.trans (Finset.erase_subset _ _), by omega, h3⟩
        · simp only [hP]
          push_cast
          linarith
    have hx_top : ∀ t ∈ T, (qb_x P (T.erase t) n : ℚ) / (n.choose n)
        = if P (T.erase t) then 0 else 1 := by
      intro t ht
      have hTe : (T.erase t).card = n := by rw [Finset.card_erase_of_mem ht, hT]; rfl
      rw [Nat.choose_self, Nat.cast_one, div_one, ← hTe, qb_x_top]
      split_ifs <;> simp
    have hdc : ∀ i, ∑ t ∈ T, (qb_x P (T.erase t) i : ℚ) = ((n + 1 - i : ℕ) : ℚ) * qb_x P T i := by
      intro i
      have h := qb_dc P T i
      rw [hT] at h
      exact_mod_cast h
    have hsum : ∑ t ∈ T, (∑ i ∈ Finset.range n, (qb_x P (T.erase t) i : ℚ) / (n.choose i)
          + (if P (T.erase t) then 0 else 1))
        = ((n + 1 : ℕ) : ℚ) * ∑ i ∈ Finset.range (n + 1), (qb_x P T i : ℚ) / ((n + 1).choose i) := by
      calc ∑ t ∈ T, (∑ i ∈ Finset.range n, (qb_x P (T.erase t) i : ℚ) / (n.choose i)
            + (if P (T.erase t) then 0 else 1))
          = ∑ t ∈ T, ∑ i ∈ Finset.range (n + 1), (qb_x P (T.erase t) i : ℚ) / (n.choose i) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_range_succ, hx_top t ht]
        _ = ∑ i ∈ Finset.range (n + 1), (∑ t ∈ T, (qb_x P (T.erase t) i : ℚ)) / (n.choose i) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_div]
        _ = ∑ i ∈ Finset.range (n + 1), ((n + 1 : ℕ) : ℚ) * ((qb_x P T i : ℚ) / ((n + 1).choose i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hdc i]
            have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            have h1 : (n.choose i : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
            have h2 : ((n + 1).choose i : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
            have h3 : (n.choose i : ℚ) * ((n + 1 : ℕ) : ℚ)
                = ((n + 1).choose i : ℚ) * ((n + 1 - i : ℕ) : ℚ) := by
              exact_mod_cast Nat.choose_mul_succ_eq n i
            rw [mul_div_assoc', div_eq_div_iff h1 h2]
            linear_combination (-(qb_x P T i : ℚ)) * h3
        _ = ((n + 1 : ℕ) : ℚ) * ∑ i ∈ Finset.range (n + 1), (qb_x P T i : ℚ) / ((n + 1).choose i) := by
            rw [Finset.mul_sum]
    have hTne : T.Nonempty := by rw [← Finset.card_pos, hT]; omega
    obtain ⟨t, ht, hle⟩ : ∃ t ∈ T, (∑ i ∈ Finset.range n, (qb_x P (T.erase t) i : ℚ) / (n.choose i)
          + (if P (T.erase t) then 0 else 1))
          ≤ ∑ i ∈ Finset.range (n + 1), (qb_x P T i : ℚ) / ((n + 1).choose i) := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have h := Finset.sum_lt_sum_of_nonempty hTne hcon
      rw [hsum, Finset.sum_const, hT, nsmul_eq_mul] at h
      linarith
    obtain ⟨L, hL1, hL2, hL3⟩ := key t ht
    exact ⟨L, hL1, hL2, hL3.trans hle⟩

theorem qb_minbelow {α : Type*} [DecidableEq α] (X : Finset (Finset α)) (z : Finset α)
    (hz : z ∈ X) : ∃ a ∈ X, a ⊆ z ∧ ∀ y ∈ X, y ⊆ a → y = a := by
  obtain ⟨a, ha, hmin⟩ := (X.filter (· ⊆ z)).exists_min_image Finset.card
    ⟨z, Finset.mem_filter.2 ⟨hz, Finset.Subset.refl _⟩⟩
  rw [Finset.mem_filter] at ha
  refine ⟨a, ha.1, ha.2, fun y hy hya => ?_⟩
  exact Finset.eq_of_subset_of_card_le hya (hmin y (Finset.mem_filter.2 ⟨hy, hya.trans ha.2⟩))

theorem qb_mirsky {α : Type*} [DecidableEq α] (q : ℕ) :
    ∀ n : ℕ, ∀ X : Finset (Finset α), X.card ≤ n →
    (∀ U ⊆ X, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q) →
    ∃ K ⊆ X, (∀ x ∈ K, ∀ y ∈ K, x ⊆ y ∨ y ⊆ x) ∧ X.card ≤ q * K.card := by
  intro n
  induction n with
  | zero =>
    intro X hX _
    have h0 : X = ∅ := Finset.card_eq_zero.1 (by omega)
    exact ⟨∅, Finset.empty_subset _, by simp, by simp [h0]⟩
  | succ n ih =>
    intro X hXn hw
    rcases X.eq_empty_or_nonempty with hX | ⟨z0, hz0⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp [hX]⟩
    have hAX : X.filter (fun x => ∀ y ∈ X, y ⊆ x → y = x) ⊆ X := Finset.filter_subset _ _
    have hAq : (X.filter (fun x => ∀ y ∈ X, y ⊆ x → y = x)).card ≤ q := by
      apply hw _ hAX
      intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      exact hy.2 x hx.1 hxy
    have hex : ∀ z ∈ X, ∃ a ∈ X.filter (fun x => ∀ y ∈ X, y ⊆ x → y = x), a ⊆ z := by
      intro z hz
      obtain ⟨a, ha, haz, hmin⟩ := qb_minbelow X z hz
      exact ⟨a, Finset.mem_filter.2 ⟨ha, hmin⟩, haz⟩
    obtain ⟨a0, ha0, -⟩ := hex z0 hz0
    have hlt : (X \ X.filter (fun x => ∀ y ∈ X, y ⊆ x → y = x)).card ≤ n := by
      have h1 := Finset.card_sdiff_add_card_eq_card hAX
      have h2 : 0 < (X.filter (fun x => ∀ y ∈ X, y ⊆ x → y = x)).card :=
        Finset.card_pos.2 ⟨a0, ha0⟩
      omega
    obtain ⟨K', hK'X, hK'c, hK'card⟩ := ih _ hlt
      (fun U hU hUa => hw U (hU.trans Finset.sdiff_subset) hUa)
    have hz : ∃ z ∈ X, ∀ k ∈ K', z ⊆ k := by
      rcases K'.eq_empty_or_nonempty with hK | hK
      · exact ⟨z0, hz0, by simp [hK]⟩
      obtain ⟨m, hm, hmin⟩ := K'.exists_min_image Finset.card hK
      refine ⟨m, (Finset.mem_sdiff.1 (hK'X hm)).1, fun k hk => ?_⟩
      rcases hK'c m hm k hk with h | h
      · exact h
      · exact Finset.subset_of_eq (Finset.eq_of_subset_of_card_le h (hmin k hk)).symm
    obtain ⟨z, hzX, hzK⟩ := hz
    obtain ⟨a, haA, haz⟩ := hex z hzX
    have haK' : a ∉ K' := fun h => (Finset.mem_sdiff.1 (hK'X h)).2 haA
    refine ⟨insert a K', Finset.insert_subset (hAX haA) (hK'X.trans Finset.sdiff_subset), ?_, ?_⟩
    · intro x hx y hy
      rcases Finset.mem_insert.1 hx with hxa | hxK <;> rcases Finset.mem_insert.1 hy with hya | hyK
      · rw [hxa, hya]
        exact Or.inl (Finset.Subset.refl _)
      · rw [hxa]
        exact Or.inl (haz.trans (hzK y hyK))
      · rw [hya]
        exact Or.inr (haz.trans (hzK x hxK))
      · exact hK'c x hxK y hyK
    · rw [Finset.card_insert_of_notMem haK']
      have h1 := Finset.card_sdiff_add_card_eq_card hAX
      rw [mul_add, mul_one]
      omega

theorem qb_sandwich {r : ℕ} (K : Finset (Finset (Fin r))) (l s : ℕ) (hls : l ≤ s) (hsr : s ≤ r)
    (hK : ∀ x ∈ K, ∀ y ∈ K, x ⊆ y ∨ y ⊆ x) (hKc : ∀ x ∈ K, l ≤ x.card ∧ x.card ≤ s) :
    ∃ T T' : Finset (Fin r), T ⊆ T' ∧ T.card = l ∧ T'.card = s ∧ ∀ k ∈ K, T ⊆ k ∧ k ⊆ T' := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · obtain ⟨T', -, hT'⟩ := Finset.exists_superset_card_eq (s := (∅ : Finset (Fin r))) (n := s)
      (by simp) (by simpa using hsr)
    obtain ⟨T, hTT', hT⟩ := Finset.exists_subset_card_eq (s := T') (n := l) (by omega)
    exact ⟨T, T', hTT', hT, hT', by simp [hK0]⟩
  · obtain ⟨m, hm, hmin⟩ := K.exists_min_image Finset.card hKne
    obtain ⟨M, hM, hmax⟩ := K.exists_max_image Finset.card hKne
    have hmk : ∀ k ∈ K, m ⊆ k := fun k hk => (hK m hm k hk).elim id
      (fun h => Finset.subset_of_eq (Finset.eq_of_subset_of_card_le h (hmin k hk)).symm)
    have hkM : ∀ k ∈ K, k ⊆ M := fun k hk => (hK k hk M hM).elim id
      (fun h => Finset.subset_of_eq (Finset.eq_of_subset_of_card_le h (hmax k hk)).symm)
    obtain ⟨T', hMT', hT'⟩ := Finset.exists_superset_card_eq (s := M) (n := s) (hKc M hM).2
      (by simpa using hsr)
    obtain ⟨T, hTm, hT⟩ := Finset.exists_subset_card_eq (s := m) (n := l) (hKc m hm).1
    exact ⟨T, T', hTm.trans ((hmk M hM).trans hMT'), hT, hT',
      fun k hk => ⟨hTm.trans (hmk k hk), (hkM k hk).trans hMT'⟩⟩

theorem qb_upper {r : ℕ} (S : Finset (Finset (Fin r))) (u : ℕ) (T' : Finset (Fin r))
    (hT' : T'.card = r - u) (hur : u ≤ r) :
    ∃ U : Finset (Finset (Fin r)), (∀ x ∈ U, T' ⊆ x ∧ r - u < x.card ∧ x ∈ S) ∧
      (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) ∧
      (u : ℚ) - U.card ≤ ∑ i ∈ Finset.range u, (qb_x (fun w => wᶜ ∈ S) T'ᶜ i : ℚ) / (u.choose i) := by
  have hc : T'ᶜ.card = u := by rw [Finset.card_compl, Fintype.card_fin, hT']; omega
  obtain ⟨L, hL1, hL2, hL3⟩ := qb_lower (fun w => wᶜ ∈ S) u T'ᶜ hc
  refine ⟨L.image compl, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, h2, h3⟩ := hL1 w hw
    refine ⟨Finset.subset_compl_comm.1 h1, ?_, h3⟩
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  · intro x hx y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    rcases hL2 w hw v hv with h | h
    · exact Or.inr (Finset.compl_subset_compl.2 h)
    · exact Or.inl (Finset.compl_subset_compl.2 h)
  · rw [Finset.card_image_of_injective _ compl_injective]
    exact hL3

theorem qb_bound_le {r : ℕ} (S : Finset (Finset (Fin r))) (j : ℕ) (F : Finset (Finset (Fin r)))
    (hF : ∀ w ∈ F, w.card = j ∧ w ∉ S) :
    F.card ≤ Nat.choose r j - (S.filter (fun w => w.card = j)).card := by
  have h1 : F ⊆ (Finset.univ.powersetCard j) \ (S.filter (fun w => w.card = j)) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hF w hw
    rw [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_filter]
    exact ⟨⟨Finset.subset_univ _, h1⟩, fun h => h2 h.1⟩
  have h2 : S.filter (fun w => w.card = j) ⊆ Finset.univ.powersetCard j := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hw.2⟩
  calc F.card ≤ ((Finset.univ.powersetCard j) \ (S.filter (fun w => w.card = j))).card :=
        Finset.card_le_card h1
    _ = Nat.choose r j - (S.filter (fun w => w.card = j)).card := by
        rw [Finset.card_sdiff_of_subset h2, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]

theorem qb_div_le_min (x c b : ℕ) (hxc : x ≤ c) (hxb : x ≤ b) :
    (x : ℚ) / c ≤ min 1 ((b : ℚ) / c) := by
  apply le_min
  · rcases Nat.eq_zero_or_pos c with h | h
    · simp [h]
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast hxc
  · have : (x : ℚ) ≤ b := by exact_mod_cast hxb
    gcongr

theorem qb_main (r p q l u : ℕ) (S : Finset (Finset (Fin r))) (hq : 0 < q) (hlu : l + u ≤ r)
    (hw : ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q)
    (hh : ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ p) :
    ((r + 1 - p : ℕ) : ℚ) ≤
      (Finset.range l).sum (fun i => min (1 : ℚ)
        (((Nat.choose r i - (S.filter (fun w => w.card = i)).card : ℕ) : ℚ) / Nat.choose l i)) +
      (Finset.range (r + 1 - l - u)).sum (fun i =>
        ((q - (S.filter (fun w => w.card = l + i)).card : ℕ) : ℚ) / q) +
      (Finset.range u).sum (fun i => min (1 : ℚ)
        (((Nat.choose r (r - i) - (S.filter (fun w => w.card = r - i)).card : ℕ) : ℚ)
          / Nat.choose u i)) := by
  set m := r + 1 - l - u with hm
  set Sc := (Finset.range m).biUnion (fun i => S.filter (fun w => w.card = l + i)) with hSc
  have hSc_mem : ∀ x ∈ Sc, x ∈ S ∧ l ≤ x.card ∧ x.card ≤ r - u := by
    intro x hx
    rw [hSc, Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_range] at hi
    refine ⟨hx.1, by omega, by omega⟩
  have hScS : Sc ⊆ S := fun x hx => (hSc_mem x hx).1
  have hSc_card : Sc.card = ∑ i ∈ Finset.range m, (S.filter (fun w => w.card = l + i)).card := by
    rw [hSc]
    apply Finset.card_biUnion
    intro i _ j _ hij
    simp only [Function.onFun]
    apply Finset.disjoint_filter.2
    intro x _ h1 h2
    apply hij
    omega
  obtain ⟨K, hKSc, hKc, hKcard⟩ := qb_mirsky q Sc.card Sc le_rfl
    (fun U hU hUa => hw U (hU.trans hScS) hUa)
  obtain ⟨T, T', hTT', hT, hT', hTK⟩ := qb_sandwich K l (r - u) (by omega) (by omega) hKc
    (fun x hx => ⟨(hSc_mem x (hKSc hx)).2.1, (hSc_mem x (hKSc hx)).2.2⟩)
  obtain ⟨L, hL1, hL2, hL3⟩ := qb_lower (fun w => w ∈ S) l T hT
  obtain ⟨U, hU1, hU2, hU3⟩ := qb_upper S u T' hT' (by omega)
  have hsub : L ∪ K ∪ U ⊆ S := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact (hL1 x hx).2.2
      · exact hScS (hKSc hx)
    · exact (hU1 x hx).2.2
  have hz : ∀ x ∈ L ∪ K ∪ U, (x ∈ L ∧ x ⊆ T) ∨ (x ∈ K ∧ T ⊆ x ∧ x ⊆ T') ∨ (x ∈ U ∧ T' ⊆ x) := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact Or.inl ⟨hx, (hL1 x hx).1⟩
      · exact Or.inr (Or.inl ⟨hx, (hTK x hx).1, (hTK x hx).2⟩)
    · exact Or.inr (Or.inr ⟨hx, (hU1 x hx).1⟩)
  have hchain : ∀ x ∈ L ∪ K ∪ U, ∀ y ∈ L ∪ K ∪ U, x ⊆ y ∨ y ⊆ x := by
    intro x hx y hy
    rcases hz x hx with ⟨hxL, hxT⟩ | ⟨hxK, hTx, hxT'⟩ | ⟨hxU, hT'x⟩ <;>
    rcases hz y hy with ⟨hyL, hyT⟩ | ⟨hyK, hTy, hyT'⟩ | ⟨hyU, hT'y⟩
    · exact hL2 x hxL y hyL
    · exact Or.inl (hxT.trans hTy)
    · exact Or.inl (hxT.trans (hTT'.trans hT'y))
    · exact Or.inr (hyT.trans hTx)
    · exact hKc x hxK y hyK
    · exact Or.inl (hxT'.trans hT'y)
    · exact Or.inr (hyT.trans (hTT'.trans hT'x))
    · exact Or.inr (hyT'.trans hT'x)
    · exact hU2 x hxU y hyU
  have hp := hh _ hsub hchain
  have hdisj1 : Disjoint L K := by
    rw [Finset.disjoint_left]
    intro x hxL hxK
    have h1 := (hL1 x hxL).2.1
    have h2 := (hSc_mem x (hKSc hxK)).2.1
    omega
  have hdisj2 : Disjoint (L ∪ K) U := by
    rw [Finset.disjoint_left]
    intro x hx hxU
    have h3 := (hU1 x hxU).2.1
    rcases Finset.mem_union.1 hx with hxL | hxK
    · have h1 := (hL1 x hxL).2.1
      omega
    · have h2 := (hSc_mem x (hKSc hxK)).2.2
      omega
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1] at hp
  have hlow : (l : ℚ) - L.card ≤ (Finset.range l).sum (fun i => min (1 : ℚ)
        (((Nat.choose r i - (S.filter (fun w => w.card = i)).card : ℕ) : ℚ) / Nat.choose l i)) := by
    refine hL3.trans (Finset.sum_le_sum (fun i _ => ?_))
    apply qb_div_le_min
    · have h := qb_x_le (fun w => w ∈ S) T i
      rwa [hT] at h
    · unfold qb_x
      apply qb_bound_le
      intro w hw
      rw [Finset.mem_filter] at hw
      exact hw.2
  have hup : (u : ℚ) - U.card ≤ (Finset.range u).sum (fun i => min (1 : ℚ)
        (((Nat.choose r (r - i) - (S.filter (fun w => w.card = r - i)).card : ℕ) : ℚ)
          / Nat.choose u i)) := by
    refine hU3.trans (Finset.sum_le_sum (fun i hi => ?_))
    rw [Finset.mem_range] at hi
    apply qb_div_le_min
    · have h := qb_x_le (fun w => wᶜ ∈ S) T'ᶜ i
      rwa [Finset.card_compl, Fintype.card_fin, hT', show r - (r - u) = u by omega] at h
    · unfold qb_x
      have hinj := Finset.card_image_of_injective
        (T'ᶜ.powerset.filter (fun w => w.card = i ∧ ¬ (wᶜ ∈ S)))
        (compl_injective (α := Finset (Fin r)))
      rw [← hinj]
      apply qb_bound_le
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      rw [Finset.mem_filter, Finset.mem_powerset] at hw
      refine ⟨?_, hw.2.2⟩
      rw [Finset.card_compl, Fintype.card_fin, hw.2.1]
  have hcen : (m : ℚ) - K.card ≤ (Finset.range m).sum (fun i =>
        ((q - (S.filter (fun w => w.card = l + i)).card : ℕ) : ℚ) / q) := by
    have hqpos : (0 : ℚ) < q := by exact_mod_cast hq
    have h1 : ∀ i ∈ Finset.range m, ((q - (S.filter (fun w => w.card = l + i)).card : ℕ) : ℚ) / q
        = 1 - ((S.filter (fun w => w.card = l + i)).card : ℚ) / q := by
      intro i _
      have hle : (S.filter (fun w => w.card = l + i)).card ≤ q := by
        apply hw _ (Finset.filter_subset _ _)
        intro x hx y hy hxy
        rw [Finset.mem_filter] at hx hy
        exact Finset.eq_of_subset_of_card_le hxy (by rw [hx.2, hy.2])
      rw [Nat.cast_sub hle]
      field_simp
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have h2 : (∑ i ∈ Finset.range m, ((S.filter (fun w => w.card = l + i)).card : ℚ))
        ≤ q * K.card := by
      have h3 : (Sc.card : ℚ) ≤ q * K.card := by exact_mod_cast hKcard
      rw [hSc_card] at h3
      exact_mod_cast h3
    have h4 : (∑ i ∈ Finset.range m, ((S.filter (fun w => w.card = l + i)).card : ℚ)) / q
        ≤ K.card := by
      rw [div_le_iff₀ hqpos]
      linarith
    linarith
  rcases le_total p (r + 1) with hpr | hpr
  · have hcast : ((r + 1 - p : ℕ) : ℚ) = (r : ℚ) + 1 - p := by
      rw [Nat.cast_sub hpr]
      push_cast
      ring
    rw [hcast]
    have hlm : (l : ℚ) + m + u = r + 1 := by
      have h5 : l + m + u = r + 1 := by omega
      exact_mod_cast h5
    have hp' : (L.card : ℚ) + K.card + U.card ≤ p := by exact_mod_cast hp
    linarith
  · rw [Nat.sub_eq_zero_of_le hpr, Nat.cast_zero]
    positivity

end PEqualNP.Outside.L_lib_1404

theorem PEqualNP.Outside.L_lib_1404 : let heightAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (p : Nat) =>
  ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ p
let widthAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (q : Nat) =>
  ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q
∀ (r p q l u : Nat) (S : Finset (Finset (Fin r))), 0 < q → l+u ≤ r →
  widthAtMost S q → heightAtMost S p →
  let a := fun j : Nat => (S.filter (fun w => w.card = j)).card
  let miss := fun (n i j : Nat) => min (1 : ℚ) (((Nat.choose r j - a j : Nat) : ℚ) / Nat.choose n i)
  ((r+1-p : Nat) : ℚ) ≤
    (Finset.range l).sum (fun i => miss l i i) +
    (Finset.range (r+1-l-u)).sum (fun i => ((q-a (l+i) : Nat) : ℚ) / q) +
    (Finset.range u).sum (fun i => miss u i (r-i)) := by
  intro heightAtMost widthAtMost r p q l u S hq hlu hw hh a miss
  exact PEqualNP.Outside.L_lib_1404.qb_main r p q l u S hq hlu hw hh
