import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1055

open Finset

abbrev Cl (n : ℕ) := (Fin n × Bool) × (Fin n × Bool)

def Sat {n : ℕ} (A : Finset (Cl n)) (x : Fin n → Bool) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2

theorem bne3 {a b c : Bool} (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

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

def IntP {n : ℕ} (S : (Fin n → Bool) → Prop) : Prop :=
  ∀ s t, S s → S t → (∃ k, s k = t k) →
    ∀ w : Fin n → Bool, (∀ i, s i = t i → w i = s i) → S w

theorem intP_of {n : ℕ} (A : Finset (Cl n))
    (hadd : ∀ z : Fin n → Bool, ∃ B : Finset (Cl n), ∀ x, (Sat B x ↔ (Sat A x ∨ x = z))) :
    IntP (Sat A) := by
  intro s t hs ht ⟨k, hk⟩ w hw
  obtain ⟨B, hB⟩ := hadd (Function.update w k (!w k))
  have hm := sat_maj B _ s t ((hB _).2 (Or.inr rfl)) ((hB s).2 (Or.inl hs))
    ((hB t).2 (Or.inl ht))
  have he : (fun i => if s i = t i then s i else Function.update w k (!w k) i) = w := by
    funext i
    by_cases h : s i = t i
    · rw [if_pos h, hw i h]
    · rw [if_neg h, Function.update_of_ne]
      rintro rfl
      exact h hk
  rw [he] at hm
  rcases (hB w).1 hm with h | h
  · exact h
  · exfalso
    have := congrFun h k
    simp at this

theorem flipD {n : ℕ} (S : (Fin n → Bool) → Prop) (hP : IntP S)
    (hna : ∀ a t, S a → S t → ∃ k, a k = t k) (s0 : Fin n → Bool) (h0 : S s0) :
    ∀ D : Finset (Fin n), (∀ j ∈ D, ∃ t, S t ∧ t j ≠ s0 j) →
      S (fun i => if i ∈ D then !s0 i else s0 i) := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simpa using h0
  | insert j D hj ih =>
    intro hD
    have hy := ih (fun j' hj' => hD j' (mem_insert_of_mem hj'))
    obtain ⟨t, ht, htj⟩ := hD j (mem_insert_self j D)
    refine hP _ t hy ht (hna _ t hy ht) _ ?_
    intro i hi
    by_cases hij : i = j
    · subst hij
      exfalso
      apply htj
      rw [← hi]
      simp [hj]
    · simp [mem_insert, hij]

theorem subcube_of {n : ℕ} (S : (Fin n → Bool) → Prop) (hP : IntP S)
    (hna : ∀ a t, S a → S t → ∃ k, a k = t k) (s0 : Fin n → Bool) (h0 : S s0) :
    ∃ (I : Finset (Fin n)) (v : Fin n → Bool), ∀ x, (S x ↔ ∀ i ∈ I, x i = v i) := by
  classical
  refine ⟨univ.filter (fun i => ∀ t, S t → t i = s0 i), s0, fun x => ⟨?_, ?_⟩⟩
  · intro hx i hi
    exact (mem_filter.1 hi).2 x hx
  · intro hx
    have hD := flipD S hP hna s0 h0 (univ.filter (fun i => x i ≠ s0 i)) ?_
    · convert hD using 1
      funext i
      by_cases h : x i = s0 i
      · simp [h]
      · simp only [mem_filter, mem_univ, true_and, if_pos h]
        revert h
        cases x i <;> cases s0 i <;> simp
    · intro j hj
      have hj' : x j ≠ s0 j := (mem_filter.1 hj).2
      by_contra hc
      push Not at hc
      exact hj' (hx j (mem_filter.2 ⟨mem_univ _, hc⟩))

theorem all_of {n : ℕ} (hn : 3 ≤ n) (S : (Fin n → Bool) → Prop) (hP : IntP S)
    (a t b : Fin n → Bool) (ha : S a) (ht : S t) (hat : ∀ k, a k ≠ t k) (hb : S b)
    (hba : ∃ k, b k = a k) (hbt : ∃ k, b k = t k) : ∀ x, S x := by
  have step1 : ∀ x, (∃ k, x k = b k) → S x := by
    intro x ⟨k, hk⟩
    have hu : S (fun i => if b i = a i then a i else x i) := by
      obtain ⟨m, hm⟩ := hba
      exact hP a b ha hb ⟨m, hm.symm⟩ _ (fun i hi => by simp [hi])
    have hw : S (fun i => if b i = t i then t i else x i) := by
      obtain ⟨m, hm⟩ := hbt
      exact hP t b ht hb ⟨m, hm.symm⟩ _ (fun i hi => by simp [hi])
    refine hP _ _ hu hw ⟨k, ?_⟩ x ?_
    · have := hat k
      revert this hk
      cases a k <;> cases t k <;> cases b k <;> cases x k <;> simp
    · intro i hi
      have := hat i
      revert this hi
      cases a i <;> cases t i <;> cases b i <;> cases x i <;> simp
  obtain ⟨i0, i1, i2, h01, h02, h12⟩ : ∃ i0 i1 i2 : Fin n, i0 ≠ i1 ∧ i0 ≠ i2 ∧ i1 ≠ i2 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff]⟩
  intro x
  by_cases hx : ∃ k, x k = b k
  · exact step1 x hx
  push Not at hx
  have hp := step1 (Function.update x i0 (!x i0)) ⟨i0, by
    rw [Function.update_self]
    have := hx i0
    revert this
    cases x i0 <;> cases b i0 <;> simp⟩
  have hq := step1 (Function.update x i1 (!x i1)) ⟨i1, by
    rw [Function.update_self]
    have := hx i1
    revert this
    cases x i1 <;> cases b i1 <;> simp⟩
  refine hP _ _ hp hq ⟨i2, ?_⟩ x ?_
  · rw [Function.update_of_ne h02.symm, Function.update_of_ne h12.symm]
  · intro i hi
    by_cases hi0 : i = i0
    · rw [hi0] at hi
      rw [Function.update_self, Function.update_of_ne h01] at hi
      simp at hi
    · by_cases hi1 : i = i1
      · rw [hi1] at hi
        rw [Function.update_self, Function.update_of_ne h01.symm] at hi
        simp at hi
      · rw [Function.update_of_ne hi0]

end PEqualNP.Outside.L_lib_1055

open PEqualNP.Outside.L_lib_1055 in
theorem PEqualNP.Outside.L_lib_1055 :
let W := fun n : ℕ => Fin n → Bool
let F := fun n : ℕ => Finset ((Fin n × Bool) × (Fin n × Bool))
let sat := fun (n : ℕ) (A : F n) (x : W n) =>
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
let addable := fun (n : ℕ) (A : F n) (z : W n) =>
  ∃ B : F n, ∀ x : W n, (sat n B x ↔ (sat n A x ∨ x = z))
∀ n : ℕ, 3 ≤ n → ∀ A : F n,
  ((∀ z : W n, addable n A z) ↔
   ((∀ x : W n, ¬ sat n A x) ∨
    (∃ (I : Finset (Fin n)) (v : W n), ∀ x : W n,
       (sat n A x ↔ ∀ i ∈ I, x i = v i)) ∨
    (∃ a : W n, ∀ x : W n,
       (sat n A x ↔ (x = a ∨ x = (fun i => !(a i))))))) := by
  intro W F sat addable n hn A
  show (∀ z : Fin n → Bool, ∃ B : Finset (Cl n), ∀ x, (Sat B x ↔ (Sat A x ∨ x = z))) ↔
    ((∀ x, ¬ Sat A x) ∨ (∃ (I : Finset (Fin n)) (v : Fin n → Bool), ∀ x,
      (Sat A x ↔ ∀ i ∈ I, x i = v i)) ∨
      (∃ a : Fin n → Bool, ∀ x, (Sat A x ↔ (x = a ∨ x = (fun i => !(a i))))))
  constructor
  · intro hadd
    have hP := intP_of A hadd
    by_cases h0 : ∀ x, ¬ Sat A x
    · exact Or.inl h0
    push Not at h0
    obtain ⟨s0, hs0⟩ := h0
    by_cases hanti : ∃ a t, Sat A a ∧ Sat A t ∧ ∀ k, a k ≠ t k
    · obtain ⟨a, t, ha, ht, hat⟩ := hanti
      have hta : t = fun i => !(a i) := by
        funext i
        have := hat i
        revert this
        cases a i <;> cases t i <;> simp
      by_cases hb : ∃ b, Sat A b ∧ (∃ k, b k = a k) ∧ (∃ k, b k = t k)
      · obtain ⟨b, hb, hba, hbt⟩ := hb
        refine Or.inr (Or.inl ⟨∅, a, fun x => ⟨fun _ i hi => by simp at hi, fun _ => ?_⟩⟩)
        exact all_of hn _ hP a t b ha ht hat hb hba hbt x
      · refine Or.inr (Or.inr ⟨a, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩)
        · push Not at hb
          by_cases hxa : ∃ k, x k = a k
          · left
            have h1 := hb x hx hxa
            funext k
            have h2 := h1 k
            have h3 := congrFun hta k
            rw [h3] at h2
            revert h2
            cases x k <;> cases a k <;> simp
          · right
            push Not at hxa
            funext k
            have h2 := hxa k
            revert h2
            cases x k <;> cases a k <;> simp
        · rcases hx with rfl | rfl
          · exact ha
          · rw [← hta]
            exact ht
    · push Not at hanti
      exact Or.inr (Or.inl (subcube_of _ hP hanti s0 hs0))
  · intro h z
    refine define (fun x => Sat A x ∨ x = z) ?_
    intro x hx
    have hxz : ¬ x = z := fun e => hx (Or.inr e)
    have hxA : ¬ Sat A x := fun e => hx (Or.inl e)
    obtain ⟨k, hk⟩ : ∃ k, x k ≠ z k := by
      by_contra hc
      push Not at hc
      exact hxz (funext hc)
    rcases h with h | ⟨I, v, h⟩ | ⟨a, h⟩
    · refine ⟨k, k, fun t ht => ?_⟩
      rcases ht with ht | rfl
      · exact absurd ht (h t)
      · exact Or.inl (Ne.symm hk)
    · by_cases h1 : ∃ i ∈ I, z i = v i ∧ x i ≠ v i
      · obtain ⟨i, hi, hzi, hxi⟩ := h1
        refine ⟨i, i, fun t ht => Or.inl ?_⟩
        rcases ht with ht | rfl
        · rw [(h t).1 ht i hi]
          exact Ne.symm hxi
        · rw [hzi]
          exact Ne.symm hxi
      push Not at h1
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ I, x i ≠ v i := by
        by_contra hc
        push Not at hc
        exact hxA ((h x).2 hc)
      have hzi : z i ≠ v i := fun e => hxi (h1 i hi e)
      have hxz' : x i = z i := bne3 hxi hzi
      by_cases h2 : ∃ j ∈ I, z j ≠ v j ∧ x j = v j
      · obtain ⟨j, hj, hzj, hxj⟩ := h2
        refine ⟨i, j, fun t ht => ?_⟩
        rcases ht with ht | rfl
        · left
          rw [(h t).1 ht i hi]
          exact Ne.symm hxi
        · right
          rw [hxj]
          exact hzj
      push Not at h2
      have hkI : k ∉ I := by
        intro hkI
        by_cases hz : z k = v k
        · exact hk (by rw [h1 k hkI hz, hz])
        · exact hk (bne3 (h2 k hkI hz) hz)
      refine ⟨i, k, fun t ht => ?_⟩
      rcases ht with ht | rfl
      · left
        rw [(h t).1 ht i hi]
        exact Ne.symm hxi
      · right
        exact Ne.symm hk
    · have hxa : ¬ x = a := fun e => hxA ((h x).2 (Or.inl e))
      have hxn : ¬ x = (fun i => !(a i)) := fun e => hxA ((h x).2 (Or.inr e))
      obtain ⟨p, hp⟩ : ∃ p, x p ≠ a p := by
        by_contra hc
        push Not at hc
        exact hxa (funext hc)
      obtain ⟨q, hq⟩ : ∃ q, x q = a q := by
        by_contra hc
        push Not at hc
        apply hxn
        funext i
        have := hc i
        revert this
        cases x i <;> cases a i <;> simp
      by_cases hz1 : ∃ p', x p' ≠ a p' ∧ z p' = a p'
      · obtain ⟨p', hp', hzp⟩ := hz1
        refine ⟨p', q, fun t ht => ?_⟩
        rcases ht with ht | rfl
        · rcases (h t).1 ht with rfl | rfl
          · exact Or.inl (Ne.symm hp')
          · right
            rw [hq]
            simp
        · left
          rw [hzp]
          exact Ne.symm hp'
      by_cases hz2 : ∃ q', x q' = a q' ∧ z q' ≠ a q'
      · obtain ⟨q', hq', hzq⟩ := hz2
        refine ⟨p, q', fun t ht => ?_⟩
        rcases ht with ht | rfl
        · rcases (h t).1 ht with rfl | rfl
          · exact Or.inl (Ne.symm hp)
          · right
            rw [hq']
            simp
        · right
          rw [hq']
          exact hzq
      push Not at hz1 hz2
      exfalso
      apply hxz
      funext i
      by_cases hi : x i = a i
      · rw [hi, hz2 i hi]
      · exact bne3 hi (hz1 i hi)
