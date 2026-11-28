import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1054_aux

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem projection_reconstruction : (∀ (n : ℕ) (R : Set (Fin n → Bool)), 0 < n →
  (∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R,
    (fun i => (a i && b i) || (b i && c i) || (c i && a i)) ∈ R) →
  ∀ x : Fin n → Bool, x ∈ R ↔
    ∀ i j : Fin n, ∃ y ∈ R, y i = x i ∧ y j = x j) := by
  intro n R hn hmaj x
  constructor
  · intro hx i j
    exact ⟨x, hx, rfl, rfl⟩
  · intro hpair
    have hind : ∀ m : ℕ, ∀ S : Finset (Fin n), S.card = m → ∃ y ∈ R, ∀ i ∈ S, y i = x i := by
      intro m
      induction m with
      | zero =>
        intro S hs
        obtain ⟨y, hyR, _, _⟩ := hpair ⟨0, hn⟩ ⟨0, hn⟩
        refine ⟨y, hyR, fun i hi => ?_⟩
        rw [Finset.card_eq_zero.mp hs] at hi
        simp at hi
      | succ m ih =>
        cases m with
        | zero =>
          intro S hs
          obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
          obtain ⟨y, hyR, hya, _⟩ := hpair a a
          refine ⟨y, hyR, fun i hi => ?_⟩
          rw [Finset.mem_singleton.mp hi]
          exact hya
        | succ m =>
          cases m with
          | zero =>
            intro S hs
            obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hs
            obtain ⟨y, hyR, hya, hyb⟩ := hpair a b
            refine ⟨y, hyR, fun i hi => ?_⟩
            rcases Finset.mem_insert.mp hi with rfl | hib
            · exact hya
            · rw [Finset.mem_singleton.mp hib]
              exact hyb
          | succ k =>
            intro S hs
            have hpos0 : 0 < S.card := by omega
            obtain ⟨i1, hi1⟩ := Finset.card_pos.mp hpos0
            have hc1 : (S.erase i1).card = k + 2 := by
              rw [Finset.card_erase_of_mem hi1]
              omega
            have hpos1 : 0 < (S.erase i1).card := by omega
            obtain ⟨i2, hi2_e1⟩ := Finset.card_pos.mp hpos1
            obtain ⟨hi2_ne1, hi2⟩ := Finset.mem_erase.mp hi2_e1
            have hc2_sub : ((S.erase i1).erase i2).card = k + 1 := by
              rw [Finset.card_erase_of_mem hi2_e1]
              omega
            have hpos2 : 0 < ((S.erase i1).erase i2).card := by omega
            obtain ⟨i3, hi3_e2⟩ := Finset.card_pos.mp hpos2
            obtain ⟨hi3_ne2, hi3_e1⟩ := Finset.mem_erase.mp hi3_e2
            obtain ⟨hi3_ne1, hi3⟩ := Finset.mem_erase.mp hi3_e1
            have hc2 : (S.erase i2).card = k + 2 := by
              rw [Finset.card_erase_of_mem hi2]
              omega
            have hc3 : (S.erase i3).card = k + 2 := by
              rw [Finset.card_erase_of_mem hi3]
              omega
            obtain ⟨y1, hy1R, hy1⟩ := ih (S.erase i1) hc1
            obtain ⟨y2, hy2R, hy2⟩ := ih (S.erase i2) hc2
            obtain ⟨y3, hy3R, hy3⟩ := ih (S.erase i3) hc3
            refine ⟨fun j => (y1 j && y2 j) || (y2 j && y3 j) || (y3 j && y1 j),
              hmaj y1 hy1R y2 hy2R y3 hy3R, fun j hj => ?_⟩
            dsimp only
            by_cases hj1 : j = i1
            · have hj_ne2 : j ≠ i2 := by
                rw [hj1]
                exact hi2_ne1.symm
              have hj_ne3 : j ≠ i3 := by
                rw [hj1]
                exact hi3_ne1.symm
              have heq2 : y2 j = x j := hy2 j (Finset.mem_erase.mpr ⟨hj_ne2, hj⟩)
              have heq3 : y3 j = x j := hy3 j (Finset.mem_erase.mpr ⟨hj_ne3, hj⟩)
              rw [heq2, heq3]
              cases y1 j <;> cases x j <;> rfl
            · by_cases hj2 : j = i2
              · have hj_ne3 : j ≠ i3 := by
                  rw [hj2]
                  exact hi3_ne2.symm
                have heq1 : y1 j = x j := hy1 j (Finset.mem_erase.mpr ⟨hj1, hj⟩)
                have heq3 : y3 j = x j := hy3 j (Finset.mem_erase.mpr ⟨hj_ne3, hj⟩)
                rw [heq1, heq3]
                cases y2 j <;> cases x j <;> rfl
              · have heq1 : y1 j = x j := hy1 j (Finset.mem_erase.mpr ⟨hj1, hj⟩)
                have heq2 : y2 j = x j := hy2 j (Finset.mem_erase.mpr ⟨hj2, hj⟩)
                rw [heq1, heq2]
                cases y3 j <;> cases x j <;> rfl
    obtain ⟨y, hyR, hy⟩ := hind (Finset.univ : Finset (Fin n)).card Finset.univ rfl
    have hyx : y = x := funext (fun i => hy i (Finset.mem_univ i))
    rwa [← hyx]

open Finset
abbrev W (n : Nat) := Fin n → Bool
abbrev Clause (n : Nat) := (Fin n × Bool) × (Fin n × Bool)
abbrev F (n : Nat) := Finset (Clause n)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
def sat {n : Nat} (A : F n) (x : W n) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
def maj {n : Nat} (a b c : W n) : W n :=
  fun i => (a i && b i) || (b i && c i) || (c i && a i)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
def closed {n : Nat} (R : W n → Prop) : Prop :=
  ∀ a, R a → ∀ b, R b → ∀ c, R c → R (maj a b c)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
def addable {n : Nat} (A : F n) (z : W n) : Prop :=
  ∃ B : F n, ∀ x, sat B x ↔ sat A x ∨ x = z

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem maj_aab {n : Nat} (a b : W n) : maj a a b = a := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem maj_aba {n : Nat} (a b : W n) : maj a b a = a := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem maj_baa {n : Nat} (a b : W n) : maj b a a = a := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem maj_swap {n : Nat} (a b c : W n) : maj a b c = maj b a c := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> cases c i <;> rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem maj_rotate {n : Nat} (a b c : W n) : maj a b c = maj b c a := by
  funext i; dsimp only [maj]; cases a i <;> cases b i <;> cases c i <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem sat_closed {n : Nat} (A : F n) : closed (sat A) := by
  intro a ha b hb c hc d hd
  have logic : ∀ ai bi ci aj bj cj p q : Bool,
      (ai ≠ p ∨ aj ≠ q) → (bi ≠ p ∨ bj ≠ q) → (ci ≠ p ∨ cj ≠ q) →
      ((ai && bi) || (bi && ci) || (ci && ai)) ≠ p ∨
      ((aj && bj) || (bj && cj) || (cj && aj)) ≠ q := by decide
  exact logic _ _ _ _ _ _ _ _ (ha d hd) (hb d hd) (hc d hd)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem exists_formula {n : Nat} (R : W n → Prop) (hne : ∃ x, R x) (hR : closed R) :
    ∃ A : F n, ∀ x, sat A x ↔ R x := by
  classical
  let A : F n := univ.filter (fun c => ∀ y, R y → y c.1.1 ≠ c.1.2 ∨ y c.2.1 ≠ c.2.2)
  refine ⟨A,fun x => ?_⟩
  constructor
  · intro hx
    by_cases hn : 0 < n
    · apply (projection_reconstruction n {x | R x} hn hR x).mpr
      intro i j
      by_contra h
      have hc : ((i,x i),(j,x j)) ∈ A := by
        simp only [A, mem_filter, mem_univ, true_and]
        intro y hy
        by_contra hbad
        push Not at hbad
        exact h ⟨y,hy,hbad⟩
      exact (hx _ hc).elim (fun h => h rfl) (fun h => h rfl)
    · obtain ⟨y,hy⟩ := hne
      have hxy : x = y := by funext i; have hi := i.isLt; omega
      exact hxy ▸ hy
  · intro hx c hc
    exact (mem_filter.mp hc).2 x hx

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem addable_iff_closed {n : Nat} (A : F n) (z : W n) :
    addable A z ↔ closed (fun x => sat A x ∨ x = z) := by
  constructor
  · rintro ⟨B,hB⟩ a ha b hb c hc
    exact (hB _).mp (sat_closed B a ((hB _).mpr ha) b ((hB _).mpr hb) c ((hB _).mpr hc))
  · intro h
    exact exists_formula _ ⟨z,Or.inr rfl⟩ h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem mixed_iff_closed {n : Nat} (A : F n) (z : W n) :
    (∀ a, sat A a → ∀ b, sat A b → sat A (maj a b z) ∨ maj a b z = z) ↔
      closed (fun x => sat A x ∨ x = z) := by
  constructor
  · intro h a ha b hb c hc
    rcases ha with ha | rfl <;> rcases hb with hb | rfl <;> rcases hc with hc | rfl
    · exact Or.inl (sat_closed A a ha b hb c hc)
    · exact h a ha b hb
    · rw [maj_swap, maj_rotate]; exact h a ha c hc
    · rw [maj_baa]; exact Or.inr rfl
    · rw [maj_rotate]; exact h b hb c hc
    · rw [maj_aba]; exact Or.inr rfl
    · rw [maj_aab]; exact Or.inr rfl
    · rw [maj_aab]; exact Or.inr rfl
  · intro h a ha b hb
    exact h a (Or.inl ha) b (Or.inl hb) z (Or.inr rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem mixed_iff_test {n : Nat} (A : F n) (z : W n) :
    (∀ a, sat A a → ∀ b, sat A b → sat A (maj a b z) ∨ maj a b z = z) ↔
    ∀ c ∈ A, ∀ k : Fin n, ¬ (z c.1.1 = c.1.2 ∧ z c.2.1 = c.2.2 ∧
      (∃ a, sat A a ∧ a c.1.1 = c.1.2 ∧ a k ≠ z k) ∧
      (∃ b, sat A b ∧ b c.2.1 = c.2.2 ∧ b k ≠ z k)) := by
  classical
  constructor
  · intro h c hc k hbad
    obtain ⟨hzi,hzj,⟨a,ha,hai,hak⟩,⟨b,hb,hbj,hbk⟩⟩ := hbad
    have hi : maj a b z c.1.1 = c.1.2 := by
      dsimp only [maj]
      rw [hai,hzi]
      cases b c.1.1 <;> cases c.1.2 <;> rfl
    have hj : maj a b z c.2.1 = c.2.2 := by
      dsimp only [maj]
      rw [hbj,hzj]
      cases a c.2.1 <;> cases c.2.2 <;> rfl
    have hk : maj a b z k ≠ z k := by
      have logic : ∀ p q r : Bool, p ≠ r → q ≠ r →
          ((p&&q)||(q&&r)||(r&&p)) ≠ r := by decide
      exact logic _ _ _ hak hbk
    rcases h a ha b hb with hm | he
    · exact (hm c hc).elim (fun h => h hi) (fun h => h hj)
    · exact hk (congrFun he k)
  · intro h a ha b hb
    by_cases hs : sat A (maj a b z)
    · exact Or.inl hs
    by_cases he : maj a b z = z
    · exact Or.inr he
    exfalso
    have hc : ∃ c ∈ A, maj a b z c.1.1 = c.1.2 ∧ maj a b z c.2.1 = c.2.2 := by
      simpa only [sat, not_forall, not_or, not_not, exists_prop] using hs
    obtain ⟨c,hc,hi,hj⟩ := hc
    have hk : ∃ k, maj a b z k ≠ z k := by
      by_contra hk
      push Not at hk
      exact he (funext hk)
    obtain ⟨k,hk⟩ := hk
    have cross : ∀ ai bi zi aj bj zj p q : Bool,
        (ai ≠ p ∨ aj ≠ q) → (bi ≠ p ∨ bj ≠ q) →
        ((ai&&bi)||(bi&&zi)||(zi&&ai)) = p →
        ((aj&&bj)||(bj&&zj)||(zj&&aj)) = q →
        zi = p ∧ zj = q ∧ ((ai = p ∧ bj = q) ∨ (bi = p ∧ aj = q)) := by decide
    obtain ⟨hzi,hzj,hab⟩ := cross _ _ _ _ _ _ _ _ (ha c hc) (hb c hc) hi hj
    have different : ∀ p q r : Bool, ((p&&q)||(q&&r)||(r&&p)) ≠ r → p ≠ r ∧ q ≠ r := by decide
    obtain ⟨hak,hbk⟩ := different _ _ _ hk
    rcases hab with ⟨hai,hbj⟩ | ⟨hbi,haj⟩
    · exact h c hc k ⟨hzi,hzj,⟨a,ha,hai,hak⟩,⟨b,hb,hbj,hbk⟩⟩
    · exact h c hc k ⟨hzi,hzj,⟨b,hb,hbi,hbk⟩,⟨a,ha,haj,hak⟩⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem addable_test {n : Nat} (A : F n) (z : W n) :
    addable A z ↔ ∀ c ∈ A, ∀ k : Fin n,
      ¬ (z c.1.1 = c.1.2 ∧ z c.2.1 = c.2.2 ∧
       (∃ a, sat A a ∧ a c.1.1 = c.1.2 ∧ a k ≠ z k) ∧
       (∃ b, sat A b ∧ b c.2.1 = c.2.2 ∧ b k ≠ z k)) := by
  rw [addable_iff_closed, ← mixed_iff_closed, mixed_iff_test]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem pair_closed {n : Nat} (u v : W n) : closed (fun x => x=u ∨ x=v) := by
  intro a ha b hb c hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp only [maj_aab, maj_aba, maj_baa, true_or, or_true, eq_self]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem pair_addable {n : Nat} (A : F n) (u v z : W n)
    (hA : ∀ x, sat A x ↔ x=u ∨ x=v)
    (hm : maj u v z = u ∨ maj u v z = v ∨ maj u v z = z) : addable A z := by
  rw [addable_iff_closed, ← mixed_iff_closed]
  intro a ha b hb
  have ha := (hA a).mp ha
  have hb := (hA b).mp hb
  have hm' : sat A (maj u v z) ∨ maj u v z=z := by
    rcases hm with h | h | h
    · exact Or.inl ((hA _).mpr (Or.inl h))
    · exact Or.inl ((hA _).mpr (Or.inr h))
    · exact Or.inr h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [maj_aab]; exact Or.inl ((hA _).mpr (Or.inl rfl))
  · exact hm'
  · rw [maj_swap]; exact hm'
  · rw [maj_aab]; exact Or.inl ((hA _).mpr (Or.inr rfl))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
def word {n : Nat} (S : Finset (Fin n)) : W n := fun i => decide (i∈S)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem sharp (n : Nat) (hn : 3 ≤ n) :
    ∃ A : F n, ¬ ∃ D : F n, ∀ z, sat D z ↔ addable A z := by
  classical
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let c : Fin n := ⟨2,by omega⟩
  have hab : a ≠ b := by simp [a,b]
  have hac : a ≠ c := by simp [a,c]
  have hbc : b ≠ c := by simp [b,c]
  let u : W n := word ∅
  let v : W n := word {a,b}
  let z1 : W n := word {b}
  let z2 : W n := word {a,b,c}
  let z3 : W n := word {c}
  let bad : W n := word {b,c}
  obtain ⟨A,hA⟩ := exists_formula (fun x => x=u ∨ x=v) ⟨u,Or.inl rfl⟩ (pair_closed u v)
  have hm1 : maj u v z1 = z1 := by
    funext i
    by_cases ha : i=a <;> by_cases hb : i=b <;>
      simp [maj,u,v,z1,word,ha,hb]
  have hm2 : maj u v z2 = v := by
    funext i
    by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;>
      simp [maj,u,v,z2,word,ha,hb,hc]
  have hm3 : maj u v z3 = u := by
    funext i
    by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;>
      simp_all [maj,u,v,z3,word]
  have hmb : maj u v bad = z1 := by
    funext i
    by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;>
      simp_all [maj,u,v,bad,z1,word]
  have hmz : maj z1 z2 z3 = bad := by
    funext i
    by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;>
      simp_all [maj,z1,z2,z3,bad,word]
  have h1 := pair_addable A u v z1 hA (Or.inr (Or.inr hm1))
  have h2 := pair_addable A u v z2 hA (Or.inr (Or.inl hm2))
  have h3 := pair_addable A u v z3 hA (Or.inl hm3)
  have hbad : ¬ addable A bad := by
    intro h
    have hh := (addable_iff_closed A bad).mp h
    have hu : sat A u := (hA u).mpr (Or.inl rfl)
    have hv : sat A v := (hA v).mpr (Or.inr rfl)
    have hh := hh u (Or.inl hu) v (Or.inl hv) bad (Or.inr rfl)
    rw [hmb] at hh
    rcases hh with h | h
    · rcases (hA z1).mp h with h | h
      · have he := congrFun h b
        simp [z1,u,word] at he
      · have he := congrFun h a
        simp [z1,v,word,hab] at he
    · have he := congrFun h c
      simp [z1,bad,word,hbc.symm] at he
  refine ⟨A,?_⟩
  rintro ⟨D,hD⟩
  have hclosed := sat_closed D z1 ((hD z1).mpr h1) z2 ((hD z2).mpr h2) z3 ((hD z3).mpr h3)
  rw [hmz] at hclosed
  exact hbad ((hD bad).mp hclosed)

end PEqualNP.Outside.L_lib_1054_aux

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
open PEqualNP.Outside.L_lib_1054_aux in
theorem PEqualNP.Outside.L_lib_1054 : let W := fun n : ℕ => Fin n → Bool
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
  dsimp only
  constructor
  · intro n A z
    exact addable_test A z
  · exact sharp
