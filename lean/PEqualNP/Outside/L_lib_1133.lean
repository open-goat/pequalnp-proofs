import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1133

namespace Local1133Core
open scoped BigOperators
variable {α : Type} [DecidableEq α]
variable {n m : ℕ}

def flip (x y : Finset α) : Finset α := (x\y)∪(y\x)

theorem in_flip {x y : Finset α} {a : α} :
    a∈flip x y ↔ (a∈x ∧ a∉y) ∨ (a∈y ∧ a∉x) := by simp [flip]

theorem flip_cancel (x y : Finset α) : flip (flip x y) y=x := by
  ext a
  simp only [in_flip]
  tauto

theorem flip_cancel_left (x y : Finset α) : flip x (flip x y)=y := by
  ext a
  simp only [in_flip]
  tauto

theorem flip_comm (x y : Finset α) : flip x y=flip y x := by
  ext a
  simp [in_flip,or_comm]

theorem flip_filter (x y : Finset α) (p : α→Prop) [DecidablePred p] :
    (flip x y).filter p=flip (x.filter p) (y.filter p) := by
  ext a
  simp only [Finset.mem_filter,in_flip]
  tauto

theorem flip_card (x y : Finset α) :
    (flip x y).card + 2*(x∩y).card=x.card+y.card := by
  have dis : Disjoint (x\y) (y\x) := Finset.disjoint_left.mpr (fun a hx hy =>
    (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1)
  have a := Finset.card_sdiff_add_card_inter x y
  have b := Finset.card_sdiff_add_card_inter y x
  rw [Finset.inter_comm y x] at b
  unfold flip
  rw [Finset.card_union_of_disjoint dis]
  omega

def ends (u v : Fin m→Fin n) (x : Finset (Fin m)) (j : Fin n) : ℕ :=
  (x.filter fun i => u i=j).card+(x.filter fun i => v i=j).card

def boundary (u v : Fin m→Fin n) (x : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter fun j => ends u v x j % 2=1

def crossing (u v : Fin m→Fin n) (U : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i => decide (u i∈U) != decide (v i∈U)

theorem boundary_flip (u v : Fin m→Fin n) (x y : Finset (Fin m)) :
    boundary u v (flip x y)=flip (boundary u v x) (boundary u v y) := by
  ext j
  simp only [boundary,in_flip,Finset.mem_filter,Finset.mem_univ,true_and]
  have A := flip_card (x.filter fun i => u i=j) (y.filter fun i => u i=j)
  have B := flip_card (x.filter fun i => v i=j) (y.filter fun i => v i=j)
  unfold ends
  rw [flip_filter,flip_filter]
  omega

theorem boundary_singleton (u v : Fin m→Fin n) (i : Fin m) :
    boundary u v {i}=flip {u i} {v i} := by
  ext j
  simp only [boundary,ends,in_flip,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  have au : (j=u i) ↔ (u i=j) := eq_comm
  have av : (j=v i) ↔ (v i=j) := eq_comm
  by_cases a : u i=j <;> by_cases b : v i=j <;>
    simp [Finset.filter_singleton,au,av,a,b]

theorem boundary_empty (u v : Fin m→Fin n) : boundary u v ∅=∅ := by simp [boundary,ends]

theorem sum_ends (u : Fin m→Fin n) (x : Finset (Fin m)) (U : Finset (Fin n)) :
    ∑ j ∈ U, (x.filter fun i => u i=j).card = ∑ i∈x, (if u i∈U then 1 else 0 : ℕ) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [eq_comm]

theorem sum_mod_parity {β : Type} (f : β→ℕ) (A : Finset β) :
    (∑ j ∈ A, f j % 2) % 2=(∑ j ∈ A,f j) % 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Nat.add_mod (f a % 2),Nat.add_mod (f a)]
    rw [Nat.mod_mod, ih]

theorem indicate (f : Finset α) (p q : α→Prop) [DecidablePred p] [DecidablePred q] :
    (∑ i∈f, ((if p i then 1 else 0)+(if q i then 1 else 0) : ℕ)) % 2 =
      (∑ i∈f, (if (decide (p i) != decide (q i)) then 1 else 0 : ℕ)) % 2 := by
  rw [←sum_mod_parity _ f]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases a : p i <;> by_cases b : q i <;> simp [a,b]

theorem boundary_parity (u v : Fin m→Fin n) (x : Finset (Fin m)) (U : Finset (Fin n)) :
    ((boundary u v x)∩U).card % 2 = (x∩crossing u v U).card % 2 := by
  have a : (boundary u v x)∩U=U.filter (fun j => ends u v x j % 2=1) := by
    ext j
    simp [boundary,and_comm]
  have b : x∩crossing u v U=x.filter (fun i => decide (u i∈U) != decide (v i∈U)) := by
    ext i
    simp [crossing]
  rw [a,b,Finset.card_filter,Finset.card_filter]
  have e : (∑ j ∈ U, (if ends u v x j % 2=1 then 1 else 0 : ℕ))=(∑ j ∈ U, ends u v x j % 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    split <;> omega
  rw [e,sum_mod_parity]
  unfold ends
  rw [Finset.sum_add_distrib,sum_ends,sum_ends,←Finset.sum_add_distrib]
  exact indicate x (fun i => u i∈U) (fun i => v i∈U)

end Local1133Core

namespace Local1133Formula
open Local1133Core
open scoped BigOperators
variable {n m : ℕ}

abbrev Clause (m : ℕ) := Finset (Fin m×Bool)

abbrev holds (x : Finset (Fin m)) (C : Clause m) :=
  ∃ l∈C, decide (l.1∈x)=l.2

def valid (T : Finset (Fin m)) (t w : ℕ) (F : Finset (Clause m)) :=
  F.card≤t ∧ ∀ C∈F,C.card≤w ∧ ∀ l∈C,l.1∈T

def rows (u v : Fin m→Fin n) (D : Finset (Fin n)) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun x => boundary u v x=D)

def total (u v : Fin m→Fin n) (D : Finset (Fin n)) (F : Finset (Clause m)) :=
  ((rows u v D).filter (fun x => ∀ C∈F,holds x C)).card

def separates (u v : Fin m→Fin n) (T : Finset (Fin m)) (D E : Finset (Fin n)) (k : ℕ) :=
  ∃ U : Finset (Fin n), crossing u v U⊆T ∧ (crossing u v U).card≤k ∧
    (D∩U).card % 2≠(E∩U).card % 2

theorem mem_rows {u v : Fin m→Fin n} {D : Finset (Fin n)} {x : Finset (Fin m)} :
    x∈rows u v D ↔ boundary u v x=D := by simp [rows]

theorem positive_total {u v : Fin m→Fin n} {D : Finset (Fin n)} {F : Finset (Clause m)} :
    0<total u v D F ↔ ∃ x : Finset (Fin m),boundary u v x=D ∧ ∀ C∈F,holds x C := by
  unfold total
  simp only [Finset.card_pos,Finset.Nonempty,Finset.mem_filter,mem_rows]

theorem zero_total {u v : Fin m→Fin n} {D : Finset (Fin n)} {F : Finset (Clause m)}
    (none : ¬ ∃ x : Finset (Fin m),boundary u v x=D ∧ ∀ C∈F,holds x C) :
    total u v D F=0 := by
  by_contra bad
  exact none (positive_total.mp (by omega))

def support (F : Finset (Clause m)) : Finset (Fin m) :=
  F.biUnion (fun C => C.image Prod.fst)

theorem support_mem {F : Finset (Clause m)} {C : Clause m} (CF : C∈F)
    {l : Fin m×Bool} (lC : l∈C) : l.1∈support F :=
  Finset.mem_biUnion.mpr ⟨C,CF,Finset.mem_image_of_mem Prod.fst lC⟩

theorem support_ok {T : Finset (Fin m)} {t w : ℕ} {F : Finset (Clause m)} (f : valid T t w F) :
    support F⊆T ∧ (support F).card≤t*w := by
  constructor
  · intro i im
    obtain ⟨C,CF,me⟩ := Finset.mem_biUnion.mp im
    obtain ⟨l,lC,e⟩ := Finset.mem_image.mp me
    exact e ▸ (f.2 C CF).2 l lC
  · unfold support
    refine Finset.card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ C∈F, w := by
        apply Finset.sum_le_sum
        intro C CF
        exact Finset.card_image_le.trans (f.2 C CF).1
      _ ≤ t*w := by simpa using Nat.mul_le_mul_right w f.1

def Agrees (S x y : Finset (Fin m)) : Prop :=
  ∀ i∈S,(i∈x ↔ i∈y)

theorem same_at {x z S : Finset (Fin m)} (no : Disjoint z S) :
    Agrees S x (flip x z) := by
  intro i im
  have nz : i∉z := fun h => Finset.disjoint_left.mp no h im
  simp [in_flip,nz]

theorem mem_bool {x y S : Finset (Fin m)} (a : Agrees S x y) (i : Fin m) (im : i∈S) :
    decide (i∈x)=decide (i∈y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact a i im

theorem preserve {F : Finset (Clause m)} {x y : Finset (Fin m)}
    (a : Agrees (support F) x y) :
    (∀ C∈F,holds x C) ↔ ∀ C∈F,holds y C := by
  constructor
  · intro f C CF
    obtain ⟨l,lc,lv⟩ := f C CF
    exact ⟨l,lc,(mem_bool a l.1 (support_mem CF lc)).symm.trans lv⟩
  · intro f C CF
    obtain ⟨l,lc,lv⟩ := f C CF
    exact ⟨l,lc,(mem_bool a l.1 (support_mem CF lc)).trans lv⟩

theorem cut_for_delta (D E U : Finset (Fin n)) :
    (D∩U).card % 2 ≠ (E∩U).card % 2 ↔ ((flip D E)∩U).card % 2=1 := by
  have fq : (flip D E)∩U=flip (D∩U) (E∩U) := by
    ext i
    simp only [Finset.mem_inter,in_flip]
    tauto
  rw [fq]
  have q := flip_card (D∩U) (E∩U)
  omega

theorem translate {u v : Fin m→Fin n} {D E : Finset (Fin n)} {x z : Finset (Fin m)}
    (xd : boundary u v x=D) (ze : boundary u v z=flip D E) :
    boundary u v (flip x z)=E := by
  rw [boundary_flip,xd,ze,flip_cancel_left]

theorem count_shift (u v : Fin m→Fin n) (D E : Finset (Fin n)) (F : Finset (Clause m))
    (z : Finset (Fin m)) (dz : Disjoint z (support F))
    (ze : boundary u v z=flip D E) :
    total u v D F=total u v E F := by
  classical
  have ze' : boundary u v z=flip E D := ze.trans (flip_comm _ _)
  unfold total
  refine Finset.card_bij' (fun x _ => flip x z) (fun y _ => flip y z) ?_ ?_ ?_ ?_
  · intro x h
    obtain ⟨xD,xF⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨mem_rows.mpr (translate (mem_rows.mp xD) ze), (preserve (same_at dz)).mp xF⟩
  · intro x h
    obtain ⟨xD,xF⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨mem_rows.mpr (translate (mem_rows.mp xD) ze'), (preserve (same_at dz)).mp xF⟩
  · intro x _
    exact flip_cancel _ _
  · intro x _
    exact flip_cancel _ _

end Local1133Formula

namespace Worker1133Counting

variable {m : ℕ}
abbrev Row (m : ℕ) := Finset (Fin m)
abbrev Clause (m : ℕ) := Finset (Fin m × Bool)

def holds (x : Row m) (C : Clause m) : Prop :=
  ∃ l ∈ C, decide (l.1 ∈ x) = l.2

def valid (T : Row m) (t w : ℕ) (F : Finset (Clause m)) : Prop :=
  F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T

def sat (F : Finset (Clause m)) (x : Row m) : Prop :=
  ∀ C ∈ F, holds x C

def pin (S : Row m) (p : Fin m → Bool) (x : Row m) : Prop :=
  ∀ i ∈ S, decide (i ∈ x) = p i

noncomputable def countCnf (A : Finset (Row m)) (F : Finset (Clause m)) : ℕ := by
  classical
  exact (A.filter (sat F)).card

noncomputable def pinRows (A : Finset (Row m)) (S : Row m) (p : Fin m → Bool) : Finset (Row m) := by
  classical
  exact A.filter (pin S p)

theorem mem_pinRows {A : Finset (Row m)} {S : Row m} {p : Fin m → Bool} {x : Row m} :
    x ∈ pinRows A S p ↔ x ∈ A ∧ pin S p x := by
  classical
  exact Finset.mem_filter

def forb (S : Row m) (p : Fin m → Bool) : Clause m :=
  S.image fun i => (i, !(p i))

theorem forb_card (S : Row m) (p : Fin m → Bool) : (forb S p).card = S.card :=
  Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h

theorem forb_vars {S : Row m} {p : Fin m → Bool} {l : Fin m × Bool}
    (h : l ∈ forb S p) : l.1 ∈ S := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
  exact hi

theorem not_holds_forb (S : Row m) (p : Fin m → Bool) (x : Row m) :
    ¬ holds x (forb S p) ↔ pin S p x := by
  constructor
  · intro h i hi
    by_contra hn
    have hbad : decide (i ∈ x) = !(p i) := by
      cases h1 : decide (i ∈ x) <;> cases h2 : p i <;> simp_all
    exact h ⟨(i, !(p i)), Finset.mem_image_of_mem _ hi, hbad⟩
  · intro h hh
    obtain ⟨l,hl,he⟩ := hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    change decide (i ∈ x) = !(p i) at he
    have hp := h i hi
    rw [hp] at he
    cases heq : p i <;> simp [heq] at he

theorem count_split (A : Finset (Row m)) (S : Row m) (p : Fin m → Bool)
    (F : Finset (Clause m)) :
    countCnf (pinRows A S p) F + countCnf A (insert (forb S p) F) = countCnf A F := by
  classical
  let good := (A.filter (sat F)).filter (holds · (forb S p))
  let bad := (A.filter (sat F)).filter (fun x => ¬ holds x (forb S p))
  have he : good.card + bad.card = (A.filter (sat F)).card := by
    exact Finset.card_filter_add_card_filter_not (s := A.filter (sat F)) _
  have hg : A.filter (sat (insert (forb S p) F)) = good := by
    ext x
    simp only [good, Finset.mem_filter, sat, Finset.forall_mem_insert]
    tauto
  have hb : (pinRows A S p).filter (sat F) = bad := by
    ext x
    simp only [bad, Finset.mem_filter, mem_pinRows, not_holds_forb]
    tauto
  have ha (B : Finset (Row m)) (G : Finset (Clause m)) :
      countCnf B G = (B.filter (sat G)).card := rfl
  rw [ha, ha, ha, hb, hg]
  omega

theorem equal_pins_of_equal_cnfs (T : Row m) (w t : ℕ) :
    ∀ (S : Row m) (p : Fin m → Bool) (A B : Finset (Row m)), S ⊆ T →
      S.card ≤ t * w →
      (∀ F, valid T t w F → countCnf A F = countCnf B F) →
      (pinRows A S p).card = (pinRows B S p).card := by
  induction t with
  | zero =>
    intro S p A B _ hS he
    have hSE : S = ∅ := Finset.card_eq_zero.mp (by simpa using hS)
    subst S
    have pin_empty (E : Finset (Row m)) : pinRows E ∅ p = E := by
      ext x
      simp [mem_pinRows, pin]
    rw [pin_empty, pin_empty]
    have hvalid : valid T 0 w ∅ := by simp [valid]
    have hh := he ∅ hvalid
    have hce (E : Finset (Row m)) : countCnf E ∅ = E.card := by
      classical
      unfold countCnf
      congr 1
      ext x
      simp [sat]
    simpa only [hce] using hh
  | succ t ih =>
    intro S p A B hST hS he
    obtain ⟨D,hDS,hD⟩ := Finset.exists_subset_card_eq (Nat.min_le_right w S.card)
    let R := S \ D
    have hRT : R ⊆ T := (Finset.sdiff_subset : R ⊆ S).trans hST
    have hDwidth : D.card ≤ w := hD.trans_le (Nat.min_le_left _ _)
    have hR : R.card ≤ t * w := by
      have hh : R.card + D.card = S.card := Finset.card_sdiff_add_card_eq_card hDS
      rw [Nat.succ_mul] at hS
      by_cases h : w ≤ S.card
      · rw [hD, min_eq_left h] at hh
        omega
      · rw [hD, min_eq_right (by omega)] at hh
        omega
    have hsame (F : Finset (Clause m)) (hF : valid T t w F) :
        countCnf (pinRows A D p) F = countCnf (pinRows B D p) F := by
      have hv : valid T (t+1) w F := ⟨by have := hF.1; omega, hF.2⟩
      have hv' : valid T (t+1) w (insert (forb D p) F) := by
        constructor
        · have hh := Finset.card_insert_le (s := F) (a := forb D p)
          have hh' := hF.1
          omega
        · intro C hC
          rcases Finset.mem_insert.mp hC with e | hc
          · subst C
            exact ⟨(forb_card D p).trans_le hDwidth, fun _ hl => hST (hDS (forb_vars hl))⟩
          · exact hF.2 C hc
      have e0 := he F hv
      have e1 := he _ hv'
      have sA := count_split A D p F
      have sB := count_split B D p F
      omega
    have eq := ih R p (pinRows A D p) (pinRows B D p) hRT hR hsame
    have hmerge (E : Finset (Row m)) : pinRows (pinRows E D p) R p = pinRows E S p := by
      ext x
      simp only [mem_pinRows, pin]
      constructor
      · rintro ⟨⟨hx,hDpin⟩,hRpin⟩
        refine ⟨hx, fun i hi => ?_⟩
        by_cases h : i ∈ D
        · exact hDpin i h
        · exact hRpin i (Finset.mem_sdiff.mpr ⟨hi,h⟩)
      · rintro ⟨hx,hSp⟩
        exact ⟨⟨hx, fun i hi => hSp i (hDS hi)⟩, fun i hi => hSp i (Finset.mem_sdiff.mp hi).1⟩
    simpa only [hmerge] using eq

theorem count_witness (T S : Row m) (p : Fin m → Bool) (t w : ℕ)
    (A B : Finset (Row m)) (hST : S ⊆ T) (hS : S.card ≤ t*w)
    (hneq : (pinRows A S p).card ≠ (pinRows B S p).card) :
    ∃ F, valid T t w F ∧ countCnf A F ≠ countCnf B F := by
  classical
  by_contra h
  apply hneq
  apply equal_pins_of_equal_cnfs T w t S p A B hST hS
  intro F hF
  by_contra hn
  exact h ⟨F,hF,hn⟩

end Worker1133Counting

namespace Worker1133Dual

open scoped symmDiff

private theorem sx_mem_subset {α : Type*} [DecidableEq α]
    {a b c : Finset α} (ha : a ⊆ c) (hb : b ⊆ c) : a ∆ b ⊆ c := by
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with h | h
  · exact ha h.1
  · exact hb h.1

private theorem sx_subtract {α : Type*} [DecidableEq α]
    {a b : Finset α} (h : b ⊆ a) : a ∆ b = a \ b := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
  constructor
  · rintro (hj | hj)
    · exact hj
    · exact (hj.2 (h hj.1)).elim
  · exact Or.inl

private theorem pair_eq {α : Type*} [DecidableEq α] {p q : α}
    (ne : p ≠ q) : ({p} : Finset α) ∆ {q} = {p,q} := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  by_cases hp : j=p <;> by_cases hq : j=q <;> simp_all

private theorem pair_cancel {α : Type*} [DecidableEq α] (p q r : α) :
    (({p} : Finset α) ∆ {q}) ∆ (({q} : Finset α) ∆ {r}) =
      ({p} : Finset α) ∆ {r} := by
  simp [symmDiff_assoc, symmDiff_symmDiff_cancel_left]

private theorem sx_inter {α : Type*} [DecidableEq α] (a b c : Finset α) :
    (a ∆ b) ∩ c = (a ∩ c) ∆ (b ∩ c) := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_inter]
  tauto

private theorem sx_parity {α : Type*} [DecidableEq α] (a b : Finset α) :
    (a ∆ b).card % 2 = (a.card + b.card) % 2 := by
  have disj : Disjoint (a \ b) (b \ a) := by
    rw [Finset.disjoint_left]
    intro j h₁ h₂
    exact (Finset.mem_sdiff.mp h₁).2 (Finset.mem_sdiff.mp h₂).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disj]
  have ha := Finset.card_sdiff_add_card_inter a b
  have hb := Finset.card_sdiff_add_card_inter b a
  rw [Finset.inter_comm b a] at hb
  omega


theorem separator {m n : ℕ} (u v : Fin m → Fin n)
    (B : Finset (Fin m) → Finset (Fin n))
    (K : Finset (Fin n) → Finset (Fin m))
    (empty : B ∅ = ∅)
    (bx : ∀ a b, B (a ∆ b) = B a ∆ B b)
    (sing : ∀ i, B {i} = ({u i} : Finset (Fin n)) ∆ {v i})
    (kdef : ∀ U i, i ∈ K U ↔
      ((u i ∈ U ∧ v i ∉ U) ∨ (v i ∈ U ∧ u i ∉ U)))
    (par : ∀ a U, ((B a) ∩ U).card % 2 = (a ∩ K U).card % 2)
    (S : Finset (Fin m)) (Z : Finset (Fin n))
    (no : ¬ ∃ a, a ⊆ Finset.univ \ S ∧ B a = Z) :
    ∃ U : Finset (Fin n), K U ⊆ S ∧ (Z ∩ U).card % 2 = 1 := by
  classical
  let C := (Finset.univ : Finset (Fin m)) \ S
  let L := (Finset.univ : Finset (Finset (Fin m))).filter (· ⊆ C)
  have nonemptyL : L.Nonempty := ⟨∅, by simp [L]⟩
  obtain ⟨X,hX,hmin⟩ := Finset.exists_min_image L (fun a => (Z ∆ B a).card) nonemptyL
  have allowedX : X ⊆ C := (Finset.mem_filter.mp hX).2
  let R := Z ∆ B X
  have nonemptyR : R.Nonempty := Finset.symmDiff_nonempty.mpr
    (fun e => no ⟨X,allowedX,e.symm⟩)
  obtain ⟨p,hp⟩ := nonemptyR
  let U := (Finset.univ : Finset (Fin n)).filter
    (fun q => ∃ a, a ⊆ C ∧ B a = ({p} : Finset (Fin n)) ∆ {q})
  have reach (q : Fin n) : q ∈ U ↔ ∃ a, a ⊆ C ∧ B a = ({p} : Finset (Fin n)) ∆ {q} := by
    simp [U]
  have pU : p ∈ U := (reach p).2 ⟨∅,Finset.empty_subset _,by simp [empty]⟩
  have travel (q r : Fin n) (i : Fin m) (ic : i ∈ C)
      (e : B {i} = ({q} : Finset (Fin n)) ∆ {r}) (hq : q ∈ U) : r ∈ U := by
    obtain ⟨a,ha,hBa⟩ := (reach q).1 hq
    have hi : ({i} : Finset (Fin m)) ⊆ C := Finset.singleton_subset_iff.mpr ic
    refine (reach r).2 ⟨a ∆ {i},sx_mem_subset ha hi,?_⟩
    rw [bx,hBa,e,pair_cancel]
  have kS : K U ⊆ S := by
    intro i iK
    by_contra hi
    have ic : i ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩
    rcases (kdef U i).1 iK with hh | hh
    · exact hh.2 (travel (u i) (v i) i ic (sing i) hh.1)
    · have e : B {i} = ({v i} : Finset (Fin n)) ∆ {u i} :=
        (sing i).trans (symmDiff_comm _ _)
      exact hh.2 (travel (v i) (u i) i ic e hh.1)
  have uUnique : ∀ q ∈ R, q ∈ U → q = p := by
    intro q hq qU
    by_contra different
    obtain ⟨a,ha,eqBa⟩ := (reach q).1 qU
    have hh : X ∆ a ∈ L := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sx_mem_subset allowedX ha⟩
    have hle := hmin (X ∆ a) hh
    have pqInside : ({p,q} : Finset (Fin n)) ⊆ R := by
      intro a aa
      rcases Finset.mem_insert.mp aa with hh | hh
      · simpa only [hh] using hp
      · simpa only [Finset.mem_singleton.mp hh] using hq
    have simplified : Z ∆ B (X ∆ a) = R \ {p,q} := by
      rw [bx,←symmDiff_assoc,eqBa,pair_eq (Ne.symm different)]
      exact sx_subtract pqInside
    rw [simplified,Finset.card_sdiff_of_subset pqInside] at hle
    have hpos : 0 < ({p,q} : Finset (Fin n)).card :=
      Finset.card_pos.mpr ⟨p,Finset.mem_insert_self _ _⟩
    have hqle := Finset.card_le_card pqInside
    change R.card ≤ R.card - ({p,q} : Finset (Fin n)).card at hle
    omega
  have single : R ∩ U = {p} := by
    ext q
    simp only [Finset.mem_inter,Finset.mem_singleton]
    exact ⟨fun h => uUnique q h.1 h.2,fun h => h.symm ▸ ⟨hp,pU⟩⟩
  have zero : X ∩ K U = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i h
    obtain ⟨ix,ik⟩ := Finset.mem_inter.mp h
    exact (Finset.mem_sdiff.mp (allowedX ix)).2 (kS ik)
  have even : ((B X) ∩ U).card % 2 = 0 := by rw [par,zero]; simp
  have h := sx_parity (Z ∩ U) (B X ∩ U)
  rw [← sx_inter] at h
  change (R ∩ U).card % 2 = _ at h
  rw [single,Finset.card_singleton, Nat.add_mod,even,Nat.add_zero,Nat.mod_mod] at h
  exact ⟨U,kS,h.symm⟩

theorem obstructed {m n : ℕ} (B : Finset (Fin m) → Finset (Fin n))
    (K : Finset (Fin n) → Finset (Fin m))
    (par : ∀ a U, ((B a) ∩ U).card % 2 = (a ∩ K U).card % 2)
    (S : Finset (Fin m)) (Z U : Finset (Fin n))
    (sub : K U ⊆ S) (odd : (Z ∩ U).card % 2 = 1) :
    ¬ ∃ a, a ⊆ Finset.univ \ S ∧ B a = Z := by
  rintro ⟨a, allowed, eq⟩
  have zero : a ∩ K U = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i h
    obtain ⟨ia,ik⟩ := Finset.mem_inter.mp h
    exact (Finset.mem_sdiff.mp (allowed ia)).2 (sub ik)
  have h := par a U
  rw [eq,odd,zero,Finset.card_empty] at h
  omega

theorem charge_parity_disagree {α : Type*} [DecidableEq α]
    (d e U : Finset α) :
    ((d ∆ e) ∩ U).card % 2 = 1 ↔
      (d ∩ U).card % 2 ≠ (e ∩ U).card % 2 := by
  rw [sx_inter,sx_parity]
  omega


end Worker1133Dual

namespace Worker1133Dual
open Local1133Core
open scoped symmDiff

variable {m n : ℕ}

private theorem crossingMem (u v : Fin m → Fin n) (U : Finset (Fin n)) (i : Fin m) :
    i ∈ crossing u v U ↔ ((u i ∈ U ∧ v i ∉ U) ∨ (v i ∈ U ∧ u i ∉ U)) := by
  by_cases hu : u i ∈ U <;> by_cases hv : v i ∈ U <;> simp [crossing,hu,hv]

theorem allowed_iff_disjoint {S z : Finset (Fin m)} :
    z ⊆ Finset.univ \ S ↔ Disjoint z S := by
  rw [Finset.disjoint_left]
  constructor
  · intro h i hi
    exact (Finset.mem_sdiff.mp (h hi)).2
  · intro h i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h hi⟩


theorem shiftOrCut (u v : Fin m → Fin n) (S : Finset (Fin m)) (D E : Finset (Fin n)) :
    (∃ z, Disjoint z S ∧ boundary u v z = flip D E) ∨
    (∃ U : Finset (Fin n), crossing u v U ⊆ S ∧ (D∩U).card % 2 ≠ (E∩U).card % 2) := by
  classical
  by_cases h : ∃ z, Disjoint z S ∧ boundary u v z = flip D E
  · exact Or.inl h
  · have none : ¬ ∃ z, z ⊆ Finset.univ \ S ∧ boundary u v z = flip D E := by
      rintro ⟨z,s,e⟩
      exact h ⟨z,allowed_iff_disjoint.mp s,e⟩
    obtain ⟨U,sub,odd⟩ := separator u v (boundary u v) (crossing u v)
      (boundary_empty u v) (boundary_flip u v) (boundary_singleton u v)
      (crossingMem u v) (boundary_parity u v) S (flip D E) none
    exact Or.inr ⟨U,sub,(charge_parity_disagree D E U).mp odd⟩

theorem noShiftOfCut (u v : Fin m → Fin n) (S : Finset (Fin m)) (D E U : Finset (Fin n))
    (sub : crossing u v U ⊆ S) (different : (D∩U).card % 2 ≠ (E∩U).card % 2) :
    ¬ ∃ z, Disjoint z S ∧ boundary u v z = flip D E := by
  rintro ⟨z,h,e⟩
  exact obstructed (boundary u v) (crossing u v) (boundary_parity u v) S (flip D E) U sub
    ((charge_parity_disagree D E U).mpr different) ⟨z,allowed_iff_disjoint.mpr h,e⟩

end Worker1133Dual

namespace Worker1133Dual
open Local1133Core Local1133Formula

variable {m n : ℕ}


theorem shift_noSep (u v : Fin m → Fin n) (T S : Finset (Fin m)) (D E : Finset (Fin n)) (k : ℕ)
    (none : ¬ separates u v T D E k) (st : S ⊆ T) (size : S.card ≤ k) :
    ∃ z, Disjoint z S ∧ boundary u v z = flip D E := by
  rcases shiftOrCut u v S D E with h | ⟨U, sub, hneq⟩
  · exact h
  · exact (none ⟨U,sub.trans st,(Finset.card_le_card sub).trans size,hneq⟩).elim


theorem equal_counts_noSep (u v : Fin m → Fin n) (T : Finset (Fin m)) (D E : Finset (Fin n))
    (t w : ℕ) (F : Finset (Clause m)) (form : valid T t w F)
    (none : ¬ separates u v T D E (t*w)) :
    total u v D F = total u v E F := by
  obtain ⟨sub,sz⟩ := support_ok form
  obtain ⟨z,dis,eq⟩ := shift_noSep u v T (support F) D E (t*w) none sub sz
  exact count_shift u v D E F z dis eq

end Worker1133Dual

namespace Local1133Witness
open Local1133Core Local1133Formula
variable {n m : ℕ}

def CanShift (u v : Fin m→Fin n) (T : Finset (Fin m)) (D E : Finset (Fin n)) (k : ℕ) : Prop :=
  ∀ S⊆T,S.card≤k → ∃ z : Finset (Fin m), Disjoint z S ∧ boundary u v z=flip D E

theorem shift_sat {u v : Fin m→Fin n} {T : Finset (Fin m)} {D E : Finset (Fin n)}
    {t w : ℕ} {F : Finset (Clause m)}
    (vf : valid T t w F) (available : CanShift u v T D E t) :
    0<total u v D F → 0<total u v E F := by
  classical
  intro a
  obtain ⟨x,xd,xf⟩ := positive_total.mp a
  have selection (c : {q // q∈F}) : ∃ l∈c.val,decide (l.1∈x)=l.2 := xf c.val c.property
  choose pick cpick lpick using selection
  let S := F.attach.image (fun q => (pick q).1)
  have sT : S⊆T := by
    intro i im
    obtain ⟨c,_,cz⟩ := Finset.mem_image.mp im
    exact cz ▸ (vf.2 c.val c.property).2 (pick c) (cpick c)
  have sc : S.card≤t := by
    have k := Finset.card_image_le (s:=F.attach) (f:=fun q => (pick q).1)
    rw [Finset.card_attach] at k
    exact k.trans vf.1
  obtain ⟨z,dj,zd⟩ := available S sT sc
  refine positive_total.mpr ⟨flip x z,translate xd zd,?_⟩
  intro c cf
  let cc : {q // q∈F} := ⟨c,cf⟩
  have there : (pick cc).1∈S := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
  have eq := mem_bool (same_at (x:=x) dj) _ there
  exact ⟨pick cc,cpick cc,eq.symm.trans (lpick cc)⟩

theorem cannot_agree {u v : Fin m→Fin n} {D E U : Finset (Fin n)} {x y : Finset (Fin m)}
    (xd : boundary u v x=D) (ye : boundary u v y=E)
    (par : (D∩U).card % 2≠(E∩U).card % 2) :
    ¬ Agrees (crossing u v U) x y := by
  intro a
  have e : x∩crossing u v U=y∩crossing u v U := by
    ext i
    simp only [Finset.mem_inter]
    exact ⟨fun ⟨a1,a2⟩ => ⟨(a i a2).mp a1,a2⟩,
      fun ⟨a1,a2⟩ => ⟨(a i a2).mpr a1,a2⟩⟩
  apply par
  rw [←xd,←ye,boundary_parity,boundary_parity,e]

def units (S x : Finset (Fin m)) : Finset (Clause m) :=
  S.image (fun i => {(i,decide (i∈x))})

theorem unit_valid {S T x : Finset (Fin m)} {t w : ℕ} (ss : S⊆T) (st : S.card≤t)
    (wh : 0<w) :
    valid T t w (units S x) ∧ ∀ C∈units S x,C.card=1 := by
  constructor
  · constructor
    · exact Finset.card_image_le.trans st
    · intro C h
      obtain ⟨i,ii,e⟩ := Finset.mem_image.mp h
      subst C
      refine ⟨by simpa using Nat.succ_le_of_lt wh,?_⟩
      intro l li
      obtain rfl := Finset.mem_singleton.mp li
      exact ss ii
  · intro C h
    obtain ⟨i,ii,rfl⟩ := Finset.mem_image.mp h
    simp

theorem unit_agrees (S x y : Finset (Fin m)) :
    (∀ C∈units S x,holds y C) ↔ Agrees S x y := by
  constructor
  · intro h i im
    obtain ⟨l,lm,lv⟩ := h _ (Finset.mem_image_of_mem _ im)
    obtain rfl := Finset.mem_singleton.mp lm
    change decide (i∈y)=decide (i∈x) at lv
    simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp lv.symm
  · intro a C h
    obtain ⟨i,im,rfl⟩ := Finset.mem_image.mp h
    exact ⟨(i,decide (i∈x)),Finset.mem_singleton_self _,(mem_bool a _ im).symm⟩

theorem directed {u v : Fin m→Fin n} {D E : Finset (Fin n)} {T : Finset (Fin m)} {t w : ℕ}
    (wh : 0<w) (feas : ∃ x,boundary u v x=D) (s : separates u v T D E t) :
    ∃ F : Finset (Clause m),valid T t w F ∧ (∀ C∈F,C.card=1) ∧
      0<total u v D F ∧ total u v E F=0 := by
  obtain ⟨x,xd⟩ := feas
  obtain ⟨U,ut,uc,up⟩ := s
  let S := crossing u v U
  have val := unit_valid (x:=x) ut uc wh
  refine ⟨units S x,val.1,val.2,?_,?_⟩
  · exact positive_total.mpr ⟨x,xd,(unit_agrees S x x).mpr (fun _ _ => Iff.rfl)⟩
  · apply zero_total
    rintro ⟨y,ye,yy⟩
    exact cannot_agree xd ye up ((unit_agrees S x y).mp yy)

theorem count_witness {u v : Fin m→Fin n} {T : Finset (Fin m)} {D E : Finset (Fin n)} {t w : ℕ}
    (feas : ∃ x,boundary u v x=D) (s : separates u v T D E (t*w)) :
    ∃ F : Finset (Clause m),valid T t w F ∧ total u v D F≠total u v E F := by
  classical
  obtain ⟨x,xd⟩ := feas
  obtain ⟨U,ut,uc,up⟩ := s
  let S := crossing u v U
  let p := fun i : Fin m => decide (i∈x)
  let A := rows u v D
  let B := rows u v E
  have on : x∈Worker1133Counting.pinRows A S p :=
    Worker1133Counting.mem_pinRows.mpr ⟨mem_rows.mpr xd,fun _ _ => rfl⟩
  have off : Worker1133Counting.pinRows B S p=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y h
    obtain ⟨ye,hy⟩ := Worker1133Counting.mem_pinRows.mp h
    apply cannot_agree xd (mem_rows.mp ye) up
    intro i im
    have a := hy i im
    have iff := Bool.eq_iff_iff.mp a.symm
    simpa [p] using iff
  have z := Finset.card_pos.mpr ⟨x,on⟩
  have ne : (Worker1133Counting.pinRows A S p).card≠(Worker1133Counting.pinRows B S p).card := by
    rw [off,Finset.card_empty]
    omega
  obtain ⟨F,validW,neqW⟩ := Worker1133Counting.count_witness T S p t w A B ut uc ne
  have agree (R : Finset (Fin n)) :
      Worker1133Counting.countCnf (rows u v R) F=total u v R F := by
    unfold Worker1133Counting.countCnf total
    apply congrArg Finset.card
    exact Finset.filter_congr_decidable _ (fun y => ∀ C∈F, holds y C) _
  refine ⟨F,validW,fun h => neqW ?_⟩
  exact (agree D).trans (h.trans (agree E).symm)

end Local1133Witness

namespace Local1133Main
open Local1133Core Local1133Formula Local1133Witness
variable {n m : ℕ}

theorem symm {u v : Fin m→Fin n} {T : Finset (Fin m)} {D E : Finset (Fin n)} {k : ℕ} :
    separates u v T D E k → separates u v T E D k := by
  rintro ⟨U,S,z,h⟩
  exact ⟨U,S,z,h.symm⟩

theorem result (u v : Fin m→Fin n) (T : Finset (Fin m)) (t w : ℕ) (wh : 0<w)
    (D E : Finset (Fin n)) (hd : ∃ x,boundary u v x=D) :
    ((∃ F,valid T t w F ∧ ¬ (0<total u v D F ↔ 0<total u v E F)) ↔ separates u v T D E t) ∧
    ((∃ F,valid T t w F ∧ total u v D F≠total u v E F) ↔ separates u v T D E (t*w)) ∧
    (separates u v T D E t → ∃ F,valid T t w F ∧ (∀ C∈F,C.card=1) ∧
      0<total u v D F ∧ total u v E F=0) := by
  classical
  refine ⟨⟨?_,?_⟩,⟨?_,count_witness hd⟩,directed wh hd⟩
  · rintro ⟨F,fv,h⟩
    by_contra none
    have none' : ¬ separates u v T E D t := fun e => none (symm e)
    have dE : CanShift u v T D E t := fun S st sc =>
      Worker1133Dual.shift_noSep u v T S D E t none st sc
    have eD : CanShift u v T E D t := fun S st sc =>
      Worker1133Dual.shift_noSep u v T S E D t none' st sc
    exact h ⟨shift_sat fv dE,shift_sat fv eD⟩
  · intro sep
    obtain ⟨F,fv,fu,fd,fe⟩ := directed wh hd sep
    exact ⟨F,fv,fun h => by have a := h.mp fd; omega⟩
  · rintro ⟨F,fv,h⟩
    by_contra none
    exact h (Worker1133Dual.equal_counts_noSep u v T D E t w F fv none)

theorem total_raw (u v : Fin m→Fin n) (D : Finset (Fin n)) (F : Finset (Clause m)) :
    total u v D F =
      ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => boundary u v x=D ∧ ∀ C∈F,holds x C)).card := by
  unfold total rows
  congr 1
  ext x
  exact ⟨fun h => by
    obtain ⟨a,b⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp a).2,b⟩,
    fun h => by
    obtain ⟨a,b,c⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨a,b⟩,c⟩⟩

end Local1133Main

end PEqualNP.Outside.L_lib_1133

theorem PEqualNP.Outside.L_lib_1133 :
∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)) (t w : Nat), 0 < w →
  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let crossing := fun (U : Finset (Fin n)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun i => decide (u i ∈ U) != decide (v i ∈ U))

  let Clause := Finset (Fin m × Bool)
  let holds := fun (x : Finset (Fin m)) (C : Clause) =>
    ∃ l ∈ C, decide (l.1 ∈ x) = l.2
  let valid := fun (F : Finset Clause) =>
    F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T

  let total := fun (d : Finset (Fin n)) (F : Finset Clause) =>
    (cube.filter (fun x => boundary x = d ∧ ∀ C ∈ F, holds x C)).card

  ∀ d e : Finset (Fin n), (∃ x ∈ cube, boundary x = d) →
    (∃ x ∈ cube, boundary x = e) →
    let separates := fun (k : Nat) => ∃ U ∈ vertices,
      crossing U ⊆ T ∧ (crossing U).card ≤ k ∧ (d ∩ U).card % 2 ≠ (e ∩ U).card % 2
    ((∃ F, valid F ∧ ¬ (0 < total d F ↔ 0 < total e F)) ↔ separates t) ∧
    ((∃ F, valid F ∧ total d F ≠ total e F) ↔ separates (t * w)) ∧
    (separates t → ∃ F, valid F ∧ (∀ C ∈ F, C.card = 1) ∧
      0 < total d F ∧ total e F = 0) := by
  intro n m u v T t w wh
  dsimp only
  intro D E hd he
  have H : ∃ x, PEqualNP.Outside.L_lib_1133.Local1133Core.boundary u v x=D := by
    obtain ⟨x,_,hx⟩ := hd
    exact ⟨x,hx⟩
  have answer := PEqualNP.Outside.L_lib_1133.Local1133Main.result u v T t w wh D E H
  simp only [PEqualNP.Outside.L_lib_1133.Local1133Main.total_raw,
    PEqualNP.Outside.L_lib_1133.Local1133Formula.valid,
    PEqualNP.Outside.L_lib_1133.Local1133Formula.holds,
    PEqualNP.Outside.L_lib_1133.Local1133Formula.separates,
    PEqualNP.Outside.L_lib_1133.Local1133Core.crossing,
    PEqualNP.Outside.L_lib_1133.Local1133Core.boundary,
    PEqualNP.Outside.L_lib_1133.Local1133Core.ends,
    Finset.mem_univ, true_and] at answer
  simp only [Finset.mem_univ, true_and]
  exact answer
