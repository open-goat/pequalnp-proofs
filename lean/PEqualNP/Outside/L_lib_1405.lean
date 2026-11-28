import Mathlib

namespace PEqualNP.Outside.L_lib_1405_aux.Decomposition.Interface
namespace Poset

theorem matchUp {r q : Nat} (S : Finset (Finset (Fin r)))
    (width : ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q) :
    ∃ f : ↥S → (↥S ⊕ Fin q), Function.Injective f ∧
      ∀ x y : ↥S, f x = Sum.inl y → x.val ⊂ y.val := by
  classical
  let higher := fun x : ↥S => Finset.univ.filter (fun y : ↥S => x.val ⊂ y.val)
  let choices := fun x : ↥S => (higher x).disjSum (Finset.univ : Finset (Fin q))
  obtain ⟨f, inj, good⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp (by
    intro u
    rcases u.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · simp
    let above := u.biUnion higher
    let mins := u \ above
    let actual := mins.image Subtype.val
    have inS : actual ⊆ S := by
      intro x hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      exact a.property
    have anti : ∀ x ∈ actual, ∀ y ∈ actual, x ⊆ y → x = y := by
      intro x hx y hy le
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      by_contra hne
      have lt : a.val ⊂ b.val := lt_of_le_of_ne le hne
      have hab : b ∈ above := Finset.mem_biUnion.mpr
        ⟨a,(Finset.mem_sdiff.mp ha).1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩⟩
      exact (Finset.mem_sdiff.mp hb).2 hab
    have cm : mins.card ≤ q := by
      simpa [actual, Finset.card_image_of_injective _ Subtype.val_injective] using width actual inS anti
    have cu : u ⊆ mins ∪ above := by
      intro x mem
      by_cases h : x ∈ above
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨mem,h⟩)
    have right : above.disjSum (Finset.univ : Finset (Fin q)) ⊆ u.biUnion choices := by
      intro z hz
      cases z with
      | inl y =>
        have hy : y ∈ above := by simpa using hz
        obtain ⟨x,hx,hm⟩ := Finset.mem_biUnion.mp hy
        exact Finset.mem_biUnion.mpr ⟨x,hx,by simpa [choices] using hm⟩
      | inr j => exact Finset.mem_biUnion.mpr ⟨w,hw,by simp [choices]⟩
    have h1 := Finset.card_le_card cu
    have h2 := Finset.card_union_le mins above
    have h3 := Finset.card_le_card right
    rw [Finset.card_disjSum,Finset.card_univ,Fintype.card_fin] at h3
    omega)
  refine ⟨f,inj,?_⟩
  intro x y eq
  have mem := good x
  rw [eq] at mem
  have higher_mem : y ∈ higher x := by simpa [choices] using mem
  exact (Finset.mem_filter.mp higher_mem).2

noncomputable def prev {X Y : Type} (f : X → X ⊕ Y) (z : X ⊕ Y) : Option X := by
  classical
  exact if h : ∃ x, f x = z then some h.choose else none

theorem prev_eq_some {X Y : Type} {f : X → X ⊕ Y} (inj : Function.Injective f)
    (z : X ⊕ Y) (x : X) : prev f z = some x ↔ f x = z := by
  classical
  unfold prev
  split <;> rename_i h
  · constructor
    · intro eq
      rw [← Option.some.inj eq]
      exact h.choose_spec
    · intro eq
      exact congrArg some (inj (h.choose_spec.trans eq.symm))
  · simp only [reduceCtorEq, false_iff]
    exact fun eq => h ⟨x,eq⟩

noncomputable def predAt {X Y : Type} (f : X → X ⊕ Y) (j : Y) : Nat → Option X
  | 0 => prev f (.inr j)
  | n + 1 => (predAt f j n).bind (fun x => prev f (.inl x))

theorem all_on_path {r q : Nat} {S : Finset (Finset (Fin r))}
    (f : ↥S → (↥S ⊕ Fin q)) (inj : Function.Injective f)
    (greater : ∀ x y : ↥S, f x = .inl y → x.val ⊂ y.val) (x : ↥S) :
    ∃ (j : Fin q) (n : Nat), predAt f j n = some x := by
  classical
  suffices ∀ k (x : ↥S), r - x.val.card = k → ∃ j n, predAt f j n = some x by exact this _ x rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro x hx
    cases eq : f x with
    | inr j => exact ⟨j,0,(prev_eq_some inj _ _).mpr eq⟩
    | inl y =>
      have hxy := Finset.card_lt_card (greater x y eq)
      have hy : y.val.card ≤ r := by simpa using Finset.card_le_univ y.val
      obtain ⟨j,n,at_y⟩ := ih (r-y.val.card) (by omega) y rfl
      refine ⟨j,n+1,?_⟩
      rw [predAt,at_y]
      exact (prev_eq_some inj _ _).mpr eq

theorem same_path_subset {r q : Nat} {S : Finset (Finset (Fin r))}
    (f : ↥S → (↥S ⊕ Fin q)) (inj : Function.Injective f)
    (greater : ∀ x y : ↥S, f x = .inl y → x.val ⊂ y.val) (j : Fin q)
    {i k : Nat} (le : i ≤ k) {x y : ↥S}
    (hx : predAt f j i = some x) (hy : predAt f j k = some y) : y.val ⊆ x.val := by
  induction le generalizing y with
  | refl =>
    have eq : x = y := Option.some.inj (hx.symm.trans hy)
    exact eq ▸ Finset.Subset.refl _
  | @step k _ ih =>
    obtain ⟨z,hz,hm⟩ := Option.bind_eq_some_iff.mp hy
    have fy : f y = .inl z := (prev_eq_some inj _ _).mp hm
    exact le_trans (le_of_lt (greater y z fy)) (ih hz)

theorem width_colors {r q : Nat} (S : Finset (Finset (Fin r)))
    (width : ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q) :
    ∃ color : ↥S → Fin q, ∀ x y : ↥S, color x = color y → x.val ⊆ y.val ∨ y.val ⊆ x.val := by
  classical
  obtain ⟨f,inj,greater⟩ := matchUp S width
  choose color depth found using all_on_path f inj greater
  refine ⟨color,?_⟩
  intro x y eq
  have hx := found x
  have hy := found y
  rw [← eq] at hy
  rcases le_total (depth x) (depth y) with le | ge
  · exact Or.inr (same_path_subset f inj greater _ le hx hy)
  · exact Or.inl (same_path_subset f inj greater _ ge hy hx)

end Poset
end PEqualNP.Outside.L_lib_1405_aux.Decomposition.Interface

namespace PEqualNP.Outside.L_lib_1405_aux.Decomposition
open scoped Classical
variable {α : Type} [DecidableEq α]

def ChainData (s : Finset α) (I : Type) (low : I → ℕ) (cell : I → ℕ → Finset α) :=
  (∀ i, 2*low i ≤ s.card) ∧
  (∀ i k, low i ≤ k → k+low i ≤ s.card → cell i k ⊆ s ∧ (cell i k).card=k) ∧
  (∀ i k l, low i ≤ k → k ≤ l → l+low i ≤ s.card → cell i k ⊆ cell i l) ∧
  (∀ w ⊆ s, ∃ i, low i ≤ w.card ∧ w.card+low i ≤ s.card ∧ cell i w.card=w) ∧
  (∀ i j k, low i ≤ k → k+low i ≤ s.card → low j ≤ k → k+low j ≤ s.card →
    cell i k=cell j k → i=j)

def Chart (s : Finset α) := Σ I : Type, Fintype I ×
  (Σ low : I → ℕ, {cell : I → ℕ → Finset α // ChainData s I low cell})

namespace Chart
variable {s : Finset α} (B : Chart s)
abbrev Id := B.1
abbrev finite : Fintype B.Id := B.2.1
abbrev low : B.Id → ℕ := B.2.2.1
abbrev cell : B.Id → ℕ → Finset α := B.2.2.2.val
theorem valid : ∀ i, 2*B.low i ≤ s.card := B.2.2.2.property.1
theorem spec : ∀ i k, B.low i ≤ k → k+B.low i ≤ s.card →
    B.cell i k ⊆ s ∧ (B.cell i k).card=k := B.2.2.2.property.2.1
theorem grow : ∀ i k l, B.low i ≤ k → k ≤ l → l+B.low i ≤ s.card →
    B.cell i k ⊆ B.cell i l := B.2.2.2.property.2.2.1
theorem cover : ∀ w ⊆ s, ∃ i, B.low i ≤ w.card ∧ w.card+B.low i ≤ s.card ∧
    B.cell i w.card=w := B.2.2.2.property.2.2.2.1
theorem uniq : ∀ i j k, B.low i ≤ k → k+B.low i ≤ s.card → B.low j ≤ k → k+B.low j ≤ s.card →
    B.cell i k=B.cell j k → i=j := B.2.2.2.property.2.2.2.2
end Chart

private def oneChart : Chart (∅ : Finset α) := by
  refine ⟨Unit,inferInstance,fun _ => 0,fun _ _ => ∅,?_,?_,?_,?_,?_⟩
  · simp
  · simp
  · simp
  · intro w sub
    obtain rfl := Finset.subset_empty.mp sub
    exact ⟨(),by simp⟩
  · simp

variable {s : Finset α} (B : Chart s) (x : α)
private abbrev Side := B.Id ⊕ {i : B.Id // 2*B.low i < s.card}
private def sideLow : Side B → Nat
  | .inl i => B.low i
  | .inr i => B.low i.val+1
private def sideCell : Side B → Nat → Finset α
  | .inl i, k => if k+B.low i ≤ s.card then B.cell i k else insert x (B.cell i (k-1))
  | .inr i, k => insert x (B.cell i.val (k-1))

private theorem noOld (hx : x ∉ s) (i : B.Id) (k) (a : B.low i ≤ k) (b : k+B.low i ≤ s.card) :
    x ∉ B.cell i k := fun m => hx ((B.spec i k a b).1 m)

private theorem sideSpec (hx : x ∉ s) (i : Side B) (k) (a : sideLow B i ≤ k) (b : k+sideLow B i ≤ s.card+1) :
    sideCell B x i k ⊆ insert x s ∧ (sideCell B x i k).card=k := by
  cases i with
  | inl i =>
    change B.low i ≤ k at a
    change k+B.low i ≤ s.card+1 at b
    simp only [sideCell]
    split
    · rename_i z
      exact ⟨(B.spec i k a z).1.trans (Finset.subset_insert ..),(B.spec i k a z).2⟩
    · rename_i z
      have q := B.valid i
      have aa : B.low i ≤ k-1 := by omega
      have bb : k-1+B.low i ≤ s.card := by omega
      obtain ⟨sub,card⟩ := B.spec i _ aa bb
      exact ⟨Finset.insert_subset_insert _ sub,by rw [Finset.card_insert_of_notMem (noOld B x hx _ _ aa bb),card]; omega⟩
  | inr i =>
    change B.low i.val+1 ≤ k at a
    change k+(B.low i.val+1) ≤ s.card+1 at b
    have aa : B.low i.val ≤ k-1 := by omega
    have bb : k-1+B.low i.val ≤ s.card := by omega
    obtain ⟨sub,card⟩ := B.spec i.val _ aa bb
    exact ⟨Finset.insert_subset_insert _ sub,by
      change (insert x (B.cell i.val (k-1))).card=k
      rw [Finset.card_insert_of_notMem (noOld B x hx _ _ aa bb),card]; omega⟩

private theorem sideGrow (i : Side B) (k l) (a : sideLow B i ≤ k) (b : k ≤ l)
    (c : l+sideLow B i ≤ s.card+1) : sideCell B x i k ⊆ sideCell B x i l := by
  cases i with
  | inr i =>
    change B.low i.val+1 ≤ k at a
    change l+(B.low i.val+1) ≤ s.card+1 at c
    exact Finset.insert_subset_insert _ (B.grow _ _ _ (by omega) (by omega) (by omega))
  | inl i =>
    change B.low i ≤ k at a
    change l+B.low i ≤ s.card+1 at c
    by_cases zl : l+B.low i ≤ s.card
    · simp only [sideCell,if_pos zl,if_pos (by omega : k+B.low i ≤ s.card)]
      exact B.grow _ _ _ a b zl
    · by_cases eq : k=l
      · subst l; rfl
      · have z : k+B.low i ≤ s.card := by omega
        simp only [sideCell,if_pos z,if_neg zl]
        exact (B.grow _ _ _ a (by omega) (by omega)).trans (Finset.subset_insert ..)

private theorem sideCover (w : Finset α) (sub : w ⊆ insert x s) :
    ∃ i, sideLow B i ≤ w.card ∧ w.card+sideLow B i ≤ s.card+1 ∧ sideCell B x i w.card=w := by
  by_cases mem : x∈w
  · let v := w.erase x
    have sv : v ⊆ s := by
      intro a ha
      obtain ⟨ne,hw⟩ := Finset.mem_erase.mp ha
      exact (Finset.mem_insert.mp (sub hw)).resolve_left ne
    obtain ⟨i,lo,hi,eq⟩ := B.cover v sv
    have card : w.card=v.card+1 := by dsimp [v]; rw [Finset.card_erase_of_mem mem]; have := Finset.card_pos.mpr ⟨_,mem⟩; omega
    have restore : insert x v=w := Finset.insert_erase mem
    by_cases top : v.card+B.low i=s.card
    · refine ⟨Sum.inl i,by change B.low i ≤ _; omega,by change _+B.low i ≤ _; omega,?_⟩
      simp [sideCell,card,show ¬v.card+1+B.low i ≤ s.card by omega,eq,restore]
    · have short : 2*B.low i < s.card := by omega
      refine ⟨Sum.inr ⟨i,short⟩,by change B.low i+1 ≤ _; omega,by change _+(B.low i+1) ≤ _; omega,?_⟩
      simp [sideCell,card,eq,restore]
  · have sw : w ⊆ s := by
      intro a ha
      exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun z => mem (z ▸ ha))
    obtain ⟨i,a,b,eq⟩ := B.cover w sw
    exact ⟨Sum.inl i,a,by change _+B.low i ≤ _; omega,by simp [sideCell,b,eq]⟩

private def parent : Side B → B.Id := Sum.elim id Subtype.val
private def added (i : Side B) (k : ℕ) : Prop := match i with
  | .inl j => ¬ k+B.low j ≤ s.card
  | .inr _ => True
private theorem sideOld (hx : x ∉ s) (i : Side B) (k) (lo : sideLow B i ≤ k) (hi : k+sideLow B i ≤ s.card+1) :
    let j := parent B i
    let m := if x ∈ sideCell B x i k then k-1 else k
    B.low j ≤ m ∧ m+B.low j ≤ s.card ∧
      (sideCell B x i k).erase x = B.cell j m ∧ (x∈sideCell B x i k ↔ added B i k) := by
  cases i with
  | inl i =>
    change B.low i ≤ k at lo
    change k+B.low i ≤ s.card+1 at hi
    by_cases z : k+B.low i ≤ s.card
    · simp [sideCell,z,noOld B x hx i k lo z,parent,added,Finset.erase_eq_of_notMem,lo]
    · have q := B.valid i
      have a : B.low i ≤ k-1 := by omega
      have b : k-1+B.low i ≤ s.card := by omega
      simp [sideCell,z,noOld B x hx i (k-1) a b,parent,added,a,b]
  | inr i =>
    change B.low i.val+1 ≤ k at lo
    change k+(B.low i.val+1) ≤ s.card+1 at hi
    have a : B.low i.val ≤ k-1 := by omega
    have b : k-1+B.low i.val ≤ s.card := by omega
    simp [sideCell,noOld B x hx i.val _ a b,parent,added,a,b]

private theorem sideUniq (hx : x ∉ s) (i j : Side B) k (il : sideLow B i ≤ k) (iu : k+sideLow B i ≤ s.card+1)
    (jl : sideLow B j ≤ k) (ju : k+sideLow B j ≤ s.card+1) (eq : sideCell B x i k=sideCell B x j k) :
    i=j := by
  obtain ⟨a,b,v,flag⟩ := sideOld B x hx i k il iu
  obtain ⟨a',b',v',flag'⟩ := sideOld B x hx j k jl ju
  rw [eq] at a b v flag
  have same := B.uniq _ _ _ a b a' b' (v.symm.trans v')
  have flags := flag.symm.trans flag'
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl same
    | inr j =>
      change i=j.val at same
      have notle : ¬k+B.low i ≤ s.card := flags.mpr trivial
      change k+(B.low j.val+1) ≤ s.card+1 at ju
      rw [same] at notle
      omega
  | inr i =>
    cases j with
    | inr j => exact congrArg Sum.inr (Subtype.ext same)
    | inl j =>
      change i.val=j at same
      have notle : ¬k+B.low j ≤ s.card := flags.mp trivial
      change k+(B.low i.val+1) ≤ s.card+1 at iu
      rw [←same] at notle
      omega

noncomputable def next (hx : x ∉ s) : Chart (insert x s) := by
  classical
  letI := B.finite
  refine ⟨Side B,inferInstanceAs (Fintype (B.Id ⊕ {i : B.Id // 2*B.low i < s.card})),
    sideLow B,sideCell B x,?_,?_,?_,?_,?_⟩
  ·
    intro i
    rw [Finset.card_insert_of_notMem hx]
    cases i with
    | inl i => have := B.valid i; change 2*B.low i ≤ _; omega
    | inr i => have := i.property; change 2*(B.low i.val+1) ≤ _; omega
  · simpa [Finset.card_insert_of_notMem hx] using sideSpec B x hx
  · simpa [Finset.card_insert_of_notMem hx] using sideGrow B x
  · simpa [Finset.card_insert_of_notMem hx] using sideCover B x
  · simpa [Finset.card_insert_of_notMem hx] using sideUniq B x hx

theorem chartExists (s : Finset α) : Nonempty (Chart s) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨oneChart⟩
  | insert a s ha ih => exact ⟨next ih.some a ha⟩
end PEqualNP.Outside.L_lib_1405_aux.Decomposition

namespace PEqualNP.Outside.L_lib_1405_aux.Decomposition
open scoped Classical
abbrev Wd (r : ℕ) := Finset (Fin r)
abbrev Grid (r : ℕ) := Chart (Finset.univ : Wd r)
variable {r : ℕ} (B : Grid r)
noncomputable def key (w : Wd r) : B.Id := (B.cover w (Finset.subset_univ _)).choose
theorem keySpec (w : Wd r) :
    B.low (key B w) ≤ w.card ∧ w.card+B.low (key B w) ≤ r ∧ B.cell (key B w) w.card=w := by
  simpa only [Finset.card_univ,Fintype.card_fin,key] using (B.cover w (Finset.subset_univ _)).choose_spec
theorem cellSpec (i : B.Id) (k : ℕ) (a : B.low i ≤ k) (b : k+B.low i ≤ r) :
    (B.cell i k).card=k ∧ key B (B.cell i k)=i := by
  have sz := (B.spec i k a (by simpa using b)).2
  have ⟨l,u,eq⟩ := keySpec B (B.cell i k)
  rw [sz] at l u eq
  exact ⟨sz,B.uniq _ i k l (by simpa using u) a (by simpa using b) eq⟩
theorem same_chain {x y : Wd r} (same : key B x=key B y) : x⊆y ∨ y⊆x := by
  obtain ⟨a,b,ex⟩ := keySpec B x
  obtain ⟨d,e,ey⟩ := keySpec B y
  rw [← same] at d e ey
  rcases le_total x.card y.card with lt|lt
  · apply Or.inl
    simpa only [ex,ey] using B.grow _ _ _ a lt (by simpa using e)
  · apply Or.inr
    simpa only [ex,ey] using B.grow _ _ _ d lt (by simpa using b)

def wdLayer (S : Finset (Wd r)) (k : ℕ) := S.filter (fun w => w.card=k)
noncomputable def idsAt (k : ℕ) : Finset B.Id := by
  classical
  letI := B.finite
  exact Finset.univ.filter fun i => B.low i ≤ k ∧ k+B.low i ≤ r
theorem in_ids {i k} : i ∈ idsAt B k ↔ B.low i ≤ k ∧ k+B.low i ≤ r := by
  classical
  simp [idsAt]
theorem layerImage (k : ℕ) : (idsAt B k).image (fun i => B.cell i k) = (Finset.univ : Wd r).powersetCard k := by
  ext x
  constructor
  · rintro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a,b⟩ := (in_ids B).mp hi
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(cellSpec B i k a b).1⟩
  · intro hx
    have card := (Finset.mem_powersetCard.mp hx).2
    obtain ⟨a,b,eq⟩ := keySpec B x
    rw [card] at a b eq
    exact Finset.mem_image.mpr ⟨key B x,(in_ids B).mpr ⟨a,b⟩,eq⟩
theorem idsCard (k : ℕ) : (idsAt B k).card=r.choose k := by
  have inj : ((idsAt B k : Finset B.Id) : Set B.Id).InjOn fun i => B.cell i k := by
    intro a ha b hb eq
    have aa := (in_ids B).mp ha
    have bb := (in_ids B).mp hb
    exact B.uniq _ _ k aa.1 (by simpa using aa.2) bb.1 (by simpa using bb.2) eq
  rw [← Finset.card_image_of_injOn inj,layerImage,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

def central (r p : ℕ) := Finset.Ico ((r+1-p)/2) ((r+1-p)/2+p)
def middle (r p : ℕ) : Finset (Wd r) := Finset.univ.filter (fun w => w.card ∈ central r p)
theorem centralCard : (central r p).card=p := by simp [central]
theorem centralSum (F : ℕ → ℕ) (p : ℕ) :
    (central r p).sum F = (Finset.range p).sum (fun j => F ((r+1-p)/2+j)) := by
  simp [central,Finset.sum_Ico_eq_sum_range,Nat.add_comm]

def Width (S : Finset (Wd r)) (q : ℕ) := ∀ U ⊆ S,
  (∀ x∈U, ∀ y∈U, x⊆y → x=y) → U.card ≤ q
def Height (S : Finset (Wd r)) (p : ℕ) := ∀ U ⊆ S,
  (∀ x∈U, ∀ y∈U, x⊆y ∨ y⊆x) → U.card ≤ p
theorem heightMiddle (p : ℕ) : Height (middle r p) p := by
  intro U sub ch
  have lim := Finset.card_le_card_of_injOn (s:=U) (t:=central r p) Finset.card
    (fun x hx => (Finset.mem_filter.mp (sub hx)).2) (by
      intro x hx y hy eq
      rcases ch x hx y hy with a|b
      · exact Finset.eq_of_subset_of_card_le a eq.ge
      · exact (Finset.eq_of_subset_of_card_le b eq.le).symm)
  simpa [centralCard] using lim

end PEqualNP.Outside.L_lib_1405_aux.Decomposition

namespace PEqualNP.Outside.L_lib_1405_aux.Decomposition
private theorem highest {β : Type*} [DecidableEq β] (c : β → ℕ) (p : ℕ) (B : Finset β)
    (hp : p ≤ B.card) : ∃ Q ⊆ B, Q.card = p ∧
    ∀ i ∈ Q, ∀ j ∈ B, j ∉ Q → c j ≤ c i := by
  induction p generalizing B with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ p ih =>
    obtain ⟨x,hx,hm⟩ := B.exists_max_image c (Finset.card_pos.mp (by omega))
    obtain ⟨Q,hQ,hc,hord⟩ := ih (B.erase x) (by rw [Finset.card_erase_of_mem hx]; omega)
    have hxQ : x ∉ Q := fun h => (Finset.mem_erase.mp (hQ h)).1 rfl
    refine ⟨insert x Q, Finset.insert_subset hx (hQ.trans (Finset.erase_subset ..)),
      by simp [hxQ,hc], ?_⟩
    intro i hi j hj hjQ
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hm j hj
    · exact hord i hi j (Finset.mem_erase.mpr ⟨fun e => hjQ (e ▸ Finset.mem_insert_self ..),hj⟩)
        (fun h => hjQ (Finset.mem_insert_of_mem h))

open scoped Classical
variable {r : ℕ} (B : Grid r)
private theorem chooseKeys (q : ℕ) :
    ∃ Q : Finset B.Id, Q.card ≤ q ∧ ∀ k, (Q ∩ idsAt B k).card = min q (r.choose k) := by
  classical
  letI := B.finite
  let allKeys : Finset B.Id := Finset.univ
  obtain ⟨Q,sub,sz,top⟩ := highest (fun i => r-B.low i) (min q allKeys.card) allKeys (Nat.min_le_right ..)
  refine ⟨Q,by omega,?_⟩
  intro k
  let A := idsAt B k
  have na : A.card=r.choose k := idsCard B k
  have cap : A.card ≤ allKeys.card := Finset.card_le_card (Finset.subset_univ _)
  by_cases all : Q ⊆ A
  · change (Q∩A).card=_
    rw [Finset.inter_eq_left.mpr all]
    have := Finset.card_le_card all
    omega
  · obtain ⟨i,hi,notIn⟩ := Finset.not_subset.mp all
    have rev : A ⊆ Q := by
      intro j hj
      by_contra no
      have order := top i hi j (Finset.mem_univ _) no
      have b₁ : 2*B.low i ≤ r := by simpa using B.valid i
      have b₂ : 2*B.low j ≤ r := by simpa using B.valid j
      have ⟨l,u⟩ := (in_ids B).mp hj
      exact notIn ((in_ids B).mpr ⟨by omega,by omega⟩)
    have := Finset.card_le_card rev
    change (Q∩A).card=_
    rw [Finset.inter_eq_right.mpr rev]
    omega

theorem lowerFamily (B : Grid r) (q p : ℕ) :
    ∃ S : Finset (Wd r), S.card=(Finset.range p).sum (fun j => min q (r.choose ((r+1-p)/2+j))) ∧
      Width S q ∧ Height S p := by
  classical
  obtain ⟨Q,cap,byRank⟩ := chooseKeys B q
  let S := (middle r p).filter (fun w => key B w ∈ Q)
  have form (k) (hk : k ∈ central r p) :
      wdLayer S k = (Q∩idsAt B k).image (fun i => B.cell i k) := by
    ext w
    constructor
    · intro hw
      obtain ⟨wS,eq⟩ := Finset.mem_filter.mp hw
      have selected := (Finset.mem_filter.mp wS).2
      obtain ⟨a,b,cell⟩ := keySpec B w
      rw [eq] at a b cell
      exact Finset.mem_image.mpr ⟨key B w,Finset.mem_inter.mpr ⟨selected,(in_ids B).mpr ⟨a,b⟩⟩,cell⟩
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hi,active⟩ := Finset.mem_inter.mp hi
      obtain ⟨l,u⟩ := (in_ids B).mp active
      obtain ⟨card,keyeq⟩ := cellSpec B i k l u
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,card.symm ▸ hk⟩,keyeq.symm ▸ hi⟩,card⟩
  have pop (k) (hk : k∈central r p) : (wdLayer S k).card=min q (r.choose k) := by
    rw [form k hk,Finset.card_image_of_injOn]
    · exact byRank k
    · intro i hi j hj eq
      have a := (in_ids B).mp (Finset.mem_inter.mp hi).2
      have b := (in_ids B).mp (Finset.mem_inter.mp hj).2
      exact B.uniq _ _ k a.1 (by simpa using a.2) b.1 (by simpa using b.2) eq
  have within {w} (hw : w∈S) : w.card ∈ central r p := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
  have total := Finset.sum_card_fiberwise_eq_card_filter S (central r p) Finset.card
  rw [Finset.filter_true_of_mem (fun w hw => within hw)] at total
  refine ⟨S,?_,?_,?_⟩
  · calc
      _ = (central r p).sum (fun k => (wdLayer S k).card) := total.symm
      _ = _ := (Finset.sum_congr rfl pop).trans (centralSum _ p)
  · intro U sub anti
    apply le_trans (Finset.card_le_card_of_injOn (s:=U) (t:=Q) (key B)
      (fun x hx => (Finset.mem_filter.mp (sub hx)).2) ?_) cap
    intro x hx y hy eq
    rcases same_chain B eq with le|ge
    · exact anti x hx y hy le
    · exact (anti y hy x hx ge).symm
  · intro U sub ch
    exact heightMiddle p U (sub.trans (Finset.filter_subset ..)) ch
end PEqualNP.Outside.L_lib_1405_aux.Decomposition

namespace PEqualNP.Outside.L_lib_1405_aux
abbrev Word (r : ℕ) := Finset (Fin r)
variable {r : ℕ}

def Comparable (U : Finset (Word r)) := ∀ A∈U, ∀ B∈U, A ⊆ B ∨ B ⊆ A
def Walk (r : ℕ) := Fin (r+1) → Word r
def Ranked (f : Walk r) := Monotone f ∧ ∀ j, (f j).card = j.val

private theorem extendPartial (U : Finset (Word r)) (chain : Comparable U) (n : ℕ) (hn : n ≤ r) :
    ∃ f : ℕ → Word r, Monotone f ∧ (∀ j ≤ n,(f j).card=j) ∧
      ∀ A∈U, ∀ j ≤ n, (j ≤ A.card → f j ⊆ A) ∧ (A.card ≤ j → A ⊆ f j) := by
  classical
  induction n with
  | zero =>
    exact ⟨fun _ => ∅,fun _ _ _ => le_rfl,by simp,by
      intro A h j hj
      obtain rfl : j=0 := by omega
      simp⟩
  | succ n ih =>
    obtain ⟨f,mono,sz,rel⟩ := ih (by omega)
    let big := (insert (Finset.univ : Word r) U).filter (fun A => n < A.card)
    have bigTop : (Finset.univ : Word r) ∈ big := by simp [big,show n<r by omega]
    obtain ⟨B,memB,minB⟩ := big.exists_min_image Finset.card ⟨_,bigTop⟩
    have bsz := (Finset.mem_filter.mp memB).2
    have first {A : Word r} (ha : A∈U) (more : n < A.card) : B ⊆ A := by
      have least := minB A (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem ha,more⟩)
      rcases Finset.mem_insert.mp (Finset.mem_filter.mp memB).1 with top|hb
      · exact (Finset.eq_of_subset_of_card_le (top ▸ Finset.subset_univ A) least).symm.le
      · rcases chain B hb A ha with ba|ab
        · exact ba
        · exact (Finset.eq_of_subset_of_card_le ab least).symm.le
    have diff : ¬B ⊆ f n := by
      intro sub
      have := Finset.card_le_card sub
      rw [sz n le_rfl] at this
      omega
    obtain ⟨x,hx,fresh⟩ := Finset.not_subset.mp diff
    let g (j : ℕ) := if j≤n then f j else insert x (f n)
    have gs : (insert x (f n)).card=n+1 := by rw [Finset.card_insert_of_notMem fresh,sz n le_rfl]
    refine ⟨g,?_,?_,?_⟩
    · intro i j le
      by_cases h : j≤n
      · simpa [g,h,le.trans h] using mono le
      · by_cases hi : i≤n
        · simpa [g,hi,h] using (mono hi).trans (Finset.subset_insert x (f n))
        · simp [g,h,hi]
    · intro j hj
      by_cases h : j≤n
      · simpa [g,h] using sz j h
      · obtain rfl : j=n+1 := by omega
        simpa [g] using gs
    · intro A ha j hj
      by_cases h : j≤n
      · simpa [g,h] using rel A ha j h
      · obtain rfl : j=n+1 := by omega
        simp only [g, Nat.not_succ_le_self,ite_false]
        have up (more : n+1 ≤ A.card) : insert x (f n) ⊆ A :=
          Finset.insert_subset (first ha more hx) ((rel A ha n le_rfl).1 (by omega))
        refine ⟨up,fun le => ?_⟩
        by_cases small : A.card ≤ n
        · exact ((rel A ha n le_rfl).2 small).trans (Finset.subset_insert ..)
        · exact (Finset.eq_of_subset_of_card_le (up (by omega)) (gs ▸ le)).symm.le

theorem fullWalk (U : Finset (Word r)) (ch : Comparable U) :
    ∃ f : Walk r, Ranked f ∧ ∀ A∈U, ∀ j, A.card=j.val → f j=A := by
  obtain ⟨f,mon,sz,rel⟩ := extendPartial U ch r le_rfl
  refine ⟨fun j => f j.val,⟨fun _ _ h => mon h,fun j => sz _ (by omega)⟩,?_⟩
  intro A hA j eq
  exact Finset.eq_of_subset_of_card_le ((rel A hA j.val (by omega)).1 eq.ge)
    (by rw [sz _ (by omega),eq])
end PEqualNP.Outside.L_lib_1405_aux

namespace PEqualNP.Outside.L_lib_1405_aux
variable {r : ℕ}
def lowFlip (f : Walk r) (k j : Fin (r+1)) : Word r :=
  if j<k then f k \ f ⟨k.val-j.val,by omega⟩ else f j

theorem flipRanked {f : Walk r} (hf : Ranked f) (k : Fin (r+1)) : Ranked (lowFlip f k) := by
  obtain ⟨mono,sz⟩ := hf
  constructor
  · intro i j le
    by_cases jlow : j<k
    · have ilow := lt_of_le_of_lt le jlow
      simp only [lowFlip,ilow,jlow,ite_true]
      apply Finset.sdiff_subset_sdiff (by rfl)
      apply mono
      change k.val-j.val ≤ k.val-i.val
      exact Nat.sub_le_sub_left le _
    · by_cases ilow : i<k
      · simp only [lowFlip,ilow,jlow,ite_true,ite_false]
        exact (Finset.sdiff_subset).trans (mono (le_of_not_gt jlow))
      · simpa [lowFlip,ilow,jlow] using mono le
  · intro j
    by_cases h : j<k
    · simp only [lowFlip,h,ite_true]
      rw [Finset.card_sdiff_of_subset (mono (a:=⟨k.val-j.val,by omega⟩) (b:=k) (by change k.val-j.val ≤ k.val; omega)),sz,sz]
      have := j.isLt
      change k.val-(k.val-j.val)=j.val
      omega
    · simp [lowFlip,h,sz]

theorem flipDifferent {f : Walk r} (hf : Ranked f) {k j : Fin (r+1)} (hj : 0<j.val) (jk : j<k) :
    f j ≠ lowFlip f k j := by
  let one : Fin (r+1) := ⟨1,by omega⟩
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(f one).card by rw [hf.2]; exact Nat.zero_lt_one)
  have xj := hf.1 (show one≤j from hj) hx
  have xd := hf.1 (show one≤(⟨k.val-j.val,by omega⟩ : Fin (r+1)) by change 1≤k.val-j.val; omega) hx
  intro eq
  rw [eq] at xj
  simp only [lowFlip,jk,ite_true,Finset.mem_sdiff] at xj
  exact xj.2 xd

def dual (f : Walk r) (j : Fin (r+1)) : Word r := (f j.rev)ᶜ

theorem dualRanked {f : Walk r} (hf : Ranked f) : Ranked (dual f) := by
  constructor
  · intro i j le
    exact Finset.compl_subset_compl.mpr (hf.1 (Fin.rev_le_rev.mpr le))
  · intro j
    simp [dual,Finset.card_compl,hf.2,Fin.rev]
    omega

theorem pairWalk {f : Walk r} (hf : Ranked f) (k : Fin (r+1)) (hk : k≤k.rev) :
    ∃ g : Walk r, Ranked g ∧ (∀ j,k≤j → j≤k.rev → f j=g j) ∧
      ∀ j, 0<j.val → j.val<r → (j<k ∨ k.rev<j) → f j ≠ g j := by
  let h := lowFlip f k
  let g := dual (lowFlip (dual h) k)
  have same (j : Fin (r+1)) (hj : j≤k.rev) : g j=h j := by
    have a : ¬j.rev<k := not_lt.mpr (by simpa using Fin.rev_le_rev.mpr hj)
    simp [g,dual,lowFlip,a]
  refine ⟨g,dualRanked (flipRanked (dualRanked (flipRanked hf k)) k),?_,?_⟩
  · intro j lo hi
    rw [same j hi]
    simp [h,lowFlip,not_lt.mpr lo]
  · intro j pos lt interior
    rcases interior with low|high
    · rw [same j (low.le.trans hk)]
      exact flipDifferent hf pos low
    · have jhi : ¬j<k := not_lt.mpr (hk.trans high.le)
      have eq : f j = h j := by simp [h,lowFlip,jhi]
      have revlt : j.rev < k := by simpa using Fin.rev_lt_rev.mpr high
      have revpos : 0<j.rev.val := by simp [Fin.rev]; omega
      have diff := flipDifferent (dualRanked (flipRanked hf k)) revpos revlt
      intro samefg
      apply diff
      have e := congrArg (fun w : Word r => wᶜ) (eq.symm.trans samefg)
      simpa [g,dual] using e
end PEqualNP.Outside.L_lib_1405_aux

namespace PEqualNP.Outside.L_lib_1405_aux
variable {r : ℕ}
def Wide (S : Finset (Word r)) (q : ℕ) := ∀ U ⊆ S,
  (∀ x∈U, ∀ y∈U, x⊆y → x=y) → U.card ≤ q
def Tall (S : Finset (Word r)) (p : ℕ) := ∀ U ⊆ S, Comparable U → U.card ≤ p

theorem clippedWidth {S : Finset (Word r)} {q : ℕ} (h : Wide S q) : Wide S (min q (r.choose (r/2))) := by
  intro U sub anti
  apply le_min (h U sub anti)
  have ha : IsAntichain (· ⊆ ·) (U : Set (Word r)) :=
    fun _ hx _ hy ne le => ne (anti _ hx _ hy le)
  simpa using ha.sperner

theorem halfMono {i j : ℕ} (ij : i ≤ j) (jh : j ≤ r/2) : r.choose i ≤ r.choose j := by
  induction j, ij using Nat.le_induction with
  | base => rfl
  | succ n _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem centralWindow {q : ℕ} (hr : 2≤r) (hq : 2≤q) (qm : q≤r.choose (r/2)) :
    ∃ k : Fin (r+1), 0<k.val ∧ k≤k.rev ∧
      ∀ j : Fin (r+1), (q≤r.choose j.val ↔ k≤j ∧ j≤k.rev) := by
  classical
  have ex : ∃ i, i≤r/2 ∧ q≤r.choose i := ⟨r/2,le_rfl,qm⟩
  let n := Nat.find ex
  have spec : n≤r/2 ∧ q≤r.choose n := Nat.find_spec ex
  have pos : 0<n := by
    by_contra! z
    have ne : n=0 := by omega
    have := spec.2
    rw [ne,Nat.choose_zero_right] at this
    omega
  let k : Fin (r+1) := ⟨n,by omega⟩
  refine ⟨k,pos,?_,?_⟩
  · change n≤r+1-(n+1)
    omega
  · intro j
    let t := min j.val (r-j.val)
    have th : t≤r/2 := by dsimp [t]; omega
    have eq : r.choose t=r.choose j.val := by
      rcases le_total j.val (r-j.val) with le|ge
      · simp [t,min_eq_left le]
      · simp only [t,min_eq_right ge,Nat.choose_symm (show j.val ≤ r by omega)]
    have iff : q≤r.choose t ↔ n≤t := ⟨fun qt => Nat.find_min' ex ⟨th,qt⟩,fun nt => spec.2.trans (halfMono nt th)⟩
    rw [← eq,iff]
    change n ≤ min j.val (r-j.val) ↔ n≤j.val ∧ j.val≤r+1-(n+1)
    omega

def layer (S : Finset (Word r)) (j : ℕ) := S.filter (fun w => w.card=j)
def pop (S : Finset (Word r)) (j : ℕ) := (layer S j).card
def limit (r q j : ℕ) := min q (r.choose j)

theorem popLe {S : Finset (Word r)} {q : ℕ} (width : Wide S q) (j : ℕ) :
    pop S j ≤ limit r q j := by
  apply le_min
  · apply width _ (Finset.filter_subset ..)
    intro x hx y hy sub
    exact Finset.eq_of_subset_of_card_le sub (((Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hx).2.symm).le)
  · have sub : layer S j ⊆ (Finset.univ : Word r).powersetCard j := fun x hx =>
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(Finset.mem_filter.mp hx).2⟩
    simpa [pop] using Finset.card_le_card sub

theorem popSum (S : Finset (Word r)) : ∑ j : Fin (r+1),pop S j.val = S.card := by
  have maps (w : Word r) (_ : w∈S) : w.card ∈ Finset.range (r+1) :=
    Finset.mem_range.mpr (by have := Finset.card_le_univ w; simpa using Nat.lt_succ_of_le this)
  rw [Fin.sum_univ_eq_sum_range (pop S)]
  simpa only [pop,layer,Finset.filter_true_of_mem maps] using
    Finset.sum_card_fiberwise_eq_card_filter S (Finset.range (r+1)) Finset.card
end PEqualNP.Outside.L_lib_1405_aux

namespace PEqualNP.Outside.L_lib_1405_aux
variable {r : ℕ}
def miss (S : Finset (Word r)) (w : Word r) : ℕ := if w∈S then 0 else 1
theorem missEq (S : Finset (Word r)) (w : Word r) : miss S w = if w∉S then 1 else 0 := by
  by_cases h : w∈S <;> simp [miss,h]

def extra (S : Finset (Word r)) (j : Fin (r+1)) : ℕ :=
  (if j.val=0 then miss S ∅ else 0) + (if j.val=r then miss S Finset.univ else 0)
def ends (S : Finset (Word r)) := miss S ∅ + miss S Finset.univ

theorem sumExtra (S : Finset (Word r)) : ∑j,extra S j = ends S := by
  classical
  have last (j : Fin (r+1)) : j.val=r ↔ j=Fin.last r := by rw [Fin.ext_iff]; simp
  have zero (j : Fin (r+1)) : j.val=0 ↔ j=0 := by rw [Fin.ext_iff]; simp
  simp [extra,ends,Finset.sum_add_distrib,last,zero]

def hitIndices {ι : Type} [Fintype ι] (S : Finset (Word r)) (f : ι → Word r) := Finset.univ.filter (fun i => f i∈S)

theorem memHits {ι : Type} [Fintype ι] (S : Finset (Word r)) (f : ι → Word r) (i : ι) : i∈hitIndices S f ↔ f i∈S := by simp [hitIndices]

theorem sumMiss {ι : Type} [Fintype ι] (S : Finset (Word r)) (f : ι → Word r) :
    (∑i,miss S (f i)) = Fintype.card ι - (hitIndices S f).card := by
  classical
  calc
    _ = (Finset.univ.filter (fun i => f i∉S)).card := by
      simpa only [missEq,Nat.cast_id] using (Finset.sum_boole (R:=ℕ) (fun i => f i∉S) Finset.univ)
    _ = _ := by rw [hitIndices,Finset.filter_not,Finset.card_sdiff_of_subset (Finset.filter_subset ..),Finset.card_univ]

theorem missedOnWalk {S : Finset (Word r)} {p : ℕ} (height : Tall S p) {f : Walk r} (hf : Ranked f) :
    r+1-p ≤ ∑j,miss S (f j) := by
  classical
  let H := hitIndices S f
  have inj : Function.Injective f := fun x y eq => Fin.ext (by simpa only [hf.2] using congrArg Finset.card eq)
  have popBound : H.card ≤ p := by
    rw [← Finset.card_image_of_injective H inj]
    apply height
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      exact (memHits S f j).mp hj
    · intro x hx y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      rcases le_total i j with le|le
      · exact Or.inl (hf.1 le)
      · exact Or.inr (hf.1 le)
  have eq : ∑j,miss S (f j) = r+1-H.card := by
    simpa only [H,Fintype.card_fin] using (sumMiss (ι:=Fin (r+1)) S (fun (j : Fin (r+1)) => f j))
  omega

theorem missingPair {S : Finset (Word r)} {j : Fin (r+1)} {a b : Word r}
    (ha : a.card=j.val) (hb : b.card=j.val)
    (hd : 0<j.val → j.val<r → a≠b) :
    miss S a + miss S b ≤ r.choose j.val - pop S j.val + extra S j := by
  classical
  let Full := (Finset.univ : Word r).powersetCard j.val
  let D := Full \ layer S j.val
  have fullSub : layer S j.val ⊆ Full := fun w hw =>
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(Finset.mem_filter.mp hw).2⟩
  have dc : D.card=r.choose j.val-pop S j.val := by
    simp [D,Full,Finset.card_sdiff_of_subset fullSub,pop]
  have mem {w : Word r} (hw : w.card=j.val) (hn : w∉S) : w∈D :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hw⟩,fun h => hn (Finset.mem_filter.mp h).1⟩
  rw [←dc]
  by_cases ina : a∈S <;> by_cases inb : b∈S
  · simp [miss,ina,inb]
  · have := Finset.card_pos.mpr ⟨b,mem hb inb⟩
    simp only [miss,ina,inb,ite_true,ite_false]
    omega
  · have := Finset.card_pos.mpr ⟨a,mem ha ina⟩
    simp only [miss,ina,inb,ite_true,ite_false]
    omega
  · have one := Finset.card_pos.mpr ⟨a,mem ha ina⟩
    simp only [miss,ina,inb,ite_false]
    by_cases eq : a=b
    · by_cases z : j.val=0
      · have a0 : a=∅ := Finset.card_eq_zero.mp (ha.trans z)
        have no : (∅ : Word r)∉S := a0 ▸ ina
        simp [extra,miss,z,no]
        omega
      · have jr : j.val=r := by
          by_contra ne
          exact hd (by omega) (by omega) eq
        have au : a=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [ha,jr])
        have no : (Finset.univ : Word r)∉S := au ▸ ina
        simp [extra,miss,z,jr,no]
        omega
    · have two : ({a,b} : Finset (Word r)).card ≤ D.card :=
        Finset.card_le_card (Finset.insert_subset (mem ha ina) (Finset.singleton_subset_iff.mpr (mem hb inb)))
      simp [eq] at two
      omega

theorem centralMiss {S : Finset (Word r)} {q : ℕ} (F : Fin q → Walk r) (j : Fin (r+1))
    (color : ↥S → Fin q) (hit : ∀ w : ↥S, w.val.card=j.val → F (color w) j=w.val) :
    ∑ i,miss S (F i j) ≤ q-pop S j.val := by
  classical
  let H := hitIndices S (fun i => F i j)
  have bound : pop S j.val ≤ H.card := by
    let col (x : ↥(layer S j.val)) := color ⟨x.val,(Finset.mem_filter.mp x.property).1⟩
    have eval (x : ↥(layer S j.val)) : F (col x) j=x.val := hit _ (Finset.mem_filter.mp x.property).2
    have sz := Finset.card_le_card_of_injOn (s:=(layer S j.val).attach) (t:=H) col (by
      intro x _
      apply (memHits S _ _).mpr
      change F (col x) j∈S
      rw [eval x]
      exact (Finset.mem_filter.mp x.property).1) (by
      intro x _ y _ eq
      apply Subtype.ext
      rw [←eval x,←eval y,eq])
    simpa [pop] using sz
  have eq : ∑ i,miss S (F i j) = q-H.card := by
    simpa [H] using sumMiss S (fun i => F i j)
  omega
end PEqualNP.Outside.L_lib_1405_aux

namespace PEqualNP.Outside.L_lib_1405_aux
variable {r : ℕ}
def total (r q : ℕ) := (Finset.range (r+1)).sum (limit r q)
theorem deficitClipped {S : Finset (Word r)} {q p : ℕ} (width : Wide S q) (height : Tall S p)
    (hr : 2≤r) (hq : 2≤q) (qm : q≤r.choose (r/2)) :
    2*(r+1-p) ≤ (total r q - S.card)+ends S := by
  classical
  obtain ⟨k,_,hk,band⟩ := centralWindow hr hq qm
  obtain ⟨color,colChain⟩ := PEqualNP.Outside.L_lib_1405_aux.Decomposition.Interface.Poset.width_colors S width
  let U (i : Fin q) := (S.attach.filter (fun w => color w=i)).image (fun w => w.val)
  have comp (i) : Comparable (U i) := by
    intro A ha B hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    exact colChain x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  choose F ranked hits using fun i => fullWalk (U i) (comp i)
  choose G rankedG matchG diffG using fun i => pairWalk (ranked i) k hk
  have hit (w : ↥S) (j : Fin (r+1)) (eq : w.val.card=j.val) : F (color w) j=w.val :=
    hits _ _ (Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,rfl⟩,rfl⟩) j eq
  let cost (j : Fin (r+1)) := limit r q j.val - pop S j.val + extra S j
  let lost (i : Fin q) (j : Fin (r+1)) := miss S (F i j)+miss S (G i j)
  have low (i : Fin q) : 2*(r+1-p) ≤ ∑j,lost i j := by
    simpa only [two_mul,lost,Finset.sum_add_distrib] using
      Nat.add_le_add (missedOnWalk height (ranked i)) (missedOnWalk height (rankedG i))
  have high (j : Fin (r+1)) : ∑i,lost i j ≤ q*cost j := by
    by_cases inside : q≤r.choose j.val
    · have loc := (band j).mp inside
      have same (i) : F i j=G i j := matchG i j loc.1 loc.2
      have bound := centralMiss F j color (fun w eq => hit w j eq)
      have eq : ∑i,lost i j = 2*(∑i,miss S (F i j)) := by
        simp only [two_mul,lost,Finset.sum_add_distrib,←same]
      rw [eq]
      calc
        _ ≤ q*(q-pop S j.val) := Nat.mul_le_mul hq bound
        _ ≤ _ := Nat.mul_le_mul_left _ (by simp [cost,limit,min_eq_left inside])
    · have out : j<k ∨ k.rev<j := by
        have := mt (band j).mpr inside
        omega
      have cap : limit r q j.val =r.choose j.val := min_eq_right (by omega)
      have each (i) : lost i j ≤ cost j := by
        simpa only [lost,cost,cap] using missingPair (ranked i |>.2 j) (rankedG i |>.2 j)
          (fun a b => diffG i j a b out)
      simpa using (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => each i))
  have both : q*(2*(r+1-p)) ≤ q*∑j,cost j := by
    calc
      _ = ∑_i : Fin q,2*(r+1-p) := by simp
      _ ≤ ∑i,∑j,lost i j := Finset.sum_le_sum (fun i _ => low i)
      _ = ∑j,∑i,lost i j := Finset.sum_comm
      _ ≤ ∑j,q*cost j := Finset.sum_le_sum (fun j _ => high j)
      _ = _ := (Finset.mul_sum ..).symm
  have sumCost : ∑j,cost j=(total r q-S.card)+ends S := by
    rw [show (∑j,cost j) = _ from Finset.sum_add_distrib,Finset.sum_tsub_distrib Finset.univ (fun (j : Fin (r+1)) _ => popLe width j.val),popSum,sumExtra]
    rw [Fin.sum_univ_eq_sum_range (limit r q),total]
  rw [sumCost] at both
  exact Nat.le_of_mul_le_mul_left both (by omega)

theorem deficit {S : Finset (Word r)} {q p : ℕ} (width : Wide S q) (height : Tall S p)
    (hr : 2≤r) (hq : 2≤q) : 2*(r+1-p) ≤ (total r q - S.card)+ends S := by
  let c := min q (r.choose (r/2))
  have cen : 2≤r.choose (r/2) := (hr.trans (by simp : r≤r.choose 1)).trans (Nat.choose_le_middle 1 r)
  have res := deficitClipped (q:=c) (clippedWidth width) height hr (le_min hq cen) (min_le_right ..)
  have eq (j) : limit r c j=limit r q j := by
    simp [limit,c,min_assoc,min_eq_right (Nat.choose_le_middle j r)]
  simpa only [total,eq] using res
end PEqualNP.Outside.L_lib_1405_aux

namespace PEqualNP.Outside.L_lib_1405_aux
open PEqualNP.Outside.L_lib_1405_aux.Decomposition
variable {r : ℕ}
theorem trimSum (q : ℕ) (hq : 2≤q) (hr : 2≤r) (t : ℕ) (ht : t≤2) :
    (∑ j∈Finset.range (r+1-t),limit r q ((r+1-(r+1-t))/2+j))+t =
    ∑j∈Finset.range (r+1),limit r q j := by
  have left : limit r q 0=1 := by simp [limit,min_eq_right (show 1≤q by omega)]
  have right : limit r q r=1 := by simp [limit,min_eq_right (show 1≤q by omega)]
  interval_cases t
  · simp
  · simp only [Nat.add_sub_cancel,Nat.add_sub_cancel_left,Nat.reduceDiv,zero_add]
    rw [Finset.sum_range_succ (limit r q) r,right]
  · obtain ⟨n,hn⟩ : ∃ n, r=n+1 := ⟨r-1,by omega⟩
    have a : r+1-2=n := by omega
    have b : (r+1-n)/2=1 := by omega
    rw [a,b,Finset.sum_range_succ (limit r q) r,right]
    conv_rhs => rw [hn,Finset.sum_range_succ']
    simp only [←hn,left]
    simp only [Nat.add_comm 1]

theorem attain {q t : ℕ} (hr : 2≤r) (hq : 2≤q) (ht : t≤2) :
    ∃ S : Finset (Word r), Wide S q ∧ Tall S (r+1-t) ∧
      S.card=(Finset.range (r+1)).sum (limit r q)-t := by
  let B : Grid r := (chartExists (Finset.univ : Wd r)).some
  obtain ⟨S,sz,wd,h⟩ := lowerFamily B q (r+1-t)
  refine ⟨S,wd,h,?_⟩
  have sum := trimSum q hq hr t ht
  change S.card=(∑j∈Finset.range (r+1-t),limit r q ((r+1-(r+1-t))/2+j)) at sz
  rw [←sum,Nat.add_sub_cancel]
  exact sz
end PEqualNP.Outside.L_lib_1405_aux

namespace PEqualNP.Outside.L_lib_1405_aux
variable {r q : ℕ}

theorem uniqueLayer {S : Finset (Word r)} {k : ℕ} (A : Word r) (spec : ∀ w : Word r, w.card=k ↔ w=A) :
    pop S k = if A∈S then 1 else 0 := by
  classical
  by_cases h : A∈S
  · have eq : layer S k = {A} := by
      ext w
      simp only [layer,Finset.mem_filter,Finset.mem_singleton,spec]
      grind
    simp [pop,eq,h]
  · have eq : layer S k = ∅ := by
      ext w
      simp [layer,spec]
      grind
    simp [pop,eq,h]

theorem edgeGap {S : Finset (Word r)} (hq : 2≤q) (hr : 2≤r) (j : Fin (r+1))
    (edge : j.val=0 ∨ j.val=r) : limit r q j.val - pop S j.val = extra S j := by
  have qr : 1≤q := by omega
  rcases edge with z|top
  · have non : j.val≠r := by omega
    rw [z,uniqueLayer ∅ (fun _ => Finset.card_eq_zero)]
    by_cases h : (∅ : Word r)∈S <;> simp [limit,min_eq_right qr,extra,z,non,miss,h,show r≠0 by omega,show 0≠r by omega]
  · have non : j.val≠0 := by omega
    have spec (w : Word r) : w.card=r ↔ w=Finset.univ := by
      constructor
      · intro h
        exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [h])
      · rintro rfl
        simp
    rw [top,uniqueLayer Finset.univ spec]
    by_cases h : (Finset.univ : Word r)∈S <;> simp [limit,min_eq_right qr,extra,non,top,miss,h,show r≠0 by omega,show 0≠r by omega]

theorem optimum {S : Finset (Word r)} {t : ℕ} (hr : 2≤r) (hq : 2≤q) (ht : t≤2)
    (width : Wide S q) (height : Tall S (r+1-t)) :
    S.card≤total r q-t ∧ (S.card=total r q-t ↔ ends S=t ∧
      ∀j : ℕ,0<j → j<r → pop S j=limit r q j) := by
  classical
  let gap (j : Fin (r+1)) := limit r q j.val-pop S j.val
  have gapSum : ∑j,gap j = total r q - S.card := by
    rw [show (∑j,gap j)=_ from Finset.sum_tsub_distrib Finset.univ (fun (j : Fin (r+1)) _ => popLe width j.val),
      popSum,Fin.sum_univ_eq_sum_range (limit r q),total]
  have work : S.card ≤ total r q := by
    rw [← popSum S,total,←Fin.sum_univ_eq_sum_range (limit r q)]
    exact Finset.sum_le_sum (fun j _ => popLe width j.val)
  have edgeLe (j : Fin (r+1)) : extra S j ≤ gap j := by
    by_cases h : j.val=0 ∨ j.val=r
    · exact (edgeGap hq hr j h).ge
    · simp [extra,not_or.mp h |>.1,not_or.mp h |>.2]
  have endsLe : ends S ≤ total r q-S.card := by
    rw [← sumExtra,←gapSum]
    exact Finset.sum_le_sum (fun j _ => edgeLe j)
  have defic := deficit width height hr hq
  have eqt : r+1-(r+1-t)=t := by omega
  rw [eqt] at defic
  refine ⟨by omega,?_,?_⟩
  · intro size
    have eqEnds : ends S=t := by omega
    refine ⟨eqEnds,?_⟩
    have sumZero : (∑j : Fin (r+1), (gap j - extra S j))=0 := by
      rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => edgeLe j),gapSum,sumExtra]
      omega
    intro l pos lt
    let j : Fin (r+1) := ⟨l,by omega⟩
    have small := Finset.single_le_sum (s:=Finset.univ) (f:=fun j => gap j-extra S j)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    have ez : extra S j=0 := by simp [extra,j,show l≠0 by omega,show l≠r by omega]
    rw [sumZero,ez,Nat.sub_zero] at small
    have le := popLe width l
    change limit r q l-pop S l ≤ 0 at small
    omega
  · rintro ⟨et,full⟩
    have eq (j : Fin (r+1)) : gap j=extra S j := by
      by_cases h : j.val=0 ∨ j.val=r
      · exact edgeGap hq hr j h
      · obtain ⟨z,top⟩ := not_or.mp h
        simp [gap,extra,z,top,full j.val (by omega) (by omega)]
    have same := Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ => eq j)
    rw [gapSum,sumExtra,et] at same
    omega
end PEqualNP.Outside.L_lib_1405_aux

open PEqualNP.Outside.L_lib_1405_aux in
theorem PEqualNP.Outside.L_lib_1405 :
let heightAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (p : Nat) =>
  ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ p
let widthAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (q : Nat) =>
  ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q
∀ (r q : Nat), 2 ≤ r → 2 ≤ q →
  let T := (Finset.range (r+1)).sum (fun j => min q (Nat.choose r j))
  let ends := fun (S : Finset (Finset (Fin r))) =>
    (if (∅ : Finset (Fin r)) ∈ S then 0 else 1) +
    (if (Finset.univ : Finset (Fin r)) ∈ S then 0 else 1 : Nat)
  (∀ (S : Finset (Finset (Fin r))) (p : Nat), widthAtMost S q → heightAtMost S p →
    2*(r+1-p) ≤ (T-S.card) + ends S) ∧
  ∀ t : Nat, t ≤ 2 →
    (∃ S : Finset (Finset (Fin r)), widthAtMost S q ∧ heightAtMost S (r+1-t) ∧ S.card = T-t) ∧
    ∀ S : Finset (Finset (Fin r)), widthAtMost S q → heightAtMost S (r+1-t) →
      S.card ≤ T-t ∧ (S.card = T-t ↔
        ends S = t ∧ ∀ j : Nat, 0 < j → j < r →
          (S.filter (fun w => w.card = j)).card = min q (Nat.choose r j)) := by
  dsimp only
  intro r q hr hq
  constructor
  · intro S p width height
    exact deficit width height hr hq
  · intro t ht
    exact ⟨attain hr hq ht,fun _ wd htall => optimum hr hq ht wd htall⟩
