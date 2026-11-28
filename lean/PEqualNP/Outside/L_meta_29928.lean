import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_29928_aux
namespace ParityMixer29928
abbrev F := ZMod 2
private theorem eq3 {a b c d : F} (h : a+b+c=0) (g : b+c+d=0) : d=a := by linear_combination g-h
private theorem per {v : ℕ → F} (h : ∀ n, v n+v (n+1)+v (n+2)=0) (n : ℕ) : v (n+3)=v n := eq3 (h n) (h (n+1))
private theorem perAdd {v : ℕ → F} (h : ∀ n, v n+v (n+1)+v (n+2)=0) (i j : ℕ) : v (3*i+j)=v j := by
  induction i with
  | zero => simp
  | succ i ih => rw [show 3*(i+1)+j=3*i+j+3 by omega,per h,ih]

theorem sparse {k : ℕ} (hk : 25 ≤ k) (w : Fin k → F) (S : Finset (Fin k)) (small : S.card ≤ 15)
    (supp : ∀ i, w i ≠ 0 → i ∈ S)
    (rec : ∀ n : ℕ, let t := fun j : ℕ => w ⟨j%k,Nat.mod_lt _ (by omega)⟩; t n+t (n+1)+t (n+2)=0) : w=0 := by
  let v := fun j : ℕ => w ⟨j%k,Nat.mod_lt _ (by omega)⟩
  have h : ∀ n, v n+v (n+1)+v (n+2)=0 := rec
  by_contra bad
  have nz : ¬(v 0=0 ∧ v 1=0 ∧ v 2=0) := by
    rintro ⟨a,b,c⟩; apply bad; funext i
    change w i=0
    have e : v i.val=w i := by simp [v,Nat.mod_eq_of_lt i.isLt]
    rw [←e,show i.val=3*(i.val/3)+i.val % 3 by omega,perAdd h]
    rcases (show i.val % 3=0 ∨ i.val % 3=1 ∨ i.val % 3=2 by omega) with t|t|t <;> rwa [t]
  have pair : ∃ a b : Fin 3, a<b ∧ v a.val≠0 ∧ v b.val≠0 := by
    have hh := h 0
    by_cases a : v 0=0 <;> by_cases b : v 1=0 <;> by_cases c : v 2=0
    all_goals first | exact ⟨0,1,by decide,a,b⟩ | exact ⟨0,2,by decide,a,c⟩ | exact ⟨1,2,by decide,b,c⟩ | exact False.elim (nz ⟨a,b,c⟩) | simp_all
  obtain ⟨a,b,hab,ha,hb⟩ := pair
  let f : Fin 16 → Fin k := fun i => ⟨3*(i.val/2)+(if i.val % 2=0 then a.val else b.val),by split <;> omega⟩
  have inj : Function.Injective f := by
    intro i j e; have he := congrArg Fin.val e; simp only [f] at he
    apply Fin.ext; split at he <;> split at he <;> omega
  have mem (i : Fin 16) : f i ∈ S := by
    apply supp; have e : v (f i).val=w (f i) := by simp [v,Nat.mod_eq_of_lt (f i).isLt]
    rw [←e]; change v (3*(i.val/2)+_)≠0; rw [perAdd h]; split <;> assumption
  have bound := Fintype.card_le_of_injective (fun i : Fin 16 => (⟨f i,mem i⟩ : S)) (fun _ _ e => inj (congrArg Subtype.val e))
  simp at bound; omega
end ParityMixer29928

namespace ParityEncode29928
abbrev F := ZMod 2
variable {k : ℕ} [NeZero k]
abbrev W (k : ℕ) := Fin k → F
abbrev D (k : ℕ) := W k →ₗ[F] F
def tap (i : Fin k) : D k := (LinearMap.proj i : D k) + (LinearMap.proj (i+1) : D k) + (LinearMap.proj (i-1) : D k)
def code (S : Finset (Fin k)) : D k := ∑ i ∈ S, tap i
def bit (S : Finset (Fin k)) (i : Fin k) : F := if i∈S then 1 else 0
private theorem atDelta (S : Finset (Fin k)) (j : Fin k) : code S (Pi.single j 1) = bit S j + bit S (j-1) + bit S (j+1) := by
  classical
  simp only [code,LinearMap.sum_apply,tap,LinearMap.add_apply,LinearMap.proj_apply,Finset.sum_add_distrib,Pi.single_apply]
  have e (i : Fin k) : (i+1=j) ↔ i=j-1 := (eq_sub_iff_add_eq).symm
  simp [e,sub_eq_iff_eq_add,bit]
private theorem two (a : F) : a+a=0 := by fin_cases a <;> decide
private theorem bit_inj {A B : Finset (Fin k)} (h : bit A=bit B) : A=B := by
  ext i; have e := congrFun h i; by_cases a : i∈A <;> by_cases b : i∈B <;> simp_all [bit]
theorem vanish {k : ℕ} [NeZero k] (hk : 25≤k) (A B C : Finset (Fin k))
    (tiny : (A ∪ B ∪ C).card ≤ 15) (h : code A+code B+code C=0) : ∀ i,bit A i+bit B i+bit C i=0 := by
  let w := fun i => bit A i+bit B i+bit C i
  have hx (j : Fin k) := LinearMap.congr_fun h (Pi.single j 1)
  simp only [LinearMap.add_apply,atDelta,LinearMap.zero_apply] at hx
  have recur (n : ℕ) : let t := fun j : ℕ => w ⟨j%k,Nat.mod_lt _ (by omega)⟩; t n+t (n+1)+t (n+2)=0 := by
    let t := fun m : ℕ => (⟨m%k,Nat.mod_lt _ (by omega)⟩ : Fin k)
    have step (m : ℕ) : t (m+1)=t m+1 := by apply Fin.ext; simp [t,Fin.add_def,Nat.add_mod]
    have e := hx (t (n+1))
    change w (t n)+w (t (n+1))+w (t ((n+1)+1))=0
    simp only [step,add_sub_cancel_right,w] at e ⊢
    linear_combination e
  have z := ParityMixer29928.sparse hk w (A∪B∪C) tiny (by intro i hi; contrapose! hi; simp_all [w,bit]) recur
  exact fun i => congrFun z i
end ParityEncode29928

namespace ParityGlue29928
open ParityEncode29928
open scoped symmDiff
variable {k : ℕ} [NeZero k]
private theorem tiny {A B C : Finset (Fin k)} (a : A.card ≤ 5) (b : B.card ≤ 5) (c : C.card ≤ 5) : (A∪B∪C).card ≤ 15 := by
  have := Finset.card_union_le A B; have := Finset.card_union_le (A∪B) C; omega
private theorem uniqueRep (hk : 25≤k) {A B : Finset (Fin k)} (a : A.card≤5) (b : B.card≤5) (eq : code A=code B) : A=B := by
  have h := vanish hk A B ∅ (tiny a b (by simp)) (by rw [eq]; ext x; simp [ParityEncode29928.code,CharTwo.add_self_eq_zero])
  ext i; specialize h i; by_cases ha:i∈A <;> by_cases hb:i∈B <;> simp_all [bit]
private theorem third (hk : 25≤k) {A B C : Finset (Fin k)} (a : A.card≤5) (b : B.card≤5) (c : C.card≤5) (eq : code C=code A+code B) : C=A∆B := by
  have h := vanish hk A B C (tiny a b c) (by rw [←eq]; ext x; simp [CharTwo.add_self_eq_zero])
  ext i; specialize h i; by_cases ha:i∈A <;> by_cases hb:i∈B <;> by_cases hc:i∈C <;> simp_all [bit,Finset.mem_symmDiff,CharTwo.add_self_eq_zero]
theorem glue (hk : 25≤k) (M : Fin k → Prop) (R : Fin k → Finset (Fin k) → Prop) (q r : D k)
    (localRep : ∀ i, M i → ∃ S, R i S ∧ S.card≤5 ∧ (code S=q ∨ code S=r ∨ code S=q+r)) :
    ∃ A B : Finset (Fin k), ∀ i, M i → R i A ∨ R i B ∨ R i (A∆B) := by
  classical
  let Live := fun l : D k => ∃ S : Finset (Fin k), S.card≤5 ∧ code S=l
  let pick := fun l : D k => if h : Live l then h.choose else ∅
  have good {l} (h : Live l) : (pick l).card≤5 ∧ code (pick l)=l := by simpa only [pick,dif_pos h] using h.choose_spec
  have useRep {S : Finset (Fin k)} (hs : S.card≤5) : S=pick (code S) := by
    have hh := good (show Live (code S) from ⟨S,hs,rfl⟩); exact uniqueRep hk hs hh.1 hh.2.symm
  have choices (i) (hi : M i) : (Live q ∧ R i (pick q)) ∨ (Live r ∧ R i (pick r)) ∨ (Live (q+r) ∧ R i (pick (q+r))) := by
    obtain ⟨S,hr,hs,he⟩ := localRep i hi; have h := useRep hs; rcases he with e|e|e <;> rw [e] at h
    · exact Or.inl ⟨⟨S,hs,e⟩,h ▸ hr⟩
    · exact Or.inr (Or.inl ⟨⟨S,hs,e⟩,h ▸ hr⟩)
    · exact Or.inr (Or.inr ⟨⟨S,hs,e⟩,h ▸ hr⟩)
  by_cases hq : Live q
  · by_cases hr : Live r
    · refine ⟨pick q,pick r,?_⟩; intro i hi; rcases choices i hi with h|h|h
      · exact Or.inl h.2
      · exact Or.inr (Or.inl h.2)
      · have e := third hk (good hq).1 (good hr).1 (good h.1).1 (by rw [(good hq).2,(good hr).2,(good h.1).2]); exact Or.inr (Or.inr (e ▸ h.2))
    · refine ⟨pick q,pick (q+r),?_⟩; intro i hi; rcases choices i hi with h|h|h
      · exact Or.inl h.2
      · exact (hr h.1).elim
      · exact Or.inr (Or.inl h.2)
  · refine ⟨pick r,pick (q+r),?_⟩; intro i hi; rcases choices i hi with h|h|h
    · exact (hq h.1).elim
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
end ParityGlue29928

namespace ParityMask29928
open ParityEncode29928
variable {k : ℕ} [NeZero k]
def pos (i : Fin k) (t : Fin 5) : Fin k := i + Fin.ofNat k t.val
def coeff (a b d e : F) : Fin 5 → F := ![d,a,e,b,d+e]
def mask (a b d e : F) (t : Fin 5) : Bool := decide (coeff a b d e t ≠ 0)
def sites (i : Fin k) (p : Fin 5 → Bool) : Finset (Fin k) := (Finset.univ.filter (fun t => p t)).image (pos i)
private theorem inj (hk : 25≤k) (i : Fin k) : Function.Injective (pos i) := by
  intro x y h; have eq := add_left_cancel h; apply Fin.ext; have := congrArg Fin.val eq
  simpa [Fin.ofNat,Nat.mod_eq_of_lt (show x.val<k by omega),Nat.mod_eq_of_lt (show y.val<k by omega)] using this
theorem bound (i : Fin k) (p : Fin 5 → Bool) : (sites i p).card≤5 := by
  exact (Finset.card_image_le).trans ((Finset.card_filter_le ..).trans (by simp))
theorem even (a b d e : F) : (mask a b d e 0 ^^ mask a b d e 2 ^^ mask a b d e 4)=false := by fin_cases d <;> fin_cases e <;> decide +revert
theorem inhabited (i : Fin k) (a b d e : F) (nz : a≠0 ∨ b≠0 ∨ d≠0 ∨ e≠0) : (sites i (mask a b d e)).Nonempty := by
  apply Finset.Nonempty.image; rcases nz with h|h|h|h
  · exact ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true h⟩⟩
  · exact ⟨3,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true h⟩⟩
  · exact ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true h⟩⟩
  · exact ⟨2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true h⟩⟩
theorem value (hk : 25≤k) (i : Fin k) (a b d e : F) :
    ParityEncode29928.code (sites i (mask a b d e)) = a • tap (pos i 1) + b • tap (pos i 3) + d • (tap (pos i 0)+tap (pos i 4)) + e • (tap (pos i 2)+tap (pos i 4)) := by
  unfold ParityEncode29928.code sites; rw [Finset.sum_image (fun x _ y _ h => inj hk i h),Finset.sum_filter]
  have elem (t : Fin 5) : (if mask a b d e t = true then tap (pos i t) else 0) = coeff a b d e t • tap (pos i t) := by
    unfold mask; generalize coeff a b d e t=c
    have vals : ∀ c : F, c=0 ∨ c=1 := by decide
    rcases vals c with rfl|rfl <;> simp
  simp_rw [elem]; rw [Fin.sum_univ_five]; simp [coeff,add_smul,smul_add]; abel
end ParityMask29928

namespace ParityCover29928
open ParityEncode29928 ParityMask29928
open scoped symmDiff
variable {k : ℕ} [NeZero k]
def permitted (i : Fin k) (S : Finset (Fin k)) : Prop := S.Nonempty ∧ ∃ p : Fin 5 → Bool, (p 0 ^^ p 2 ^^ p 4)=false ∧ S=sites i p
def raw (i : Fin k) (a b d e : F) : D k := a • tap (pos i 1) + b • tap (pos i 3) + d • (tap (pos i 0)+tap (pos i 4)) + e • (tap (pos i 2)+tap (pos i 4))
theorem cover (hk : 25≤k) (M : Fin k → Prop) (q r : D k)
    (h : ∀ i, M i → ∃ a b d e : F, (a≠0 ∨ b≠0 ∨ d≠0 ∨ e≠0) ∧ (raw i a b d e=0 ∨ raw i a b d e=q ∨ raw i a b d e=r ∨ raw i a b d e=q+r)) :
    ∃ A B : Finset (Fin k), ∀ i, M i → permitted i A ∨ permitted i B ∨ permitted i (A∆B) := by
  apply ParityGlue29928.glue hk M permitted q r
  intro i hi; obtain ⟨a,b,d,e,nz,h⟩ := h i hi
  let S := sites i (mask a b d e)
  have sz : S.card≤5 := bound ..
  have ne : S.Nonempty := inhabited i a b d e nz
  have val : ParityEncode29928.code S=raw i a b d e := value hk i a b d e
  refine ⟨S,⟨ne,_,even a b d e,rfl⟩,sz,?_⟩; rw [←val] at h; rcases h with zero|rest
  · obtain ⟨j,hj⟩ := ne
    have z := vanish hk S ∅ ∅ (by simpa using sz.trans (show 5≤15 by decide)) (by rw [zero]; simp [ParityEncode29928.code]) j
    simp [bit,hj] at z
  · exact rest
end ParityCover29928


namespace ParityLocal29928

abbrev F := ZMod 2
abbrev Cube := Fin 4 → F
variable {W V : Type*} [AddCommGroup W] [Module F W] [AddCommGroup V] [Module F V]

def diff {U : Type*} [Add U] (f : U → F) (v x : U) := f (x+v) - f x
def Cubic {U : Type*} [Add U] (f : U → F) : Prop :=
  ∀ (v : Fin 4 → U) x, (List.ofFn v).foldl diff f x = 0

omit [Module F W] in
private lemma fold_sub (l : List W) (f g : W → F) :
    l.foldl diff (fun x => f x - g x) = fun x => l.foldl diff f x - l.foldl diff g x := by
  induction l generalizing f g with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldl_cons]
    rw [show diff (fun x => f x-g x) v = fun x => diff f v x - diff g v x by
      funext x; dsimp [diff]; ring]
    exact ih _ _

private lemma fold_pull (A : V →ₗ[F] W) (l : List V) (f : W → F) :
    l.foldl diff (fun x => f (A x)) = fun x => (l.map A).foldl diff f (A x) := by
  induction l generalizing f with
  | nil => rfl
  | cons v l ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [show diff (fun x => f (A x)) v = fun x => diff f (A v) (A x) by
      funext x; simp [diff]]
    exact ih _

private lemma cubic_pull (A : V →ₗ[F] W) {f : W → F} (hf : Cubic f) : Cubic (fun x => f (A x)) := by
  intro v x
  rw [fold_pull, List.map_ofFn]
  exact hf _ _

private def unit (j : Fin 4) : Cube := Pi.single j 1
private def poly (c : Cube) (x : Cube) : F :=
  (x 0+c 0)*(x 1+c 1)*(x 2+c 2)*(x 3+c 3)

private lemma top_difference : ∀ a b c d : F,
    (List.ofFn unit).foldl diff (poly ![a,b,c,d]) (0 : Cube) = 1 := by decide +kernel

private lemma not_cubic (c : Cube) : ¬ Cubic (poly c) := by
  intro h
  have hc : c = ![c 0,c 1,c 2,c 3] := by ext j; fin_cases j <;> rfl
  have h1 := top_difference (c 0) (c 1) (c 2) (c 3)
  rw [← hc] at h1
  exact zero_ne_one ((h unit 0).symm.trans h1)

private lemma dual_four (φ : Cube →ₗ[F] F) (x : Cube) :
    φ x = φ (unit 0)*x 0 + φ (unit 1)*x 1 + φ (unit 2)*x 2 + φ (unit 3)*x 3 := by
  have e : x = x 0 • unit 0 + x 1 • unit 1 + x 2 • unit 2 + x 3 • unit 3 := by
    funext j; fin_cases j <;> simp [unit, Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [e]
  simp [mul_comm, smul_eq_mul]

private lemma kernel_pair (q r L : W →ₗ[F] F)
    (h : ∀ x, q x = 0 → r x = 0 → L x = 0) :
    L = 0 ∨ L = q ∨ L = r ∨ L = q+r := by
  classical
  let S : Fin 2 → W →ₗ[F] F := ![q,r]
  have hle : (⨅ i, LinearMap.ker (S i)) ≤ LinearMap.ker L := by
    intro x hx; exact h x ((Submodule.mem_iInf _).mp hx 0) ((Submodule.mem_iInf _).mp hx 1)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (mem_span_of_iInf_ker_le_ker hle)
  simp [Fin.sum_univ_two, S] at hc
  have casesF (a : F) : a=0 ∨ a=1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases casesF (c 0) with h0|h0 <;> rcases casesF (c 1) with h1|h1 <;> simp_all


theorem necessary (T : Fin 5 → W →ₗ[F] F) (c : Fin 5 → F) (q r : W →ₗ[F] F)
    (f g : W → F) (hf : Cubic f) (hg : Cubic g)
    (agree : ∀ x, q x=0 → r x=0 → let t := fun j => T j x+c j;
      f x = g x + t 1*t 3*(t 0+t 4)*(t 2+t 4)) :
    ∃ a b d e : F, (a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) ∧
      let L := a • T 1 + b • T 3 + d • (T 0+T 4) + e • (T 2+T 4);
      L=0 ∨ L=q ∨ L=r ∨ L=q+r := by
  classical
  let K := LinearMap.ker q ⊓ LinearMap.ker r
  let Y : W →ₗ[F] Cube := LinearMap.pi ![T 1,T 3,T 0+T 4,T 2+T 4]
  let A := Y.comp K.subtype
  let u : Cube := ![c 1,c 3,c 0+c 4,c 2+c 4]
  have heq (x : K) : f x - g x = poly u (A x) := by
    have h := agree x x.property.1 x.property.2
    change f x - g x = (T 1 x+c 1)*(T 3 x+c 3)*((T 0 x+T 4 x)+(c 0+c 4))*((T 2 x+T 4 x)+(c 2+c 4))
    dsimp only at h; rw [h]; ring
  have hrange : LinearMap.range A ≠ ⊤ := by
    intro top
    obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective top
    have sec : Function.RightInverse B A := LinearMap.ext_iff.mp hB
    let C := K.subtype.comp B
    have iden : poly u = fun x => f (C x)-g (C x) := by
      funext x; exact (sec x ▸ heq (B x)).symm
    apply not_cubic u
    rw [iden]
    intro v x
    simp only [fold_sub, cubic_pull C hf v x, cubic_pull C hg v x, sub_self]
  obtain ⟨φ, hn, hz⟩ := (LinearMap.range A).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hrange)
  let a := φ (unit 0); let b := φ (unit 1); let d := φ (unit 2); let e := φ (unit 3)
  refine ⟨a,b,d,e,?_,?_⟩
  · by_contra! allzero
    apply hn; apply LinearMap.ext; intro x
    rw [LinearMap.zero_apply]
    simpa only [a,b,d,e, allzero.1,allzero.2.1,allzero.2.2.1,allzero.2.2.2,zero_mul,zero_add] using dual_four φ x
  · apply kernel_pair
    intro x qx rx
    have h := hz (show A ⟨x,qx,rx⟩ ∈ LinearMap.range A from ⟨_,rfl⟩)
    change φ (A ⟨x,qx,rx⟩) = 0 at h
    rw [dual_four] at h
    exact h


theorem coefficients (w : Fin 5 → F) :
    (∃ a b d e : F, (a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) ∧
      w = ![d,a,e,b,d+e]) ↔ w ≠ 0 ∧ w 0+w 2+w 4=0 := by
  have dbl (x : F) : x+x=0 := by fin_cases x <;> decide
  constructor
  · rintro ⟨a,b,d,e,hn,rfl⟩
    refine ⟨fun h => ?_,?_⟩
    · have ha := congrFun h 1; have hb := congrFun h 3
      have hd := congrFun h 0; have he := congrFun h 2
      rcases hn with h|h|h|h
      · exact h ha
      · exact h hb
      · exact h hd
      · exact h he
    · exact dbl (d+e)
  · rintro ⟨hn,h⟩
    have h4 : w 4 = w 0+w 2 := by linear_combination h - dbl (w 0+w 2)
    refine ⟨w 1,w 3,w 0,w 2,?_,?_⟩
    · by_contra! hh
      apply hn; funext j; fin_cases j <;> simp_all
    · funext j; fin_cases j <;> first | rfl | exact h4

private lemma cubic_three (m : F) (A B C : W →ₗ[F] F) (a b c : F) :
    Cubic (fun x => m*(A x+a)*(B x+b)*(C x+c)) := by
  intro v x
  change diff (diff (diff (diff _ (v 0)) (v 1)) (v 2)) (v 3) x=0
  simp only [diff,map_add]; ring

private lemma pivot : ∀ b d e h x y z w : F, x+b*y+d*z+e*w=h →
    x*y*z*w=(h-b-d-e)*y*z*w := by decide +kernel


theorem sufficient (T : Fin 4 → W →ₗ[F] F) (c : Cube) (a b d e h : F)
    (hn : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) :
    ∃ f : W → F, Cubic f ∧ ∀ x, let t := fun j => T j x+c j;
      a*t 0+b*t 1+d*t 2+e*t 3=h → t 0*t 1*t 2*t 3=f x := by
  have one {p : F} (hp : p ≠ 0) : p=1 := by fin_cases p <;> first | rfl | exact (hp rfl).elim
  rcases hn with hn|hn|hn|hn
  · refine ⟨_,cubic_three (h-b-d-e) (T 1) (T 2) (T 3) (c 1) (c 2) (c 3),?_⟩
    intro x tx rel
    exact pivot b d e h (tx 0) (tx 1) (tx 2) (tx 3) (by simpa only [one hn,one_mul] using rel)
  · refine ⟨_,cubic_three (h-a-d-e) (T 0) (T 2) (T 3) (c 0) (c 2) (c 3),?_⟩
    intro x tx rel
    rw [one hn,one_mul] at rel
    have key := pivot a d e h (tx 1) (tx 0) (tx 2) (tx 3) (by linear_combination rel)
    change tx 0*tx 1*tx 2*tx 3=(h-a-d-e)*tx 0*tx 2*tx 3
    linear_combination key
  · refine ⟨_,cubic_three (h-a-b-e) (T 0) (T 1) (T 3) (c 0) (c 1) (c 3),?_⟩
    intro x tx rel
    rw [one hn,one_mul] at rel
    have key := pivot a b e h (tx 2) (tx 0) (tx 1) (tx 3) (by linear_combination rel)
    change tx 0*tx 1*tx 2*tx 3=(h-a-b-e)*tx 0*tx 1*tx 3
    linear_combination key
  · refine ⟨_,cubic_three (h-a-b-d) (T 0) (T 1) (T 2) (c 0) (c 1) (c 2),?_⟩
    intro x tx rel
    rw [one hn,one_mul] at rel
    have key := pivot a b d h (tx 3) (tx 0) (tx 1) (tx 2) (by linear_combination rel)
    change tx 0*tx 1*tx 2*tx 3=(h-a-b-d)*tx 0*tx 1*tx 2
    linear_combination key


theorem run_zero (ask : Fin 2 → ℕ → W →ₗ[F] F) (x : W)
    (h : ask 0 0 x=0) (h' : ask 1 0 x=0) :
    (List.finRange 2).foldl (fun n j => 2*n+(if ask j n x=0 then 0 else 1)) 0=0 := by
  change 2*(2*0+(if ask 0 0 x=0 then 0 else 1))+
    (if ask 1 (2*0+(if ask 0 0 x=0 then 0 else 1)) x=0 then 0 else 1)=0
  simp [h,h']


theorem marked_zero_leaf (T : Fin 5 → W →ₗ[F] F) (c : Fin 5 → F)
    (ask : Fin 2 → ℕ → W →ₗ[F] F) (readout : ℕ → W → F)
    (out g : W → F) (hg : Cubic g) (hf : Cubic (readout 0))
    (decomp : ∀ x, let t := fun j => T j x+c j;
       out x = g x+t 1*t 3*(t 0+t 4)*(t 2+t 4))
    (correct : ∀ x, out x = readout ((List.finRange 2).foldl
      (fun n j => 2*n+(if ask j n x=0 then 0 else 1)) 0) x) :
    ∃ w : Fin 5 → F, w ≠ 0 ∧ w 0+w 2+w 4=0 ∧
      let L := ∑ j, w j • T j
      L=0 ∨ L=ask 0 0 ∨ L=ask 1 0 ∨ L=ask 0 0 + ask 1 0 := by
  obtain ⟨a,b,d,e,hn,hL⟩ := necessary T c (ask 0 0) (ask 1 0) (readout 0) g hf hg
    (fun x hq hr => by rw [←run_zero ask x hq hr,←correct]; exact decomp x)
  let w : Fin 5 → F := ![d,a,e,b,d+e]
  have hw := (coefficients w).mp ⟨a,b,d,e,hn,rfl⟩
  refine ⟨w,hw.1,hw.2,?_⟩
  have hsum : ∑ j, w j • T j = a • T 1+b • T 3+d • (T 0+T 4)+e • (T 2+T 4) := by
    simp [w,Fin.sum_univ_succ,smul_add,add_smul,add_assoc,add_left_comm]
  simpa only [hsum] using hL

end ParityLocal29928


namespace PC29928
abbrev F := ZMod 2
abbrev W (k : ℕ) := Fin k → F
abbrev D (k : ℕ) := W k →ₗ[F] F
variable {k : ℕ}

def delta (f : W k → F) (u x : W k) := f (x+u) - f x
def Cubic (f : W k → F) := ∀ (v : Fin 4 → W k) x, (List.ofFn v).foldl delta f x = 0

inductive P : ℕ → (W k → F) → Prop where
  | con (n : ℕ) (c : F) : P n (fun _ => c)
  | add {n f g} : P n f → P n g → P n (fun x => f x + g x)
  | amul {n f} (l : D k) (c : F) : P n f → P (n+1) (fun x => (l x+c)*f x)

lemma P.up {n f} (p : @P k n f) : P (n+1) f := by
  induction p with
  | con => exact .con _ _
  | add _ _ ih jh => exact .add ih jh
  | amul l c _ ih => exact .amul l c ih
lemma P.lift {n m f} (p : @P k n f) (h : n ≤ m) : P m f := by
  induction h with
  | refl => exact p
  | step _ ih => exact ih.up
lemma P.scale {n f} (p : @P k n f) (a : F) : P n (fun x => a*f x) := by
  induction p with
  | con => exact .con _ _
  | add _ _ ih jh => simpa only [mul_add] using P.add ih jh
  | amul l c _ ih => simpa only [mul_left_comm a] using P.amul l c ih
lemma P.mul {n m f g} (p : @P k n f) (q : P m g) : P (n+m) (fun x => f x*g x) := by
  induction p with
  | con n c => exact (q.scale c).lift (by omega)
  | add _ _ ih jh => simpa only [add_mul] using P.add ih jh
  | amul l c _ ih => simpa only [Nat.succ_add,mul_assoc] using P.amul l c ih
lemma P.aff (l : D k) (c : F) : P 1 (fun x => l x+c) := by
  simpa only [mul_one] using P.amul l c (P.con 0 1)
lemma P.diff {n f} (p : @P k n f) (u : W k) :
    (n=0 → ∀ x, delta f u x=0) ∧ P (n-1) (delta f u) := by
  induction p with
  | con n c =>
    have e : delta (fun _ : W k => c) u = fun _ => 0 := by funext x; simp [delta]
    rw [e]; exact ⟨fun _ _ => rfl,.con _ _⟩
  | add p q ih jh =>
    have e : ∀ f g : W k → F, delta (fun x => f x+g x) u = fun x => delta f u x+delta g u x := by
      intro f g; funext x; simp [delta]; ring
    rw [e]; exact ⟨fun h x => by simp only [ih.1 h x,jh.1 h x,add_zero], .add ih.2 jh.2⟩
  | @amul n f l c pf ih =>
    refine ⟨by omega, ?_⟩
    have e : delta (fun x => (l x+c)*f x) u = fun x => (l x+(c+l u))*delta f u x + l u*f x := by
      funext x; simp [delta]; ring
    rw [e]; simp only [Nat.add_sub_cancel]
    cases n with
    | zero =>
      simpa only [ih.1 rfl, mul_zero, zero_add] using pf.scale (l u)
    | succ n => exact .add (.amul l (c+l u) ih.2) (pf.scale (l u))
lemma P.cubic {f : W k → F} (p : P 3 f) : Cubic f := by
  intro v x
  simp only [List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  exact ((((p.diff _).2.diff _).2.diff _).2.diff _).1 rfl x

def ix (hk : 0<k) (j : ℕ) : Fin k := ⟨j%k,Nat.mod_lt _ hk⟩
def adv (hk : 0<k) (i : Fin k) (n : ℕ) := ix hk (i.val+n)
def back (hk : 0<k) (i : Fin k) (s : ℕ) := ix hk (i.val+k-s%k)
@[simp] lemma adv_adv (hk : 0<k) (i : Fin k) (m n : ℕ) : adv hk (adv hk i m) n = adv hk i (m+n) := by
  apply Fin.ext; simp [adv,ix,Nat.mod_add_mod,Nat.add_assoc]
@[simp] lemma adv_zero (hk : 0<k) (i : Fin k) : adv hk i 0 = i := by
  apply Fin.ext; simp [adv,ix,Nat.mod_eq_of_lt i.isLt]
lemma back_next (hk : 0<k) (hk' : 25≤k) (i : Fin k) : back hk (adv hk i 1) 1 = i := by
  apply Fin.ext; change (((i.val+1)%k+k-1%k)%k)=i.val
  have hi := i.isLt
  rw [Nat.mod_eq_of_lt (show 1<k by omega)]
  by_cases h : i.val+1<k
  · rw [Nat.mod_eq_of_lt h,show i.val+1+k-1=i.val+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
  · rw [show i.val+1=k by omega,Nat.mod_self,zero_add,Nat.mod_eq_of_lt (by omega)]; omega

def proj (i : Fin k) : D k := LinearMap.proj i

def mixed (hk : 0<k) (i : Fin k) : D k :=
  proj (back hk i 1) + proj (back hk (adv hk i 1) 1) + proj (back hk (back hk i 1) 1)
def z (hk : 0<k) (nm : W k) (i : Fin k) (x : W k) :=
  let r := fun j : Fin k => x (back hk j 1)+nm j
  r i+r (adv hk i 1)+r (back hk i 1)
def tap (hk : 0<k) (nm : W k) (i : Fin k) (n : ℕ) := z hk nm (adv hk i n)
lemma tap_split (hk : 0<k) (nm : W k) (i : Fin k) (n : ℕ) (x : W k) :
    tap hk nm i n x = mixed hk (adv hk i n) x + z hk nm (adv hk i n) 0 := by
  simp [tap,z,mixed,proj]; ring
lemma z_aff (hk : 0<k) (nm : W k) (i : Fin k) : P 1 (z hk nm i) := by
  simpa only [tap,adv_zero] using (show P 1 (tap hk nm i 0) by
    simp only [funext (tap_split hk nm i 0)]; exact P.aff _ _)

def y (hk : 0<k) (nm c₁ : W k) (i : Fin k) (x : W k) :=
  z hk nm i x + (1+tap hk nm i 1 x)*tap hk nm i 2 x + x (back hk i 0) + c₁ i
def mixY (hk : 0<k) (nm c₁ : W k) (i : Fin k) (x : W k) :=
  y hk nm c₁ i x + y hk nm c₁ (adv hk i 1) x + y hk nm c₁ (back hk i 1) x
def row (hk : 0<k) (nm c₁ c₂ : W k) (i : Fin k) (x : W k) :=
  mixY hk nm c₁ i x + (1+mixY hk nm c₁ (adv hk i 1) x)*mixY hk nm c₁ (adv hk i 2) x + x (back hk i 2) + c₂ i

def baseY (hk : 0<k) (nm c₁ : W k) (i : Fin k) (x : W k) :=
  z hk nm i x + tap hk nm i 2 x + x (back hk i 0) + c₁ i
def mixBase (hk : 0<k) (nm c₁ : W k) (i : Fin k) (x : W k) :=
  baseY hk nm c₁ i x + baseY hk nm c₁ (adv hk i 1) x + baseY hk nm c₁ (back hk i 1) x

private def core (a b c d e u v : F) :=
  u*(v+(b*c+c*d)+d*e)+v*(a*b+(b*c+c*d)) + a*b*c+c*d*e+(b*c+c*d)+b*d*e
private lemma core_id : ∀ a b c d e u v : F,
  (u+(a*b+b*c+c*d))*(v+(b*c+c*d+d*e)) = core a b c d e u v + b*d*(a+e)*(c+e) := by decide

def remn (hk : 0<k) (nm c₁ c₂ : W k) (i : Fin k) (x : W k) :=
  let t := fun n => tap hk nm i n x
  let u := 1+mixBase hk nm c₁ (adv hk i 1) x
  let v := mixBase hk nm c₁ (adv hk i 2) x
  mixY hk nm c₁ i x + core (t 1) (t 2) (t 3) (t 4) (t 5) u v + x (back hk i 2) + c₂ i

lemma row_decomp (hk : 0<k) (hk' : 25≤k) (nm c₁ c₂ : W k) (i : Fin k) (x : W k) :
    row hk nm c₁ c₂ i x = remn hk nm c₁ c₂ i x + tap hk nm i 2 x * tap hk nm i 4 x *
      (tap hk nm i 1 x + tap hk nm i 5 x) * (tap hk nm i 3 x + tap hk nm i 5 x) := by
  let t := fun n => tap hk nm i n x
  have yy (j : Fin k) : y hk nm c₁ j x = baseY hk nm c₁ j x + tap hk nm j 1 x * tap hk nm j 2 x := by
    simp [y,baseY]; ring
  have bt : back hk (adv hk i 2) 1 = adv hk i 1 := by simpa using back_next hk hk' (adv hk i 1)
  have h1 : 1+mixY hk nm c₁ (adv hk i 1) x = (1+mixBase hk nm c₁ (adv hk i 1) x)+(t 1*t 2+t 2*t 3+t 3*t 4) := by
    simp only [mixY,mixBase,yy,t,tap,adv_adv,back_next hk hk']; ring
  have h2 : mixY hk nm c₁ (adv hk i 2) x = mixBase hk nm c₁ (adv hk i 2) x+(t 2*t 3+t 3*t 4+t 4*t 5) := by
    simp only [mixY,mixBase,yy,t,tap,adv_adv,bt]; ring
  change _ = mixY hk nm c₁ i x + core _ _ _ _ _ _ _ + _ + _ + _
  unfold row; rw [h1,h2,core_id]; ring

lemma proj_aff (i : Fin k) : P 1 (fun x : W k => x i) := by
  simpa only [proj,LinearMap.proj_apply,add_zero] using P.aff (proj i) 0
lemma remn_poly (hk : 0<k) (nm c₁ c₂ : W k) (i : Fin k) : P 3 (remn hk nm c₁ c₂ i) := by
  have t (j : Fin k) (n : ℕ) : P 1 (tap hk nm j n) := z_aff hk nm _
  have z' (j : Fin k) := z_aff hk nm j
  have y' (j : Fin k) : P 2 (y hk nm c₁ j) :=
    .add (.add (.add (z' j).up ((P.add (.con 1 1) (t j 1)).mul (t j 2))) (proj_aff _).up) (.con _ _)
  have m (j : Fin k) : P 2 (mixY hk nm c₁ j) := .add (.add (y' _) (y' _)) (y' _)
  have b (j : Fin k) : P 1 (baseY hk nm c₁ j) := .add (.add (.add (z' _) (t _ _)) (proj_aff _)) (.con _ _)
  have mb (j : Fin k) : P 1 (mixBase hk nm c₁ j) := .add (.add (b _) (b _)) (b _)
  have u := P.add (P.con 1 1) (mb (adv hk i 1))
  have v := mb (adv hk i 2)
  have t' := t i
  have E := P.add ((t' 2).mul (t' 3)) ((t' 3).mul (t' 4))
  have C₁ := u.mul (.add (.add v.up E) ((t' 4).mul (t' 5)))
  have C₂ := v.mul (.add ((t' 1).mul (t' 2)) E)
  have C₃ := ((t' 1).mul (t' 2)).mul (t' 3)
  have C₄ := ((t' 3).mul (t' 4)).mul (t' 5)
  have C₅ := ((t' 2).mul (t' 4)).mul (t' 5)
  have C := (((((C₁.add C₂).add C₃).add C₄).add E.up).add C₅)
  exact (((m i).up.add C).add (proj_aff _).up.up).add (P.con _ _)
lemma remn_cubic (hk : 0<k) (nm c₁ c₂ : W k) (i : Fin k) : Cubic (remn hk nm c₁ c₂ i) :=
  (remn_poly hk nm c₁ c₂ i).cubic

def M (hk : 0<k) (i : Fin k) (j : ℕ) := mixed hk (adv hk i j)
def Eligible (hk : 0<k) (i : Fin k) (q : D k) : Prop :=
  q=M hk i 2 ∨ q=M hk i 4 ∨ q=M hk i 2+M hk i 4 ∨
  q=M hk i 1+M hk i 5 ∨ q=M hk i 3+M hk i 5 ∨ q=M hk i 1+M hk i 3
def Tied (f : W k → F) (q : D k) : Prop := ∀ x, f x = q x + f 0
lemma tied_tap (hk : 0<k) (nm : W k) (i : Fin k) (n : ℕ) : Tied (tap hk nm i n) (M hk i n) :=
  tap_split hk nm i n
lemma Tied.add {f g : W k → F} {q r : D k} (hf : Tied f q) (hg : Tied g r) :
    Tied (fun x => f x+g x) (q+r) := by
  intro x; simp only [LinearMap.add_apply]; rw [hf x,hg x]; ring
def Lock (a b : W k → F) (q : D k) := Tied a q ∨ Tied b q ∨ Tied (fun x => a x+b x) q
private lemma cancelF : ∀ a b c : F, (a+c)+(b+c)=a+b := by decide
private lemma product_sum : ∀ a b : F, a*b = (a+b+1)*a := by decide
lemma lock_read {a b : W k → F} {q : D k} (ha : P 1 a) (hb : P 1 b) (h : Lock a b q) (s : F) :
    ∃ f, P 1 f ∧ ∀ x, q x=s → a x*b x=f x := by
  rcases h with h|h|h
  · exact ⟨_,hb.scale (s+a 0),fun x hx => by rw [h x,hx]⟩
  · exact ⟨_,ha.scale (s+b 0),fun x hx => by rw [h x,hx,mul_comm]⟩
  · refine ⟨_,ha.scale (s+(a 0+b 0)+1),fun x hx => ?_⟩
    have e : a x+b x=s+(a 0+b 0) := (h x).trans (by rw [hx])
    rw [product_sum,e]

lemma eligible_read (hk : 0<k) (hk' : 25≤k) (nm c₁ c₂ : W k) (i : Fin k) (q : D k)
    (hq : Eligible hk i q) (s : F) :
    ∃ f, Cubic f ∧ ∀ x, q x=s → row hk nm c₁ c₂ i x=f x := by
  let t := tap hk nm i
  let a := t 2
  let b := t 4
  let c := fun x => t 1 x+t 5 x
  let d := fun x => t 3 x+t 5 x
  have T (n : ℕ) : P 1 (t n) := z_aff hk nm _
  have ha : P 1 a := T 2
  have hb : P 1 b := T 4
  have hc : P 1 c := (T 1).add (T 5)
  have hd : P 1 d := (T 3).add (T 5)
  have L (n : ℕ) : Tied (t n) (M hk i n) := tied_tap hk nm i n
  have lock : Lock a b q ∨ Lock c d q := by
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    · exact .inl (.inl (L 2))
    · exact .inl (.inr (.inl (L 4)))
    · exact .inl (.inr (.inr ((L 2).add (L 4))))
    · exact .inr (.inl ((L 1).add (L 5)))
    · exact .inr (.inr (.inl ((L 3).add (L 5))))
    · right; right; right
      simpa only [c,d,cancelF] using (show Tied (fun x => t 1 x+t 3 x) (M hk i 1+M hk i 3) from (L 1).add (L 3))
  have e (x) : row hk nm c₁ c₂ i x = remn hk nm c₁ c₂ i x + (a x*b x)*(c x*d x) := by
    rw [row_decomp hk hk']; simp only [a,b,c,d,t,mul_assoc]
  rcases lock with h|h
  · obtain ⟨f,hf,ef⟩ := lock_read ha hb h s
    exact ⟨_,((remn_poly hk nm c₁ c₂ i).add (hf.mul (hc.mul hd))).cubic,
      fun x hx => by rw [e,ef x hx]⟩
  · obtain ⟨f,hf,ef⟩ := lock_read hc hd h s
    exact ⟨_,((remn_poly hk nm c₁ c₂ i).add ((ha.mul hb).mul hf)).cubic,
      fun x hx => by rw [e,ef x hx]⟩

def Triple (hk : 0<k) (a i : Fin k) := i=a ∨ i=adv hk a 1 ∨ i=adv hk a 2
def Except (hk : 0<k) (a i : Fin k) :=
  i=a ∨ i=adv hk a 2 ∨ i=adv hk a 3 ∨ i=adv hk a 4 ∨ i=adv hk a 6
lemma triple_rows (hk : 0<k) (a i : Fin k) (h : Triple hk a i) :
    Eligible hk i (M hk a 3+M hk a 5) := by
  rcases h with rfl|rfl|rfl <;> simp only [Eligible,M,adv_adv,Nat.reduceAdd] <;> tauto
lemma except_rows (hk : 0<k) (a i : Fin k) (h : Except hk a i) :
    Eligible hk i (M hk a 4) ∨ Eligible hk i (M hk a 8) ∨ Eligible hk i (M hk a 4+M hk a 8) := by
  rcases h with rfl|rfl|rfl|rfl|rfl <;> simp only [Eligible,M,adv_adv,Nat.reduceAdd] <;> tauto

def Cover (hk : 0<k) (mark : Fin k → Bool) :=
  (∃ a b, ∀ i, mark i=true → Triple hk a i ∨ Triple hk b i) ∨
  (∃ a, ∀ i, mark i=true → Except hk a i)
lemma eligible_cover (hk : 0<k) (mark : Fin k → Bool) (h : Cover hk mark) :
    ∃ q r : D k, ∀ i, mark i=true → Eligible hk i q ∨ Eligible hk i r ∨ Eligible hk i (q+r) := by
  rcases h with ⟨a,b,h⟩|⟨a,h⟩
  · refine ⟨M hk a 3+M hk a 5,M hk b 3+M hk b 5,fun i hi => ?_⟩
    rcases h i hi with h|h
    · exact .inl (triple_rows hk a i h)
    · exact .inr (.inl (triple_rows hk b i h))
  · exact ⟨_,_,fun i hi => except_rows hk a i (h i hi)⟩

def ask₂ (q r : D k) (j : Fin 2) (_ : ℕ) := if j=0 then q else r
def run₂ (ask : Fin 2 → ℕ → D k) (x : W k) :=
  (List.finRange 2).foldl (fun h j => 2*h + (if ask j h x=0 then 0 else 1)) (0:ℕ)
def firstBit (h : ℕ) : F := if h/2=0 then 0 else 1
def lastBit (h : ℕ) : F := if h%2=0 then 0 else 1
lemma run₂_decode (q r : D k) (x : W k) :
    firstBit (run₂ (ask₂ q r) x)=q x ∧ lastBit (run₂ (ask₂ q r) x)=r x := by
  have z2 : ∀ t : F, t=0 ∨ t=1 := by decide
  have e : List.finRange 2 = [0,1] := by decide
  rcases z2 (q x) with hq|hq <;> rcases z2 (r x) with hr|hr <;>
    simp [run₂,ask₂,e,hq,hr,firstBit,lastBit]

theorem sufficient (hk : 0<k) (hk' : 25≤k) (mark : Fin k → Bool) (nm c₁ c₂ : W k)
    (cover : Cover hk mark) :
    ∃ (ask : Fin 2 → ℕ → D k) (readout : ℕ → Fin k → W k → F),
      (∀ h i, Cubic (readout h i)) ∧
      ∀ x i, mark i=true → row hk nm c₁ c₂ i x=readout (run₂ ask x) i x := by
  classical
  obtain ⟨q,r,H⟩ := eligible_cover hk mark cover
  have leaf (h : ℕ) (i : Fin k) : ∃ f, Cubic f ∧
      ∀ x, mark i=true → q x=firstBit h → r x=lastBit h → row hk nm c₁ c₂ i x=f x := by
    by_cases hi : mark i=true
    · rcases H i hi with hq|hr|hs
      · obtain ⟨f,hf,ef⟩ := eligible_read hk hk' nm c₁ c₂ i q hq (firstBit h)
        exact ⟨f,hf,fun x _ e _ => ef x e⟩
      · obtain ⟨f,hf,ef⟩ := eligible_read hk hk' nm c₁ c₂ i r hr (lastBit h)
        exact ⟨f,hf,fun x _ _ e => ef x e⟩
      · obtain ⟨f,hf,ef⟩ := eligible_read hk hk' nm c₁ c₂ i (q+r) hs (firstBit h+lastBit h)
        exact ⟨f,hf,fun x _ e g => ef x (by simp [e,g])⟩
    · exact ⟨_,(P.con 3 0).cubic,fun _ j => False.elim (hi j)⟩
  refine ⟨ask₂ q r,fun h i => (leaf h i).choose,fun h i => (leaf h i).choose_spec.1,?_⟩
  intro x i hi
  obtain ⟨a,b⟩ := run₂_decode q r x
  exact (leaf _ i).choose_spec.2 x hi a.symm b.symm

end PC29928


namespace ParityWindows29928

structure Window (P : ℕ → Prop) (r : ℕ) : Prop where
  hit : ∃ n, P n
  bounds : ∀ n, P n → r ≤ n ∧ n ≤ r+4
  left : P r → P (r+2) ∨ P (r+4)
  mid : P (r+2) → P r ∨ P (r+4)
  right : P (r+4) → P r ∨ P (r+2)

private theorem fromRight {P : ℕ → Prop} {a b : ℕ} (w : Window P a)
    (gap : a+3 ≤ b) (sub : ∀ n, P n → b ≤ n) : b=a+3 ∧ ∀ n, P n ↔ n=a+3 := by
  have no0 (h : P a) := sub _ h
  have no2 (h : P (a+2)) := sub _ h
  have no4 (h : P (a+4)) : False := by rcases w.right h with t|t <;> first | have := no0 t; omega | have := no2 t; omega
  have only (n) (h : P n) : n=a+3 := by
    have := sub _ h; have := w.bounds _ h
    by_contra ne; have e : n=a+4 := by omega
    exact no4 (e ▸ h)
  obtain ⟨n,hn⟩ := w.hit
  have en := only _ hn; have := sub _ hn
  exact ⟨by omega,fun m => ⟨only m,fun e => (e.trans en.symm) ▸ hn⟩⟩

private theorem fromLeft {P : ℕ → Prop} {b c : ℕ} (w : Window P c)
    (gap : b+3 ≤ c) (sub : ∀ n, P n → n ≤ b+4) : c=b+3 ∧ ∀ n, P n ↔ n=c+1 := by
  have no2 (h : P (c+2)) := sub _ h
  have no4 (h : P (c+4)) := sub _ h
  have no0 (h : P c) : False := by rcases w.left h with t|t <;> first | have := no2 t; omega | have := no4 t; omega
  have only (n) (h : P n) : n=c+1 := by
    have := sub _ h; have := w.bounds _ h
    by_contra ne; have e : n=c := by omega
    exact no0 (e ▸ h)
  obtain ⟨n,hn⟩ := w.hit
  have en := only _ hn; have := sub _ hn
  exact ⟨by omega,fun m => ⟨only m,fun e => (e.trans en.symm) ▸ hn⟩⟩

private theorem singleton {P : ℕ → Prop} {n r : ℕ} (w : Window P r) (p : ∀ t, P t ↔ t=n) : n=r+1 ∨ n=r+3 := by
  have h := w.bounds n ((p n).2 rfl)
  have A := w.left; have B := w.mid; have C := w.right
  simp only [p] at A B C
  omega

private theorem apart {P : ℕ → Prop} {a b : ℕ} (wa : Window P a) (wb : Window P b) (gap : a+3 ≤ b) : False := by
  obtain ⟨e,p⟩ := fromRight wa gap (fun n h => (wb.bounds n h).1)
  have := singleton wb p; omega

private theorem line {M : ℕ → Prop} (P : Fin 3 → ℕ → Prop)
    (served : ∀ r, M r → ∃ j, Window (P j) r)
    (cancel : ∀ j l m : Fin 3, j≠l → j≠m → l≠m → ∀ n, P j n → P l n ∨ P m n) :
    (∃ a b : ℕ, ∀ r, M r → (a ≤ r ∧ r ≤ a+2) ∨ (b ≤ r ∧ r ≤ b+2)) ∨
    (∃ a : ℕ, ∀ r, M r → r=a ∨ r=a+2 ∨ r=a+3 ∨ r=a+4 ∨ r=a+6) := by
  classical
  by_cases hA : ∃ r, M r
  · let a := Nat.find hA
    have ha : M a := Nat.find_spec hA
    have minA : ∀ r, M r → a ≤ r := fun _ h => Nat.find_min' hA h
    by_cases hB : ∃ r, M r ∧ a+3 ≤ r
    · let b := Nat.find hB
      obtain ⟨hb,hab⟩ : M b ∧ a+3 ≤ b := Nat.find_spec hB
      have minB : ∀ r, M r → a+3 ≤ r → b ≤ r := fun _ h g => Nat.find_min' hB ⟨h,g⟩
      by_cases hC : ∃ r, M r ∧ b+3 ≤ r
      · obtain ⟨c,hc,hbc⟩ := hC
        obtain ⟨i,wi⟩ := served a ha; obtain ⟨j,wj⟩ := served b hb; obtain ⟨k,wk⟩ := served c hc
        have ij : i≠j := fun e => apart (e ▸ wi) wj hab
        have jk : j≠k := fun e => apart (e ▸ wj) wk hbc
        have ik : i≠k := fun e => apart (e ▸ wi) wk (by omega)
        obtain ⟨eb,pi⟩ := fromRight wi hab (by
          intro n hn; rcases cancel i j k ij ik jk n hn with h|h
          · exact (wj.bounds n h).1
          · have := wi.bounds n hn; have := wk.bounds n h; omega)
        obtain ⟨ec,pk⟩ := fromLeft wk hbc (by
          intro n hn; rcases cancel k i j ik.symm jk.symm ij n hn with h|h
          · have := wi.bounds n h; have := wk.bounds n hn; omega
          · exact (wj.bounds n h).2)
        have ji : P j (a+3) := by
          rcases cancel i j k ij ik jk _ ((pi _).2 rfl) with h|h
          · exact h
          · have := (pk _).1 h; omega
        have jk' : P j (c+1) := by
          rcases cancel k i j ik.symm jk.symm ij _ ((pk _).2 rfl) with h|h
          · have := (pi _).1 h; omega
          · exact h
        right; refine ⟨a,?_⟩; intro r hr; obtain ⟨l,w⟩ := served r hr
        have cases : l=i ∨ l=j ∨ l=k := by omega
        rcases cases with e|e|e <;> subst l
        · have := singleton w pi; omega
        · have := w.bounds _ ji; have := w.bounds _ jk'; omega
        · have := singleton w pk; omega
      · left; refine ⟨a,b,?_⟩; intro r h
        have := minA r h
        by_cases g : a+3 ≤ r
        · have := minB r h g; have q : ¬ b+3 ≤ r := fun t => hC ⟨r,h,t⟩; omega
        · omega
    · left; refine ⟨a,a,?_⟩; intro r h; have := minA r h; have q : ¬a+3 ≤ r := fun t => hB ⟨r,h,t⟩; omega
  · exact Or.inl ⟨0,0,fun r h => False.elim (hA ⟨r,h⟩)⟩

open Fin.NatCast

def Serves {k : ℕ} [NeZero k] (S : Finset (Fin k)) (i : Fin k) : Prop :=
  S.Nonempty ∧ ∃ p : Fin 5 → Bool,
    ((p 0 ^^ p 2) ^^ p 4) = false ∧
    S = (Finset.univ.filter (fun t => p t = true)).image (fun t => i + (t.val : Fin k))

def Triple {k : ℕ} [NeZero k] (a i : Fin k) : Prop :=
  i=a ∨ i=a+1 ∨ i=a+2

def Pattern {k : ℕ} [NeZero k] (a i : Fin k) : Prop :=
  i=a ∨ i=a+2 ∨ i=a+3 ∨ i=a+4 ∨ i=a+6

theorem classifyFamily {k : ℕ} [NeZero k] (hk : 25 ≤ k) (M : Fin k → Prop)
    (S : Fin 3 → Finset (Fin k))
    (cancel : ∀ j l m : Fin 3, j≠l → j≠m → l≠m → ∀ n, n ∈ S j → n ∈ S l ∨ n ∈ S m)
    (served : ∀ i, M i → ∃ j, Serves (S j) i) :
    (∃ a b, ∀ i, M i → Triple a i ∨ Triple b i) ∨ (∃ a, ∀ i, M i → Pattern a i) := by
  classical
  let tap (j : Fin 3) := if h : (S j).Nonempty then h.choose else 0
  have ht (j) (h : (S j).Nonempty) : tap j ∈ S j := by simpa [tap,h] using h.choose_spec
  let bad (e : Fin 3 × Fin 8) : Fin k := tap e.1 + (e.2.val : Fin k) - 3
  let B := Finset.univ.image bad
  obtain ⟨base,outside⟩ : ∃ base : Fin k, base ∉ B := by
    by_contra! h
    have cover : B=Finset.univ := Finset.eq_univ_of_forall h
    have hcard : B.card ≤ (Finset.univ : Finset (Fin 3 × Fin 8)).card := Finset.card_image_le
    rw [cover] at hcard; simp at hcard; omega
  let f (n : ℕ) : Fin k := base + (n : Fin k)
  have inj {n m : ℕ} (hn : n<k) (hm : m<k) (e : f n=f m) : n=m := by
    have ee := congrArg Fin.val (add_left_cancel e : (n : Fin k)=(m : Fin k))
    simpa [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hm] using ee
  have addf (n t : ℕ) : f (n+t)= f n+(t : Fin k) := by simp [f,add_assoc]
  let P (j : Fin 3) (n : ℕ) := n<k ∧ f n ∈ S j
  have liftWin {r : ℕ} (hr : r<k) {j : Fin 3} (w : Serves (S j) (f r)) : Window (P j) r := by
    obtain ⟨hnz,p,par,es⟩ := w
    obtain ⟨t,_,et⟩ := Finset.mem_image.mp (es ▸ ht j hnz)
    have bound : r+4<k := by
      by_contra! wrap
      let n := k-r+3-t.val
      have tn := t.isLt
      have hn : n<8 := by dsimp [n]; omega
      have he : n+t.val+r=k+3 := by dsimp [n]; omega
      have he' : (n : Fin k)+(t.val : Fin k)+(r : Fin k)=3 := by
        rw [←Nat.cast_add,←Nat.cast_add,he]; simp
      apply outside
      apply Finset.mem_image.mpr
      refine ⟨(j,⟨n,hn⟩),Finset.mem_univ _,?_⟩
      change tap j + (n : Fin k) - 3 = base
      rw [←et]; change base + (r : Fin k) + (t.val : Fin k) + (n : Fin k) - 3 = base
      calc
        _ = base + ((n : Fin k)+(t.val : Fin k)+(r : Fin k)) - 3 := by abel
        _ = _ := by rw [he']; abel
    have mem (m : ℕ) : P j m ↔ ∃ t : Fin 5, p t=true ∧ m=r+t.val := by
      constructor
      · rintro ⟨hm,hh⟩; rw [es] at hh
        obtain ⟨t,ht',eq⟩ := Finset.mem_image.mp hh
        refine ⟨t,(Finset.mem_filter.mp ht').2,inj hm (by have := t.isLt; omega) ?_⟩
        rwa [addf,eq]
      · rintro ⟨t,hp,rfl⟩
        exact ⟨by have := t.isLt; omega,by rw [es,addf]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)⟩
    have at' (t : Fin 5) : P j (r+t.val) ↔ p t=true := by
      rw [mem]; constructor
      · rintro ⟨v,hv,e⟩; have : v=t := Fin.ext (by omega); simpa [this] using hv
      · exact fun h => ⟨t,h,rfl⟩
    have h0 : P j r ↔ p 0=true := by simpa using at' 0
    have h2 : P j (r+2) ↔ p 2=true := at' 2
    have h4 : P j (r+4) ↔ p 4=true := at' 4
    refine ⟨?_,?_,?_,?_,?_⟩
    · have hmem := ht j hnz; rw [es] at hmem
      obtain ⟨v,hv,_⟩ := Finset.mem_image.mp hmem
      exact ⟨_,(at' v).2 (Finset.mem_filter.mp hv).2⟩
    · intro m hm; obtain ⟨v,_,e⟩ := (mem m).1 hm; have := v.isLt; omega
    all_goals rw [h0,h2,h4] <;> revert par <;> cases p 0 <;> cases p 2 <;> cases p 4 <;> decide
  let L (r : ℕ) := r<k ∧ M (f r)
  have sv (r) (h : L r) : ∃ j, Window (P j) r := by
    obtain ⟨j,w⟩ := served _ h.2; exact ⟨j,liftWin h.1 w⟩
  have ca : ∀ j l m : Fin 3, j≠l → j≠m → l≠m → ∀ n, P j n → P l n ∨ P m n := by
    rintro j l m jl jm lm n ⟨hn,h⟩
    rcases cancel j l m jl jm lm _ h with t|t
    · exact Or.inl ⟨hn,t⟩
    · exact Or.inr ⟨hn,t⟩
  have repr (i : Fin k) : f (i-base).val=i := by simp [f]
  have tri {a r : ℕ} (lo : a ≤ r) (hi : r ≤ a+2) : Triple (f a) (f r) := by
    rcases (show r=a ∨ r=a+1 ∨ r=a+2 by omega) with e|e|e <;> simp [Triple,e,addf]
  rcases line P sv ca with ⟨a,b,h⟩|⟨a,h⟩
  · left; refine ⟨f a,f b,?_⟩; intro i hi
    have hr : L (i-base).val := ⟨(i-base).isLt,(repr i).symm ▸ hi⟩
    rw [←repr i]; rcases h _ hr with t|t
    · exact Or.inl (tri t.1 t.2)
    · exact Or.inr (tri t.1 t.2)
  · right; refine ⟨f a,?_⟩; intro i hi
    have hr : L (i-base).val := ⟨(i-base).isLt,(repr i).symm ▸ hi⟩
    rw [←repr i]; rcases h _ hr with e|e|e|e|e <;> simp [Pattern,e,addf]

end ParityWindows29928


namespace ParityRow29928
open PC29928
open scoped symmDiff
variable {k : ℕ} [NeZero k]

private lemma adv_cast (hk : 0<k) (i : Fin k) (n : ℕ) : adv hk i n=i+Fin.ofNat k n := by
  apply Fin.ext; simp [adv,ix,Fin.add_def,Fin.ofNat,Nat.add_mod_mod]

private lemma next_one (hk : 0<k) (i : Fin k) : adv hk i 1=i+1 := adv_cast hk i 1

private lemma prev_one (hk : 0<k) (hk' : 25≤k) (i : Fin k) : back hk i 1=i-1 := by
  simpa only [next_one,sub_add_cancel] using back_next hk hk' (i-1)


theorem mixed_tap (hk : 0<k) (hk' : 25≤k) (i : Fin k) (j : Fin 5) :
    mixed hk (adv hk i (j.val+1)) = ParityEncode29928.tap (ParityMask29928.pos i j) := by
  rw [←adv_adv hk i j.val 1, adv_cast hk i j.val]
  simp only [mixed,prev_one hk hk',next_one,add_sub_cancel_right,ParityEncode29928.tap,
    ParityMask29928.pos,proj]


theorem rowCover (hk : 0<k) (hk' : 25≤k) (mark : Fin k → Bool) (nm c₁ c₂ : W k)
    (ask : Fin 2 → ℕ → D k) (readout : ℕ → Fin k → W k → F)
    (cub : ∀ h i, Cubic (readout h i))
    (correct : ∀ x i, mark i=true → row hk nm c₁ c₂ i x=readout (run₂ ask x) i x) :
    ∃ A B : Finset (Fin k), ∀ i, mark i=true → ParityCover29928.permitted i A ∨
      ParityCover29928.permitted i B ∨ ParityCover29928.permitted i (A∆B) := by
  apply ParityCover29928.cover hk' (fun i => mark i=true) (ask 0 0) (ask 1 0)
  intro i hi
  let T := fun j : Fin 5 => ParityEncode29928.tap (ParityMask29928.pos i j)
  let c := fun j : Fin 5 => z hk nm (adv hk i (j.val+1)) 0
  apply ParityLocal29928.necessary T c (ask 0 0) (ask 1 0) (readout 0 i) (remn hk nm c₁ c₂ i)
    (cub 0 i) (remn_cubic hk nm c₁ c₂ i)
  intro x hq hr
  have hz : run₂ ask x=0 := ParityLocal29928.run_zero ask x hq hr
  have he := correct x i hi
  rw [hz] at he
  rw [←he,row_decomp hk hk']
  have tap_eq (j : Fin 5) : tap hk nm i (j.val+1) x = T j x + c j := by
    rw [tap_split,mixed_tap hk hk']
  exact congrArg (fun f : F => remn hk nm c₁ c₂ i x + f)
    (congrArg₂ (·*·) (congrArg₂ (·*·) (congrArg₂ (·*·) (tap_eq 1) (tap_eq 3))
      (congrArg₂ (·+·) (tap_eq 0) (tap_eq 4))) (congrArg₂ (·+·) (tap_eq 2) (tap_eq 4)))

end ParityRow29928

open scoped symmDiff
namespace ParityFinal29928
private theorem classify {k : ℕ} [NeZero k] (hk : 0<k) (hk' : 25≤k) (mark : Fin k → Bool)
    (H : ∃ A B : Finset (Fin k), ∀ i, mark i=true → ParityCover29928.permitted i A ∨ ParityCover29928.permitted i B ∨ ParityCover29928.permitted i (A∆B)) : PC29928.Cover hk mark := by
  obtain ⟨A,B,hh⟩ := H
  let S : Fin 3 → Finset (Fin k) := ![A,B,A∆B]
  have cc (j l m : Fin 3) (jl:j≠l) (jm:j≠m) (lm:l≠m) (n : Fin k) (hn:n∈S j) : n∈S l ∨ n∈S m := by
    fin_cases j <;> fin_cases l <;> fin_cases m <;> simp_all [S,Finset.mem_symmDiff] <;> tauto
  have ss (i : Fin k) (hi : mark i=true) : ∃ j, ParityWindows29928.Serves (S j) i := by
    rcases hh i hi with h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  have ad (a : Fin k) (n : ℕ) : PC29928.adv hk a n = a + Fin.ofNat k n := by
    apply Fin.ext; simp [PC29928.adv,PC29928.ix,Fin.add_def,Fin.ofNat,Nat.add_mod]
  have a1 (a : Fin k) : PC29928.adv hk a 1 = a+1 := by rw [ad]; rfl
  have a2 (a : Fin k) : PC29928.adv hk a 2 = a+2 := by rw [ad]; rfl
  have a3 (a : Fin k) : PC29928.adv hk a 3 = a+3 := by rw [ad]; rfl
  have a4 (a : Fin k) : PC29928.adv hk a 4 = a+4 := by rw [ad]; rfl
  have a6 (a : Fin k) : PC29928.adv hk a 6 = a+6 := by rw [ad]; rfl
  simpa only [PC29928.Cover,PC29928.Triple,PC29928.Except,ParityWindows29928.Triple,ParityWindows29928.Pattern,a1,a2,a3,a4,a6] using ParityWindows29928.classifyFamily hk' (fun i => mark i=true) S cc ss
end ParityFinal29928

end PEqualNP.Outside.L_meta_29928_aux
open PEqualNP.Outside.L_meta_29928_aux

theorem PEqualNP.Outside.L_meta_29928 :
  let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
      (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
    let F := ZMod 2
    let W := Fin k → F
    let D := W →ₗ[F] F
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
    let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
      x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
    let step := fun (x : W) (i : Fin k) =>
      x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
    let gap := fun b : Bool => if b then 2 else (1 : ℕ)
    let spin := fun b : Bool => if b then 3 else (1 : ℕ)
    let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
    let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
    let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
    let out := fun (x : W) (b : Bool) =>
      let z := mix (gap b) (rot (spin b) x + name b)
      let y := step z + rot (if b then 4 else 0) x + c₁ b
      step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
      (∀ h b i, cubic (readout h b i)) ∧
      ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
        out x b i = readout (run ask x) b i x
  ∀ (k : ℕ) (hk : 0 < k), 25 ≤ k →
    ∀ (mark : Fin k → Bool) (name c₁ c₂ : Bool → Fin k → ZMod 2),
      let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let triple := fun (a i : Fin k) =>
        i = a ∨ i = ix (a.val + 1) ∨ i = ix (a.val + 2)
      fits k hk (fun i => (mark i, false)) 2 name c₁ c₂ ↔
        (∃ a b : Fin k, ∀ i, mark i = true → triple a i ∨ triple b i) ∨
        (∃ a : Fin k, ∀ i, mark i = true →
          i = a ∨ i = ix (a.val + 2) ∨ i = ix (a.val + 3) ∨
          i = ix (a.val + 4) ∨ i = ix (a.val + 6)) := by
  dsimp only
  intro k hk hk' mark nm c₁ c₂
  letI : NeZero k := ⟨by omega⟩
  constructor
  · rintro ⟨ask,rd,cub,correct⟩
    apply ParityFinal29928.classify hk hk' mark
    exact ParityRow29928.rowCover hk hk' mark (nm false) (c₁ false) (c₂ false) ask (fun h i => rd h false i) (fun h i => cub h false i) (fun x i hi => correct x false i hi)
  · intro cov
    obtain ⟨ask,rd,cub,correct⟩ := PC29928.sufficient hk hk' mark (nm false) (c₁ false) (c₂ false) cov
    refine ⟨ask,fun h _ i => rd h i,fun h _ i => cub h i,?_⟩
    intro x b i h; cases b with
    | false => exact correct x i h
    | true => contradiction
