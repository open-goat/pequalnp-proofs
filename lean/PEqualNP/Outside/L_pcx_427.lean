import Mathlib
import PEqualNP.Defs

/-!
# Exact second parity batch cost for local binary quadratics

On the common radical `R` of the restricted polars, the derivative of block `i` at a base
point is a linear functional on `R`. The periods of the outputs on a translate `a + S` are the
common kernel of the chosen functionals inside `R`. Rado's theorem with deficiency (for linear
matroids) gives the best choice of base points, and the kernel of all available functionals
of the blocks in `J` is the space of `R`-directions which are global periods on `J`.
-/

namespace PEqualNP.Outside.L_pcx_427_aux

open Submodule Module

/-! ### Rado's theorem with deficiency for linear matroids -/

section RadoDef

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*}

/-- The union of the sets `A j` over `j ∈ s`. -/
def un (A : ι → Finset W) (s : Finset ι) : Set W := ⋃ j ∈ s, (A j : Set W)

lemma un_finite (A : ι → Finset W) (s : Finset ι) : (un A s).Finite :=
  s.finite_toSet.biUnion fun j _ => (A j).finite_toSet

lemma un_insert [DecidableEq ι] (A : ι → Finset W) (i : ι) (s : Finset ι) :
    un A (insert i s) = (A i : Set W) ∪ un A s := by
  simp only [un, Finset.set_biUnion_insert]

lemma un_union [DecidableEq ι] (A : ι → Finset W) (s t : Finset ι) :
    un A (s ∪ t) = un A s ∪ un A t := by
  simp only [un, Finset.set_biUnion_union]

lemma un_mono (A : ι → Finset W) {s t : Finset ι} (h : s ⊆ t) : un A s ⊆ un A t :=
  Set.biUnion_subset_biUnion_left (fun _ hx => h hx)

lemma un_update_of_not_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∉ s) : un (Function.update A i B) s = un A s := by
  unfold un
  refine Set.iUnion₂_congr fun j hj => ?_
  rw [Function.update_of_ne (by rintro rfl; exact h hj)]

lemma un_update_of_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∈ s) :
    un (Function.update A i B) s = (B : Set W) ∪ un A (s.erase i) := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [un_insert, un_update_of_not_mem _ _ _ _ (Finset.notMem_erase i s),
    Function.update_self]

/-- The rank condition with deficiency `d`. -/
def GoodD (K : Type*) [Field K] [Module K W] (d : ℕ) (A : ι → Finset W) : Prop :=
  ∀ s : Finset ι, s.card ≤ finrank K (span K (un A s)) + d

lemma finrank_span_mono {X Y : Set W} (hY : Y.Finite) (h : X ⊆ Y) :
    finrank K (span K X) ≤ finrank K (span K Y) := by
  haveI := FiniteDimensional.span_of_finite K hY
  exact Submodule.finrank_mono (span_mono h)

lemma bad_erase [DecidableEq ι] [DecidableEq W] (d : ℕ) (A : ι → Finset W)
    (hA : GoodD K d A) (i : ι)
    (c : W) (h : ¬ GoodD K d (Function.update A i ((A i).erase c))) :
    ∃ t : Finset ι, i ∉ t ∧
      finrank K (span K ((((A i).erase c : Finset W) : Set W) ∪ un A t)) + d ≤ t.card := by
  simp only [GoodD, not_forall, not_le] at h
  obtain ⟨s, hs⟩ := h
  by_cases hi : i ∈ s
  · refine ⟨s.erase i, Finset.notMem_erase i s, ?_⟩
    rw [un_update_of_mem _ _ _ _ hi] at hs
    have := Finset.card_erase_add_one hi
    omega
  · rw [un_update_of_not_mem _ _ _ _ hi] at hs
    exact absurd (hA s) (not_le.mpr hs)

lemma erase_good [DecidableEq ι] [DecidableEq W] (d : ℕ) (A : ι → Finset W)
    (hA : GoodD K d A) (i : ι)
    {a b : W} (ha : a ∈ A i) (hb : b ∈ A i) (hab : a ≠ b) :
    GoodD K d (Function.update A i ((A i).erase a)) ∨
      GoodD K d (Function.update A i ((A i).erase b)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨t1, hi1, h1⟩ := bad_erase d A hA i a hcon.1
  obtain ⟨t2, hi2, h2⟩ := bad_erase d A hA i b hcon.2
  set X : Set W := (((A i).erase a : Finset W) : Set W) ∪ un A t1 with hX
  set Y : Set W := (((A i).erase b : Finset W) : Set W) ∪ un A t2 with hY
  have hXf : X.Finite := ((A i).erase a).finite_toSet.union (un_finite A t1)
  have hYf : Y.Finite := ((A i).erase b).finite_toSet.union (un_finite A t2)
  haveI : FiniteDimensional K (span K X) := FiniteDimensional.span_of_finite K hXf
  haveI : FiniteDimensional K (span K Y) := FiniteDimensional.span_of_finite K hYf
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span K X) (span K Y)
  have hU : un A (insert i (t1 ∪ t2)) ⊆ X ∪ Y := by
    rw [un_insert, un_union]
    intro x hx
    rcases hx with hx | hx | hx
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inr (Or.inl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hab, ha⟩)))
      · exact Or.inl (Or.inl (by simp [Finset.mem_erase, hxa, hx]))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)
  have hi12 : i ∉ t1 ∪ t2 := by simp [hi1, hi2]
  have hcardU := hA (insert i (t1 ∪ t2))
  rw [Finset.card_insert_of_notMem hi12] at hcardU
  have hsup : finrank K (span K (un A (insert i (t1 ∪ t2)))) ≤
      finrank K ↥(span K X ⊔ span K Y) := by
    rw [← Submodule.span_union]
    exact finrank_span_mono (hXf.union hYf) hU
  have hinf : finrank K (span K (un A (t1 ∩ t2))) ≤ finrank K ↥(span K X ⊓ span K Y) := by
    haveI : FiniteDimensional K ↥(span K X ⊓ span K Y) :=
      Submodule.finiteDimensional_inf_left _ _
    refine Submodule.finrank_mono (le_inf (span_mono ?_) (span_mono ?_))
    · exact (un_mono A Finset.inter_subset_left).trans Set.subset_union_right
    · exact (un_mono A Finset.inter_subset_right).trans Set.subset_union_right
  have hcardI := hA (t1 ∩ t2)
  have hc := Finset.card_union_add_card_inter t1 t2
  omega

/-- Rado's theorem with deficiency, by induction on the total size of the sets. -/
theorem rado_def [Fintype ι] [DecidableEq ι] [DecidableEq W] (d : ℕ) :
    ∀ n : ℕ, ∀ A : ι → Finset W, ∑ j, (A j).card = n → GoodD K d A →
      (∀ j, (A j).Nonempty) →
      ∃ f : ι → W, (∀ j, f j ∈ A j) ∧
        Fintype.card ι ≤ finrank K (span K (Set.range f)) + d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hA hne
  by_cases hbig : ∃ i, 1 < (A i).card
  · obtain ⟨i, hi⟩ := hbig
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi
    have key : ∃ c ∈ A i, GoodD K d (Function.update A i ((A i).erase c)) := by
      rcases erase_good d A hA i ha hb hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    obtain ⟨c, hc, hgood⟩ := key
    set A' := Function.update A i ((A i).erase c) with hA'
    have hlt : ∑ j, (A' j).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [hA', Function.update_self]
          exact Finset.card_erase_le
        · simp only [hA', Function.update_of_ne hj, le_refl]
      · simp only [hA', Function.update_self]
        exact Finset.card_erase_lt_of_mem hc
    have hne' : ∀ j, (A' j).Nonempty := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [hA', Function.update_self]
        rw [← Finset.card_pos, Finset.card_erase_of_mem hc]
        omega
      · simp only [hA', Function.update_of_ne hj]
        exact hne j
    obtain ⟨f, hf, hli⟩ := ih _ hlt A' rfl hgood hne'
    refine ⟨f, fun j => ?_, hli⟩
    have := hf j
    by_cases hj : j = i
    · subst hj; simp only [hA', Function.update_self] at this
      exact Finset.mem_of_mem_erase this
    · simpa only [hA', Function.update_of_ne hj] using this
  · push_neg at hbig
    have hone : ∀ j, ∃ v, A j = {v} := by
      intro j
      exact Finset.card_eq_one.mp (le_antisymm (hbig j) (Finset.card_pos.mpr (hne j)))
    choose f hf using hone
    refine ⟨f, fun j => by simp [hf j], ?_⟩
    have h := hA Finset.univ
    have hr : un A Finset.univ = Set.range f := by
      ext x; simp [un, hf, eq_comm]
    rw [hr, Finset.card_univ] at h
    exact h

/-- Min-max form: a choice of representatives whose rank is at least
`|ι| - |J| + rank (⋃_{j ∈ J} A j)` for some `J`. -/
theorem rado_minmax [Fintype ι] [DecidableEq ι] [DecidableEq W] (A : ι → Finset W)
    (hne : ∀ j, (A j).Nonempty) :
    ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ ∃ J : Finset ι,
      Fintype.card ι + finrank K (span K (un A J)) ≤
        finrank K (span K (Set.range f)) + J.card := by
  obtain ⟨J, -, hJ⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset ι))
    (fun s => s.card - finrank K (span K (un A s))) Finset.univ_nonempty
  have hgood : GoodD K (J.card - finrank K (span K (un A J))) A := by
    intro s
    have := hJ s (Finset.mem_univ _)
    omega
  obtain ⟨f, hf, hcard⟩ := rado_def (K := K) _ _ A rfl hgood hne
  refine ⟨f, hf, ?_⟩
  by_cases hle : J.card ≤ finrank K (span K (un A J))
  · refine ⟨∅, ?_⟩
    have h0 : un A (∅ : Finset ι) = ∅ := by simp [un]
    rw [h0, Submodule.span_empty, finrank_bot, Finset.card_empty]
    omega
  · exact ⟨J, by omega⟩

end RadoDef

/-! ### Linear algebra helpers -/

section LinAlg

variable {K : Type*} [Field K]

lemma mem_coann_span {V : Type*} [AddCommGroup V] [Module K V] (Φ : Set (Module.Dual K V))
    (x : V) : x ∈ (span K Φ).dualCoannihilator ↔ ∀ φ ∈ Φ, φ x = 0 := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h φ hφ
    exact h φ (subset_span hφ)
  · intro h φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]

/-- Padding by zeros. -/
def pad (K : Type*) [Field K] (m e : ℕ) : (Fin m → K) →ₗ[K] (Fin e → K) where
  toFun y j := if h : (j : ℕ) < m then y ⟨j, h⟩ else 0
  map_add' y y' := by
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c y := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

lemma pad_injective {m e : ℕ} (hme : m ≤ e) : Function.Injective (pad K m e) := by
  intro y y' h
  funext j
  have := congrFun h ⟨j, lt_of_lt_of_le j.2 hme⟩
  simpa [pad, j.isLt] using this

/-- A linear query map whose kernel on `S` lies in `P`, when `dim S ≤ e + dim P`. -/
lemma exists_ask {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (S P : Submodule K X) (hPS : P ≤ S) (e : ℕ)
    (hdim : finrank K S ≤ e + finrank K P) :
    ∃ ask : X →ₗ[K] (Fin e → K), ∀ w ∈ S, ask w = 0 → w ∈ P := by
  set P' : Submodule K S := P.comap S.subtype with hP'
  have hP'f : finrank K P' = finrank K P := by
    rw [← Submodule.finrank_map_subtype_eq S P', hP', Submodule.map_comap_subtype,
      inf_eq_right.mpr hPS]
  have hq := Submodule.finrank_quotient_add_finrank P'
  have hme : finrank K (S ⧸ P') ≤ e := by omega
  let b := Module.finBasis K (S ⧸ P')
  let g0 : S →ₗ[K] (Fin e → K) :=
    (pad K _ e) ∘ₗ b.equivFun.toLinearMap ∘ₗ P'.mkQ
  obtain ⟨ask, hask⟩ := LinearMap.exists_extend g0
  refine ⟨ask, fun w hw h0 => ?_⟩
  have h1 : g0 ⟨w, hw⟩ = 0 := by
    have := LinearMap.congr_fun hask ⟨w, hw⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [← this, h0]
  have h2 : b.equivFun (P'.mkQ ⟨w, hw⟩) = 0 := by
    apply pad_injective hme
    simpa [g0] using h1
  have h3 : P'.mkQ ⟨w, hw⟩ = 0 := by
    have := congrArg b.equivFun.symm h2
    simpa using this
  have h4 : (⟨w, hw⟩ : S) ∈ P' := by
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  simpa [hP'] using h4

/-- Answers from the queries. -/
lemma exists_ask_out {X Y : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (S P : Submodule K X) (hPS : P ≤ S) (e : ℕ)
    (hdim : finrank K S ≤ e + finrank K P) (g : X → Y) (a : X)
    (hper : ∀ w ∈ S, ∀ k ∈ P, g (a + w + k) = g (a + w)) :
    ∃ (ask : X →ₗ[K] (Fin e → K)) (out : (Fin e → K) → Y),
      ∀ w ∈ S, out (ask (a + w)) = g (a + w) := by
  classical
  obtain ⟨ask, hask⟩ := exists_ask S P hPS e hdim
  refine ⟨ask, fun y => if h : ∃ w, w ∈ S ∧ ask (a + w) = y then g (a + h.choose) else g a,
    fun w hw => ?_⟩
  have hex : ∃ w', w' ∈ S ∧ ask (a + w') = ask (a + w) := ⟨w, hw, rfl⟩
  dsimp only
  rw [dif_pos hex]
  obtain ⟨hS', hask'⟩ := hex.choose_spec
  set w' := hex.choose
  have hk : w' - w ∈ P := by
    apply hask _ (S.sub_mem hS' hw)
    rw [map_sub]
    simp only [map_add] at hask'
    rw [add_right_inj] at hask'
    rw [hask', sub_self]
  have := hper w hw (w' - w) hk
  rw [← this]
  congr 1
  abel

lemma natCard_sub {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M] :
    Nat.card M = 2 ^ finrank (ZMod 2) M := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end LinAlg

/-! ### The blocks -/

section Blocks

variable {r : ℕ} {n : Fin r → ℕ}

/-- The ambient space. -/
abbrev Xs (n : Fin r → ℕ) : Type := (i : Fin r) → Fin (n i) → ZMod 2

/-- The polar form of a block function. -/
def Bf (f : (i : Fin r) → (Fin (n i) → ZMod 2) → ZMod 2) (i : Fin r)
    (u v : Fin (n i) → ZMod 2) : ZMod 2 :=
  f i (u+v) + f i u + f i v + f i 0

lemma z2_add_eq_zero : ∀ x y : ZMod 2, x + y = 0 ↔ x = y := by decide

lemma z2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

variable (f : (i : Fin r) → (Fin (n i) → ZMod 2) → ZMod 2)

lemma Bf_symm (i : Fin r) (u v : Fin (n i) → ZMod 2) : Bf f i u v = Bf f i v u := by
  unfold Bf
  rw [add_comm u v]
  ring

lemma Bf_zero_left (i : Fin r) (v : Fin (n i) → ZMod 2) : Bf f i 0 v = 0 := by
  unfold Bf
  rw [zero_add]
  have key : ∀ x y : ZMod 2, x + y + x + y = 0 := by decide
  exact key _ _

variable (hf : ∀ (i : Fin r) (p u v : Fin (n i) → ZMod 2),
  f i (p+u+v) + f i (p+u) + f i (p+v) + f i p = Bf f i u v)

include hf

lemma Bf_add_left (i : Fin r) (u u' v : Fin (n i) → ZMod 2) :
    Bf f i (u + u') v = Bf f i u v + Bf f i u' v := by
  have h := hf i u u' v
  unfold Bf at h ⊢
  grind

lemma rad_sum (S : Submodule (ZMod 2) (Xs n)) {u u' : Xs n}
    (hu : u ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i (u i) (v i) = 0)
    (hu' : u' ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i (u' i) (v i) = 0) :
    u + u' ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i ((u + u') i) (v i) = 0 := by
  refine ⟨S.add_mem hu.1 hu'.1, fun w hw i => ?_⟩
  simp only [Pi.add_apply]
  rw [Bf_add_left f hf, hu.2 w hw i, hu'.2 w hw i, add_zero]

omit hf in
lemma rad_zero (S : Submodule (ZMod 2) (Xs n)) :
    (0 : Xs n) ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i ((0 : Xs n) i) (v i) = 0 :=
  ⟨S.zero_mem, fun w _ i => Bf_zero_left f i (w i)⟩

omit hf in
lemma rad_smul (S : Submodule (ZMod 2) (Xs n)) (c : ZMod 2) {u : Xs n}
    (hu : u ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i (u i) (v i) = 0) :
    c • u ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i ((c • u) i) (v i) = 0 := by
  rcases z2_cases c with rfl | rfl
  · rw [zero_smul]
    exact rad_zero f S
  · rw [one_smul]
    exact hu

/-- The common radical of the restricted polars. -/
def Rad (S : Submodule (ZMod 2) (Xs n)) : Submodule (ZMod 2) (Xs n) :=
  ⟨⟨⟨{u | u ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i (u i) (v i) = 0}, fun hu hv => rad_sum f hf S hu hv⟩,
    rad_zero f S⟩, fun c _ hu => rad_smul f S c hu⟩

lemma mem_Rad (S : Submodule (ZMod 2) (Xs n)) (u : Xs n) :
    u ∈ Rad f hf S ↔ u ∈ S ∧ ∀ v ∈ S, ∀ i, Bf f i (u i) (v i) = 0 := Iff.rfl

/-- The derivative of block `i` at the base point `p`, as a functional on the radical. -/
def Lam (S : Submodule (ZMod 2) (Xs n)) (i : Fin r) (p : Fin (n i) → ZMod 2) :
    Module.Dual (ZMod 2) (Rad f hf S) where
  toFun k := f i (p + (k : Xs n) i) + f i p
  map_add' k k' := by
    have h := hf i p ((k : Xs n) i) ((k' : Xs n) i)
    have h0 : Bf f i ((k : Xs n) i) ((k' : Xs n) i) = 0 :=
      ((mem_Rad f hf S _).1 k.2).2 k' ((mem_Rad f hf S _).1 k'.2).1 i
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [← add_assoc p]
    grind
  map_smul' c k := by
    rcases z2_cases c with rfl | rfl
    · simp
      grind
    · simp

lemma Lam_apply (S : Submodule (ZMod 2) (Xs n)) (i : Fin r) (p : Fin (n i) → ZMod 2)
    (k : Rad f hf S) : Lam f hf S i p k = f i (p + (k : Xs n) i) + f i p := rfl

/-- The available functionals of block `i`. -/
noncomputable def Av (S : Submodule (ZMod 2) (Xs n)) (i : Fin r) :
    Finset (Module.Dual (ZMod 2) (Rad f hf S)) := by
  classical exact Finset.univ.image (Lam f hf S i)

lemma mem_Av (S : Submodule (ZMod 2) (Xs n)) (i : Fin r) (φ : Module.Dual (ZMod 2) (Rad f hf S)) :
    φ ∈ Av f hf S i ↔ ∃ p, Lam f hf S i p = φ := by
  simp [Av]

lemma mem_un_Av (S : Submodule (ZMod 2) (Xs n)) (J : Finset (Fin r))
    (φ : Module.Dual (ZMod 2) (Rad f hf S)) :
    φ ∈ un (Av f hf S) J ↔ ∃ i ∈ J, ∃ p, Lam f hf S i p = φ := by
  simp only [un, Set.mem_iUnion, Finset.mem_coe, mem_Av, exists_prop]

/-- Periods inside the radical for the block bases `a`. -/
def Pa (S : Submodule (ZMod 2) (Xs n)) (a : Xs n) : Submodule (ZMod 2) (Rad f hf S) :=
  (span (ZMod 2) (Set.range fun i => Lam f hf S i (a i))).dualCoannihilator

/-- Radical directions which are global periods on the blocks in `J`. -/
noncomputable def RJ (S : Submodule (ZMod 2) (Xs n)) (J : Finset (Fin r)) :
    Submodule (ZMod 2) (Rad f hf S) :=
  (span (ZMod 2) (un (Av f hf S) J)).dualCoannihilator

lemma finrank_Pa (S : Submodule (ZMod 2) (Xs n)) (a : Xs n) :
    finrank (ZMod 2) (span (ZMod 2) (Set.range fun i => Lam f hf S i (a i))) +
      finrank (ZMod 2) (Pa f hf S a) = finrank (ZMod 2) (Rad f hf S) :=
  Subspace.finrank_add_finrank_dualCoannihilator_eq _

lemma finrank_RJ (S : Submodule (ZMod 2) (Xs n)) (J : Finset (Fin r)) :
    finrank (ZMod 2) (span (ZMod 2) (un (Av f hf S) J)) +
      finrank (ZMod 2) (RJ f hf S J) = finrank (ZMod 2) (Rad f hf S) :=
  Subspace.finrank_add_finrank_dualCoannihilator_eq _

lemma mem_Pa (S : Submodule (ZMod 2) (Xs n)) (a : Xs n) (k : Rad f hf S) :
    k ∈ Pa f hf S a ↔ ∀ i, f i (a i + (k : Xs n) i) = f i (a i) := by
  unfold Pa
  rw [mem_coann_span]
  constructor
  · intro h i
    have := h _ ⟨i, rfl⟩
    simp only [Lam_apply] at this
    exact (z2_add_eq_zero _ _).1 this
  · rintro h _ ⟨i, rfl⟩
    simp only [Lam_apply]
    exact (z2_add_eq_zero _ _).2 (h i)

lemma mem_RJ (S : Submodule (ZMod 2) (Xs n)) (J : Finset (Fin r)) (k : Rad f hf S) :
    k ∈ RJ f hf S J ↔ ∀ i ∈ J, ∀ p, f i (p + (k : Xs n) i) = f i p := by
  unfold RJ
  rw [mem_coann_span]
  constructor
  · intro h i hi p
    have := h (Lam f hf S i p) ((mem_un_Av f hf S J _).2 ⟨i, hi, p, rfl⟩)
    rw [Lam_apply] at this
    exact (z2_add_eq_zero _ _).1 this
  · intro h φ hφ
    obtain ⟨i, hi, p, rfl⟩ := (mem_un_Av f hf S J φ).1 hφ
    rw [Lam_apply]
    exact (z2_add_eq_zero _ _).2 (h i hi p)

/-- Queries for the translate `a + S` give the lower bound in terms of the periods. -/
lemma lhs_to_dim (S : Submodule (ZMod 2) (Xs n)) (e : ℕ) (a : Xs n)
    (h : ∃ (ask : Xs n →ₗ[ZMod 2] (Fin e → ZMod 2))
      (out : (Fin e → ZMod 2) → (Fin r → ZMod 2)),
      ∀ w ∈ S, ∀ i : Fin r, out (ask (a+w)) i = f i (a i + w i)) :
    finrank (ZMod 2) S ≤ e + finrank (ZMod 2) (Pa f hf S a) := by
  obtain ⟨ask, out, hout⟩ := h
  have hrn := LinearMap.finrank_range_add_finrank_ker (ask ∘ₗ S.subtype)
  have hr : finrank (ZMod 2) (LinearMap.range (ask ∘ₗ S.subtype)) ≤ e := by
    have := Submodule.finrank_le (LinearMap.range (ask ∘ₗ S.subtype))
    simpa using this
  have hker : (LinearMap.ker (ask ∘ₗ S.subtype)).map S.subtype ≤
      (Pa f hf S a).map (Rad f hf S).subtype := by
    rintro x ⟨w, hw, rfl⟩
    have hw0 : ask (w : Xs n) = 0 := LinearMap.mem_ker.mp hw
    have per : ∀ w' ∈ S, ∀ i, f i (a i + w' i + (w : Xs n) i) = f i (a i + w' i) := by
      intro w' hw' i
      have h1 := hout (w' + w) (S.add_mem hw' w.2) i
      have h2 := hout w' hw' i
      have : ask (a + (w' + (w : Xs n))) = ask (a + w') := by
        simp [map_add, hw0]
      rw [this, h2] at h1
      simpa [Pi.add_apply, add_assoc] using h1.symm
    have hR : (w : Xs n) ∈ Rad f hf S := by
      refine (mem_Rad f hf S _).2 ⟨w.2, fun v hv i => ?_⟩
      have h := hf i (a i) (v i) ((w : Xs n) i)
      have e1 := per v hv i
      have e2 := per 0 S.zero_mem i
      simp only [Pi.zero_apply, add_zero] at e2
      rw [Bf_symm]
      grind
    refine ⟨⟨w, hR⟩, (mem_Pa f hf S a _).2 ?_, rfl⟩
    intro i
    have e2 := per 0 S.zero_mem i
    simpa using e2
  have := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq] at this
  omega

/-- Conversely, enough queries exist once the period space is large. -/
lemma dim_to_lhs (S : Submodule (ZMod 2) (Xs n)) (e : ℕ) (a : Xs n)
    (hdim : finrank (ZMod 2) S ≤ e + finrank (ZMod 2) (Pa f hf S a)) :
    ∃ (ask : Xs n →ₗ[ZMod 2] (Fin e → ZMod 2))
      (out : (Fin e → ZMod 2) → (Fin r → ZMod 2)),
      ∀ w ∈ S, ∀ i : Fin r, out (ask (a+w)) i = f i (a i + w i) := by
  have hPS : (Pa f hf S a).map (Rad f hf S).subtype ≤ S := by
    rintro x ⟨k, -, rfl⟩
    exact ((mem_Rad f hf S _).1 k.2).1
  have hdim' : finrank (ZMod 2) S ≤
      e + finrank (ZMod 2) ((Pa f hf S a).map (Rad f hf S).subtype) := by
    rw [Submodule.finrank_map_subtype_eq]; exact hdim
  obtain ⟨ask, out, hao⟩ := exists_ask_out S _ hPS e hdim'
    (fun x : Xs n => fun i => f i (x i)) a (by
      rintro w hw x ⟨k, hk, rfl⟩
      funext i
      have hk := (mem_Pa f hf S a k).1 hk
      have h := hf i (a i) (w i) ((k : Xs n) i)
      have hB : Bf f i ((k : Xs n) i) (w i) = 0 := ((mem_Rad f hf S _).1 k.2).2 w hw i
      rw [Bf_symm] at hB
      have hk' := hk i
      simp only [Pi.add_apply, Submodule.subtype_apply]
      grind)
  exact ⟨ask, out, fun w hw i => congrFun (hao w hw) i⟩

/-- The easy half of the min-max: any block bases and any `J`. -/
lemma C1 (S : Submodule (ZMod 2) (Xs n)) (a : Xs n) (J : Finset (Fin r)) :
    finrank (ZMod 2) (RJ f hf S J) ≤ finrank (ZMod 2) (Pa f hf S a) + (r - J.card) := by
  classical
  have h1 := finrank_Pa f hf S a
  have h2 := finrank_RJ f hf S J
  have hsub : (Set.range fun i => Lam f hf S i (a i)) ⊆ un (Av f hf S) J ∪
      Set.range (fun i : {i : Fin r // i ∉ J} => Lam f hf S i (a i)) := by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ J
    · left
      exact (mem_un_Av f hf S J _).2 ⟨i, hi, a i, rfl⟩
    · right
      exact ⟨⟨i, hi⟩, rfl⟩
  have hm := Submodule.finrank_mono (span_mono (R := ZMod 2) hsub)
  rw [Submodule.span_union] at hm
  have ha := Submodule.finrank_add_le_finrank_add_finrank (span (ZMod 2) (un (Av f hf S) J))
    (span (ZMod 2) (Set.range (fun i : {i : Fin r // i ∉ J} => Lam f hf S i (a i))))
  have hb : finrank (ZMod 2)
      (span (ZMod 2) (Set.range (fun i : {i : Fin r // i ∉ J} => Lam f hf S i (a i)))) ≤
      Fintype.card {i : Fin r // i ∉ J} :=
    finrank_range_le_card (R := ZMod 2) (fun i : {i : Fin r // i ∉ J} => Lam f hf S i (a i))
  have hcard : Fintype.card {i : Fin r // i ∉ J} = r - J.card := by
    simp [Fintype.card_subtype_compl, Fintype.card_coe]
  omega

/-- The hard half of the min-max, from Rado's theorem with deficiency. -/
lemma C2 (S : Submodule (ZMod 2) (Xs n)) : ∃ (a : Xs n) (J : Finset (Fin r)),
    finrank (ZMod 2) (Pa f hf S a) + (r - J.card) ≤ finrank (ZMod 2) (RJ f hf S J) := by
  classical
  have hne : ∀ i, (Av f hf S i).Nonempty :=
    fun i => ⟨Lam f hf S i 0, (mem_Av f hf S i _).2 ⟨0, rfl⟩⟩
  obtain ⟨c, hc, J, hJ⟩ := rado_minmax (K := ZMod 2) (Av f hf S) hne
  have hc' : ∀ i, ∃ p, Lam f hf S i p = c i := fun i => (mem_Av f hf S i _).1 (hc i)
  choose a ha using hc'
  refine ⟨a, J, ?_⟩
  have hrange : (Set.range fun i => Lam f hf S i (a i)) = Set.range c := by
    congr 1
    funext i
    exact ha i
  have h1 := finrank_Pa f hf S a
  have h2 := finrank_RJ f hf S J
  rw [hrange] at h1
  have hJr : J.card ≤ r := by simpa using Finset.card_le_univ J
  rw [Fintype.card_fin] at hJ
  omega

lemma core_dim (S : Submodule (ZMod 2) (Xs n)) (e : ℕ) :
    (∀ a : Xs n, ∃ (ask : Xs n →ₗ[ZMod 2] (Fin e → ZMod 2))
      (out : (Fin e → ZMod 2) → (Fin r → ZMod 2)),
      ∀ w ∈ S, ∀ i : Fin r, out (ask (a+w)) i = f i (a i + w i)) ↔
    ∃ J : Finset (Fin r), (r - J.card) + finrank (ZMod 2) S ≤
      e + finrank (ZMod 2) (RJ f hf S J) := by
  constructor
  · intro h
    obtain ⟨a, J, hJ⟩ := C2 f hf S
    have := lhs_to_dim f hf S e a (h a)
    exact ⟨J, by omega⟩
  · rintro ⟨J, hJ⟩ a
    apply dim_to_lhs f hf S e a
    have := C1 f hf S a J
    omega

lemma card_RJ (S : Submodule (ZMod 2) (Xs n)) (J : Finset (Fin r)) :
    Nat.card {u : S // (∀ i ∈ J, ∀ p : Fin (n i) → ZMod 2, f i (p+u.val i) = f i p) ∧
        ∀ v : S, ∀ i : Fin r, Bf f i (u.val i) (v.val i) = 0} = Nat.card (RJ f hf S J) := by
  apply Nat.card_congr
  exact
    { toFun := fun u => ⟨⟨u.1.1, (mem_Rad f hf S _).2 ⟨u.1.2, fun v hv i => u.2.2 ⟨v, hv⟩ i⟩⟩,
        (mem_RJ f hf S J _).2 u.2.1⟩
      invFun := fun x => ⟨⟨x.1.1, ((mem_Rad f hf S _).1 x.1.2).1⟩,
        ⟨(mem_RJ f hf S J _).1 x.2, fun v i => ((mem_Rad f hf S _).1 x.1.2).2 v.1 v.2 i⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem core (S : Submodule (ZMod 2) (Xs n)) (e : ℕ) :
    (∀ a : Xs n, ∃ (ask : Xs n →ₗ[ZMod 2] (Fin e → ZMod 2))
      (out : (Fin e → ZMod 2) → (Fin r → ZMod 2)),
      ∀ w ∈ S, ∀ i : Fin r, out (ask (a+w)) i = f i (a i + w i)) ↔
    ∃ J : Finset (Fin r), 2^(r-J.card) * Nat.card S ≤ 2^e * Nat.card
      {u : S // (∀ i ∈ J, ∀ p : Fin (n i) → ZMod 2, f i (p+u.val i) = f i p) ∧
        ∀ v : S, ∀ i : Fin r, Bf f i (u.val i) (v.val i) = 0} := by
  rw [core_dim f hf S e]
  apply exists_congr
  intro J
  rw [card_RJ f hf S J, natCard_sub, natCard_sub, ← pow_add, ← pow_add,
    pow_le_pow_iff_right₀ (by norm_num)]

end Blocks

end PEqualNP.Outside.L_pcx_427_aux

theorem PEqualNP.Outside.L_pcx_427 :
∀ (r : ℕ) (n : Fin r → ℕ),
  let F := ZMod 2
  let V := fun i : Fin r => Fin (n i) → F
  let X := (i : Fin r) → V i
  let Y := Fin r → F
  ∀ (f : (i : Fin r) → V i → F),
    let B := fun (i : Fin r) (u v : V i) => f i (u+v) + f i u + f i v + f i 0
    (∀ (i : Fin r) (p u v : V i),
      f i (p+u+v) + f i (p+u) + f i (p+v) + f i p = B i u v) →
    ∀ (S : Submodule F X) (e : ℕ),
      (∀ a : X, ∃ (ask : X →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y),
        ∀ w ∈ S, ∀ i : Fin r, out (ask (a+w)) i = f i (a i+w i)) ↔
      ∃ J : Finset (Fin r), 2^(r-J.card)*Nat.card S ≤ 2^e*Nat.card
        {u : S // (∀ i ∈ J, ∀ p : V i, f i (p+u.val i) = f i p) ∧
          ∀ v : S, ∀ i : Fin r, B i (u.val i) (v.val i) = 0} := by
  intro r n F V X Y f B hf S e
  exact PEqualNP.Outside.L_pcx_427_aux.core f hf S e
