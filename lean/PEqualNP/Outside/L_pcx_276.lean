import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_276

open PEqualNP.CircuitLowerBounds

/- The wire lemmas below are adapted from the recorded proofs of L-meta-25647 and L-meta-25830
(Apache-2.0). -/

/-- The wire values of the gate list `gs` on the input bits `x`. -/
def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

theorem foldl_append_start {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_start
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

/-- A bit as an element of the two-element field. -/
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_decide : ∀ v : ZMod 2, b2z (decide (v = 1)) = v := by decide

theorem decide_b2z (b : Bool) : decide (b2z b = 1) = b := by
  cases b <;> simp [b2z]

theorem z2_cases : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide

theorem z2_add_self : ∀ v : ZMod 2, v + v = 0 := by decide

theorem z2_eq_of_add : ∀ a b : ZMod 2, 1 + a + b = 1 → a = b := by decide

theorem ev_and : ∀ u v : ZMod 2,
    b2z (GateOp.eval GateOp.and [decide (u = 1), decide (v = 1)]) = u * v := by decide

theorem ev_or : ∀ u v : ZMod 2,
    b2z (GateOp.eval GateOp.or [decide (u = 1), decide (v = 1)]) = u + v + u * v := by decide

theorem ev_mod0 : b2z (GateOp.eval (GateOp.mod 2) []) = 1 := by decide

theorem ev_mod1 : ∀ u : ZMod 2,
    b2z (GateOp.eval (GateOp.mod 2) [decide (u = 1)]) = 1 + u := by decide

theorem ev_mod2 : ∀ u v : ZMod 2,
    b2z (GateOp.eval (GateOp.mod 2) [decide (u = 1), decide (v = 1)]) = 1 + u + v := by decide

theorem ev_not : ∀ u : ZMod 2,
    b2z (GateOp.eval GateOp.not [decide (u = 1)]) = 1 + u := by decide

/-- The product of the coordinates in `T`. -/
def mono {n : ℕ} (T : Finset (Fin n)) : (Fin n → ZMod 2) → ZMod 2 := fun x => ∏ i ∈ T, x i

/-- The functions on the cube spanned by the products of at most `d` coordinates. -/
def LowDeg (n d : ℕ) : Submodule (ZMod 2) ((Fin n → ZMod 2) → ZMod 2) :=
  Submodule.span (ZMod 2) (mono '' {T : Finset (Fin n) | T.card ≤ d})

theorem mono_mem {n d : ℕ} (T : Finset (Fin n)) (h : T.card ≤ d) : mono T ∈ LowDeg n d :=
  Submodule.subset_span ⟨T, h, rfl⟩

theorem lowDeg_le {n d d' : ℕ} (h : d ≤ d') : LowDeg n d ≤ LowDeg n d' :=
  Submodule.span_mono (Set.image_mono fun T hT => le_trans hT h)

theorem one_mem_lowDeg (n d : ℕ) : (1 : (Fin n → ZMod 2) → ZMod 2) ∈ LowDeg n d := by
  have h : mono (∅ : Finset (Fin n)) = 1 := by
    funext x
    simp [mono]
  rw [← h]
  exact mono_mem ∅ (by simp)

theorem coord_mem {n : ℕ} (i : Fin n) :
    (fun x : Fin n → ZMod 2 => x i) ∈ LowDeg n 1 := by
  have h : mono ({i} : Finset (Fin n)) = fun x : Fin n → ZMod 2 => x i := by
    funext x
    simp [mono]
  rw [← h]
  exact mono_mem {i} (by simp)

theorem mono_mul {n : ℕ} (T T' : Finset (Fin n)) : mono T * mono T' = mono (T ∪ T') := by
  funext x
  show (∏ i ∈ T, x i) * (∏ i ∈ T', x i) = ∏ i ∈ T ∪ T', x i
  by_cases h : ∀ i ∈ T ∪ T', x i = 1
  · rw [Finset.prod_eq_one fun i hi => h i (Finset.mem_union_left _ hi),
      Finset.prod_eq_one fun i hi => h i (Finset.mem_union_right _ hi),
      Finset.prod_eq_one h, mul_one]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    obtain ⟨hiT, hx⟩ := Classical.not_imp.mp hi
    have hx0 : x i = 0 := (z2_cases (x i)).resolve_right hx
    rw [Finset.prod_eq_zero hiT hx0]
    rcases Finset.mem_union.mp hiT with h1 | h1
    · rw [Finset.prod_eq_zero h1 hx0, zero_mul]
    · rw [Finset.prod_eq_zero h1 hx0, mul_zero]

theorem mul_mem_lowDeg {n d1 d2 : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2}
    (hf : f ∈ LowDeg n d1) (hg : g ∈ LowDeg n d2) : f * g ∈ LowDeg n (d1 + d2) := by
  have h := Submodule.mul_mem_mul hf hg
  unfold LowDeg at h ⊢
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨T, hT, rfl⟩, _, ⟨T', hT', rfl⟩, rfl⟩
  refine ⟨T ∪ T', ?_, (mono_mul T T').symm⟩
  exact (Finset.card_union_le T T').trans (Nat.add_le_add hT hT')

theorem prod_mem_lowDeg {n : ℕ} {ι : Type} (S : Finset ι)
    (f : ι → (Fin n → ZMod 2) → ZMod 2) (d : ι → ℕ) (h : ∀ j ∈ S, f j ∈ LowDeg n (d j)) :
    (∏ j ∈ S, f j) ∈ LowDeg n (∑ j ∈ S, d j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact one_mem_lowDeg n _
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_lowDeg (h a (Finset.mem_insert_self a S))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A function of degree below the dimension sums to zero over the cube. -/
theorem sum_eq_zero_of_lowDeg {n d : ℕ} (hd : d < n) {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : f ∈ LowDeg n d) : ∑ x, f x = 0 := by
  have hker : LowDeg n d ≤ LinearMap.ker
      (∑ x : Fin n → ZMod 2, (LinearMap.proj x :
        ((Fin n → ZMod 2) → ZMod 2) →ₗ[ZMod 2] ZMod 2)) := by
    unfold LowDeg
    rw [Submodule.span_le]
    rintro _ ⟨T, hT, rfl⟩
    have hTn : T.card < n := lt_of_le_of_lt hT hd
    obtain ⟨i0, hi0⟩ : ∃ i0 : Fin n, i0 ∉ T := by
      by_contra hall
      have hTu : T = Finset.univ := Finset.eq_univ_iff_forall.mpr
        fun i => not_not.mp (not_exists.mp hall i)
      rw [hTu, Finset.card_univ, Fintype.card_fin] at hTn
      exact lt_irrefl _ hTn
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply]
    refine Finset.sum_involution (fun x _ => Function.update x i0 (x i0 + 1)) ?_ ?_ ?_ ?_
    · intro x _
      have h1 : mono T (Function.update x i0 (x i0 + 1)) = mono T x := by
        unfold mono
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hi0)]
      rw [h1]
      exact z2_add_self _
    · intro x _ _ heq
      have h2 := congrFun heq i0
      rw [Function.update_self] at h2
      have h3 : ∀ v : ZMod 2, v + 1 ≠ v := by decide
      exact h3 _ h2
    · intro x _
      exact Finset.mem_univ _
    · intro x _
      funext i
      by_cases hi : i = i0
      · subst hi
        simp only [Function.update_self]
        have h3 : ∀ v : ZMod 2, v + 1 + 1 = v := by decide
        exact h3 _
      · simp [Function.update_of_ne hi]
  have h := hker hf
  simpa [LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply] using h

/-- The value of coordinate `i`, zero past the end. -/
def coordD {n : ℕ} (x : Fin n → ZMod 2) (i : ℕ) : ZMod 2 := if h : i < n then x ⟨i, h⟩ else 0

/-- The value of the gate `g` on the wire values `x`. -/
def gateFn {n : ℕ} (g : Gate) (x : Fin n → ZMod 2) : ZMod 2 :=
  b2z (g.op.eval (g.inputs.map fun i => decide (coordD x i = 1)))

theorem coordD_mem (n i : ℕ) : (fun x : Fin n → ZMod 2 => coordD x i) ∈ LowDeg n 1 := by
  by_cases h : i < n
  · have e : (fun x : Fin n → ZMod 2 => coordD x i) = fun x => x ⟨i, h⟩ := by
      funext x
      simp [coordD, h]
    rw [e]
    exact coord_mem _
  · have e : (fun x : Fin n → ZMod 2 => coordD x i) = 0 := by
      funext x
      simp [coordD, h]
    rw [e]
    exact Submodule.zero_mem _

theorem gateFn_mem_two (n : ℕ) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (fun x : Fin n → ZMod 2 => gateFn g x) ∈ LowDeg n 2 := by
  obtain ⟨hop, hlen⟩ := h
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have hmul : (fun x : Fin n → ZMod 2 => coordD x a * coordD x b) ∈ LowDeg n 2 := by
    have h0 : ((fun x : Fin n → ZMod 2 => coordD x a) * fun x : Fin n → ZMod 2 => coordD x b) ∈
        LowDeg n (1 + 1) := mul_mem_lowDeg (coordD_mem n a) (coordD_mem n b)
    have e0 : ((fun x : Fin n → ZMod 2 => coordD x a) * fun x : Fin n → ZMod 2 => coordD x b) =
        fun x => coordD x a * coordD x b := by
      funext x
      exact Pi.mul_apply _ _ x
    rw [e0] at h0
    exact h0
  rcases hop with hop | hop
  · have e : (fun x : Fin n → ZMod 2 => gateFn g x) = fun x => coordD x a * coordD x b := by
      funext x
      unfold gateFn
      rw [hop, hab]
      exact ev_and _ _
    rw [e]
    exact hmul
  · have e : (fun x : Fin n → ZMod 2 => gateFn g x) =
        (fun x => coordD x a) + (fun x => coordD x b) + fun x => coordD x a * coordD x b := by
      funext x
      unfold gateFn
      rw [hop, hab]
      exact ev_or _ _
    rw [e]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (lowDeg_le (by norm_num) (coordD_mem n a))
        (lowDeg_le (by norm_num) (coordD_mem n b))) hmul

theorem gateFn_mem_one (n : ℕ) (g : Gate)
    (h : (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (fun x : Fin n → ZMod 2 => gateFn g x) ∈ LowDeg n 1 := by
  rcases h with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
  · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · have e : (fun x : Fin n → ZMod 2 => gateFn g x) = 1 := by
        funext x
        unfold gateFn
        rw [hop, hin]
        exact ev_mod0
      rw [e]
      exact one_mem_lowDeg n 1
    · have e : (fun x : Fin n → ZMod 2 => gateFn g x) = 1 + fun x => coordD x a := by
        funext x
        unfold gateFn
        rw [hop, hin]
        exact ev_mod1 _
      rw [e]
      exact Submodule.add_mem _ (one_mem_lowDeg n 1) (coordD_mem n a)
    · have e : (fun x : Fin n → ZMod 2 => gateFn g x) =
          1 + (fun x => coordD x a) + fun x => coordD x b := by
        funext x
        unfold gateFn
        rw [hop, hin]
        exact ev_mod2 _ _
      rw [e]
      exact Submodule.add_mem _ (Submodule.add_mem _ (one_mem_lowDeg n 1) (coordD_mem n a))
        (coordD_mem n b)
    · rw [hin] at hlen
      simp at hlen
  · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    have e : (fun x : Fin n → ZMod 2 => gateFn g x) = 1 + fun x => coordD x a := by
      funext x
      unfold gateFn
      rw [hop, ha]
      exact ev_not _
    rw [e]
    exact Submodule.add_mem _ (one_mem_lowDeg n 1) (coordD_mem n a)

/-- The factor of gate `j`: it is one exactly when wire `r + j` carries the gate's value. -/
def factor (r : ℕ) (gs : List Gate) (j : Fin gs.length) :
    (Fin (r + gs.length) → ZMod 2) → ZMod 2 :=
  fun x => 1 + x ⟨r + j, by omega⟩ + gateFn gs[j] x

/-- The true wire values on the input `z`. -/
def emb (r : ℕ) (gs : List Gate) (z : Fin r → ZMod 2) : Fin (r + gs.length) → ZMod 2 :=
  fun i => b2z ((wiresOf (List.ofFn fun i => decide (z i = 1)) gs).getD i false)

theorem decide_coordD_emb (r : ℕ) (gs : List Gate) (z : Fin r → ZMod 2) (a : ℕ) :
    decide (coordD (emb r gs z) a = 1) =
      (wiresOf (List.ofFn fun i => decide (z i = 1)) gs).getD a false := by
  by_cases h : a < r + gs.length
  · simp only [coordD, h, dif_pos, emb]
    exact decide_b2z _
  · have hlen : (wiresOf (List.ofFn fun i => decide (z i = 1)) gs).length ≤ a := by
      rw [wiresOf_length, List.length_ofFn]
      omega
    rw [List.getD_eq_default _ _ hlen]
    simp [coordD, h]

theorem factor_emb (r : ℕ) (gs : List Gate)
    (hrb : ∀ (j : ℕ) (hj : j < gs.length), ∀ a ∈ (gs[j]).inputs, a < r + j)
    (z : Fin r → ZMod 2) (j : Fin gs.length) : factor r gs j (emb r gs z) = 1 := by
  unfold factor
  have h1 : emb r gs z ⟨r + j, by omega⟩ = gateFn gs[j] (emb r gs z) := by
    unfold gateFn
    simp only [emb]
    have h2 := wiresOf_getD_gate (List.ofFn fun i => decide (z i = 1)) gs j.isLt
      (by
        intro a ha
        rw [List.length_ofFn]
        exact hrb j j.isLt a ha)
    rw [List.length_ofFn] at h2
    rw [h2]
    congr 2
    refine List.map_congr_left fun a _ => ?_
    exact (decide_coordD_emb r gs z a).symm
  rw [h1, add_assoc, z2_add_self, add_zero]

theorem emb_input (r : ℕ) (gs : List Gate) (z : Fin r → ZMod 2) (i : Fin r) :
    emb r gs z ⟨i, by omega⟩ = z i := by
  simp only [emb]
  rw [wiresOf_getD_input _ _ (by rw [List.length_ofFn]; exact i.isLt)]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  exact b2z_decide _

theorem emb_injective (r : ℕ) (gs : List Gate) : Function.Injective (emb r gs) := by
  intro z z' h
  funext i
  rw [← emb_input r gs z i, ← emb_input r gs z' i, h]

/-- Wire values on which every factor is one are the true wire values of their input part. -/
theorem eq_emb_of_factors (r : ℕ) (gs : List Gate)
    (hrb : ∀ (j : ℕ) (hj : j < gs.length), ∀ a ∈ (gs[j]).inputs, a < r + j)
    (x : Fin (r + gs.length) → ZMod 2) (hx : ∀ j : Fin gs.length, factor r gs j x = 1) :
    x = emb r gs (fun i => x ⟨i, by omega⟩) := by
  have key : ∀ m : ℕ, ∀ i : Fin (r + gs.length), i.val < m →
      x i = emb r gs (fun i => x ⟨i, by omega⟩) i := by
    intro m
    induction m with
    | zero =>
      intro i hi
      exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      by_cases hir : i.val < r
      · have h1 := emb_input r gs (fun i => x ⟨i, by omega⟩) ⟨i.val, hir⟩
        exact h1.symm
      · have hj : i.val - r < gs.length := by omega
        have hfac := hx ⟨i.val - r, hj⟩
        unfold factor at hfac
        have hidx : (⟨r + (⟨i.val - r, hj⟩ : Fin gs.length), by omega⟩ : Fin (r + gs.length)) = i := by
          apply Fin.ext
          show r + (i.val - r) = i.val
          omega
        rw [hidx] at hfac
        have h2 := z2_eq_of_add _ _ hfac
        have h3 := factor_emb r gs hrb (fun i => x ⟨i, by omega⟩) ⟨i.val - r, hj⟩
        unfold factor at h3
        rw [hidx] at h3
        have h4 := z2_eq_of_add _ _ h3
        rw [h2, h4]
        unfold gateFn
        congr 2
        refine List.map_congr_left fun a ha => ?_
        have hlt : a < r + (i.val - r) := hrb (i.val - r) hj a ha
        have han : a < r + gs.length := by omega
        have h5 := ih ⟨a, han⟩ (by show a < m; omega)
        simp only [coordD, han, dite_true]
        rw [h5]
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- Summing against the product of all factors picks out the true wire values. -/
theorem sum_factors (r : ℕ) (gs : List Gate)
    (hrb : ∀ (j : ℕ) (hj : j < gs.length), ∀ a ∈ (gs[j]).inputs, a < r + j)
    (psi : (Fin (r + gs.length) → ZMod 2) → ZMod 2) :
    ∑ x, (∏ j : Fin gs.length, factor r gs j x) * psi x = ∑ z, psi (emb r gs z) := by
  classical
  have h1 : ∑ x ∈ (Finset.univ.image (emb r gs)), (∏ j : Fin gs.length, factor r gs j x) * psi x =
      ∑ x, (∏ j : Fin gs.length, factor r gs j x) * psi x := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
    have hzero : ∏ j : Fin gs.length, factor r gs j x = 0 := by
      by_contra hne
      have hall : ∀ j : Fin gs.length, factor r gs j x = 1 := by
        intro j
        have hj : factor r gs j x ≠ 0 := Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ j)
        exact (z2_cases _).resolve_left hj
      have hx' := eq_emb_of_factors r gs hrb x hall
      exact hx (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hx'.symm⟩)
    rw [hzero, zero_mul]
  rw [← h1, Finset.sum_image (fun a _ b _ h => emb_injective r gs h)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_eq_one (fun j _ => factor_emb r gs hrb z j), one_mul]

/-- The leading word `u` admits a suffix circuit with at most `s` AND/OR gates that computes
`z ↦ send (u, z)`. -/
def Fits (k r s : ℕ) (send : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → (Fin k → ZMod 2))
    (u : Fin k → ZMod 2) : Prop :=
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin k → Fin (r+C.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack r C ∧
    (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
    C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ s ∧
    ∀ (z : Fin r → ZMod 2) (j : Fin k),
      (C.wires (List.ofFn (fun i => decide (z i = 1)))).getD (out j).val false =
        decide (send (u,z) j = 1)

/-- The number of cheap prefixes. -/
noncomputable def cheap (k r s : ℕ)
    (send : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → (Fin k → ZMod 2)) : ℕ :=
  (@Finset.filter (Fin k → ZMod 2) (Fits k r s send) (Classical.decPred _) Finset.univ).card

/-- The number of erroneous triples. -/
def errors (k r c : ℕ) (send : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → (Fin k → ZMod 2))
    (tag : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → Fin c → Bool) : ℕ :=
  (Finset.univ.filter (fun v : Fin 3 → ((Fin k → ZMod 2) × (Fin r → ZMod 2)) =>
    (v 0).1 = (v 1).1 ∧ send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧
      ¬(v 0 = v 1 ∧ v 1 = v 2))).card

/-- Whether a gate is an AND or an OR gate. -/
noncomputable def nl (g : Gate) : Bool :=
  @decide (g.op = GateOp.and ∨ g.op = GateOp.or) (Classical.propDecidable _)

theorem nl_iff (g : Gate) : nl g = true ↔ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  unfold nl
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem factor_mem (r : ℕ) (gs : List Gate)
    (hshape : ∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1))
    (j : Fin gs.length) :
    factor r gs j ∈ LowDeg (r + gs.length) (if nl gs[j] = true then 2 else 1) := by
  have hg := hshape gs[j] (List.getElem_mem _)
  have hcoord : (fun x : Fin (r + gs.length) → ZMod 2 => x ⟨r + j, by omega⟩) ∈
      LowDeg (r + gs.length) 1 := coord_mem _
  have hfac : factor r gs j =
      1 + (fun x : Fin (r + gs.length) → ZMod 2 => x ⟨r + j, by omega⟩) +
        fun x => gateFn gs[j] x := by
    funext x
    simp only [factor, Pi.add_apply, Pi.one_apply]
  rw [hfac]
  by_cases hnl : nl gs[j] = true
  · rw [if_pos hnl]
    have hop := (nl_iff _).mp hnl
    have h2 : (fun x : Fin (r + gs.length) → ZMod 2 => gateFn gs[j] x) ∈
        LowDeg (r + gs.length) 2 := by
      rcases hg with h | h | h
      · exact gateFn_mem_two _ _ h
      · exfalso
        rcases hop with h' | h' <;> rw [h.1] at h' <;> cases h'
      · exfalso
        rcases hop with h' | h' <;> rw [h.1] at h' <;> cases h'
    exact Submodule.add_mem _ (Submodule.add_mem _ (one_mem_lowDeg _ 2)
      (lowDeg_le (by norm_num) hcoord)) h2
  · rw [if_neg hnl]
    have hop : ¬ (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) :=
      fun h => hnl ((nl_iff _).mpr h)
    have h1 : (fun x : Fin (r + gs.length) → ZMod 2 => gateFn gs[j] x) ∈
        LowDeg (r + gs.length) 1 := by
      rcases hg with h | h | h
      · exact absurd h.1 hop
      · exact gateFn_mem_one _ _ (Or.inl h)
      · exact gateFn_mem_one _ _ (Or.inr h)
    exact Submodule.add_mem _ (Submodule.add_mem _ (one_mem_lowDeg _ 1) hcoord) h1

theorem sum_fin_getElem (gs : List Gate) (f : Gate → ℕ) :
    ∑ j : Fin gs.length, f gs[j] = (gs.map f).sum := by
  have h : (List.ofFn fun j : Fin gs.length => f gs[j]) = gs.map f := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [← h, List.sum_ofFn]

theorem sum_deg (gs : List Gate) :
    ∑ j : Fin gs.length, (if nl gs[j] = true then 2 else 1) = gs.length + gs.countP nl := by
  rw [sum_fin_getElem gs (fun g => if nl g = true then 2 else 1)]
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.length_cons]
    cases hn : nl g <;> simp <;> omega

theorem prodFactor_mem (r : ℕ) (gs : List Gate)
    (hshape : ∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1))
    (s : ℕ) (hs : gs.countP nl ≤ s) :
    (∏ j : Fin gs.length, factor r gs j) ∈ LowDeg (r + gs.length) (gs.length + s) := by
  have h := prod_mem_lowDeg Finset.univ (fun j : Fin gs.length => factor r gs j)
    (fun j => if nl gs[j] = true then 2 else 1) (fun j _ => factor_mem r gs hshape j)
  rw [sum_deg] at h
  exact lowDeg_le (by omega) h

/-- The parity of the fibre of `y` under `z ↦ send (u, z)`. -/
def fib (k r : ℕ) (send : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → (Fin k → ZMod 2))
    (u : Fin k → ZMod 2) : (Fin k → ZMod 2) → ZMod 2 :=
  fun y => ∑ z : Fin r → ZMod 2, if send (u, z) = y then 1 else 0

theorem ind_eq_prod {k : ℕ} (a b : Fin k → ZMod 2) :
    (if a = b then (1 : ZMod 2) else 0) = ∏ j, (b j + (1 + a j)) := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    refine (Finset.prod_eq_one fun j _ => ?_).symm
    have h1 : ∀ v : ZMod 2, v + (1 + v) = 1 := by decide
    exact h1 _
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    have h1 : ∀ v w : ZMod 2, v ≠ w → w + (1 + v) = 0 := by decide
    exact h1 _ _ hj

/-- The fibre parity of a cheap leading word has low degree. -/
theorem fib_mem (k r s : ℕ) (send : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → (Fin k → ZMod 2))
    (u : Fin k → ZMod 2) (hfit : Fits k r s send u) :
    fib k r send u ∈ LowDeg k (min k (k + s - r)) := by
  classical
  obtain ⟨C, out, hrb, hshape, hcount, hval⟩ := hfit
  have hrb' : ∀ (j : ℕ) (hj : j < C.gates.length), ∀ a ∈ (C.gates[j]).inputs, a < r + j := by
    intro j hj a ha
    refine hrb j hj a ?_
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
      List.getD_eq_getElem _ _ hj
    rw [e]
    exact ha
  have hcount' : C.gates.countP nl ≤ s := hcount
  have hval' : ∀ (z : Fin r → ZMod 2) (j : Fin k),
      emb r C.gates z (out j) = send (u, z) j := by
    intro z j
    have h1 := hval z j
    show b2z ((C.wires (List.ofFn fun i => decide (z i = 1))).getD (out j).val false) =
      send (u, z) j
    rw [h1]
    exact b2z_decide _
  have hpt : ∀ y : Fin k → ZMod 2, fib k r send u y =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∑ x : Fin (r + C.gates.length) → ZMod 2,
          (∏ j : Fin C.gates.length, factor r C.gates j x) *
            ∏ i ∈ Finset.univ \ T, (1 + x (out i))) * ∏ i ∈ T, y i := by
    intro y
    have h1 : ∀ z : Fin r → ZMod 2, (if send (u, z) = y then (1 : ZMod 2) else 0) =
        ∏ j, (y j + (1 + emb r C.gates z (out j))) := by
      intro z
      rw [ind_eq_prod (send (u, z)) y]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hval' z j]
    unfold fib
    simp only [h1]
    rw [← sum_factors r C.gates hrb' (fun x => ∏ j, (y j + (1 + x (out j))))]
    calc ∑ x : Fin (r + C.gates.length) → ZMod 2,
          (∏ j : Fin C.gates.length, factor r C.gates j x) * ∏ j, (y j + (1 + x (out j)))
        = ∑ x : Fin (r + C.gates.length) → ZMod 2,
            ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
              (∏ j : Fin C.gates.length, factor r C.gates j x) *
                ((∏ i ∈ T, y i) * ∏ i ∈ Finset.univ \ T, (1 + x (out i))) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.prod_add, Finset.mul_sum]
      _ = ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
            ∑ x : Fin (r + C.gates.length) → ZMod 2,
              (∏ j : Fin C.gates.length, factor r C.gates j x) *
                ((∏ i ∈ T, y i) * ∏ i ∈ Finset.univ \ T, (1 + x (out i))) := Finset.sum_comm
      _ = ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
            (∑ x : Fin (r + C.gates.length) → ZMod 2,
              (∏ j : Fin C.gates.length, factor r C.gates j x) *
                ∏ i ∈ Finset.univ \ T, (1 + x (out i))) * ∏ i ∈ T, y i := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
  have hformula : fib k r send u = ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ x : Fin (r + C.gates.length) → ZMod 2,
        (∏ j : Fin C.gates.length, factor r C.gates j x) *
          ∏ i ∈ Finset.univ \ T, (1 + x (out i))) • mono T := by
    funext y
    rw [hpt y]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mono]
  rw [hformula]
  refine Submodule.sum_mem _ fun T _ => ?_
  by_cases hT : T.card ≤ min k (k + s - r)
  · exact Submodule.smul_mem _ _ (mono_mem T hT)
  · have hTk : T.card ≤ k := by
      have h1 := Finset.card_le_univ T
      rwa [Fintype.card_fin] at h1
    have hbig : k + s - r < T.card := by
      rw [not_le, min_lt_iff] at hT
      rcases hT with h | h
      · omega
      · exact h
    have hQ : (∏ i ∈ Finset.univ \ T,
        fun x : Fin (r + C.gates.length) → ZMod 2 => 1 + x (out i)) ∈
        LowDeg (r + C.gates.length) (k - T.card) := by
      have h := prod_mem_lowDeg (Finset.univ \ T)
        (fun (i : Fin k) (x : Fin (r + C.gates.length) → ZMod 2) => 1 + x (out i)) (fun _ => 1)
        (fun i _ => Submodule.add_mem _ (one_mem_lowDeg _ 1) (coord_mem (out i)))
      have hcard : ∑ _i ∈ Finset.univ \ T, 1 = k - T.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_sdiff_of_subset (Finset.subset_univ T),
          Finset.card_univ, Fintype.card_fin]
      rw [hcard] at h
      exact h
    have hmem := mul_mem_lowDeg (prodFactor_mem r C.gates hshape s hcount') hQ
    have hdeg : C.gates.length + s + (k - T.card) < r + C.gates.length := by omega
    have hzero := sum_eq_zero_of_lowDeg hdeg hmem
    have hc : (∑ x : Fin (r + C.gates.length) → ZMod 2,
        (∏ j : Fin C.gates.length, factor r C.gates j x) *
          ∏ i ∈ Finset.univ \ T, (1 + x (out i))) = 0 := by
      rw [← hzero]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Pi.mul_apply, Finset.prod_apply]
    rw [hc, zero_smul]
    exact Submodule.zero_mem _

/-- A linearly independent family of low-degree functions is small. -/
theorem lowDeg_card_le (k d : ℕ) {ι : Type} [Fintype ι]
    (v : ι → (Fin k → ZMod 2) → ZMod 2) (hv : ∀ i, v i ∈ LowDeg k d)
    (hli : LinearIndependent (ZMod 2) v) :
    Fintype.card ι ≤ ∑ j ∈ Finset.range (d + 1), k.choose j := by
  classical
  have hspan : LowDeg k d = Submodule.span (ZMod 2)
      ((((Finset.univ : Finset (Finset (Fin k))).filter (fun T => T.card ≤ d)).image mono :
        Finset ((Fin k → ZMod 2) → ZMod 2)) : Set ((Fin k → ZMod 2) → ZMod 2)) := by
    unfold LowDeg
    congr 1
    ext f
    simp
  have hfin : Module.finrank (ZMod 2) (LowDeg k d) ≤
      (((Finset.univ : Finset (Finset (Fin k))).filter (fun T => T.card ≤ d)).image mono).card := by
    rw [hspan]
    exact finrank_span_finset_le_card _
  have hcardTS : ((Finset.univ : Finset (Finset (Fin k))).filter (fun T => T.card ≤ d)).card ≤
      ∑ j ∈ Finset.range (d + 1), k.choose j := by
    have hsub : ((Finset.univ : Finset (Finset (Fin k))).filter (fun T => T.card ≤ d)) ⊆
        (Finset.range (d + 1)).biUnion
          (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin k))) := by
      intro T hT
      rw [Finset.mem_filter] at hT
      exact Finset.mem_biUnion.mpr ⟨T.card, Finset.mem_range.mpr (by omega),
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hw : LinearIndependent (ZMod 2) (fun i => (⟨v i, hv i⟩ : LowDeg k d)) :=
    LinearIndependent.of_comp (LowDeg k d).subtype hli
  have h1 := hw.fintype_card_le_finrank
  exact h1.trans (hfin.trans (Finset.card_image_le.trans hcardTS))

theorem claim1 (k r c s : ℕ) (send : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → (Fin k → ZMod 2))
    (tag : ((Fin k → ZMod 2) × (Fin r → ZMod 2)) → Fin c → Bool) :
    2 ^ r * cheap k r s send ≤
      errors k r c send tag + 2 ^ c * ∑ j ∈ Finset.range (min k (k+s-r) + 1), k.choose j := by
  classical
  have hWc_card : ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
      (fun w => Fits k r s send w.1)).card = 2 ^ r * cheap k r s send := by
    have e : (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
        (fun w => Fits k r s send w.1) =
        (@Finset.filter (Fin k → ZMod 2) (Fits k r s send) (Classical.decPred _) Finset.univ) ×ˢ
          (Finset.univ : Finset (Fin r → ZMod 2)) := by
      ext ⟨u, z⟩
      simp
    rw [e, Finset.card_product]
    unfold cheap
    have hc : (Finset.univ : Finset (Fin r → ZMod 2)).card = 2 ^ r := by
      simp
    rw [hc, mul_comm]
  have hbad_card : ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
      (fun w0 => ∃ w1 w2 : (Fin k → ZMod 2) × (Fin r → ZMod 2),
        w0.1 = w1.1 ∧ send w1 = send w2 ∧ tag w2 = tag w0 ∧ ¬(w0 = w1 ∧ w1 = w2))).card ≤
      errors k r c send tag := by
    unfold errors
    refine Finset.card_le_card_of_surjOn
      (fun v : Fin 3 → ((Fin k → ZMod 2) × (Fin r → ZMod 2)) => v 0) ?_
    intro w0 hw0
    rw [Finset.mem_coe, Finset.mem_filter] at hw0
    obtain ⟨_, w1, w2, h1, h2, h3, h4⟩ := hw0
    refine ⟨![w0, w1, w2], ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h1, h2, h3, h4⟩
  have hsplit := Finset.card_le_card_sdiff_add_card
    (s := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
      (fun w => Fits k r s send w.1))
    (t := (Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
      (fun w0 => ∃ w1 w2 : (Fin k → ZMod 2) × (Fin r → ZMod 2),
        w0.1 = w1.1 ∧ send w1 = send w2 ∧ tag w2 = tag w0 ∧ ¬(w0 = w1 ∧ w1 = w2)))
  have hgood : (((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
      (fun w => Fits k r s send w.1)) \
      ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
      (fun w0 => ∃ w1 w2 : (Fin k → ZMod 2) × (Fin r → ZMod 2),
        w0.1 = w1.1 ∧ send w1 = send w2 ∧ tag w2 = tag w0 ∧ ¬(w0 = w1 ∧ w1 = w2)))).card ≤
      2 ^ c * ∑ j ∈ Finset.range (min k (k+s-r) + 1), k.choose j := by
    rw [Finset.card_eq_sum_card_fiberwise (f := tag) (t := Finset.univ)
      (fun w _ => Finset.mem_univ (tag w))]
    have hτ : ∀ τ : Fin c → Bool,
        ((((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
          (fun w => Fits k r s send w.1)) \
          ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
          (fun w0 => ∃ w1 w2 : (Fin k → ZMod 2) × (Fin r → ZMod 2),
            w0.1 = w1.1 ∧ send w1 = send w2 ∧ tag w2 = tag w0 ∧ ¬(w0 = w1 ∧ w1 = w2)))).filter
          (fun w => tag w = τ)).card ≤
        ∑ j ∈ Finset.range (min k (k+s-r) + 1), k.choose j := by
      intro τ
      generalize hE : ((((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
          (fun w => Fits k r s send w.1)) \
          ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → ZMod 2))).filter
          (fun w0 => ∃ w1 w2 : (Fin k → ZMod 2) × (Fin r → ZMod 2),
            w0.1 = w1.1 ∧ send w1 = send w2 ∧ tag w2 = tag w0 ∧ ¬(w0 = w1 ∧ w1 = w2)))).filter
          (fun w => tag w = τ)) = E
      have hprop : ∀ w ∈ E, Fits k r s send w.1 ∧ tag w = τ ∧
          ∀ w1 w2 : (Fin k → ZMod 2) × (Fin r → ZMod 2),
            w.1 = w1.1 → send w1 = send w2 → tag w2 = tag w → (w = w1 ∧ w1 = w2) := by
        intro w hw
        rw [← hE, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hw
        obtain ⟨⟨⟨_, hfit⟩, hnb⟩, htag⟩ := hw
        refine ⟨hfit, htag, fun w1 w2 h1 h2 h3 => ?_⟩
        by_contra hcon
        exact hnb ⟨Finset.mem_univ _, w1, w2, h1, h2, h3, hcon⟩
      have hval : ∀ w ∈ E, ∀ w' ∈ E,
          fib k r send w.1 (send w') = if w = w' then 1 else 0 := by
        intro w hw w' hw'
        obtain ⟨_, htw, hw3⟩ := hprop w hw
        obtain ⟨_, htw', _⟩ := hprop w' hw'
        unfold fib
        by_cases heq : w = w'
        · subst heq
          rw [if_pos rfl, Finset.sum_eq_single w.2]
          · rw [if_pos rfl]
          · intro z _ hz
            rw [if_neg]
            intro hs
            have h5 := hw3 (w.1, z) w rfl hs rfl
            exact hz (congrArg Prod.snd h5.1).symm
          · intro h
            exact absurd (Finset.mem_univ _) h
        · rw [if_neg heq]
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [if_neg]
          intro hs
          have h5 := hw3 (w.1, z) w' rfl hs (htw'.trans htw.symm)
          exact heq (h5.1.trans h5.2)
      have hli : LinearIndependent (ZMod 2) (fun w : E => fib k r send w.1.1) := by
        rw [linearIndependent_iff']
        intro S g hsum w0 hw0
        have h1 := congrFun hsum (send w0.1)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
        rw [Finset.sum_eq_single w0] at h1
        · rw [hval w0.1 w0.2 w0.1 w0.2, if_pos rfl, mul_one] at h1
          exact h1
        · intro w _ hne
          rw [hval w.1 w.2 w0.1 w0.2, if_neg (fun h => hne (Subtype.ext h)), mul_zero]
        · intro h
          exact absurd hw0 h
      have hmem : ∀ w : E, fib k r send w.1.1 ∈ LowDeg k (min k (k + s - r)) :=
        fun w => fib_mem k r s send w.1.1 (hprop w.1 w.2).1
      have h6 := lowDeg_card_le k (min k (k + s - r)) (fun w : E => fib k r send w.1.1) hmem hli
      rw [Fintype.card_coe] at h6
      exact h6
    refine (Finset.sum_le_sum fun τ _ => hτ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hc : Fintype.card (Fin c → Bool) = 2 ^ c := by simp
    rw [hc]
  rw [← hWc_card]
  omega

/-- Binomial tail bound: the first `a+1` binomial coefficients of `k` sum to at most
`2^k * exp (-2k/B^2)` once `a` lies below `k/2` by at least `k/B`. -/
theorem binom_tail (k a B : ℕ) (hak : a ≤ k) (hB : 0 < B)
    (h : (a:ℝ) - (k:ℝ)/2 ≤ -(k:ℝ)/(B:ℝ)) :
    ∑ j ∈ Finset.range (a+1), (k.choose j : ℝ) ≤
      (2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2) := by
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 4/(B:ℝ) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have h1 : ∑ j ∈ Finset.range (a+1), (k.choose j : ℝ) ≤
      ∑ j ∈ Finset.range (a+1), (k.choose j : ℝ) * Real.exp (θ * ((a:ℝ) - (j:ℝ))) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hja : (j:ℝ) ≤ (a:ℝ) := by exact_mod_cast hj'
    have hone : 1 ≤ Real.exp (θ * ((a:ℝ) - (j:ℝ))) :=
      Real.one_le_exp (mul_nonneg hθ0 (by linarith))
    have hc : (0:ℝ) ≤ (k.choose j : ℝ) := Nat.cast_nonneg _
    exact le_mul_of_one_le_right hc hone
  have h2 :
      ∑ j ∈ Finset.range (a+1), (k.choose j : ℝ) * Real.exp (θ * ((a:ℝ) - (j:ℝ))) ≤
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) * Real.exp (θ * ((a:ℝ) - (j:ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (by omega)
    · intro j _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have h3 :
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) * Real.exp (θ * ((a:ℝ) - (j:ℝ))) =
      Real.exp (θ * (a:ℝ)) * (Real.exp (-θ) + 1)^k := by
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, ← Real.exp_nat_mul,
      show θ * ((a:ℝ) - (j:ℝ)) = θ * (a:ℝ) + (j:ℝ) * (-θ) by ring, Real.exp_add]
    ring
  have h4 : Real.exp (-θ) + 1 ≤ 2 * Real.exp (-(θ/2) + (θ/2)^2/2) := by
    have hc := Real.cosh_le_exp_half_sq (θ/2)
    rw [Real.cosh_eq] at hc
    have e1 : Real.exp (-θ) = Real.exp (-(θ/2)) * Real.exp (-(θ/2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(θ/2)) * Real.exp (θ/2) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have e3 : Real.exp (-(θ/2) + (θ/2)^2/2) =
        Real.exp (-(θ/2)) * Real.exp ((θ/2)^2/2) := Real.exp_add _ _
    have hm := mul_le_mul_of_nonneg_left hc (Real.exp_pos (-(θ/2))).le
    rw [e3, e1]
    linarith
  have h5 : θ * (a:ℝ) + (k:ℝ) * (-(θ/2) + (θ/2)^2/2) ≤ -(2*(k:ℝ))/(B:ℝ)^2 := by
    have hmul : θ * ((a:ℝ) - (k:ℝ)/2) ≤ θ * (-(k:ℝ)/(B:ℝ)) :=
      mul_le_mul_of_nonneg_left h hθ0
    have e : θ * (-(k:ℝ)/(B:ℝ)) + (k:ℝ) * θ^2/8 = -(2*(k:ℝ))/(B:ℝ)^2 := by
      rw [hθ]; field_simp; ring
    linarith
  calc ∑ j ∈ Finset.range (a+1), (k.choose j : ℝ)
      ≤ Real.exp (θ * (a:ℝ)) * (Real.exp (-θ) + 1)^k := by
        rw [← h3]; exact h1.trans h2
    _ ≤ Real.exp (θ * (a:ℝ)) * (2 * Real.exp (-(θ/2) + (θ/2)^2/2))^k := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (by positivity) h4 k
    _ = (2:ℝ)^k * Real.exp (θ * (a:ℝ) + (k:ℝ) * (-(θ/2) + (θ/2)^2/2)) := by
        rw [mul_pow, ← Real.exp_nat_mul, Real.exp_add]; ring
    _ ≤ (2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr h5

/-- Exponent bookkeeping in the naturals. -/
theorem expo_arith (A B k c : ℕ) (hB : 3 ≤ B) (hk1 : 2^(2*B*B*A) ≤ k)
    (hk2 : 2*B*B*(A+1) ≤ k) (hc : c ≤ k+A*(k/(max 1 (Nat.log2 k))+1)) :
    c + 1 + k/(B*B) ≤ k + 2*k/(B*B) := by
  have hlog : 2*B*B*A ≤ Nat.log2 k := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by norm_num) hk1
  have hL : 2*B*B*A ≤ max 1 (Nat.log2 k) := le_trans hlog (le_max_right _ _)
  have hBB : 0 < 2*B*B := by positivity
  have hBB' : 0 < B*B := by positivity
  have h1 : A*(k/(max 1 (Nat.log2 k))) ≤ k/(2*B*B) := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · subst hA; simp
    · have hpos : 0 < 2*B*B*A := by positivity
      have hdiv : k/(max 1 (Nat.log2 k)) ≤ k/(2*B*B*A) := Nat.div_le_div_left hL hpos
      rw [Nat.le_div_iff_mul_le hBB]
      calc A*(k/(max 1 (Nat.log2 k))) * (2*B*B)
          ≤ A * (k/(2*B*B*A)) * (2*B*B) := by gcongr
        _ = (k/(2*B*B*A)) * (2*B*B*A) := by ring
        _ ≤ k := Nat.div_mul_le_self _ _
  have h2 : A+1 ≤ k/(2*B*B) := by
    rw [Nat.le_div_iff_mul_le hBB]
    calc (A+1)*(2*B*B) = 2*B*B*(A+1) := by ring
      _ ≤ k := hk2
  have h3 : 2*(k/(2*B*B)) ≤ k/(B*B) := by
    rw [Nat.le_div_iff_mul_le hBB']
    calc 2*(k/(2*B*B))*(B*B) = (k/(2*B*B))*(2*B*B) := by ring
      _ ≤ k := Nat.div_mul_le_self _ _
  have h4 : 2*(k/(B*B)) ≤ 2*k/(B*B) := by
    rw [Nat.le_div_iff_mul_le hBB']
    calc 2*(k/(B*B))*(B*B) = 2*((k/(B*B))*(B*B)) := by ring
      _ ≤ 2*k := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _)
  have h5 : A*(k/(max 1 (Nat.log2 k))+1) = A*(k/(max 1 (Nat.log2 k))) + A := by ring
  omega

/-- The real-number estimate behind the exponent count. -/
theorem real_est (B k c q m : ℕ) (hm : m = 2*k/(B*B))
    (hcq : c + 1 + q ≤ k + m) (hq : 1 + q ≤ 2*k) :
    (2:ℝ)^c * ((2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) ≤ (2:ℝ)^(2*k-1-q) := by
  have h2e : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hmle : (m:ℝ) ≤ 2*(k:ℝ)/(B:ℝ)^2 := by
    have h := Nat.cast_div_le (α := ℝ) (m := 2*k) (n := B*B)
    rw [← hm] at h
    push_cast at h
    rw [pow_two]
    exact h
  have h2m : (2:ℝ)^m ≤ Real.exp (2*(k:ℝ)/(B:ℝ)^2) := by
    calc (2:ℝ)^m ≤ (Real.exp 1)^m := pow_le_pow_left₀ (by norm_num) h2e m
      _ = Real.exp (m:ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp (2*(k:ℝ)/(B:ℝ)^2) := Real.exp_le_exp.mpr hmle
  have hpow : (2:ℝ)^(c+1+q) ≤ (2:ℝ)^(k+m) := pow_le_pow_right₀ (by norm_num) hcq
  have hsplit : (2:ℝ)^(2*k-1-q) * (2:ℝ)^(1+q) = (2:ℝ)^k * (2:ℝ)^k := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hexp : Real.exp (2*(k:ℝ)/(B:ℝ)^2) * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2) = 1 := by
    rw [← Real.exp_add]
    have h0 : 2*(k:ℝ)/(B:ℝ)^2 + -(2*(k:ℝ))/(B:ℝ)^2 = 0 := by ring
    rw [h0, Real.exp_zero]
  have hpos : (0:ℝ) < (2:ℝ)^(1+q) := by positivity
  rw [← mul_le_mul_iff_of_pos_right hpos, hsplit]
  calc (2:ℝ)^c * ((2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) * (2:ℝ)^(1+q)
      = (2:ℝ)^(c+1+q) * ((2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) := by
        rw [pow_add, pow_add, pow_add]; ring
    _ ≤ (2:ℝ)^(k+m) * ((2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (2:ℝ)^k * (2:ℝ)^k * ((2:ℝ)^m * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) := by
        rw [pow_add]; ring
    _ ≤ (2:ℝ)^k * (2:ℝ)^k *
          (Real.exp (2*(k:ℝ)/(B:ℝ)^2) * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right h2m (Real.exp_pos _).le
    _ = (2:ℝ)^k * (2:ℝ)^k := by rw [hexp, mul_one]

theorem claim2 (A B : ℕ) (hB : 3 ≤ B) : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ c s : ℕ,
    c ≤ k+A*(k/(max 1 (Nat.log2 k))+1) → 2*B*(s+1)+2*k ≤ B*k →
    ∀ (send : ((Fin k → ZMod 2) × (Fin (k-1) → ZMod 2)) → (Fin k → ZMod 2))
      (tag : ((Fin k → ZMod 2) × (Fin (k-1) → ZMod 2)) → Fin c → Bool),
      2 ^ (k-1) * cheap k (k-1) s send ≤ errors k (k-1) c send tag + 2^(2*k-1-k/(B*B)) := by
  refine ⟨2^(2*B*B*A) + 2*B*B*(A+1) + 2, ?_⟩
  intro k hK c s hc hs send tag
  have hpos0 : 0 < 2^(2*B*B*A) := by positivity
  have hk1 : 2^(2*B*B*A) ≤ k := by omega
  have hk2 : 2*B*B*(A+1) ≤ k := by omega
  have hk0 : 1 ≤ k := by omega
  have hBpos : 0 < B := by omega
  have hsk : s + 1 ≤ k := by nlinarith
  have hmin : min k (k+s-(k-1)) = s+1 := by
    have hsub : k+s-(k-1) = s+1 := by omega
    rw [hsub]; exact min_eq_right hsk
  have hc1 := claim1 k (k-1) c s send tag
  rw [hmin] at hc1
  have hBR : (0:ℝ) < (B:ℝ) := by exact_mod_cast hBpos
  have hsR : (2:ℝ)*(B:ℝ)*((s:ℝ)+1) + 2*(k:ℝ) ≤ (B:ℝ)*(k:ℝ) := by exact_mod_cast hs
  have hgap : ((s+1 : ℕ) : ℝ) - (k:ℝ)/2 ≤ -(k:ℝ)/(B:ℝ) := by
    have e : (-(k:ℝ)/(B:ℝ)) - (((s:ℝ)+1) - (k:ℝ)/2) =
        ((B:ℝ)*(k:ℝ) - (2*(B:ℝ)*((s:ℝ)+1) + 2*(k:ℝ)))/(2*(B:ℝ)) := by
      field_simp; ring
    have hnn : 0 ≤ ((B:ℝ)*(k:ℝ) - (2*(B:ℝ)*((s:ℝ)+1) + 2*(k:ℝ)))/(2*(B:ℝ)) :=
      div_nonneg (by linarith) (by positivity)
    push_cast
    linarith
  have htail := binom_tail k (s+1) B hsk hBpos hgap
  have hbook := expo_arith A B k c hB hk1 hk2 hc
  have hq : 1 + k/(B*B) ≤ 2*k := by
    have hle : k/(B*B) ≤ k := Nat.div_le_self _ _
    omega
  have hreal := real_est B k c (k/(B*B)) (2*k/(B*B)) rfl hbook hq
  have key : 2^c * ∑ j ∈ Finset.range (s+1+1), k.choose j ≤ 2^(2*k-1-k/(B*B)) := by
    have hR : ((2^c * ∑ j ∈ Finset.range (s+1+1), k.choose j : ℕ) : ℝ) ≤
        ((2^(2*k-1-k/(B*B)) : ℕ) : ℝ) := by
      push_cast
      calc (2:ℝ)^c * ∑ j ∈ Finset.range (s+1+1), (k.choose j : ℝ)
          ≤ (2:ℝ)^c * ((2:ℝ)^k * Real.exp (-(2*(k:ℝ))/(B:ℝ)^2)) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ ≤ (2:ℝ)^(2*k-1-k/(B*B)) := hreal
    exact_mod_cast hR
  exact le_trans hc1 (Nat.add_le_add_left key _)

end PEqualNP.Outside.L_pcx_276

theorem PEqualNP.Outside.L_pcx_276 : let F := ZMod 2
let Row := fun n : ℕ => Fin n → F
let statistics := fun (k r c s : ℕ) (send : (Row k × Row r) → Row k)
    (tag : (Row k × Row r) → Fin c → Bool) =>
  let W := Row k × Row r
  let fits := fun u : Row k =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin k → Fin (r+C.size)),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack r C ∧
      (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
      C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ s ∧
      ∀ (z : Row r) (j : Fin k),
        (C.wires (List.ofFn (fun i => decide (z i = 1)))).getD (out j).val false =
          decide (send (u,z) j = 1)
  let cheap := (@Finset.filter (Row k) fits (Classical.decPred _) Finset.univ).card
  let errors := (Finset.univ.filter (fun v : Fin 3 → W => (v 0).1 = (v 1).1 ∧
    send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧ ¬(v 0 = v 1 ∧ v 1 = v 2))).card
  (2^r * cheap, errors)
(∀ (k r c s : ℕ) (send : (Row k × Row r) → Row k) (tag : (Row k × Row r) → Fin c → Bool),
  let pair := statistics k r c s send tag
  pair.1 ≤ pair.2 + 2^c * ∑ j ∈ Finset.range (min k (k+s-r) + 1), k.choose j) ∧
∀ A B : ℕ, 3 ≤ B → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ c s : ℕ,
  c ≤ k+A*(k/(max 1 (Nat.log2 k))+1) → 2*B*(s+1)+2*k ≤ B*k →
  ∀ (send : (Row k × Row (k-1)) → Row k) (tag : (Row k × Row (k-1)) → Fin c → Bool),
    let pair := statistics k (k-1) c s send tag
    pair.1 ≤ pair.2 + 2^(2*k-1-k/(B*B)) := by
  intro F Row statistics
  exact ⟨fun k r c s send tag => PEqualNP.Outside.L_pcx_276.claim1 k r c s send tag,
    fun A B hB => PEqualNP.Outside.L_pcx_276.claim2 A B hB⟩
