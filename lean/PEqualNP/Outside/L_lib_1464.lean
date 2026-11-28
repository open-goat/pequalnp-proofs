import Mathlib
import PEqualNP.Defs

-- Private input copies for every output of a fault-tolerant decoder.
--
-- Bit i gets the wires W i gained at its step in the chain of sampled sets {0, ..., j - 1}. The circuit
-- for bit i is rewired: a read of a raw input outside W i becomes a read of the constant true if that
-- input is on at the lower end of the step and of the constant false otherwise; the same is done to the
-- output pointer. Reads of gate wires, operations and numbers of reads are unchanged.
-- Three quantities are computed along the gate list by the same kind of fold: wire values, delays and
-- signed occurrence counts. Each new entry depends on the earlier ones only through the wires the gate
-- reads, so one lemma (`Gf_remap`) transfers all three: every rewired wire equals the old wire on the
-- changed initial list. For values the changed list is the lower end of the step with the queried copy of
-- W i; for delays nothing changes because all raw inputs and constants have delay 0; for occurrences the
-- reads outside W i now count nothing.
-- Recovery on the whole cube: the rewired query agrees with the lower end of the step outside W i. If
-- i is in A the upper end differs from the query only by wires of W i lost in Y, a subset of the losses
-- admitted for the copy word; if i is not in A the lower end differs only by wires of W i gained in Y, a
-- subset of the allowed gains, because W i is disjoint from the copies of the other bits.

namespace PEqualNP.Outside.L_lib_1464

open PEqualNP.CircuitLowerBounds

theorem ifT {α : Type} (c : Prop) [Decidable c] (x y : α) (h : c) : (if c then x else y) = x := by
  simp [h]

theorem ifF {α : Type} (c : Prop) [Decidable c] (x y : α) (h : ¬ c) : (if c then x else y) = y := by
  simp [h]

theorem dec_true {p : Prop} {inst : Decidable p} (h : p) : @decide p inst = true := by
  simp [h]

theorem dec_false {p : Prop} {inst : Decidable p} (h : ¬ p) : @decide p inst = false := by
  simp [h]

theorem dec_congr {p q : Prop} {i1 : Decidable p} {i2 : Decidable q} (h : p ↔ q) :
    @decide p i1 = @decide q i2 := by
  by_cases hp : p
  · rw [dec_true hp, dec_true (h.1 hp)]
  · rw [dec_false hp, dec_false (fun hq => hp (h.2 hq))]

theorem difT {α : Type} (c : Prop) [Decidable c] (x : c → α) (y : ¬ c → α) (h : c) :
    dite c x y = x h := by
  simp [h]

theorem difF {α : Type} (c : Prop) [Decidable c] (x : c → α) (y : ¬ c → α) (h : ¬ c) :
    dite c x y = y h := by
  simp [h]

/-- A fold over the gate list in which each new entry is computed from the entries the gate reads. -/
def Gf {α : Type} (F : Gate → (ℕ → α) → α) (d : α) (gs : List Gate) (xs : List α) : List α :=
  gs.foldl (fun zs g => zs ++ [F g (fun j => zs.getD j d)]) xs

theorem Gf_snoc {α : Type} (F : Gate → (ℕ → α) → α) (d : α) (gs : List Gate) (g : Gate)
    (xs : List α) :
    Gf F d (gs ++ [g]) xs = Gf F d gs xs ++ [F g (fun j => (Gf F d gs xs).getD j d)] := by
  simp [Gf, List.foldl_append]

theorem Gf_len {α : Type} (F : Gate → (ℕ → α) → α) (d : α) (gs : List Gate) (xs : List α) :
    (Gf F d gs xs).length = xs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Gf]
  | append_singleton gs g ih => rw [Gf_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (V : List α) (e d : α) (i : ℕ) :
    (V ++ [e]).getD i d = if i = V.length then e else V.getD i d := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- A gate with its reads moved. -/
def remap (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

/-- Moving the reads of every gate moves the entries of the fold. -/
theorem Gf_remap {α : Type} (F : Gate → (ℕ → α) → α) (d : α) (ρ : ℕ → ℕ) (N : ℕ)
    (hnat : ∀ g v, F (remap ρ g) v = F g (fun j => v (ρ j)))
    (hcong : ∀ g v v', (∀ j ∈ g.inputs, v j = v' j) → F g v = F g v')
    (hρ : ∀ w, N ≤ w → ρ w = w) (hρlt : ∀ w, w < N → ρ w < N)
    (xsE xsD : List α) (hlE : xsE.length = N) (hlD : xsD.length = N)
    (hbase : ∀ w < N, xsE.getD (ρ w) d = xsD.getD w d) :
    ∀ gs : List Gate, (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ a ∈ g.inputs, a < N + j) →
      ∀ w < N + gs.length,
        (Gf F d (gs.map (remap ρ)) xsE).getD (ρ w) d = (Gf F d gs xsD).getD w d := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w hw
    exact hbase w (by simpa using hw)
  | append_singleton gs g ih =>
    intro hR w hw
    have ih' := ih (fun j g' hj a ha => hR j g' (by
        have hjl : j < gs.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hj
          simp at hj
        rw [List.getElem?_append_left hjl]
        exact hj) a ha)
    have hin : ∀ a ∈ g.inputs, a < N + gs.length := hR gs.length g (by simp)
    have eE : (Gf F d (gs.map (remap ρ) ++ [remap ρ g]) xsE).getD (ρ w) d =
        if ρ w = N + gs.length then
          F (remap ρ g) (fun j => (Gf F d (gs.map (remap ρ)) xsE).getD j d)
        else (Gf F d (gs.map (remap ρ)) xsE).getD (ρ w) d := by
      rw [Gf_snoc, getD_snoc, Gf_len, List.length_map, hlE]
    have eD : (Gf F d (gs ++ [g]) xsD).getD w d =
        if w = N + gs.length then F g (fun j => (Gf F d gs xsD).getD j d)
        else (Gf F d gs xsD).getD w d := by
      rw [Gf_snoc, getD_snoc, Gf_len, hlD]
    rw [List.map_append, List.map_singleton, eE, eD]
    by_cases hw2 : w = N + gs.length
    · have hρw : ρ w = N + gs.length := by rw [hρ w (by omega)]; exact hw2
      rw [ifT _ _ _ hρw, ifT _ _ _ hw2, hnat]
      apply hcong
      intro j hj
      exact ih' j (hin j hj)
    · have hw3 : w < N + gs.length := by
        simp only [List.length_append, List.length_singleton] at hw
        omega
      have hρw : ¬ ρ w = N + gs.length := by
        by_cases hwN : w < N
        · have h1 := hρlt w hwN
          omega
        · rw [hρ w (by omega)]
          exact hw2
      rw [ifF _ _ _ hρw, ifF _ _ _ hw2]
      exact ih' w hw3

/-! ### The three folds -/

/-- Wire values. -/
def Fw (g : Gate) (v : ℕ → Bool) : Bool := g.op.eval (g.inputs.map v)

theorem Fw_nat (ρ : ℕ → ℕ) (g : Gate) (v : ℕ → Bool) :
    Fw (remap ρ g) v = Fw g (fun j => v (ρ j)) := by
  show g.op.eval ((g.inputs.map ρ).map v) = g.op.eval (g.inputs.map fun j => v (ρ j))
  rw [List.map_map]
  rfl

theorem Fw_cong (g : Gate) (v v' : ℕ → Bool) (h : ∀ j ∈ g.inputs, v j = v' j) :
    Fw g v = Fw g v' := by
  unfold Fw
  rw [List.map_congr_left h]

open Classical in
/-- Delays with cost `c` for AND and `e` for OR. -/
noncomputable def Ft (c e : ℕ) (g : Gate) (v : ℕ → ℕ) : ℕ :=
  if g.op = GateOp.not then (g.inputs.head?.map v).getD 0
  else g.inputs.foldl (fun acc j => max acc (v j)) 0 + (if g.op = GateOp.and then c else e)

theorem Ft_nat (c e : ℕ) (ρ : ℕ → ℕ) (g : Gate) (v : ℕ → ℕ) :
    Ft c e (remap ρ g) v = Ft c e g (fun j => v (ρ j)) := by
  dsimp only [Ft, remap]
  rw [List.head?_map, Option.map_map, List.foldl_map]
  rfl

theorem Ft_cong (c e : ℕ) (g : Gate) (v v' : ℕ → ℕ) (h : ∀ j ∈ g.inputs, v j = v' j) :
    Ft c e g v = Ft c e g v' := by
  have e1 : g.inputs.head?.map v = g.inputs.head?.map v' := by
    rcases hgi : g.inputs with _ | ⟨a, t⟩
    · rfl
    · have h1 := h a (by rw [hgi]; exact List.mem_cons_self)
      simp [h1]
  have e2 : g.inputs.foldl (fun acc j => max acc (v j)) 0 =
      g.inputs.foldl (fun acc j => max acc (v' j)) 0 :=
    List.foldl_ext _ _ _ (fun acc j hj => by rw [h j hj])
  unfold Ft
  rw [e1, e2]

open Classical in
/-- Signed occurrence counts. -/
noncomputable def Fo (g : Gate) (v : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  if g.op = GateOp.not then
    (((g.inputs.head?.map v).getD (0, 0)).2, ((g.inputs.head?.map v).getD (0, 0)).1)
  else g.inputs.foldl (fun acc j => (acc.1 + (v j).1, acc.2 + (v j).2)) (0, 0)

theorem Fo_nat (ρ : ℕ → ℕ) (g : Gate) (v : ℕ → ℕ × ℕ) :
    Fo (remap ρ g) v = Fo g (fun j => v (ρ j)) := by
  dsimp only [Fo, remap]
  rw [List.head?_map, Option.map_map, List.foldl_map]
  rfl

theorem Fo_cong (g : Gate) (v v' : ℕ → ℕ × ℕ) (h : ∀ j ∈ g.inputs, v j = v' j) :
    Fo g v = Fo g v' := by
  have e1 : g.inputs.head?.map v = g.inputs.head?.map v' := by
    rcases hgi : g.inputs with _ | ⟨a, t⟩
    · rfl
    · have h1 := h a (by rw [hgi]; exact List.mem_cons_self)
      simp [h1]
  have e2 : g.inputs.foldl (fun acc j => (acc.1 + (v j).1, acc.2 + (v j).2)) (0, 0) =
      g.inputs.foldl (fun acc j => (acc.1 + (v' j).1, acc.2 + (v' j).2)) (0, 0) :=
    List.foldl_ext _ _ _ (fun acc j hj => by rw [h j hj])
  unfold Fo
  rw [e1, e2]

/-! ### The rewiring -/

/-- Where a read goes: raw inputs outside `Wi` go to the constant true (wire k + 1) if they are in `P`
and to the constant false (wire k) otherwise. -/
def rho (k : ℕ) (Wi P : Finset (Fin k)) (w : ℕ) : ℕ :=
  if h : w < k then
    (if (⟨w, h⟩ : Fin k) ∈ Wi then w else if (⟨w, h⟩ : Fin k) ∈ P then k + 1 else k)
  else w

theorem rho_ge (k : ℕ) (Wi P : Finset (Fin k)) (w : ℕ) (hw : k ≤ w) : rho k Wi P w = w := by
  unfold rho
  rw [difF _ _ _ (by omega)]

theorem rho_in (k : ℕ) (Wi P : Finset (Fin k)) (w : ℕ) (hw : w < k)
    (h : (⟨w, hw⟩ : Fin k) ∈ Wi) : rho k Wi P w = w := by
  unfold rho
  rw [difT _ _ _ hw, ifT _ _ _ h]

theorem rho_P (k : ℕ) (Wi P : Finset (Fin k)) (w : ℕ) (hw : w < k)
    (h : (⟨w, hw⟩ : Fin k) ∉ Wi) (hP : (⟨w, hw⟩ : Fin k) ∈ P) : rho k Wi P w = k + 1 := by
  unfold rho
  rw [difT _ _ _ hw, ifF _ _ _ h, ifT _ _ _ hP]

theorem rho_out (k : ℕ) (Wi P : Finset (Fin k)) (w : ℕ) (hw : w < k)
    (h : (⟨w, hw⟩ : Fin k) ∉ Wi) (hP : (⟨w, hw⟩ : Fin k) ∉ P) : rho k Wi P w = k := by
  unfold rho
  rw [difT _ _ _ hw, ifF _ _ _ h, ifF _ _ _ hP]

theorem rho_lt (k : ℕ) (Wi P : Finset (Fin k)) (w : ℕ) (hw : w < k + 2) :
    rho k Wi P w < k + 2 := by
  by_cases hk : w < k
  · by_cases h : (⟨w, hk⟩ : Fin k) ∈ Wi
    · rw [rho_in k Wi P w hk h]; omega
    · by_cases hP : (⟨w, hk⟩ : Fin k) ∈ P
      · rw [rho_P k Wi P w hk h hP]; omega
      · rw [rho_out k Wi P w hk h hP]; omega
  · rw [rho_ge k Wi P w (by omega)]; exact hw

theorem rho_bound (k : ℕ) (Wi P : Finset (Fin k)) (w m : ℕ) (hw : w < k + 2 + m) :
    rho k Wi P w < k + 2 + m := by
  by_cases hk : w < k + 2
  · have h1 := rho_lt k Wi P w hk
    omega
  · rw [rho_ge k Wi P w (by omega)]; exact hw

theorem ofFn_getD {α : Type} {k : ℕ} (f : Fin k → α) (tl : List α) (d : α) (w : ℕ) (hw : w < k) :
    (List.ofFn f ++ tl).getD w d = f ⟨w, hw⟩ := by
  rw [List.getD_append _ _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem ofFn_getD_right {α : Type} {k : ℕ} (f : Fin k → α) (tl : List α) (d : α) (j : ℕ) :
    (List.ofFn f ++ tl).getD (k + j) d = tl.getD j d := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The initial lists agree after the rewiring: inside `Wi` the entries agree, outside the new list
has the constants `c0` (at wire k) and `c1` (at wire k + 1). -/
theorem base_agree {α : Type} {k : ℕ} (Wi P : Finset (Fin k)) (fE fD : Fin k → α) (c0 c1 d : α)
    (h1 : ∀ x ∈ Wi, fE x = fD x) (h2 : ∀ x, x ∉ Wi → x ∈ P → fD x = c1)
    (h3 : ∀ x, x ∉ Wi → x ∉ P → fD x = c0) :
    ∀ w < k + 2, (List.ofFn fE ++ [c0, c1]).getD (rho k Wi P w) d =
      (List.ofFn fD ++ [c0, c1]).getD w d := by
  intro w hw
  by_cases hk : w < k
  · rw [ofFn_getD fD _ d w hk]
    by_cases h : (⟨w, hk⟩ : Fin k) ∈ Wi
    · rw [rho_in k Wi P w hk h, ofFn_getD fE _ d w hk]
      exact h1 _ h
    · by_cases hP : (⟨w, hk⟩ : Fin k) ∈ P
      · rw [rho_P k Wi P w hk h hP, ofFn_getD_right fE _ d 1, h2 _ h hP]
        rfl
      · rw [rho_out k Wi P w hk h hP, h3 _ h hP]
        have e := ofFn_getD_right fE [c0, c1] d 0
        rw [Nat.add_zero] at e
        rw [e]
        rfl
  · rw [rho_ge k Wi P w (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, w = k + j := ⟨w - k, by omega⟩
    rw [ofFn_getD_right, ofFn_getD_right]

theorem rb_of (N : ℕ) (C : Circuit)
    (h : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ x ∈ g.inputs, x < N + j) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N C := by
  intro j hj i hi
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hi
  exact h j _ (List.getElem?_eq_getElem hj) i hi

theorem rb_to (N : ℕ) (C : Circuit) (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C) :
    ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ x ∈ g.inputs, x < N + j := by
  intro j g hj a ha
  have hjl : j < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    simp at hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, hj]
    rfl
  exact hR j hjl a (by rw [e]; exact ha)

/-- The rewired circuit. -/
def rew (k : ℕ) (Wi P : Finset (Fin k)) (D : Circuit) : Circuit :=
  ⟨D.gates.map (remap (rho k Wi P)), rho k Wi P D.output⟩

theorem rew_valid (k : ℕ) (Wi P : Finset (Fin k)) (D : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo D)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + 2) D)
    (ho : D.output < k + 2 + D.size) :
    PEqualNP.MetaComplexity.FanInTwo (rew k Wi P D) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + 2) (rew k Wi P D) ∧
      (rew k Wi P D).output < k + 2 + (rew k Wi P D).size := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hF g0 hg0
    exact ⟨h1, by simpa [remap] using h2⟩
  · apply rb_of
    intro j g hg x hx
    have hg' : (D.gates.map (remap (rho k Wi P)))[j]? = some g := hg
    rw [List.getElem?_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact rho_bound k Wi P y j (rb_to (k + 2) D hR j g0 hg0 y hy)
  · show rho k Wi P D.output < k + 2 + (D.gates.map (remap (rho k Wi P))).length
    rw [List.length_map]
    exact rho_bound k Wi P D.output _ ho

theorem rew_shape (k : ℕ) (Wi P : Finset (Fin k)) (D : Circuit) :
    (rew k Wi P D).gates.map (fun h => (h.op, h.inputs.length)) =
      D.gates.map (fun h => (h.op, h.inputs.length)) := by
  show (D.gates.map (remap (rho k Wi P))).map (fun h => (h.op, h.inputs.length)) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro g _
  simp [remap]

/-- Every fold of the rewired circuit reads at its output what the old one reads there. -/
theorem rew_fold {α : Type} (F : Gate → (ℕ → α) → α) (d c0 c1 : α) (k : ℕ)
    (Wi P : Finset (Fin k)) (D : Circuit)
    (hnat : ∀ ρ g v, F (remap ρ g) v = F g (fun j => v (ρ j)))
    (hcong : ∀ g v v', (∀ j ∈ g.inputs, v j = v' j) → F g v = F g v')
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + 2) D)
    (ho : D.output < k + 2 + D.size) (fE fD : Fin k → α)
    (h1 : ∀ x ∈ Wi, fE x = fD x) (h2 : ∀ x, x ∉ Wi → x ∈ P → fD x = c1)
    (h3 : ∀ x, x ∉ Wi → x ∉ P → fD x = c0) :
    (Gf F d (rew k Wi P D).gates (List.ofFn fE ++ [c0, c1])).getD (rew k Wi P D).output d =
      (Gf F d D.gates (List.ofFn fD ++ [c0, c1])).getD D.output d :=
  Gf_remap F d (rho k Wi P) (k + 2) (hnat (rho k Wi P)) hcong
    (fun w hw => rho_ge k Wi P w (by omega)) (fun w hw => rho_lt k Wi P w hw)
    (List.ofFn fE ++ [c0, c1]) (List.ofFn fD ++ [c0, c1]) (by simp) (by simp)
    (base_agree Wi P fE fD c0 c1 d h1 h2 h3) D.gates (rb_to (k + 2) D hR) D.output ho

theorem rep_getD (m w : ℕ) : (List.replicate m (0 : ℕ)).getD w 0 = 0 := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    cases w with
    | zero => simp [List.replicate_succ]
    | succ w => simp [List.replicate_succ]

/-- Delays are unchanged. -/
theorem rew_delay (c e k : ℕ) (Wi P : Finset (Fin k)) (D : Circuit)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + 2) D)
    (ho : D.output < k + 2 + D.size) :
    (Gf (Ft c e) 0 (rew k Wi P D).gates (List.replicate (k + 2) 0)).getD (rew k Wi P D).output 0 =
      (Gf (Ft c e) 0 D.gates (List.replicate (k + 2) 0)).getD D.output 0 :=
  Gf_remap (Ft c e) 0 (rho k Wi P) (k + 2) (Ft_nat c e (rho k Wi P)) (Ft_cong c e)
    (fun w hw => rho_ge k Wi P w (by omega)) (fun w hw => rho_lt k Wi P w hw)
    (List.replicate (k + 2) 0) (List.replicate (k + 2) 0) (by simp) (by simp)
    (fun w _ => by rw [rep_getD, rep_getD]) D.gates (rb_to (k + 2) D hR) D.output ho

section
variable {k : ℕ} [DecidableEq (Fin k)]

/-- Recovery when the bit is in the set: the upper end of the step is close to the rewired query. -/
theorem in_case (P Q cA Y : Finset (Fin k)) (fault : Finset (Fin k) → Finset (Fin k) → Prop)
    (hher : ∀ L G L' G', fault L G → L' ⊆ L → G' ⊆ G → fault L' G') (hPQ : P ⊆ Q)
    (hW : Q \ P ⊆ cA) (hf : fault (cA \ Y) (Y \ cA)) :
    fault (Q \ (P ∪ (Y ∩ (Q \ P)))) ((P ∪ (Y ∩ (Q \ P))) \ Q) := by
  refine hher _ _ _ _ hf ?_ ?_
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx ⊢
    have hxP : x ∉ P := fun h => hx.2 (Or.inl h)
    exact ⟨hW (Finset.mem_sdiff.2 ⟨hx.1, hxP⟩), fun hxY => hx.2 (Or.inr ⟨hxY, hx.1, hxP⟩)⟩
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx
    rcases hx.1 with h | h
    · exact absurd (hPQ h) hx.2
    · exact absurd h.2.1 hx.2

/-- Recovery when the bit is not in the set: the lower end of the step is close to the query. -/
theorem out_case (P Q cA Y : Finset (Fin k)) (fault : Finset (Fin k) → Finset (Fin k) → Prop)
    (hher : ∀ L G L' G', fault L G → L' ⊆ L → G' ⊆ G → fault L' G')
    (hW : ∀ x ∈ Q \ P, x ∉ cA) (hf : fault (cA \ Y) (Y \ cA)) :
    fault (P \ (P ∪ (Y ∩ (Q \ P)))) ((P ∪ (Y ∩ (Q \ P))) \ P) := by
  refine hher _ _ _ _ hf ?_ ?_
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx
    exact absurd (Or.inl hx.1) hx.2
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx.1 with h | h
    · exact absurd h hx.2
    · exact ⟨h.1, hW x (Finset.mem_sdiff.2 h.2)⟩

/-- The steps of a chain gain disjoint sets of wires. -/
theorem step_disj (A0 A1 B C : Finset (Fin k)) (h : A1 ⊆ B) : Disjoint (A1 \ A0) (C \ B) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  exact (Finset.mem_sdiff.1 hx2).2 (h (Finset.mem_sdiff.1 hx).1)

end

end PEqualNP.Outside.L_lib_1464

theorem PEqualNP.Outside.L_lib_1464 :
letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
  ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
let delay := fun (k c e : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let times := D.gates.foldl (fun (ts : List Nat) g =>
    let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
    ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((g.inputs.head?.map (fun j => ts.getD j 0)).getD 0)
      else mx+(if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then c else e)]) (List.replicate (k+2) 0)
  times.getD D.output 0
let occ := fun {k : Nat} (J : Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let xs := List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0,0),(0,0)]
  let ws := D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
    let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0,0)
      (acc.1+z.1,acc.2+z.2)) (0,0)
    let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
    zs ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then (h.2,h.1) else ab]) xs
  ws.getD D.output (0,0)
∀ (n k : Nat) (sample : Finset (Fin n) → Prop) (fault : Fin n → Finset (Fin k) → Finset (Fin k) → Prop),
  let pref := fun (j : Nat) => Finset.univ.filter (fun i : Fin n => i.val<j)
  (∀ j ≤ n, sample (pref j)) →
  (∀ i L G L' G', fault i L G → L' ⊆ L → G' ⊆ G → fault i L' G') →
  ∀ (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → PEqualNP.CircuitLowerBounds.Circuit),
    (∀ A B, sample A → sample B → A ⊆ B → g A ⊆ g B) → (∀ i, valid k (D i)) →
    (∀ A, sample A → ∀ Y i, fault i (g A \ Y) (Y \ g A) → run (D i) Y=decide (i ∈ A)) →
    let W := fun (i : Fin n) => g (pref (i.val+1)) \ g (pref i.val)
    let copy := fun (A : Finset (Fin n)) => A.biUnion W
    (∀ i j, i≠j → Disjoint (W i) (W j)) ∧
    ∃ E : Fin n → PEqualNP.CircuitLowerBounds.Circuit, (∀ i, valid k (E i) ∧
      ((E i).gates.map (fun h => (h.op,h.inputs.length)))=((D i).gates.map (fun h => (h.op,h.inputs.length))) ∧
      (∀ c e, delay k c e (E i)=delay k c e (D i)) ∧ (∀ J, occ J (E i)=occ (J ∩ W i) (D i)) ∧
      ∀ Y, run (E i) Y=run (D i) (g (pref i.val) ∪ (Y ∩ W i))) ∧
      ∀ A Y i, fault i (copy A \ Y) (Y \ copy A) → run (E i) Y=decide (i ∈ A) := by
  intro valid run delay occ n k sample fault pref hpref hher g D hmono hvalid hrec W copy
  let instK : DecidableEq (Fin k) := fun a b => Classical.propDecidable (a = b)
  -- the chain of sampled sets
  have hsub : ∀ a b : ℕ, a ≤ b → pref a ⊆ pref b := by
    intro a b hab x hx
    simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    omega
  have hgmono : ∀ a b : ℕ, a ≤ b → b ≤ n → g (pref a) ⊆ g (pref b) := fun a b hab hb =>
    hmono _ _ (hpref a (by omega)) (hpref b hb) (hsub a b hab)
  have hdis : ∀ i j : Fin n, i ≠ j → Disjoint (W i) (W j) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne (fun e => hij (Fin.ext e)) with h | h
    · exact PEqualNP.Outside.L_lib_1464.step_disj _ _ _ _ (hgmono (i.val + 1) j.val h (by omega))
    · exact (PEqualNP.Outside.L_lib_1464.step_disj _ _ _ _
        (hgmono (j.val + 1) i.val h (by omega))).symm
  have hWP : ∀ (i : Fin n) (x : Fin k), x ∈ W i → x ∉ g (pref i.val) := by
    intro i x hx
    have h := hx
    simp only [W, Finset.mem_sdiff] at h
    exact h.2
  have hrunAll : ∀ (i : Fin n) (Y : Finset (Fin k)),
      run (PEqualNP.Outside.L_lib_1464.rew k (W i) (g (pref i.val)) (D i)) Y =
        run (D i) (g (pref i.val) ∪ (Y ∩ W i)) := by
    intro i Y
    obtain ⟨hF, hR, ho⟩ := hvalid i
    refine PEqualNP.Outside.L_lib_1464.rew_fold PEqualNP.Outside.L_lib_1464.Fw false false true k
      _ _ (D i) PEqualNP.Outside.L_lib_1464.Fw_nat PEqualNP.Outside.L_lib_1464.Fw_cong hR ho _ _
      ?_ ?_ ?_
    · intro x hx
      refine PEqualNP.Outside.L_lib_1464.dec_congr ?_
      simp only [Finset.mem_union, Finset.mem_inter]
      exact ⟨fun h => Or.inr ⟨h, hx⟩, fun h => h.elim (fun hP => absurd hP (hWP i x hx)) (fun h => h.1)⟩
    · intro x _ hP
      refine PEqualNP.Outside.L_lib_1464.dec_true ?_
      simp only [Finset.mem_union]
      exact Or.inl hP
    · intro x hx hP
      refine PEqualNP.Outside.L_lib_1464.dec_false ?_
      simp only [Finset.mem_union, Finset.mem_inter]
      rintro (h | h)
      · exact hP h
      · exact hx h.2
  refine ⟨hdis, fun i => PEqualNP.Outside.L_lib_1464.rew k (W i) (g (pref i.val)) (D i), ?_, ?_⟩
  · intro i
    obtain ⟨hF, hR, ho⟩ := hvalid i
    refine ⟨PEqualNP.Outside.L_lib_1464.rew_valid k _ _ (D i) hF hR ho,
      PEqualNP.Outside.L_lib_1464.rew_shape k _ _ (D i), ?_, ?_, hrunAll i⟩
    · intro c e
      exact PEqualNP.Outside.L_lib_1464.rew_delay c e k _ _ (D i) hR ho
    · intro J
      refine PEqualNP.Outside.L_lib_1464.rew_fold PEqualNP.Outside.L_lib_1464.Fo (0, 0) (0, 0) (0, 0) k
        _ _ (D i) PEqualNP.Outside.L_lib_1464.Fo_nat PEqualNP.Outside.L_lib_1464.Fo_cong hR ho _ _
        ?_ ?_ ?_
      · intro x hx
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by simp only [Finset.mem_inter]; exact ⟨h1, hx⟩) h2
        · simp only [Finset.mem_inter] at h2
          exact absurd h2.1 h1
        · rfl
      · intro x hx _
        split_ifs with h2
        · simp only [Finset.mem_inter] at h2
          exact absurd h2.2 hx
        · rfl
      · intro x hx _
        split_ifs with h2
        · simp only [Finset.mem_inter] at h2
          exact absurd h2.2 hx
        · rfl
  · intro A Y i hf
    rw [hrunAll i Y]
    have hPQ : g (pref i.val) ⊆ g (pref (i.val + 1)) :=
      hgmono i.val (i.val + 1) (by omega) (by omega)
    by_cases hiA : i ∈ A
    · have hWc : W i ⊆ copy A := by
        intro x hx
        simp only [copy, Finset.mem_biUnion]
        exact ⟨i, hiA, hx⟩
      have h1 := hrec (pref (i.val + 1)) (hpref (i.val + 1) (by omega))
        (g (pref i.val) ∪ (Y ∩ W i)) i
        (PEqualNP.Outside.L_lib_1464.in_case _ _ _ _ (fault i) (hher i) hPQ hWc hf)
      rw [h1, PEqualNP.Outside.L_lib_1464.dec_true hiA]
      refine PEqualNP.Outside.L_lib_1464.dec_true ?_
      simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · have hWc : ∀ x ∈ W i, x ∉ copy A := by
        intro x hx hxc
        simp only [copy, Finset.mem_biUnion] at hxc
        obtain ⟨j, hjA, hxj⟩ := hxc
        have hij : i ≠ j := fun e => hiA (by rw [e]; exact hjA)
        exact Finset.disjoint_left.1 (hdis i j hij) hx hxj
      have h1 := hrec (pref i.val) (hpref i.val (by omega))
        (g (pref i.val) ∪ (Y ∩ W i)) i
        (PEqualNP.Outside.L_lib_1464.out_case _ _ _ _ (fault i) (hher i) hWc hf)
      rw [h1, PEqualNP.Outside.L_lib_1464.dec_false hiA]
      refine PEqualNP.Outside.L_lib_1464.dec_false ?_
      simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
